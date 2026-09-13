"""GPL-2.0-or-later. Instantiate every rounded DAG node in Lean."""
import json
from fractions import Fraction as Q
from source import HERE


def real(value):
    value = Q(value)
    return f'(({value.numerator} : ℝ) / {value.denominator})'


def export(certificate):
    nodes = certificate['nodes']
    lines = ['import BridgeSupport',
      '/- GPL-2.0-or-later. Generated conditional exact/rounded DAG semantics. -/',
      'set_option maxRecDepth 4096', 'set_option maxHeartbeats 1600000',
      'set_option exponentiation.threshold 2048', 'set_option linter.unusedVariables false',
      'set_option linter.unnecessarySeqFocus false',
      'namespace FindOrbEphemerisBridge', 'noncomputable section',
      'inductive CoefficientLimit : ℕ → ℝ → Prop where']
    for i, node in enumerate(nodes):
        if node['op'] == 'coefficient':
            lines.append(f'  | c{i} : CoefficientLimit {i} {real(node["magnitude"])}')
    lines += ['def CoefficientsBounded (c : ℕ → ℝ) : Prop := ∀ i b, CoefficientLimit i b → |c i| ≤ b']
    names = []
    for i, node in enumerate(nodes):
        op, args = node['op'], node['args']
        m, e = real(node['magnitude']), real(node['error'])
        if op in ('add', 'sub', 'mul'):
            operator = {'add': '+', 'sub': '-', 'mul': '*'}[op]
            exact = f'e{args[0]} x c {operator} e{args[1]} x c'
            rounded = f'rnd (r{args[0]} rnd x c {operator} r{args[1]} rnd x c)'
        elif op == 'literal':
            exact = rounded = str(node['value'])
        elif op == 'input-x':
            exact = rounded = 'x'
        elif op == 'coefficient':
            exact = rounded = f'c {i}'
        elif op == 'exact-scale':
            exact = rounded = real(Q(2 * node['na'], node['step']))
        else:
            raise ValueError('Unsupported bridge operation: ' + op)
        lines += [f'def e{i} (x : ℝ) (c : ℕ → ℝ) : ℝ := {exact}',
          f'def r{i} (rnd : ℝ → ℝ) (x : ℝ) (c : ℕ → ℝ) : ℝ := {rounded}']
        if 'polynomial' in node:
            coefficients = '[' + ', '.join(f'({v} : ℝ)' for v in node['polynomial']) + ']'
            lines += [f'theorem poly{i} (x : ℝ) (c : ℕ → ℝ) : e{i} x c = FindOrbEphemeris.evalCoefficients {coefficients} x := by',
              '  simp only [' + ', '.join([f'e{i}'] + [f'poly{a}' for a in dict.fromkeys(args)] + ['FindOrbEphemeris.evalCoefficients']) + '] <;> ring']
            names.append(f'poly{i}')
        lines.append(f'theorem mag{i} (x : ℝ) (c : ℕ → ℝ) (hx : |x| ≤ 1) (hc : CoefficientsBounded c) : |e{i} x c| ≤ {m} := by')
        if 'polynomial' in node:
            lines += [f'  rw [poly{i}]',
              f'  exact le_trans (FindOrbEphemeris.polynomial_l1_bound {coefficients} x hx) (by norm_num)']
        elif op == 'coefficient':
            lines.append(f'  exact hc {i} {m} CoefficientLimit.c{i}')
        elif op == 'exact-scale':
            lines.append(f'  norm_num [e{i}]')
        else:
            a, b = args
            if op in ('add', 'sub'):
                absolute = 'abs_add_le' if op == 'add' else 'abs_sub'
                lines += [f'  have h := le_trans ({absolute} (e{a} x c) (e{b} x c)) (add_le_add (mag{a} x c hx hc) (mag{b} x c hx hc))',
                  f'  exact le_trans h (by norm_num [e{i}])']
            else:
                lines += [f'  rw [e{i}, abs_mul]',
                  f'  have h := mul_le_mul (mag{a} x c hx hc) (mag{b} x c hx hc) (abs_nonneg (e{b} x c)) (by norm_num : (0 : ℝ) ≤ {real(nodes[a]["magnitude"])})',
                  '  exact le_trans h (by norm_num)']
        names.append(f'mag{i}')
        lines.append(f'theorem err{i} (rnd : ℝ → ℝ) (x : ℝ) (c : ℕ → ℝ) (hrnd : RoundingModel rnd) (hx : |x| ≤ 1) (hc : CoefficientsBounded c) : |r{i} rnd x c - e{i} x c| ≤ {e} := by')
        if op not in ('add', 'sub', 'mul'):
            lines.append(f'  simp [r{i}, e{i}]')
        else:
            a, b = args
            ma, mb = real(nodes[a]['magnitude']), real(nodes[b]['magnitude'])
            ea, eb = real(nodes[a]['error']), real(nodes[b]['error'])
            propagation = f'({ea} + {eb})' if op != 'mul' else f'({ma} * {eb} + {mb} * {ea} + {ea} * {eb})'
            inputs = f'(err{a} rnd x c hrnd hx hc) (err{b} rnd x c hrnd hx hc)'
            hp = f'FindOrb.{op}_error ' + (f'(mag{a} x c hx hc) (mag{b} x c hx hc) ' if op == 'mul' else '') + inputs
            lines += [f'  apply rounded_step rnd hrnd (propagation := {propagation}) (magnitude := {m})',
              f'  · exact {hp}', f'  · exact mag{i} x c hx hc', '  · norm_num', '  · norm_num']
        names.append(f'err{i}')
    outputs = []
    for profile in certificate['data']['profiles']:
        for kind, index in profile['outputs'].items():
            name = profile['name'].replace('-', '_') + '_' + kind + '_forward_error'
            lines += [f'theorem {name} (rnd : ℝ → ℝ) (x : ℝ) (c : ℕ → ℝ) (hrnd : RoundingModel rnd) (hx : |x| ≤ 1) (hc : CoefficientsBounded c) :',
              f'    |r{index} rnd x c - e{index} x c| ≤ {real(nodes[index]["error"])} := err{index} rnd x c hrnd hx hc']
            names.append(name)
            outputs.append({'profile': profile['name'], 'quantity': kind, 'node': index, 'theorem': name, 'error': nodes[index]['error']})
    lines += ['#print axioms ' + name for name in names]
    lines += ['end', 'end FindOrbEphemerisBridge']
    (HERE / 'RoundedDAG.lean').write_text('\n'.join(lines) + '\n')
    (HERE / 'evidence/bridge-theorems.json').write_text(json.dumps({'names': names, 'outputs': outputs}, indent=2) + '\n')
    print('Exported', len(names), 'instantiated DAG theorems')


if __name__ == '__main__':
    export(json.loads((HERE / 'evidence/certificate.json').read_text()))
