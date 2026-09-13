"""GPL-2.0-or-later. Export independently kernel-checkable exact obligations."""
import json
from fractions import Fraction as Q
from source import HERE


def q(value):
    value = Q(value)
    return f'(({value.numerator} : ℚ) / {value.denominator})'


def polynomial(values):
    terms = []
    for power, coefficient in enumerate(values):
        if coefficient:
            terms.append(f'({coefficient} : ℝ)' + (f' * x ^ {power}' if power else ''))
    return ' + '.join(terms) or '0'


def export(certificate):
    lines = ['import Mathlib.Data.Real.Basic', 'import Mathlib.Tactic.NormNum', 'import Mathlib.Tactic.Ring',
      '/- GPL-2.0-or-later. Generated from certificate.json; checked with lean --trust=0. -/',
      'set_option maxRecDepth 4096', 'set_option maxHeartbeats 800000', 'set_option exponentiation.threshold 2048',
      'set_option linter.unusedVariables false', 'namespace FindOrbEphemerisCertificates']
    names = []
    nodes = certificate['nodes']
    for index, node in enumerate(nodes):
        if 'polynomial' in node:
            op, args = node['op'], node['args']
            expression = str(node['value']) if op == 'literal' else 'x' if op == 'input-x' else f'p{args[0]} x ' + {'add': '+', 'sub': '-', 'mul': '*'}[op] + f' p{args[1]} x'
            lines.append(f'noncomputable def p{index} (x : ℝ) : ℝ := {expression}')
            name = f'polynomial_{index}'
            lines.append(f'theorem {name} (x : ℝ) : p{index} x = {polynomial(node["polynomial"])} := by')
            rewrites = [f'p{index}'] + [f'polynomial_{arg}' for arg in dict.fromkeys(args)]
            lines.append('  simp only [' + ', '.join(rewrites) + '] <;> ring')
            names.append(name)
        if node['op'] in ('add', 'sub', 'mul'):
            left, right = (nodes[arg] for arg in node['args'])
            ma, mb, ea, eb = (q(left['magnitude']), q(right['magnitude']), q(left['error']), q(right['error']))
            propagation = f'({ea} + {eb})' if node['op'] in ('add', 'sub') else f'({ma} * {eb} + {mb} * {ea} + {ea} * {eb})'
            magnitude, error = q(node['magnitude']), q(node['error'])
            bound = f'{propagation} + (1 : ℚ) / 2^53 * ({magnitude} + {propagation}) + (1 : ℚ) / 2^100'
            name = f'arithmetic_{index}'
            lines.append(f'theorem {name} : ({bound} ≤ {error}) ∧ ({magnitude} + {propagation} < (2 : ℚ)^1023) ∧ ({magnitude} + {error} < (2 : ℚ)^1023) := by norm_num')
            names.append(name)
    lines.append('theorem conservative_underflow : (1 : ℚ) / 2^1075 ≤ (1 : ℚ) / 2^100 := by norm_num')
    names.append('conservative_underflow')
    for name in names:
        lines.append('#print axioms ' + name)
    lines.append('end FindOrbEphemerisCertificates')
    (HERE / 'NumericalCertificates.lean').write_text('\n'.join(lines) + '\n')
    (HERE / 'evidence/lean-theorems.json').write_text(json.dumps(names, indent=2) + '\n')
    print('Exported', len(names), 'kernel obligations')


if __name__ == '__main__':
    export(json.loads((HERE / 'evidence/certificate.json').read_text()))
