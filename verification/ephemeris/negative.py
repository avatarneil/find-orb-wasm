"""GPL-2.0-or-later. Mutation controls: verification must fail on defects."""
import copy
import json
import tempfile
from pathlib import Path
from check import check, check_data
from source import HERE, ROOT, SOURCE, arithmetic, checked


def run():
    baseline = json.loads((HERE / 'evidence/certificate.json').read_text())
    outcomes = []
    def rejects(name, operation):
        try:
            operation()
        except (ValueError, SyntaxError, KeyError, IndexError) as error:
            outcomes.append({'name': name, 'rejected': True, 'message': str(error)})
        else:
            raise ValueError('Unsound verifier accepted mutation: ' + name)
    changed = copy.deepcopy(baseline)
    changed['nodes'][changed['basis']['position'][2]]['error'] = '0/1'
    rejects('rounding-bound-set-to-zero', lambda: check(changed))
    changed = copy.deepcopy(baseline)
    changed['nodes'][changed['basis']['velocity'][3]]['polynomial'][0] += 1
    rejects('wrong-derivative-polynomial', lambda: check(changed))
    changed = copy.deepcopy(baseline)
    changed['nodes'][changed['basis']['position'][2]]['op'] = 'add'
    rejects('recurrence-subtraction-changed-to-addition', lambda: check(changed))
    changed = copy.deepcopy(baseline)
    p = changed['data']['profiles'][0]
    p['outputs']['position'] = changed['nodes'][p['outputs']['position']]['args'][0]
    rejects('coefficient-sum-skips-last-accumulation', lambda: check(changed))
    changed = copy.deepcopy(baseline)
    for node in changed['nodes']:
        if node['op'] == 'exact-scale':
            node['step'] = 16
            break
    rejects('wrong-velocity-time-scale', lambda: check(changed))
    changed = copy.deepcopy(baseline)
    changed['arithmetic']['underflowAllowance'] = '0/1'
    rejects('subnormal-error-ignored', lambda: check(changed))
    rejects('unsupported-function-call-in-arithmetic-parser', lambda: arithmetic('twot * hypot(p1, p2)', {'twot': 'twot', 'p1': 'p1', 'p2': 'p2'}))
    with tempfile.TemporaryDirectory(prefix='ephemeris-source-', dir=ROOT / '.cache') as folder:
        folder = Path(folder)
        cpp = (SOURCE / 'jpleph.cpp').read_text()
        for name, before, after in [
            ('actual-source-derivative-term-deleted', '+ *pc_ptr + *pc_ptr - vc_ptr[-2]', '+ *pc_ptr - vc_ptr[-2]'),
            ('actual-source-coefficient-loop-off-by-one', 'for( j = ncf; j; j--)', 'for( j = ncf - 1; j; j--)'),
            ('actual-source-endpoint-correction-deleted', 'if( l == na)', 'if( false)'),
        ]:
            if before not in cpp:
                raise ValueError('Mutation source context missing')
            (folder / 'jpleph.cpp').write_text(cpp.replace(before, after, 1))
            (folder / 'jpl_int.h').write_bytes((SOURCE / 'jpl_int.h').read_bytes())
            rejects(name, lambda: checked(folder))
    changed = copy.deepcopy(baseline)
    changed['data']['profiles'][0]['bounds'][0] = '0/1'
    data = (ROOT / '.cache/linux_p1550p2650.440').read_bytes()
    rejects('understated-real-data-coefficient-envelope', lambda: check_data(changed, data))
    changed = copy.deepcopy(baseline)
    changed['data']['profiles'][0]['name'] = 'nutations'
    for node in changed['nodes']:
        if node.get('profile') == 'mercury':
            node['profile'] = 'nutations'
    rejects('consistently-relabeled-planet-and-units', lambda: check_data(changed, data))
    report = {'schema': 1, 'controls': outcomes, 'acceptedBadCertificates': 0}
    (HERE / 'evidence/negative.json').write_text(json.dumps(report, indent=2) + '\n')
    print('Rejected', len(outcomes), 'deliberate mutations')
    return report


if __name__ == '__main__':
    run()
