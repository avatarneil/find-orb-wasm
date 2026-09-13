"""GPL-2.0-or-later. Fail-closed controls against actual mutated binaries."""
import copy
import json
import z3
from model import Source, Unsupported, initial_state, F64
from wasm import Module, Reader


def negative_controls(nodes, original_path, out, obligations, env):
    from verify import run, sha, equivalence, flatten, HERE
    data=original_path.read_bytes();module=Module(data);records=[]
    cases=[('add-to-sub','dot_product','f64.add',0xa1),
           ('multiply-to-add','dot_product','f64.mul',0xa0),
           ('invert-normalize-branch','normalize_vect3','f64.ne',0x61),
           ('wrong-cross-store','vector_cross_product','f64.store','offset8'),
           ('out-of-bounds-read','dot_product','f64.load','offset24'),
           ('unsupported-f64-min','dot_product','f64.add',0xa4),
           ('invalid-i32-add','dot_product','f64.add',0x6a)]
    for label,name,opcode,replacement in cases:
        _,_,_,ops=module.function(module.locate(name))
        instruction=next(op for op in flatten(ops) if op.op==opcode)
        mutated=bytearray(data)
        if isinstance(replacement,int):mutated[instruction.offset]=replacement
        else:
            reader=Reader(data[instruction.offset+1:]);reader.leb()
            position=instruction.offset+1+reader.pos
            if data[position]&128:raise Unsupported('Mutation requires one-byte offset')
            mutated[position]=8 if replacement=='offset8' else 24
        path=out/('mutation-'+label+'.wasm');path.write_bytes(mutated)
        validation=run(['node','-e','const fs=require("fs");console.log(WebAssembly.validate(fs.readFileSync(process.argv[1])))',path],env).strip()
        if label=='invalid-i32-add':
            if validation!='false':raise AssertionError('Invalid WASM passed host validation')
            records.append({'name':label,'result':'rejected-invalid-binary','sha256':sha(mutated)});continue
        if validation!='true':raise AssertionError('Expected type-valid binary mutation')
        try:
            target=Module(bytes(mutated));formula,inputs,_=equivalence(nodes[name],target,target.locate(name))
        except Unsupported as error:
            if label not in {'unsupported-f64-min','out-of-bounds-read'}:raise
            records.append({'name':label,'result':'rejected-unsupported-or-invalid-memory','reason':str(error),'sha256':sha(mutated)})
            continue
        if label in {'unsupported-f64-min','out-of-bounds-read'}:raise AssertionError('Unsafe mutation was accepted')
        parameters=[x['name'] for x in nodes[name]['inner'] if x['kind']=='ParmVarDecl']
        arrays=[[float(3*i+j+1) for j in range(3)] for i in range(len(parameters))]
        constraints=[inputs[param+'_'+str(j)]==z3.FPVal(arrays[i][j],F64)
                     for i,param in enumerate(parameters) for j in range(3)]
        record=obligations.check('negative-'+label,z3.And(formula,*constraints),expected='sat')
        witness=out/('mutation-'+label+'.inputs.json');witness.write_text(json.dumps(arrays)+'\n')
        replay=json.loads(run(['node',HERE/'replay-witness.mjs',original_path,path,name,witness],env))
        records.append({'name':label,'result':'concrete-counterexample','sha256':sha(mutated),'obligation':record['name'],
                        'inputArrays':arrays,'actualWasmReplay':replay})
    malformed=copy.deepcopy(nodes['dot_product'])
    def corrupt(node):
        if node.get('kind')=='BinaryOperator':node['opcode']='%';return True
        return any(corrupt(child) for child in node.get('inner',[]))
    if not corrupt(malformed):raise AssertionError('No source mutation target')
    memory,env0,_=initial_state(malformed)
    try:Source(malformed,memory,env0).execute()
    except Unsupported:records.append({'name':'unsupported-source-operator','result':'rejected-unsupported-ast'})
    else:raise AssertionError('Unsupported AST accepted')
    return records
