"""GPL-2.0-or-later. Structured decoder of the actual retained production body."""
from __future__ import annotations
from dataclasses import dataclass
import sys
from pathlib import Path
TRANSLATION = Path(__file__).resolve().parents[1] / 'translation'
if str(TRANSLATION) not in sys.path: sys.path.insert(0, str(TRANSLATION))
from wasm import Module, Reader, OP as BASE_OP
from model import Unsupported

OP = dict(BASE_OP)
OP.update({0x11:'call_indirect',0x1b:'select',0x29:'i64.load',0x2d:'i32.load8_u',0x37:'i64.store',0x3a:'i32.store8',0x42:'i64.const',
 0x46:'i32.eq',0x47:'i32.ne',0x48:'i32.lt_s',0x49:'i32.lt_u',0x4a:'i32.gt_s',0x4b:'i32.gt_u',0x4c:'i32.le_s',0x4d:'i32.le_u',0x4e:'i32.ge_s',0x4f:'i32.ge_u',
 0x50:'i64.eqz',0x51:'i64.eq',0x52:'i64.ne',0x63:'f64.lt',0x64:'f64.gt',0x65:'f64.le',0x66:'f64.ge',
 0x6c:'i32.mul',0x72:'i32.or',0x74:'i32.shl',0x75:'i32.shr_s',0x76:'i32.shr_u',0x83:'i64.and',0x86:'i64.shl',0x87:'i64.shr_s',0x88:'i64.shr_u',
 0xa7:'i32.wrap_i64',0xad:'i64.extend_i32_u',0xb8:'f64.convert_i32_u',0xbd:'i64.reinterpret_f64',0xbf:'f64.reinterpret_i64'})

@dataclass
class Op:
    name: str
    args: tuple
    start: int
    end: int
    body: list | None = None
    alternate: list | None = None
    result: int = -64


def decode(reader):
    result=[]
    while reader.remaining():
        start=reader.offset+reader.pos;code=reader.byte()
        if code in (0x05,0x0b):return result,code
        if code in (0x02,0x03,0x04):
            kind=reader.leb(True,33)
            if kind not in (-64,-1,-2,-4):raise Unsupported('Unsupported block type')
            body,end=decode(reader);alternate=[]
            if end==0x05:
                if code!=0x04:raise Unsupported('Else outside if')
                alternate,end=decode(reader)
            if end!=0x0b:raise Unsupported('Unterminated structured control')
            result.append(Op({2:'block',3:'loop',4:'if'}[code],(),start,reader.offset+reader.pos,body,alternate,kind));continue
        args=()
        if code==0xfc:
            sub=reader.leb()
            if sub==3:name='i32.trunc_sat_f64_u'
            elif sub==11:name='memory.fill';args=(reader.leb(),)
            else:raise Unsupported(f'Unsupported prefixed opcode {sub}')
        else:
            if code not in OP:raise Unsupported(f'Unsupported opcode {code:x} at {start}')
            name=OP[code]
            if code in (0x0c,0x0d,0x10,0x20,0x21,0x22,0x23,0x24):args=(reader.leb(),)
            elif code==0x11:args=(reader.leb(),reader.leb())
            elif code in (0x28,0x29,0x2b,0x2d,0x36,0x37,0x39,0x3a):args=(reader.leb(),reader.leb())
            elif code in (0x41,0x42):args=(reader.leb(True,64 if code==0x42 else 32),)
            elif code==0x44:args=(int.from_bytes(reader.take(8),'little'),)
        result.append(Op(name,args,start,reader.offset+reader.pos))
    raise Unsupported('Missing function end')


def function(module,index):
    ordinal=index-len(module.imports)
    if ordinal<0:raise Unsupported('Imported target')
    params,returns=module.types[module.function_types[ordinal]]
    data,offset=module.bodies[ordinal];reader=Reader(data,offset);locals=[]
    for _ in range(reader.leb()):
        count,kind=reader.leb(),reader.byte()
        if kind not in (0x7f,0x7e,0x7c) or count>1000:raise Unsupported('Unsupported local declaration')
        locals.extend([kind]*count)
    ops,end=decode(reader);reader.end()
    if end!=0x0b:raise Unsupported('Invalid function end')
    return params,returns,locals,ops


def flatten(ops):
    for op in ops:
        yield op
        if op.body is not None:yield from flatten(op.body);yield from flatten(op.alternate)


def has_store(ops,offset):
    return any(o.name in ('i32.store','i64.store') and o.args[1]==offset for o in flatten(ops))


def locate_slice(ops):
    # Find the unique actual CFG branch containing both interpolation cache
    # counters. No byte offset or function index is assumed by this selector.
    candidates=[]
    def visit(sequence,path=()):
        for i,op in enumerate(sequence):
            if op.name=='if':
                positions=[j for j,x in enumerate(op.body) if x.body is not None and has_store([x],640)]
                velocities=[j for j,x in enumerate(op.body) if x.body is not None and has_store([x],644)]
                if len(positions)==len(velocities)==1 and positions[0]<velocities[0]:
                    first,last=positions[0],velocities[0]
                    if first+2!=last or op.body[first+1].name!='local.set':raise Unsupported('Unexpected interpolation CFG boundaries')
                    # The guard is a single stack expression directly before
                    # this if. Validate its stack semantics when executing it.
                    guard=sequence[max(0,i-7):i]
                    candidates.append((op,op.body[:last+1],guard,path+(i,)))
            if op.body is not None:
                visit(op.body,path+(i,'body'));visit(op.alternate,path+(i,'else'))
    visit(ops)
    if len(candidates)!=1:raise Unsupported(f'Expected one semantic interpolation branch, found {len(candidates)}')
    return candidates[0]
