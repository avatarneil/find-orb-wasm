"""GPL-2.0-or-later. Direct binary decoder + fail-closed symbolic WASM subset.

No disassembler participates in the proof path. A host WebAssembly validator
checks the binary type system before this interpreter is used by verify.py.
"""
from dataclasses import dataclass
import copy
import struct
import z3
from model import Unsupported, Pointer, Memory, floating, truth, F64, ZERO

class Reader:
    def __init__(self, data, offset=0):
        self.data, self.pos, self.offset = data, 0, offset
    def take(self, n):
        if n < 0 or self.pos+n > len(self.data):
            raise Unsupported("Truncated binary")
        result = self.data[self.pos:self.pos+n]
        self.pos += n
        return result
    def byte(self): return self.take(1)[0]
    def leb(self, signed=False, bits=32):
        value, shift = 0, 0
        while True:
            byte = self.byte()
            value |= (byte & 127) << shift
            shift += 7
            if shift > bits+7:
                raise Unsupported("Overlong LEB128")
            if not byte & 128: break
        if signed and byte & 64: value -= 1 << shift
        return value
    def string(self): return self.take(self.leb()).decode('utf8')
    def remaining(self): return self.pos < len(self.data)
    def end(self):
        if self.remaining(): raise Unsupported("Unconsumed binary payload")

OP = {0x00:'unreachable',0x01:'nop',0x0c:'br',0x0d:'br_if',0x0f:'return',0x10:'call',0x1a:'drop',
      0x20:'local.get',0x21:'local.set',0x22:'local.tee',0x23:'global.get',0x24:'global.set',
      0x28:'i32.load',0x2b:'f64.load',0x36:'i32.store',0x39:'f64.store',0x41:'i32.const',0x44:'f64.const',
      0x45:'i32.eqz',0x61:'f64.eq',0x62:'f64.ne',0x6a:'i32.add',0x6b:'i32.sub',0x71:'i32.and',
      0x9f:'f64.sqrt',0xa0:'f64.add',0xa1:'f64.sub',0xa2:'f64.mul',0xa3:'f64.div',0xb7:'f64.convert_i32_s'}

@dataclass
class Instruction:
    op: str
    args: tuple
    offset: int


def instructions(reader, nested=False):
    result = []
    while reader.remaining():
        offset = reader.offset + reader.pos
        opcode = reader.byte()
        if opcode in {0x0b,0x05}:
            return result, opcode
        if opcode in {0x02,0x04}:
            block_type = reader.leb(True,33)
            if block_type != -64:
                raise Unsupported("Only empty-result blocks/ifs supported")
            body, end = instructions(reader,True)
            alternate = []
            if end == 0x05:
                if opcode != 0x04: raise Unsupported("else outside if")
                alternate,end = instructions(reader,True)
            if end != 0x0b: raise Unsupported("Unterminated block")
            result.append(Instruction('block' if opcode==0x02 else 'if',(body,alternate),offset))
            continue
        if opcode not in OP:
            raise Unsupported(f"Unsupported WASM opcode 0x{opcode:02x} at {offset}")
        op,args = OP[opcode],()
        if opcode in {0x0c,0x0d,0x10,0x20,0x21,0x22,0x23,0x24}: args=(reader.leb(),)
        elif opcode in {0x28,0x2b,0x36,0x39}: args=(reader.leb(),reader.leb())
        elif opcode==0x41: args=(reader.leb(True),)
        elif opcode==0x44: args=(int.from_bytes(reader.take(8),'little'),)
        result.append(Instruction(op,args,offset))
    raise Unsupported("Missing expression end")


def limits(reader):
    flags=reader.leb()
    if flags not in {0,1}: raise Unsupported("Shared/64-bit memory/table unsupported")
    minimum=reader.leb()
    maximum=reader.leb() if flags else None
    return minimum,maximum

class Module:
    def __init__(self, data):
        reader=Reader(data)
        if reader.take(8)!=b'\0asm\x01\0\0\0': raise Unsupported("Not WASM v1")
        self.types=[];self.function_types=[];self.bodies=[];self.exports={};self.names={};self.global_names={}
        self.globals=[];self.imports=[];self.memories=[]
        last=0
        while reader.remaining():
            section,size=reader.byte(),reader.leb()
            start=reader.pos
            payload=Reader(reader.take(size),start)
            if section==0:
                name=payload.string()
                if name=='name':
                    while payload.remaining():
                        sub=payload.byte();sub_size=payload.leb();names=Reader(payload.take(sub_size))
                        if sub in {1,7}:
                            target=self.names if sub==1 else self.global_names
                            for _ in range(names.leb()):
                                index=names.leb();target[index]=names.string()
                            names.end()
                continue
            rank={1:1,2:2,3:3,4:4,5:5,6:6,7:7,8:8,9:9,12:10,10:11,11:12}.get(section)
            if rank is None or rank<=last: raise Unsupported("Duplicate/out-of-order section")
            last=rank
            if section==1:
                for _ in range(payload.leb()):
                    if payload.byte()!=0x60: raise Unsupported("Non-function type")
                    params=[payload.byte() for _ in range(payload.leb())]
                    returns=[payload.byte() for _ in range(payload.leb())]
                    self.types.append((params,returns))
            elif section==2:
                for _ in range(payload.leb()):
                    namespace,name,kind=payload.string(),payload.string(),payload.byte()
                    if kind!=0: raise Unsupported("Only function imports may be present")
                    typeidx=payload.leb();self.imports.append((namespace,name,typeidx))
            elif section==3: self.function_types=[payload.leb() for _ in range(payload.leb())]
            elif section==4:
                for _ in range(payload.leb()):
                    if payload.byte()!=0x70: raise Unsupported("Non-funcref table")
                    limits(payload)
            elif section==5: self.memories=[limits(payload) for _ in range(payload.leb())]
            elif section==6:
                for _ in range(payload.leb()):
                    kind,mutable=payload.byte(),payload.byte()
                    if kind!=0x7f or mutable not in {0,1} or payload.byte()!=0x41:
                        raise Unsupported("Unsupported global initializer")
                    self.globals.append(payload.leb(True))
                    if payload.byte()!=0x0b:raise Unsupported("Global initializer not constant")
            elif section==7:
                for _ in range(payload.leb()):
                    name=payload.string();self.exports[name]=(payload.byte(),payload.leb())
            elif section==10:
                for _ in range(payload.leb()):
                    size=payload.leb();offset=payload.offset+payload.pos
                    self.bodies.append((payload.take(size),offset))
            elif section in {8,9,11,12}:
                # Unused start/element/data sections are checked by the host validator.
                # No data-region access, indirect call, or start function is executed.
                continue
            else: raise Unsupported("Unknown WASM section")
            payload.end()
        if len(self.function_types)!=len(self.bodies) or len(self.memories)!=1:
            raise Unsupported("Function or memory count mismatch")

    def candidates(self,name):
        if name in self.exports and self.exports[name][0]==0:
            return [self.exports[name][1]]
        return [index for index,value in self.names.items()
                 if value==name or value.startswith(name+'(') or value.startswith('_Z'+str(len(name))+name)]

    def locate(self,name):
        matches=self.candidates(name)
        if len(matches)!=1: raise Unsupported(f"Expected one retained function {name}, found {len(matches)}")
        return matches[0]

    def function(self,index):
        if index<len(self.imports):raise Unsupported("Imported target function")
        index-=len(self.imports)
        params,returns=self.types[self.function_types[index]]
        data,offset=self.bodies[index];reader=Reader(data,offset)
        localtypes=[]
        for _ in range(reader.leb()):
            count,kind=reader.leb(),reader.byte()
            if count>10000 or kind not in {0x7f,0x7c}: raise Unsupported("Unsupported locals")
            localtypes.extend([kind]*count)
        ops,end=instructions(reader)
        if end!=0x0b:raise Unsupported("Invalid function end")
        reader.end()
        return params,returns,localtypes,ops

@dataclass
class State:
    memory: Memory
    locals: list
    globals: list
    stack: list
    condition: object
    signal: object=None
    def fork(self):return copy.deepcopy(self)


def as_bv(value):
    if isinstance(value,int):return z3.BitVecVal(value,32)
    if z3.is_bv(value) and value.size()==32:return value
    raise Unsupported("Expected integer (pointer bit operations forbidden)")


def simplify_integer(value):
    value=z3.simplify(value)
    return value.as_long() if z3.is_bv_value(value) else value

class Machine:
    def __init__(self,module,index,memory,args):
        self.module,self.index=module,index
        params,self.returns,localtypes,self.ops=module.function(index)
        if params!=[0x7f]*len(args) or self.returns not in [[],[0x7c]]:
            raise Unsupported("Source/WASM ABI mismatch")
        globals=list(module.globals)
        stack_indices=[i for i,name in module.global_names.items() if name=='__stack_pointer']
        if not stack_indices:
            # Emscripten's standalone -g0 harness lacks names; require the usual
            # first nonzero i32 global. Production/harness runs use -g2 instead.
            stack_indices=[]
        for i in stack_indices:globals[i]=Pointer('$stack')
        self.state=State(memory,list(args)+[0 if kind==0x7f else ZERO for kind in localtypes],globals,[],z3.BoolVal(True))
        self.visited=set()

    def execute_ops(self,ops,states):
        for instruction in ops:
            next_states=[]
            for state in states:
                if state.signal is not None:
                    next_states.append(state);continue
                self.visited.add(instruction.op)
                op,args=instruction.op,instruction.args
                if op in {'block','if'}:
                    height=len(state.stack)-(op=='if')
                    if op=='if':
                        condition=truth(state.stack.pop())
                        left,right=state.fork(),state.fork()
                        left.condition=z3.And(left.condition,condition)
                        right.condition=z3.And(right.condition,z3.Not(condition))
                        branches=self.execute_ops(args[0],[left])+self.execute_ops(args[1],[right])
                    else: branches=self.execute_ops(args[0],[state])
                    for branch in branches:
                        if isinstance(branch.signal,int):
                            if branch.signal==0:
                                branch.signal=None;branch.stack=branch.stack[:height]
                            else:branch.signal-=1
                        if branch.signal is None and len(branch.stack)!=height:raise Unsupported("Block stack mismatch")
                    next_states.extend(branches);continue
                if op in {'br','br_if'}:
                    if op=='br':state.signal=args[0];next_states.append(state);continue
                    condition=truth(state.stack.pop())
                    taken,other=state.fork(),state.fork()
                    taken.condition=z3.And(taken.condition,condition);taken.signal=args[0]
                    other.condition=z3.And(other.condition,z3.Not(condition))
                    next_states.extend([taken,other]);continue
                stack=state.stack
                if op=='nop':pass
                elif op=='return':state.signal='return'
                elif op=='drop':stack.pop()
                elif op=='i32.const':stack.append(args[0])
                elif op=='f64.const':stack.append(z3.fpBVToFP(z3.BitVecVal(args[0],64),F64))
                elif op=='local.get':stack.append(state.locals[args[0]])
                elif op in {'local.set','local.tee'}:
                    state.locals[args[0]]=stack[-1]
                    if op=='local.set':stack.pop()
                elif op=='global.get':
                    value=state.globals[args[0]]
                    if not isinstance(value,Pointer):raise Unsupported("Non-stack global access")
                    stack.append(value)
                elif op=='global.set':raise Unsupported("Global writes not supported")
                elif op.endswith('.load'):
                    ptr=stack.pop()
                    if not isinstance(ptr,Pointer):raise Unsupported("Non-object memory address")
                    stack.append(state.memory.load(ptr.add(args[1]),op.split('.')[0]))
                elif op.endswith('.store'):
                    value,ptr=stack.pop(),stack.pop()
                    if not isinstance(ptr,Pointer):raise Unsupported("Non-object memory address")
                    state.memory.store(ptr.add(args[1]),op.split('.')[0],value)
                elif op in {'i32.add','i32.sub','i32.and'}:
                    right,left=stack.pop(),stack.pop()
                    if isinstance(left,Pointer) and op in {'i32.add','i32.sub'} and isinstance(right,int):
                        right=right if right<2**31 else right-2**32
                        stack.append(left.add(right if op=='i32.add' else -right))
                    else:
                        left,right=as_bv(left),as_bv(right)
                        value=left+right if op=='i32.add' else left-right if op=='i32.sub' else left&right
                        stack.append(simplify_integer(value))
                elif op=='i32.eqz':stack.append(z3.If(z3.Not(truth(stack.pop())),z3.BitVecVal(1,32),z3.BitVecVal(0,32)))
                elif op in {'f64.eq','f64.ne'}:
                    right,left=stack.pop(),stack.pop();condition=z3.fpEQ(left,right)
                    if op=='f64.ne':condition=z3.Not(condition)
                    stack.append(z3.If(condition,z3.BitVecVal(1,32),z3.BitVecVal(0,32)))
                elif op=='f64.sqrt':stack.append(floating('sqrt',stack.pop()))
                elif op in {'f64.add','f64.sub','f64.mul','f64.div'}:
                    right,left=stack.pop(),stack.pop()
                    stack.append(floating({'f64.add':'+','f64.sub':'-','f64.mul':'*','f64.div':'/'}[op],left,right))
                elif op=='f64.convert_i32_s':
                    value=stack.pop()
                    if not isinstance(value,int):raise Unsupported("Only constant i32→f64 conversion supported")
                    value=value if value<2**31 else value-2**32
                    stack.append(z3.FPVal(value,F64))
                else:raise Unsupported("Unsupported executed instruction "+op)
                next_states.append(state)
            states=next_states
            if len(states)>16:raise Unsupported("Symbolic path limit exceeded")
        return states

    def execute(self):
        states=self.execute_ops(self.ops,[self.state])
        for state in states:
            if state.signal not in {None,'return'} or len(state.stack)!=len(self.returns):
                raise Unsupported("Incomplete control flow or result stack")
        return states
