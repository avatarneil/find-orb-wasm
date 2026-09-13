"""GPL-2.0-or-later. Direct symbolic semantics for retained integer WASM code.

Floating values are raw bit patterns: only reinterpretation is supported.
There is no host floating-point arithmetic in this interpreter.
"""
from __future__ import annotations
from dataclasses import dataclass, replace
from pathlib import Path
import sys
import z3

sys.path.insert(1, str(Path(__file__).resolve().parents[1] / 'translation'))
from wasm import Module, Reader
from model import Unsupported

KINDS = {0x7f: ('i32', 32), 0x7e: ('i64', 64), 0x7c: ('f64', 64)}
OPS = {0x00:'unreachable', 0x01:'nop', 0x0c:'br', 0x0d:'br_if', 0x0f:'return',
       0x10:'call', 0x1a:'drop', 0x1b:'select', 0x20:'local.get', 0x21:'local.set',
       0x22:'local.tee', 0x23:'global.get', 0x24:'global.set', 0x29:'i64.load',
       0x37:'i64.store', 0x41:'i32.const', 0x42:'i64.const', 0x45:'i32.eqz',
       0x46:'i32.eq', 0x47:'i32.ne', 0x48:'i32.lt_s', 0x49:'i32.lt_u',
       0x4a:'i32.gt_s', 0x4b:'i32.gt_u', 0x4c:'i32.le_s', 0x4d:'i32.le_u',
       0x4e:'i32.ge_s', 0x4f:'i32.ge_u', 0x50:'i64.eqz', 0x51:'i64.eq',
       0x52:'i64.ne', 0x53:'i64.lt_s', 0x54:'i64.lt_u', 0x55:'i64.gt_s',
       0x56:'i64.gt_u', 0x57:'i64.le_s', 0x58:'i64.le_u', 0x59:'i64.ge_s',
       0x5a:'i64.ge_u', 0x67:'i32.clz', 0x6a:'i32.add', 0x6b:'i32.sub',
       0x6c:'i32.mul', 0x71:'i32.and', 0x72:'i32.or', 0x73:'i32.xor',
       0x74:'i32.shl', 0x75:'i32.shr_s', 0x76:'i32.shr_u', 0x79:'i64.clz',
       0x7c:'i64.add', 0x7d:'i64.sub', 0x7e:'i64.mul', 0x83:'i64.and',
       0x84:'i64.or', 0x85:'i64.xor', 0x86:'i64.shl', 0x87:'i64.shr_s',
       0x88:'i64.shr_u', 0xa7:'i32.wrap_i64', 0xac:'i64.extend_i32_s',
       0xad:'i64.extend_i32_u', 0xbd:'i64.reinterpret_f64', 0xbf:'f64.reinterpret_i64'}


@dataclass(frozen=True)
class Op:
    name: str
    args: tuple
    offset: int


def decode(reader: Reader) -> tuple[list[Op], int]:
    result = []
    while reader.remaining():
        offset = reader.offset + reader.pos
        code = reader.byte()
        if code in {0x0b, 0x05}:
            return result, code
        if code in {0x02, 0x04}:
            kind = reader.leb(True, 33)
            if kind not in {-64, -1, -2, -4}:
                raise Unsupported('Unsupported block signature')
            body, end = decode(reader)
            alternate = []
            if end == 0x05:
                if code != 0x04:
                    raise Unsupported('Else outside if')
                alternate, end = decode(reader)
            if end != 0x0b:
                raise Unsupported('Unterminated block')
            result.append(Op('block' if code == 0x02 else 'if', (kind, body, alternate), offset))
            continue
        if code not in OPS:
            raise Unsupported(f'Unsupported runtime opcode {code:02x} at {offset}')
        args = ()
        if code in {0x0c,0x0d,0x10,0x20,0x21,0x22,0x23,0x24}:
            args = (reader.leb(),)
        elif code in {0x29,0x37}:
            args = (reader.leb(), reader.leb())
            if args[0] > 3:
                raise Unsupported('Invalid i64 memory alignment')
        elif code in {0x41,0x42}:
            args = (reader.leb(True, 32 if code == 0x41 else 64),)
        result.append(Op(OPS[code], args, offset))
    raise Unsupported('Unterminated function')


def function(module: Module, index: int):
    if index < len(module.imports):
        raise Unsupported('Imported function body')
    local_index = index - len(module.imports)
    params, returns = module.types[module.function_types[local_index]]
    data, offset = module.bodies[local_index]
    reader = Reader(data, offset)
    locals_ = []
    for _ in range(reader.leb()):
        count, kind = reader.leb(), reader.byte()
        if count > 128 or kind not in KINDS:
            raise Unsupported('Invalid runtime local')
        locals_.extend([kind] * count)
    if any(kind not in KINDS for kind in params + returns):
        raise Unsupported('Unsupported runtime ABI')
    ops, end = decode(reader)
    reader.end()
    if end != 0x0b:
        raise Unsupported('Function ended with else')
    return params, returns, locals_, ops


@dataclass(frozen=True)
class Value:
    kind: str
    bits: z3.BitVecRef


def integer(number: int, width=32):
    return Value('i' + str(width), z3.BitVecVal(number, width))


def clz(value):
    width = value.size()
    result = z3.BitVecVal(width, width)
    for bit in range(width):
        result = z3.If(z3.Extract(bit, bit, value) == 1, z3.BitVecVal(width-1-bit, width), result)
    return z3.simplify(result)


@dataclass
class State:
    locals: list[Value]
    stack: list[Value]
    globals: list[Value]
    memory: z3.ArrayRef
    condition: z3.BoolRef
    jump: int | None = None
    returned: bool = False

    def fork(self):
        return replace(self, locals=list(self.locals), stack=list(self.stack), globals=list(self.globals))


class Machine:
    def __init__(self, module, precondition, memory_bytes, allowed_calls):
        self.module, self.precondition = module, precondition
        self.memory_bytes = memory_bytes
        self.allowed_calls = allowed_calls
        self.accesses = []
        self.visited = set()
        self.calls = set()
        self.cache = {}

    def possible(self, condition):
        condition = z3.simplify(condition)
        if z3.is_false(condition): return False
        solver = z3.Solver(); solver.set(timeout=30000)
        solver.add(self.precondition, condition)
        answer = solver.check()
        if answer == z3.unknown:
            raise Unsupported('Unknown path feasibility: ' + solver.reason_unknown())
        return answer == z3.sat

    def split(self, state, predicate):
        branches = []
        for choice, test in [(True, predicate), (False, z3.Not(predicate))]:
            condition = z3.simplify(z3.And(state.condition, test))
            if self.possible(condition):
                child = state.fork(); child.condition = condition
                branches.append((choice, child))
        return branches

    @staticmethod
    def pop(state, kind=None):
        if not state.stack:
            raise Unsupported('Operand-stack underflow')
        value = state.stack.pop()
        if kind is not None and value.kind != kind:
            raise Unsupported(f'Operand type mismatch: {value.kind}, expected {kind}')
        return value

    def invoke(self, index, arguments, memory, globals_, condition=z3.BoolVal(True), depth=0):
        if depth > 4:
            raise Unsupported('Unexpected recursion')
        if index not in self.cache:
            self.cache[index] = function(self.module, index)
        params, returns, locals_, ops = self.cache[index]
        if [value.kind for value in arguments] != [KINDS[k][0] for k in params]:
            raise Unsupported('Call argument ABI mismatch')
        start = State(list(arguments) + [Value(KINDS[k][0], z3.BitVecVal(0,KINDS[k][1])) for k in locals_],
                      [], list(globals_), memory, condition)
        states = self.sequence(ops, [start], index, depth)
        for state in states:
            if state.jump is None and not state.returned and len(state.stack) != len(returns):
                raise Unsupported('Function fallthrough stack-height mismatch')
            if state.jump is not None:
                # A br targeting the implicit function label is a return.
                if state.jump != 0:
                    raise Unsupported('Branch escapes function labels')
                state.jump = None
            if len(state.stack) < len(returns):
                raise Unsupported('Missing function result')
            state.stack = state.stack[-len(returns):] if returns else []
            if [v.kind for v in state.stack] != [KINDS[k][0] for k in returns]:
                raise Unsupported('Return ABI mismatch')
            state.returned = False
        return states

    def sequence(self, ops, states, index, depth):
        for op in ops:
            next_states = []
            for state in states:
                if state.jump is not None or state.returned:
                    next_states.append(state); continue
                self.visited.add((index, op.offset, op.name))
                next_states.extend(self.step(op, state, index, depth))
            states = next_states
            if len(states) > 512:
                raise Unsupported('Path explosion; no incomplete proof accepted')
        return states

    def step(self, op, state, index, depth):
        name, args = op.name, op.args
        if name in {'block','if'}:
            kind, body, alternate = args
            branches = [(True,state)] if name == 'block' else self.split(state, self.pop(state,'i32').bits != 0)
            height = len(state.stack)
            arity = 0 if kind == -64 else 1
            result = []
            for choose, branch in branches:
                for child in self.sequence(body if choose else alternate,[branch],index,depth):
                    if child.jump == 0:
                        values = child.stack[-arity:] if arity else []
                        child.stack = child.stack[:height] + values; child.jump = None
                    elif child.jump is not None:
                        child.jump -= 1
                    elif not child.returned and len(child.stack) != height + arity:
                        raise Unsupported('Block stack-height mismatch')
                    result.append(child)
            return result
        if name == 'br': state.jump = args[0]
        elif name == 'br_if':
            branches = self.split(state, self.pop(state,'i32').bits != 0)
            for choose, child in branches:
                if choose: child.jump = args[0]
            return [s for _,s in branches]
        elif name == 'return': state.returned = True
        elif name == 'unreachable':
            raise Unsupported('Reachable trap')
        elif name == 'nop': pass
        elif name == 'drop': self.pop(state)
        elif name == 'select':
            condition = self.pop(state,'i32').bits != 0
            right, left = self.pop(state), self.pop(state)
            if left.kind != right.kind: raise Unsupported('Select type mismatch')
            state.stack.append(Value(left.kind,z3.simplify(z3.If(condition,left.bits,right.bits))))
        elif name == 'local.get': state.stack.append(state.locals[args[0]])
        elif name in {'local.set','local.tee'}:
            value = self.pop(state,state.locals[args[0]].kind); state.locals[args[0]] = value
            if name == 'local.tee': state.stack.append(value)
        elif name == 'global.get': state.stack.append(state.globals[args[0]])
        elif name == 'global.set':
            if args[0] != 0: raise Unsupported('Unexpected non-stack global write')
            state.globals[args[0]] = self.pop(state,'i32')
        elif name == 'call':
            target = args[0]
            if target not in self.allowed_calls:
                raise Unsupported('Reachable unapproved/imported call ' + str(target))
            self.calls.add((index,target))
            params = self.module.types[self.module.function_types[target-len(self.module.imports)]][0]
            arguments = [self.pop(state) for _ in params][::-1]
            result = []
            for finished in self.invoke(target,arguments,state.memory,state.globals,state.condition,depth+1):
                child=state.fork(); child.memory=finished.memory; child.globals=finished.globals
                child.condition=finished.condition; child.stack += finished.stack; result.append(child)
            return result
        elif name in {'i64.load','i64.store'}:
            value = self.pop(state,'i64') if name.endswith('store') else None
            base = self.pop(state,'i32').bits
            address = z3.ZeroExt(32,base) + args[1]
            valid = z3.ULE(address+8,z3.BitVecVal(self.memory_bytes,64))
            self.accesses.append((state.condition, valid, name, index, op.offset, address))
            low = z3.Extract(31,0,address)
            if value is None:
                bits=z3.Concat(*[z3.Select(state.memory,low+i) for i in reversed(range(8))])
                state.stack.append(Value('i64',z3.simplify(bits)))
            else:
                for i in range(8):
                    state.memory=z3.Store(state.memory,low+i,z3.Extract(i*8+7,i*8,value.bits))
        elif name.endswith('.const'):
            width=32 if name.startswith('i32') else 64
            state.stack.append(integer(args[0],width))
        elif name in {'i64.reinterpret_f64','f64.reinterpret_i64'}:
            dest,src=name.split('.reinterpret_'); state.stack.append(Value(dest,self.pop(state,src).bits))
        elif name == 'i32.wrap_i64': state.stack.append(Value('i32',z3.Extract(31,0,self.pop(state,'i64').bits)))
        elif name in {'i64.extend_i32_u','i64.extend_i32_s'}:
            extend=z3.ZeroExt if name.endswith('_u') else z3.SignExt
            state.stack.append(Value('i64',extend(32,self.pop(state,'i32').bits)))
        elif name.endswith('.eqz'):
            kind=name.split('.')[0]; value=self.pop(state,kind).bits
            state.stack.append(Value('i32',z3.If(value==0,z3.BitVecVal(1,32),z3.BitVecVal(0,32))))
        elif name.endswith('.clz'):
            kind=name.split('.')[0]; state.stack.append(Value(kind,clz(self.pop(state,kind).bits)))
        else:
            kind,operation=name.split('.')
            right,left=self.pop(state,kind).bits,self.pop(state,kind).bits
            width=left.size()
            numeric={'add':lambda:left+right,'sub':lambda:left-right,'mul':lambda:left*right,
                     'and':lambda:left&right,'or':lambda:left|right,'xor':lambda:left^right,
                     'shl':lambda:left<<(right&(width-1)),
                     'shr_u':lambda:z3.LShR(left,right&(width-1)),
                     'shr_s':lambda:left>>(right&(width-1))}
            compare={'eq':lambda:left==right,'ne':lambda:left!=right,
                     'lt_s':lambda:left<right,'gt_s':lambda:left>right,'le_s':lambda:left<=right,'ge_s':lambda:left>=right,
                     'lt_u':lambda:z3.ULT(left,right),'gt_u':lambda:z3.UGT(left,right),
                     'le_u':lambda:z3.ULE(left,right),'ge_u':lambda:z3.UGE(left,right)}
            if operation in numeric: result=Value(kind,numeric[operation]())
            elif operation in compare: result=Value('i32',z3.If(compare[operation](),z3.BitVecVal(1,32),z3.BitVecVal(0,32)))
            else: raise Unsupported('Unimplemented integer operation ' + name)
            state.stack.append(Value(result.kind,z3.simplify(result.bits)))
        return [state]
