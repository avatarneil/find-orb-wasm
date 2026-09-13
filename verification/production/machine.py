"""GPL-2.0-or-later. Bounded structured WASM interpreter and symbolic FP DAG.

All integer control is exhausted in finite parameter domains. Floating values
remain universally symbolic; only proved commutations normalize expressions.
"""
from __future__ import annotations
from dataclasses import dataclass
import hashlib
import struct
from decoder import Unsupported

@dataclass(frozen=True)
class FP:
    node: int

@dataclass(frozen=True)
class IntParam:
    name: str

@dataclass(frozen=True)
class Affine:
    """Exact integer a*L+b, universally for the subinterval index 0<=L<=7."""
    a: int
    b: int = 0
    def add(self, value):
        return Affine(self.a+value.a,self.b+value.b) if isinstance(value,Affine) else Affine(self.a,self.b+value)
    def scale(self, value):return Affine(self.a*value,self.b*value)
    def bounds(self):return min(self.b,self.b+7*self.a),max(self.b,self.b+7*self.a)

@dataclass(frozen=True)
class Ptr:
    region: str
    offset: int | Affine = 0
    def add(self, delta):
        if isinstance(self.offset,Affine):return Ptr(self.region,self.offset.add(delta))
        if isinstance(delta,Affine):return Ptr(self.region,delta.add(self.offset))
        if type(delta) is not int: raise Unsupported('Non-affine offset')
        return Ptr(self.region,self.offset+delta)

class Graph:
    def __init__(self): self.nodes=[];self.table={};self.commutations=0
    def intern(self, op, *args):
        key=(op,*args)
        if key not in self.table:self.table[key]=len(self.nodes);self.nodes.append(key)
        return FP(self.table[key])
    def literal(self, value):return self.bits(int.from_bytes(struct.pack('<d',float(value)),'little'))
    def bits(self, bits):return self.intern('bits',bits)
    def symbol(self, name):return self.intern('input',name)
    def operation(self, name, left, right):
        if not isinstance(left,FP) or not isinstance(right,FP):raise Unsupported('FP operand type')
        a,b=left.node,right.node
        if name in ('add','mul') and a>b:a,b=b,a;self.commutations+=1
        if name not in ('add','sub','mul','div'):raise Unsupported('Unsupported FP operation')
        return self.intern(name,a,b)
    def expression(self, tree, variables):
        if isinstance(tree,str):return variables[tree]
        if tree[0]=='constant':return self.literal(tree[1])
        return self.operation(tree[0],self.expression(tree[1],variables),self.expression(tree[2],variables))
    def fingerprint(self, value):
        hashes=[]
        for node in self.nodes:
            key=node if node[0] in ('bits','input') else (node[0],hashes[node[1]],hashes[node[2]])
            hashes.append(hashlib.sha256(repr(key).encode()).hexdigest())
        return hashes[value.node]

class Memory:
    def __init__(self, graph, regions):
        self.graph,self.regions=graph,regions;self.cells={};self.reads=[];self.writes=[];self.readonly=set()
        self.owners={};self.coefficient_stride=None
    def key(self,ptr,width):
        if not isinstance(ptr,Ptr) or ptr.region not in self.regions:raise Unsupported('Invalid object pointer')
        low,high=self.regions[ptr.region]
        if isinstance(ptr.offset,Affine):
            lo,hi=ptr.offset.bounds()
            if ptr.region!='coefficient' or width!=8 or ptr.offset.a%8 or ptr.offset.b%8 or lo<low or hi+width>high:
                raise Unsupported('Invalid affine coefficient access')
            # This stronger per-block contract gives valid addresses for EACH
            # na in {1,2,4,8} after restricting L<na, not just for na=8.
            if ptr.offset.a!=self.coefficient_stride or not 0<=ptr.offset.b<self.coefficient_stride:
                raise Unsupported('Coefficient read leaves its selected subinterval')
            return ptr.region,ptr.offset
        if ptr.offset<low or ptr.offset+width>high or ptr.offset%width:raise Unsupported(f'Out-of-bounds/unaligned {ptr}/{width}')
        return ptr.region,ptr.offset
    def put(self,ptr,kind,value,initial=False):
        width=8 if kind in ('f64','i64') else 4;key=self.key(ptr,width)
        if not initial and ptr.region in self.readonly:raise Unsupported('Write to coefficient inputs')
        if kind=='i64':
            if type(value) is not int:raise Unsupported('Only constant i64 stores supported')
            # LLVM packs the adjacent cache counters; all other i64 stores in
            # this slice initialize a double with its exact bit representation.
            if key==('ephem',640):
                self.put(ptr,'i32',value&0xffffffff,initial);self.put(ptr.add(4),'i32',value>>32,initial);return
            value=self.graph.bits(value&((1<<64)-1));kind='f64'
        if kind=='f64' and not isinstance(value,FP):raise Unsupported('Non-FP double store')
        if kind=='i32' and not (type(value) is int or isinstance(value,IntParam)):raise Unsupported('Non-i32 integer store')
        if isinstance(ptr.offset,Affine):raise Unsupported('Coefficient input write')
        for byte in range(ptr.offset,ptr.offset+width):
            owner=self.owners.get((ptr.region,byte))
            if owner is not None and owner!=(key,kind):raise Unsupported('Overlapping typed accesses')
            self.owners[(ptr.region,byte)]=(key,kind)
        self.cells[key]=(kind,value)
        if not initial:self.writes.append((key,kind,value))
    def get(self,ptr,kind):
        key=self.key(ptr,8 if kind=='f64' else 4)
        if ptr.region=='coefficient' and isinstance(ptr.offset,Affine):
            if kind!='f64':raise Unsupported('Coefficient read type')
            self.reads.append((key,kind));return self.graph.symbol(f'coefficient_{ptr.offset.a}L+{ptr.offset.b}')
        if key not in self.cells or self.cells[key][0]!=kind:raise Unsupported(f'Uninitialized/type-punned read {key}/{kind}')
        self.reads.append((key,kind));return self.cells[key][1]
    def clone(self):
        other=Memory(self.graph,self.regions);other.cells=dict(self.cells);other.readonly=set(self.readonly)
        other.owners=dict(self.owners);other.coefficient_stride=self.coefficient_stride;return other

class Machine:
    def __init__(self,graph,memory,locals,tc,cold):
        self.graph,self.memory,self.locals=graph,memory,dict(locals);self.stack=[];self.tc=tc;self.cold=cold
        self.visited=set();self.edges=set();self.steps=0;self.loop_iterations={};self.cache_tests=0
        self.written_locals=set();self.entry_reads=set()
    @staticmethod
    def signed(x):return x-2**32 if x&2**31 else x
    def fp_compare(self,name,a,b):
        if not isinstance(a,FP) or not isinstance(b,FP):raise Unsupported('FP comparison types')
        # Explicit slice domain: tc is finite; cold cached tc differs, warm
        # cached tc is the same finite value. No arbitrary comparison guessed.
        old=self.graph.symbol('cached_tc')
        if a==b==self.tc:value=True
        elif {a,b}=={old,self.tc}:value=not self.cold
        else:raise Unsupported('Unproved floating branch condition')
        self.cache_tests+=1
        return int(value if name=='f64.eq' else not value)
    def sequence(self,ops,labels=()):
        for op in ops:
            self.steps+=1
            if self.steps>30000:raise Unsupported('Bounded execution limit')
            self.visited.add(op.start)
            name,args=op.name,op.args
            if name in ('block','loop','if'):
                height=len(self.stack)-(name=='if');arity=0 if op.result==-64 else 1
                if name=='if':
                    condition=self.stack.pop()
                    if type(condition) is not int:raise Unsupported('Nonconcrete branch')
                    body=op.body if condition else op.alternate;self.edges.add((op.start,bool(condition)))
                else:body=op.body
                label=(height,0 if name=='loop' else arity)
                while True:
                    if name=='loop':
                        self.loop_iterations[op.start]=self.loop_iterations.get(op.start,0)+1
                        if self.loop_iterations[op.start]>64:raise Unsupported('Loop bound exceeded')
                    signal=self.sequence(body,(label,*labels))
                    if signal is not None:
                        if signal>0:return signal-1
                        if name=='loop':continue
                    if len(self.stack)!=height+arity:raise Unsupported('Structured block stack mismatch')
                    break
                continue
            if name in ('br','br_if'):
                condition=1 if name=='br' else self.stack.pop()
                if type(condition) is not int:raise Unsupported('Symbolic integer control')
                self.edges.add((op.start,bool(condition)))
                if condition:
                    depth=args[0]
                    if depth>=len(labels):raise Unsupported('Branch escapes selected CFG slice')
                    height,arity=labels[depth];values=self.stack[-arity:] if arity else []
                    self.stack=self.stack[:height]+values;return depth
                continue
            stack=self.stack
            if name in ('i32.const','i64.const'):stack.append(args[0]&((1<<(32 if name=='i32.const' else 64))-1))
            elif name=='f64.const':stack.append(self.graph.bits(args[0]))
            elif name=='local.get':
                if args[0] not in self.locals:raise Unsupported('Uninitialized entry local '+str(args[0]))
                if args[0] not in self.written_locals:self.entry_reads.add(args[0])
                stack.append(self.locals[args[0]])
            elif name in ('local.set','local.tee'):
                self.written_locals.add(args[0])
                self.locals[args[0]]=stack[-1]
                if name=='local.set':stack.pop()
            elif name=='drop':stack.pop()
            elif name=='select':
                condition,b,a=stack.pop(),stack.pop(),stack.pop()
                if type(condition) is not int:raise Unsupported('Nonconcrete select')
                stack.append(a if condition else b)
            elif name in ('f64.load','i32.load'):
                stack.append(self.memory.get(stack.pop().add(args[1]),name[:3]))
            elif name in ('f64.store','i32.store','i64.store'):
                value,ptr=stack.pop(),stack.pop();self.memory.put(ptr.add(args[1]),name[:3],value)
            elif name in ('f64.add','f64.sub','f64.mul','f64.div'):
                b,a=stack.pop(),stack.pop();stack.append(self.graph.operation(name[4:],a,b))
            elif name in ('f64.eq','f64.ne'):
                b,a=stack.pop(),stack.pop();stack.append(self.fp_compare(name,a,b))
            elif name=='i32.eqz':
                value=stack.pop()
                if type(value) is not int:raise Unsupported('Unproved integer-parameter zero comparison')
                stack.append(int(value==0))
            elif name.startswith('i32.'):
                b,a=stack.pop(),stack.pop();operation=name[4:]
                if isinstance(a,IntParam) or isinstance(b,IntParam):
                    if a==b and operation in ('eq','ne'):stack.append(int(operation=='eq'));continue
                    raise Unsupported('Unproved integer-parameter operation')
                if isinstance(a,Ptr) and isinstance(b,Affine) and operation=='add':stack.append(a.add(b));continue
                if isinstance(b,Ptr) and isinstance(a,Affine) and operation=='add':stack.append(b.add(a));continue
                if isinstance(a,Ptr) and operation in ('add','sub') and type(b) is int:
                    stack.append(a.add(self.signed(b)*(1 if operation=='add' else -1)));continue
                if isinstance(b,Ptr) and operation=='add' and type(a) is int:
                    stack.append(b.add(self.signed(a)));continue
                if isinstance(a,Affine) or isinstance(b,Affine):
                    if operation=='add':value=a.add(b) if isinstance(a,Affine) else b.add(a)
                    elif operation=='sub' and isinstance(a,Affine) and type(b) is int:value=a.add(-b)
                    elif operation=='mul' and isinstance(a,Affine) and type(b) is int:value=a.scale(b)
                    elif operation=='mul' and isinstance(b,Affine) and type(a) is int:value=b.scale(a)
                    elif operation=='shl' and isinstance(a,Affine) and type(b) is int:value=a.scale(1<<(b&31))
                    else:raise Unsupported('Non-affine integer operation')
                    lo,hi=value.bounds()
                    if lo<0 or hi>=2**31:raise Unsupported('Affine integer arithmetic may wrap')
                    stack.append(value);continue
                if type(a) is not int or type(b) is not int:raise Unsupported('Pointer bit operation')
                if operation=='add':value=a+b
                elif operation=='sub':value=a-b
                elif operation=='mul':value=a*b
                elif operation=='and':value=a&b
                elif operation=='or':value=a|b
                elif operation=='shl':value=a<<(b&31)
                elif operation in ('eq','ne'):value=int((a==b) if operation=='eq' else (a!=b))
                elif operation[:2] in ('lt','le','gt','ge'):
                    x,y=(self.signed(a),self.signed(b)) if operation.endswith('_s') else (a,b)
                    value=int({'lt':x<y,'le':x<=y,'gt':x>y,'ge':x>=y}[operation[:2]])
                else:raise Unsupported('Unsupported integer op '+name)
                stack.append(value&0xffffffff)
            else:raise Unsupported('Unsupported executed opcode '+name)
        return None
    def execute(self,ops):
        if self.sequence(ops) is not None or self.stack:raise Unsupported('Incomplete slice exit')
