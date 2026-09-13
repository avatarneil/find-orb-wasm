"""GPL-2.0-or-later. Execute unchanged production slice bytes in a small WASM host.

Used only for mutation witnesses. Positive universal validation is symbolic.
"""
import json
import struct
import subprocess
from pathlib import Path
from machine import Ptr,FP,Affine,IntParam

BASES={'ephem':1024,'coefficient':4096,'output':8192,'stack':12288}

def leb(value,signed=False):
    data=[]
    while True:
        byte=value&127;value>>=7
        done=(value==0 and not byte&64 or value==-1 and byte&64) if signed else value==0
        data.append(byte if done else byte|128)
        if done:return bytes(data)

def section(number,payload):return bytes([number])+leb(len(payload))+payload

def string(text):data=text.encode();return leb(len(data))+data

def evaluate(graph):
    values=[]
    for node in graph.nodes:
        op=node[0]
        if op=='bits':value=struct.unpack('<d',node[1].to_bytes(8,'little'))[0]
        elif op=='input':
            name=node[1]
            if name=='tc':value=.375
            elif name=='cached_tc':value=2.
            elif name=='vfac':value=.0625
            elif name.startswith('coefficient_'):value=(int(name.rsplit('_',1)[1])%7+1)/8
            else:value=.125
        else:
            a,b=values[node[1]],values[node[2]]
            value={'add':lambda:a+b,'sub':lambda:a-b,'mul':lambda:a*b,'div':lambda:a/b}[op]()
        values.append(value)
    return values

def wrapper(params,locals,entry,graph,slice_bytes,guard_bytes):
    values=evaluate(graph);prefix=b''
    for index,value in sorted(entry.items()):
        if isinstance(value,Ptr):value=BASES[value.region]+value.offset
        if isinstance(value,IntParam):value=1
        if isinstance(value,Affine):value=value.b
        if isinstance(value,FP):prefix+=b'\x44'+struct.pack('<d',values[value.node])
        else:prefix+=b'\x41'+leb(value,True)
        prefix+=b'\x21'+leb(index)
    kinds=params+locals
    declarations=leb(len(kinds))+b''.join(leb(1)+bytes([kind]) for kind in kinds)
    body=declarations+prefix+guard_bytes+b'\x04\x40'+slice_bytes+b'\x0b\x0b'
    return (b'\0asm\x01\0\0\0'+section(1,b'\x01\x60\x00\x00')+section(3,b'\x01\x00')+
      section(5,b'\x01\x00\x01')+section(7,b'\x02'+string('memory')+b'\x02\x00'+string('run')+b'\x00\x00')+
      section(10,b'\x01'+leb(len(body))+body))

def execute(out,name,original,mutated,memory):
    good=out/(name+'-original.wasm');bad=out/(name+'-mutated.wasm');good.write_bytes(original);bad.write_bytes(mutated)
    values=evaluate(memory.graph);cells=[]
    for (region,offset),(kind,value) in memory.cells.items():
        if kind=='f64':bits=struct.pack('<d',values[value.node]).hex()
        else:bits=int(1 if isinstance(value,IntParam) else value).to_bytes(4,'little').hex()
        cells.append({'address':BASES[region]+offset,'bytes':bits})
    fixture=out/(name+'-input.json');fixture.write_text(json.dumps(cells))
    script=Path(__file__).with_name('witness.mjs')
    result=subprocess.run(['node',str(script),str(good),str(bad),str(fixture)],text=True,capture_output=True,timeout=30)
    if result.returncode:raise RuntimeError(result.stdout+result.stderr)
    evidence=json.loads(result.stdout)
    if not evidence['different']:raise RuntimeError('Mutation did not change actual WASM execution')
    return evidence
