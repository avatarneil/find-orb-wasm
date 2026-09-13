"""GPL-2.0-or-later. Reviewed loop semantics of pinned interp source.

Recurrence arithmetic is parsed from the original C++, rather than restated as
ideal Chebyshev polynomials. Cache and descending-sum loops follow frozen source.
"""
from __future__ import annotations
import sys
from pathlib import Path
from machine import Graph, Memory, Ptr, FP, Affine, IntParam
EPHEMERIS=Path(__file__).resolve().parents[1]/'ephemeris'
if str(EPHEMERIS) not in sys.path:sys.path.append(str(EPHEMERIS))
from source import checked


def basis(graph,x,expressions):
    zero,one=graph.literal(0),graph.literal(1);twot=graph.operation('add',x,x)
    p,d=[one,x],[zero,one]
    for i in range(2,18):
        p.append(graph.expression(expressions['position'],{'twot':twot,'p1':p[i-1],'p2':p[i-2]}))
        d.append(graph.expression(expressions['velocity'],{'twot':twot,'d1':d[i-1],'d2':d[i-2],'p1':p[i-1]}))
    return p,d,twot


def initial(config,expressions,symbolic_geometry=False,body_override=None,ipt_pointer=1):
    ncf,ncm,na,l,flag,np,nv,cold=config
    graph=Graph();x=graph.symbol('tc');p,d,twot=basis(graph,x,expressions)
    memory=Memory(graph,{'ephem':(0,656),'coefficient':(0,8*ncf*ncm*na),'output':(0,8*ncm*flag),'stack':(0,160)})
    body=10 if ncm==2 else 13 if ncm==1 else 14 if flag==3 else 0
    if body_override is not None:body=body_override
    ipt_offset=168 if body==14 else 48+12*(body if body<10 else body+1)
    for i,value in enumerate((ipt_pointer,ncf,IntParam('na') if symbolic_geometry else na)):memory.put(Ptr('ephem',ipt_offset+4*i),'i32',value,True)
    for i in range(18):
        memory.put(Ptr('ephem',344+8*i),'f64',graph.symbol('old_p_'+str(i)) if symbolic_geometry or cold or i>=np else p[i],True)
        memory.put(Ptr('ephem',488+8*i),'f64',graph.symbol('old_d_'+str(i)) if symbolic_geometry or cold or i>=nv else d[i],True)
    # Both cache seeds are established by the actual initializer and invariant.
    memory.put(Ptr('ephem',344),'f64',p[0],True)
    memory.put(Ptr('ephem',352),'f64',graph.symbol('cached_tc') if symbolic_geometry or cold else x,True)
    memory.put(Ptr('ephem',488),'f64',d[0],True);memory.put(Ptr('ephem',496),'f64',d[1],True)
    memory.put(Ptr('ephem',632),'f64',graph.symbol('old_twot') if symbolic_geometry or cold else twot,True)
    memory.put(Ptr('ephem',640),'i32',IntParam('old_n_posn') if symbolic_geometry and cold else np,True)
    memory.put(Ptr('ephem',644),'i32',IntParam('old_n_vel') if symbolic_geometry and cold else nv,True)
    if symbolic_geometry:memory.coefficient_stride=8*ncf*ncm
    else:
        for i in range(ncf*ncm*na):memory.put(Ptr('coefficient',8*i),'f64',graph.symbol('coefficient_'+str(i)),True)
    for i in range(ncm*flag):
        memory.put(Ptr('output',8*i),'f64',graph.symbol('output_'+str(i)),True)
    for i in range(9):
        memory.put(Ptr('ephem',256+8*i),'f64',graph.symbol('sun_'+str(i)),True)
    memory.readonly.add('coefficient')
    scale=graph.symbol('vfac') if symbolic_geometry else graph.literal(na/16)
    locals={0:Ptr('ephem'),3:Ptr('output',-48*body if body<10 else 0),4:Ptr('output'),6:Ptr('ephem',ipt_offset),7:int(body==14),
      10:Ptr('ephem',256),12:IntParam('na') if symbolic_geometry else na,15:Ptr('stack'),17:body,19:flag,22:Ptr('ephem',488),26:Ptr('coefficient',-8*(ipt_pointer-1)),
      27:Ptr('ephem',344),30:Affine(1) if symbolic_geometry else l,33:Ptr('ephem',480),34:Ptr('ephem',336),42:scale,43:x,48:twot,
      46:graph.operation('mul',scale,graph.literal(0)),47:graph.operation('mul',scale,graph.operation('mul',scale,graph.literal(0)))}
    return graph,memory,locals,x,Ptr('ephem',256) if body==14 else Ptr('output')


def execute(memory,config,expressions,x,dest,symbolic_geometry=False):
    ncf,ncm,na,l,flag,np,nv,cold=config;g=memory.graph
    get=lambda base,i:memory.get(Ptr('ephem',base+8*i),'f64')
    put=lambda base,i,v:memory.put(Ptr('ephem',base+8*i),'f64',v)
    if cold:
        np=nv=2;memory.put(Ptr('ephem',640),'i32',2);memory.put(Ptr('ephem',644),'i32',2)
        put(344,1,x);memory.put(Ptr('ephem',632),'f64',g.operation('add',x,x))
    twot=memory.get(Ptr('ephem',632),'f64')
    for i in range(np,ncf):put(344,i,g.expression(expressions['position'],{'twot':twot,'p1':get(344,i-1),'p2':get(344,i-2)}))
    if np<ncf:memory.put(Ptr('ephem',640),'i32',ncf)
    zero=g.literal(0)
    def accumulate(base,component,low=0):
        total=zero
        for k in range(ncf-1,low-1,-1):
            b=memory.get(Ptr('stack',16+8*k),'f64') if base=='acceleration' else get(base,k)
            offset=Affine(8*ncf*ncm,8*(ncf*component+k)) if symbolic_geometry else 8*(ncf*(component+l*ncm)+k)
            cf=memory.get(Ptr('coefficient',offset),'f64')
            total=g.operation('add',total,g.operation('mul',b,cf))
        return total
    for component in range(ncm):memory.put(dest.add(8*component),'f64',accumulate(344,component))
    if flag<=1:return
    for i in range(nv,ncf):put(488,i,g.expression(expressions['velocity'],{'twot':twot,'d1':get(488,i-1),'d2':get(488,i-2),'p1':get(344,i-1)}))
    if nv<ncf:memory.put(Ptr('ephem',644),'i32',ncf)
    scale=g.symbol('vfac') if symbolic_geometry else g.literal(na/16)
    for component in range(ncm):memory.put(dest.add(8*(ncm+component)),'f64',g.operation('mul',accumulate(488,component,1),scale))
    if flag==3:
        for i in range(2):memory.put(Ptr('stack',16+8*i),'f64',zero)
        for i in range(2,ncf):
            value=g.expression(expressions['acceleration'],{'twot':twot,'d1':get(488,i-1),
                'a1':memory.get(Ptr('stack',16+8*(i-1)),'f64'),'a2':memory.get(Ptr('stack',16+8*(i-2)),'f64')})
            memory.put(Ptr('stack',16+8*i),'f64',value)
        for component in range(ncm):memory.put(dest.add(8*(2*ncm+component)),'f64',g.operation('mul',g.operation('mul',accumulate('acceleration',component),scale),scale))


def compare(expected,actual):
    # Stack scratch is not observable, but output, every cache cell/counter,
    # untouched caller memory and read-only coefficients are compared exactly.
    left={k:v for k,v in expected.cells.items() if k[0]!='stack'}
    right={k:v for k,v in actual.cells.items() if k[0]!='stack'}
    if left!=right:
        keys=sorted(k for k in left.keys()|right.keys() if left.get(k)!=right.get(k))
        raise AssertionError('Source/production memory mismatch '+repr(keys[:8]))
