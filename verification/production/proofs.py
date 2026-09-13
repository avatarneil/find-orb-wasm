"""GPL-2.0-or-later. Solver-checked numeric-rule and index lemmas.

The classified add/mul rules follow WebAssembly numerics. The exact finite-value
interpretation and deterministic rounding function are left arbitrary, so the
symmetry proof does not assume a sampled floating implementation. Correspondence
of these rules to actual IEEE instructions is an explicit specification TCB.
"""
import z3
from verify import Obligations


def establish(out):
    obligations=Obligations(out)
    a,b=z3.BitVecs('a b',64)
    value=z3.Function('exact_finite_value',z3.BitVecSort(64),z3.RealSort())
    rounded=z3.Function('round_nearest_even',z3.RealSort(),z3.BitVecSort(64))
    def fields(x):
        exponent=z3.Extract(62,52,x);fraction=z3.Extract(51,0,x)
        return z3.Extract(63,63,x),z3.And(exponent==2047,fraction!=0),z3.And(exponent==2047,fraction==0),z3.Extract(62,0,x)==0
    nan=z3.BitVecVal(0x7ff8000000000000,64)
    def zero(sign):return z3.Concat(sign,z3.BitVecVal(0,63))
    def inf(sign):return z3.Concat(sign,z3.BitVecVal(0x7ff0000000000000,63))
    def numeric(op,x,y):
        sx,nx,ix,zx=fields(x);sy,ny,iy,zy=fields(y)
        if op=='add':
            total=value(x)+value(y)
            return z3.If(z3.Or(nx,ny,z3.And(ix,iy,sx!=sy)),nan,
              z3.If(ix,inf(sx),z3.If(iy,inf(sy),
                z3.If(z3.And(zx,zy),zero(sx&sy),z3.If(total==0,zero(z3.BitVecVal(0,1)),rounded(total))))))
        return z3.If(z3.Or(nx,ny,z3.And(ix,zy),z3.And(iy,zx)),nan,
          z3.If(z3.Or(ix,iy),inf(sx^sy),z3.If(z3.Or(zx,zy),zero(sx^sy),rounded(value(x)*value(y)))))
    for op in ('add','mul'):
        obligations.check('numeric-rule-'+op+'-commutes',numeric(op,a,b)!=numeric(op,b,a),metadata={
            'scope':'All 64-bit operand encodings under explicit classified WebAssembly numeric-rule model; NaN payload/sign quotiented',
            'trustedTransfer':'Reviewed correspondence of classified numeric rules to WebAssembly/IEEE64 add/mul; not a direct SMT floating-point-builtin proof'})
    ncf,ncm,na,sub,component,k=z3.Ints('ncf ncm na sub component degree')
    domain=z3.And(ncf>=6,ncf<=14,ncm>=1,ncm<=3,z3.Or(*[na==x for x in (1,2,4,8)]),sub>=0,sub<na,component>=0,component<ncm,k>=0,k<ncf)
    index=ncf*(component+sub*ncm)+k
    obligations.check('coefficient-affine-address-domain',z3.And(domain,z3.Or(index<0,index>=ncf*ncm*na,index>=2**28)))
    count,available=z3.BitVecs('count available',32)
    for factor in (2,4):
        delta=count-available;r=delta&(factor-1);q=z3.LShR(delta-r,1 if factor==2 else 2)
        obligations.check('unrolled-loop-'+str(factor)+'-partition',z3.And(z3.UGE(count,6),z3.ULE(count,14),z3.UGE(available,2),z3.ULT(available,count),z3.Or(r+factor*q!=delta,z3.UGE(r,factor),z3.UGT(q,6))))
    x=z3.FP('tc',z3.Float64())
    obligations.check('finite-cache-self-comparison',z3.And(z3.Not(z3.fpIsNaN(x)),z3.Not(z3.fpEQ(x,x))))
    qv,expected_na,actual_na=z3.BitVecs('quantities expected_na actual_na',32)
    condition=z3.If(qv!=0,z3.If(actual_na==expected_na,z3.BitVecVal(1,32),z3.BitVecVal(0,32)),z3.BitVecVal(0,32))
    obligations.check('actual-selection-guard', (condition!=0)!=z3.And(qv!=0,actual_na==expected_na))
    buf,pointer=z3.BitVecs('record_base coefficient_pointer',32)
    obligations.check('actual-coefficient-base-address',buf+(pointer<<3)-8 != buf+((pointer-1)<<3))
    for na_value in (1,2,4,8):
        na_fp=z3.FPVal(na_value,z3.Float64())
        scale=z3.fpDiv(z3.RNE(),z3.fpAdd(z3.RNE(),na_fp,na_fp),z3.FPVal(32,z3.Float64()))
        obligations.check('source-exact-derivative-scale-'+str(na_value),scale!=z3.FPVal(str(na_value/16),z3.Float64()))
    return obligations.records
