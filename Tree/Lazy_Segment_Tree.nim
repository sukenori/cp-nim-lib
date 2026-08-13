import atcoder/lazysegtree
type
  S=int #dataの型
  F=int #lazyの型
proc op(a,b:S):S=a,b #dataの区間取得方法
proc e():S= #どんなaに対してもop(e,a)=aとなるもの（定数）
proc mapping(f:F,x:S):S=x,f #各dataのxにlazyのfをどう反映させるか
proc composition(f,g:F):F=f,g #lazyの元のgに対して次のfをどう反映させるか
proc id():F= #どんなfに対してもmapping(id,f)=fとなるもの（定数）
let n= #もしくはv=seq
var s=LazySegTree.getType(S,F,op,e,mapping,composition,id).init(n)

s[i]=x

s[p]
s[l..<r]

s.apply(l..<r,f)

import atcoder/lazysegtree
type
  S=object #dataの型
    value:int
    size:int
  F=int #lazyの型
proc op(a,b:S):S=S(value:a.value+b.value,size:a.size+b.size) #dataの区間取得方法
proc e():S=S(value:0,size:0) #どんなaに対してもop(e,a)=aとなるもの（定数）
proc mapping(f:F,x:S):S=S(value:f*x.size+x.value,size:x.size) #各dataのxにlazyのfをどう反映させるか
proc composition(f,g:F):F=f+g #lazyの元のgに対して次のfをどう反映させるか
proc id():F=0 #どんなfに対してもmapping(id,f)=fとなるもの（定数）
let n= #もしくはv=seq
var s=LazySegTree.getType(S,F,op,e,mapping,composition,id).init(v.mapIt(S(value:it,size:1)))

var n=1; while n<N: n*=2
var st,lz=Seq[2*n-1:0]
for i in 0..<N: st[n-1+i]=d[i]
for i in 0..n-2<<1: st[i]=max(st[2*i+1],st[2*i+2])
proc e(k:int)=
  if lz[k]!=0:
    st[k]+=lz[k]
    if k<n-1:
      lz[2*k+1]+=lz[k]
      lz[2*k+2]+=lz[k]
    lz[k]=0
proc u(a,b,v:int;k,l=0;r=n)=
  e(k)
  if a<=l and r<=b:
    lz[k]=v
    e(k)
  elif a<r and l<b:
    u(a,b,v,2*k+1,l,(l+r)//2)
    u(a,b,v,2*k+2,(l+r)//2,r)
    st[k]=max(st[2*k+1],st[2*k+2])
proc q(a,b:int;k,l=0;r=n):int=
  e(k)
  if r<=a or b<=l: return 0
  elif a<=l and r<=b: return st[k]
  else:
    return max(q(a,b,2*k+1,l,(l+r)//2),q(a,b,2*k+2,(l+r)//2,r))