import atcoder/segtree
type S=int
proc op(a,b:S):S=min(a,b)
proc e():S=int.inf
var s=initSegTree[S](N,op,e)
for i,di in d:
  if di<s.get(i): s[i]=di

import atcoder/segtree
type S=int
proc op(a,b:S):S=min(a,b)
proc e():S=int.inf
var s=initSegTree[S](v,op,e)

s[i]=x

s[l..<r]

var n=1; while n<N: n*=2
var st=int.inf.repeat(2*n-1)
proc u(i,v:int)=
  var j=n-1+v; st[j]=v
  while j>0:
    j=(j-1)//2
    st[j]=min(st[2*j+1],st[2*j+2])
proc q(a,b,k,l,r:int):int=
  if r<=a or b<=l: return int.inf
  elif a<=l and r<=b: return st[k]
  else:
    return min(q(a,b,2*k+1,l,(l+r)//2),q(a,b,2*k+2,(l+r)//2,r))