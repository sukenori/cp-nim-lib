import random
randomize()
let
  m=1 shl 61-1
  b=rand(m-1)

proc h(s:string):int=
  for i in 0..<s.len:
    result=(result*b+s[i].ord) mod m

#このmでは、積がオーバーフローするので、別途、積を定義する
proc m(a,b:int):int=
  let
    au=a shr 31
    ad=a and (1 shl 31-1)
    bu=b shr 31
    bd=b and (1 shl 31-1)
    m=ad*bu+au*bd
    mu=m shr 30
    md=m and (1 shl 30-1)
    x=(au*bu*2+mu+(md shl 31)+ad*bd)
    r=(x shr 61)+(x and (1 shl 61-1))
  if r<1 shl 61-1: r else: r-(1 shl 61-1)

var h,p=newSeq[int](n+1)
p[0]=1
for i in 0..<n:
  h[i+1]=(m(h[i],b)+s[i].ord) mod m
  p[i+1]=m(p[i],b) mod m

#[l,r)
(h[r]-h[l]*p[r-l]+m) mod m