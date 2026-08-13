import atcoder/fenwicktree
var f=initFenwickTree[int](A.max+1)
for i,Ai in A:
  f.add(Ai,1)
  a+=f[Ai+1..^1]