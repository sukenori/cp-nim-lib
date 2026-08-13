import atcoder/extra/math/eratosthenes
(n=N.float.sqrt.int)
let e=initEratosthenes(n)

e.prime
let p=initEratosthenes(n).prime.mapIt(it.int)

e.factor(N)
#Factor
var f:Table[int,int]
for i in 2..N.float.sqrt.int:
  while N mod i==0:
    if f.hasKeyOrPut(i,1): f[i]+=1
    N=N div i
if N>1: f[N]=1

e.divisor(N)
#Divisor
var d:seq[int]
for i in 1..N.float.sqrt.int:
  if N mod i==0:
    d.add(i)
    if i^2!=N: d.add(N div i)
d.sort