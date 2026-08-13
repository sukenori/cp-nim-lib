import atcoder/fenwicktree
var f=initFenwickTree[int](N)

f.add(i,x)

f[l..<r] # [l,r)
f[l..r] # [l,r]


var f=newSeqWith(N+1,0)

var i,x=nextInt()
while i<=N: f[i]+=x; i+=i and -i

var s=0
while i>0: s+=f[i]; i-=i and -i