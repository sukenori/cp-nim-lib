binom(n,k)

var fac,ifac=newSeq[mint](n+1)
fac[0]=1.mint; for i in 1..n: fac[i]=fac[i-1]*i
ifac[n]=fac[n].inv; for i in countdown(n-1,0): ifac[i]=ifac[i+1]*(i+1)
proc c(n,r:int):mint =
  #if r<0 or r>n: return 0.mint
  fac[n]*ifac[r]*ifac[n-r]

var t:Table[(int,int),mint]
proc c(n,r:int):mint=
  #if r<0 or r>n: return 0.mint
  if not t.hasKey((n,r)):
    t[(n,r)]=if r==0 or r==n: 1.mint else: c(n-1,r-1)+c(n-1,r)
  t[(n,r)]

var c=newSeqWith(N+1,newSeq[mint](N+1))
for n in 0..N:
  for r in 0..n:
    c[n][r]=if r==0 or r==n: 1.mint else: c[n-1][r]+c[n-1][r-1]

#重複組み合わせ全列挙
A.repeat(n).product