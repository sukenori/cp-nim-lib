#総和がM以下となる区間の最大長
let s=(@[0]&A).cumsummed
var
  r=1
  a=0
for l in 0..<N:
  while r<N and s[r]-s[l]<=M: r+=1
  a.max=r-l
echo a

#合計がM以上となるペアの数
A.sort
var
  r=N-1
  a=0
for l in 0..<N-1:
  while l<r and A[l]+A[r]>=M:
    a+=r-l
    r-=1
echo a