#最長回文半径を求める
proc m(s:string):seq[int] =
  let
    t=s.join("#")
    n=t.len
  var
    r=newSeq[int](n)
    c,m=0
  for i in 0..<n:
    if i<m: r[i]=min(m-i,r[2*c-i])
    while i-r[i]-1>=0 and i+r[i]+1<n and t[i-r[i]-1]==t[i+r[i]+1]:
      r[i]+=1
    if i+r[i]>m: c=i; m=i+r[i]
  return (0..<s.len).mapIt(r[it*2+1])