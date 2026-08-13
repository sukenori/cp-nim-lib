var g=newSeqWith(N,newSeq[int]())
var ind=newSeq[int](N)
for _ in 1..M:
  let u,v=nextInt()-1
  g[u].add(v); ind[v]+=1

var a:seq[int]
while a.len<N:
  let i=ind.find(0)
  a.add(i+1); ind[i]= -1
  for j in g[i]: ind[j]-=1
echo a

var l:seq[int]
for i in 0..<N:
  if ind[i]==0: l.add(i)
var a=0
while l.len>0:
  var nl:seq[int]
  for li in l:
    for j in g[li]:
      ind[j]-=1
      if ind[j]==0: nl.add(j)
  l=nl
  a+=1
echo a