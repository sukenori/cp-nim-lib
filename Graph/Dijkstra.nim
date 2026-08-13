import heapqueue
var
  q=[(w:0,n:0)].toHeapQueue
  w=int.inf.repeat(N)
  d=false.repeat(N)
w[0]=0
while q.len>0:
  let u=q.pop
  if not d[u.n]:
    d[u.n]=true
    for v in g[u.n]:
      let nw=u.w+v.w
      if nw<w[v.t]: w[v.t]=nw; q.push((nw,v.t))
echo w[^1]

#01-BFSはBFSに記載