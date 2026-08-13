import deques
var
  q=[0].toDeque
  d=false.repeat(N)
d[0]=true
while q.len>0:
  let u=q.popFirst
  for v in g[u]:
    if not d[v.t]:
      d[v.t]=true
      q.addLast(v.t)

#01-BFS
import deques
var
  q=[0].toDeque
  d=int.inf.repeat(N)
d[0]=0
while q.len>0:
  let u=q.popFirst
  for v in g[u]:
    if v.w==0 and d[v.t]>d[u]:
      d[v.t]=d[u]; q.addFirst(v.t)
    if v.w==1 and d[v.t]>d[u]+1:
      d[v.t]=d[u]+1; q.addLast(v.t)