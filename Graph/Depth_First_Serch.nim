var d=false.repeat(N)
proc dfs(u:int)=
  d[u]=true
  #行き preorder
  for v in g[u]:
    if not d[v.t]:
      dfs(v.t)
  #帰り postorder
  #d[u]=false #単純パス／この探索で初めて
dfs(0)

import deques
var
  q=[0].toDeque
  d=false.repeat(N)
d[0]=true
while q.len>0:
  let u=q.popLast
  for v in g[u]:
    if not d[v.t]:
      d[v.t]=true
      q.addLast(v.t)