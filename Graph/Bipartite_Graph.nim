var d=(-1).repeat(N)
var f=true
for i in 0..<N:
  proc dfs(u:int)=
    for v in g[u]:
      if d[v] == -1: d[v]=1-d[u]; dfs(v)
      elif d[u]+d[v]!=1: f=false
  if d[i] == -1: d[i]=0; dfs(i)

var d=initDSU(2*N)
for _ in 0..<M:
  let u,v=nextInt()-1
  d.merge(u,N+v); d.merge(N+u,v)
var a=bool.repeat(N)
for i in 0..<N: a[i]=d.same(i,N+i)
echo if a.all(not it): "Yes" else: "No"