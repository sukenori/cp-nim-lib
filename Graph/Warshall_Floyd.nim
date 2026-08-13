import atcoder/extra/graph/warshall_floyd
var g=int.inf.repeat(N).repeat(N)
for i in 0..<N: g[i][i]=0
for _ in 1..M:
  let u,v=nextInt()-1
  let w=nextInt()
  g[u][v]=w
let d=g.warshallFloyd
#echo d[s,t]
#echo d.path(s,t)

var d=int.inf.repeat(N).repeat(N)
for i in 0..<N: d[i][i]=0
for _ in 1..M:
  let u,v=nextInt()-1
  let w=nextInt()
  d[u][v]=w
for k in 0..<N:
  for i in 0..<N:
    for j in 0..<N:
      d[i][j].min=d[i][k]+d[k][j]