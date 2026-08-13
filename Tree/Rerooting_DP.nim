type DP=tuple[d:int] #情報として記録していく必要な要素
proc merge(u,v:DP):DP=(if u.d>=v.d:u else:v) #各隣接部分木全体の情報をどうマージするか
proc move(u:DP):DP=(u.d+1,) #自身から子への辺移動
proc e(u:int):DP=(0,) #mergeに対する単位元
var
  dp=newSeq[seq[DP]](N) #dp[u][i]は頂点uにおけるg[u][i]を根とする部分木におけるDP値
  a=newSeq[DP](N) #各頂点を根としたときの木全体に対するDP値
proc dfs(p,u:int):DP=
  dp[u]=newSeq[DP](g[u].len)
  result=u.e
  for i,v in g[u]:
    if v!=p:
      dp[u][i]=dfs(u,v)
      result=result.merge(dp[u][i].move)
discard dfs(-1,0)
proc reroot(p,u:int,dpp:DP)=
  let n=g[u].len
  var l,r=newSeq[DP](n+1)
  l[0]=u.e; r[n]=u.e
  for i in 0..<n:
    l[i+1]=l[i].merge((if g[u][i]==p: dpp else: dp[u][i]).move)
    r[n-i-1]=r[n-i].merge((if g[u][n-1-i]==p: dpp else: dp[u][n-1-i]).move)
  a[u]=l[n]
  for i,v in g[u]:
    if v!=p: reroot(u,v,merge(l[i],r[i+1]))
reroot(-1,0,-1.e)