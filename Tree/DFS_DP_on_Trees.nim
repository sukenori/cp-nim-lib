proc dfs(p,u:int)=
  #行き preorder
  for v in g[u]:
    if v.t!=p:
      dfs(u,v.t)
  #帰り postorder
dfs(-1,0)

#木DP：頂点0からの最大距離
proc dp(p,u:int):int=
  for v in g[u]:
    if v.t!=p: result.max=dp(u,v.t)+v.w
echo dp(-1,0)

#木DP：一般化
type DP=tuple[d:int] #情報として記録していく必要な要素
proc merge(u,v:DP):DP=(if u.d>=v.d:u else:v) #各隣接部分木全体の情報をどうマージするか
proc move(u:DP):DP=(u.d+1,) #自身から子への辺移動
proc e(u:int):DP=(0,) #mergeに対する単位元
var
  dp=newSeq[seq[DP]](N) #dp[u][i]は頂点uでのg[u][i]を根とする部分木におけるDP値
  a=newSeq[DP](N) #各頂点を根としたときの木全体に対するDP値
proc dfs(p,u:int):DP=
  dp[u]=newSeq[DP](g[u].len)
  result=u.e
  for i,v in g[u]:
    if v!=p:
      dp[u][i]=dfs(u,v)
      result=result.merge(dp[u][i].move)
echo dfs(-1,0)