when not declared(LIBRARY_GRAPH):
  const LIBRARY_GRAPH = true
  include "/workspaces/AtCoder-Nim/.Library/.Template/Template.nim"

  ##- Edge[T]
  ##    - 汎用グラフの辺。重み T を持つ
  type
    Edge*[T] = object
      to*: int
      weight*: T
      rev*: int
      id*: int
  ##- WeightedUnionFind[T]
  ##    - 重み付きUnionFind (ポテンシャル付きUF)。ノード間の重み差(diff)を管理
  ##    - 基本機能: find(root取得), union(併合), weight(重み取得)
  type
    WeightedUnionFind*[T] = object
      parent: seq[int]
      diff_weight: seq[T]
      size: seq[int]
      count*: int
  ##- initWeightedUnionFind(n)
  ##    - 初期化。各ノードは独立したグループとなる
  proc initWeightedUnionFind*[T](n: int): WeightedUnionFind[T] =
    result.count = n
    result.parent = newSeq[int](n)
    result.diff_weight = newSeq[T](n)
    result.size = newSeqWith(n, 1)
    for i in 0 ..< n:
      result.parent[i] = i
  ##- uf.find(i)
  ##    - 代表元（ルート）を検索しつつ経路圧縮を行う O(α(N))
  ##    - 判定: uf.find(u) == uf.find(v) なら同じグループ
  proc find*[T](uf: var WeightedUnionFind[T], i: int): int =
    if uf.parent[i] == i:
      return i
    let r = uf.find(uf.parent[i])
    uf.diff_weight[i] += uf.diff_weight[uf.parent[i]]
    uf.parent[i] = r
    r
  ##- uf.weight(i)
  ##    - 代表元に対する相対重みを取得
  ##    - 距離: uf.weight(v) - uf.weight(u) で u -> v 間の重み差を取得可能（同じグループの場合のみ有効）
  proc weight*[T](uf: var WeightedUnionFind[T], i: int): T =
    discard uf.find(i)
    uf.diff_weight[i]
  ##- uf.union(u, v, w)
  ##    - weight(v) - weight(u) = w となるように併合。矛盾があれば false を返す
  ##    - 既に同じグループの場合、整合性をチェックして結果を返す
  proc union*[T](uf: var WeightedUnionFind[T], u, v: int, w: T): bool =
    let root_u = uf.find(u)
    let root_v = uf.find(v)
    if root_u != root_v:
      let new_diff = uf.weight(u) + w - uf.weight(v)
      if uf.size[root_u] >= uf.size[root_v]:
        uf.parent[root_v] = root_u
        uf.diff_weight[root_v] = new_diff
        uf.size[root_u] += uf.size[root_v]
      else:
        uf.parent[root_u] = root_v
        uf.diff_weight[root_u] = -new_diff
        uf.size[root_v] += uf.size[root_u]
      uf.count.dec
      true
    else:
      let dist = uf.weight(v) - uf.weight(u)
      dist == w
  ##- uf.same(u, v)
  ##    - 同じグループか判定 O(α(N))
  proc same*[T](uf: var WeightedUnionFind[T], u, v: int): bool =
    uf.find(u) == uf.find(v)
  ##- uf.isRoot(i)
  ##    - そのノードが代表元（ルート）か判定 O(1)
  proc isRoot*[T](uf: var WeightedUnionFind[T], i: int): bool =
    uf.parent[i] == i
  ##- uf.size(i)
  ##    - 所属グループのサイズを取得 O(α(N))
  proc size*[T](uf: var WeightedUnionFind[T], i: int): int =
    uf.size[uf.find(i)]
  ##- uf.getGroups(n)
  ##    - 連結成分ごとの頂点リストを返す
  proc getGroups*[T](n: int, uf: var WeightedUnionFind[T]): seq[seq[int]] =
    var groupMap = initTable[int, seq[int]]()
    for i in 0 ..< n:
      let r = uf.find(i)
      if not groupMap.hasKey(r):
        groupMap[r] = @[]
      groupMap[r].add(i)
    result = @[]
    for members in groupMap.values:
      result.add(members)
  ##- GraphInfo[T]
  ##    - グリッドの付加情報
  ##    - isTree: 木かどうか (連結かつ閉路なし)
  ##    - hasCycle: 閉路が存在するか (無向/弱連結として)
  ##    - isBipartite: 二部グラフ判定 (重み1として判定)
  ##    - isConsistent: 重み付きグラフとして矛盾がないか (閉路の重み和=0)
  ##    - uf: 構築過程で使用したWeightedUnionFind。連結性判定や距離計算に再利用可能
  type
    GraphInfo*[T] = object
      isTree*: bool
      isForest*: bool
      isConnected*: bool
      hasCycle*: bool
      isBipartite*: bool
      isConsistent*: bool
      hasSelfLoop*: bool
      inDeg*: seq[int]
      uf*: WeightedUnionFind[T]
  ##- Graph[T]
  ##    - adj と info をまとめたグラフ本体
  type
    Graph*[T] = object
      adj*: seq[seq[Edge[T]]]
      info*: GraphInfo[T]
      bipUF: WeightedUnionFind[int]   ## 二部判定用 (外には公開しない)
  ##- initGraph(n)
  ##    - ノード数 n のグラフを初期化
  proc initGraph*[T](n: int): Graph[T] =
    result.adj = newSeqWith(n, newSeq[Edge[T]]())
    result.info.uf = initWeightedUnionFind[T](n)
    result.bipUF = initWeightedUnionFind[int](n)
    result.info.inDeg = newSeq[int](n)
    result.info.isConsistent = true
    result.info.isBipartite = true
    result.info.hasSelfLoop = false
    result.info.hasCycle = false
    result.info.isForest = true
    result.info.isConnected = (n <= 1)
    result.info.isTree = (n <= 1)
  proc updateInfoDirected[T](g: var Graph[T], u, v: int, w: T) =
    if u == v:
      g.info.hasSelfLoop = true
    g.info.inDeg[v].inc
    var uf = g.info.uf
    let ru = uf.find(u)
    let rv = uf.find(v)
    if ru == rv:
      g.info.hasCycle = true
      if uf.weight(v) - uf.weight(u) != w:
        g.info.isConsistent = false
    else:
      discard uf.union(u, v, w)
    g.info.uf = uf
    var buf = g.bipUF
    if not buf.union(u, v, 1):
      g.info.isBipartite = false
    g.bipUF = buf
    g.info.isConnected = (g.info.uf.count == 1)
    g.info.isForest = not g.info.hasCycle
    g.info.isTree = g.info.isConnected and g.info.isForest
  proc updateInfoUndirected[T](g: var Graph[T], u, v: int, w: T) =
    if u == v:
      g.info.hasSelfLoop = true
    g.info.inDeg[u].inc
    g.info.inDeg[v].inc
    var uf = g.info.uf
    let ru = uf.find(u)
    let rv = uf.find(v)
    if ru == rv:
      g.info.hasCycle = true
      if uf.weight(v) - uf.weight(u) != w:
        g.info.isConsistent = false
    else:
      discard uf.union(u, v, w)
    g.info.uf = uf
    var buf = g.bipUF
    if not buf.union(u, v, 1):
      g.info.isBipartite = false
    g.bipUF = buf
    g.info.isConnected = (g.info.uf.count == 1)
    g.info.isForest = not g.info.hasCycle
    g.info.isTree = g.info.isConnected and g.info.isForest
  ##- g.addEdge(u, v, w)
  ##    - 有向辺 u -> v (重み w) を追加し、GraphInfo も更新
  proc addEdge*[T](g: var Graph[T], u, v: int, weight: T = T(1), id: int = -1) =
    g.adj[u].add(Edge[T](to: v, weight: weight, rev: -1, id: id))
    g.updateInfoDirected(u, v, weight)
  ##- g.addBiEdge(u, v, w)
  ##    - 無向辺 u <-> v (重み w) を追加し、GraphInfo も更新
  proc addBiEdge*[T](g: var Graph[T], u, v: int, weight: T = T(1), id: int = -1) =
    let ru = g.adj[u].len
    let rv = g.adj[v].len
    g.adj[u].add(Edge[T](to: v, weight: weight, rev: rv, id: id))
    g.adj[v].add(Edge[T](to: u, weight: weight, rev: ru, id: id))
    g.updateInfoUndirected(u, v, weight)
  ##- iterator g.edges: tuple[u, v: int, weight: T]
  ##    - グリッド内の全辺を列挙 (u, v, w)
  iterator edges*[T](g: Graph[T]): tuple[u, v: int, weight: T] =
    for u in 0 ..< g.adj.len:
      for e in g.adj[u]:
        yield (u, e.to, e.weight)
  ##- iterator g.edgesWithId: tuple[id, u, v: int, weight: T]
  ##    - ID付きで全辺を列挙 (id, u, v, w)
  iterator edgesWithId*[T](g: Graph[T]): tuple[id, u, v: int, weight: T] =
    for u in 0 ..< g.adj.len:
      for e in g.adj[u]:
        if e.id != -1:
          yield (e.id, u, e.to, e.weight)
  ##- .to[] / .weight[]
  ##    - g.to[u]     : 隣接先だけの seq[int]
  ##    - g.weight[u] : (to, weight) タプルの seq
  type
    ToView[T] = object
      g: ptr Graph[T]
    WeightView[T] = object
      g: ptr Graph[T]
  proc to*[T](g: var Graph[T]): ToView[T] =
    ToView[T](g: addr g)
  proc weight*[T](g: var Graph[T]): WeightView[T] =
    WeightView[T](g: addr g)
  proc `[]`*[T](v: ToView[T], u: int): seq[int] =
    result = newSeq[int](v.g[].adj[u].len)
    for i, e in v.g[].adj[u]:
      result[i] = e.to
  proc `[]`*[T](v: WeightView[T], u: int): seq[tuple[to: int, weight: T]] =
    result = newSeq[tuple[to: int, weight: T]](v.g[].adj[u].len)
    for i, e in v.g[].adj[u]:
      result[i] = (e.to, e.weight)
  ##- readGraph(n, m, weighted, directed, oneBased)
  ##    - 標準入力からグラフを構築して返す
  ##    - T が int/float かつ weighted=true なら重み w も読み込む
  ##    - weighted=false のときは常に重み1として扱う
  proc readGraph*[T = int](n, m: int,
                          weighted: static bool = false,
                          directed = false,
                          oneBased = true): Graph[T] =
    var g = initGraph[T](n)
    for i in 0 ..< m:
      var u_in = int.input
      var v_in = int.input
      var w: T
      when weighted:
        when T is float or T is float64:
          w = float.input
        elif T is int or T is int64:
          w = int.input
        else:
          w = T(1)
      else:
        w = T(1)
      let u = if oneBased: u_in - 1 else: u_in
      let v = if oneBased: v_in - 1 else: v_in
      if directed:
        g.addEdge(u, v, w)
      else:
        g.addBiEdge(u, v, w)
    g