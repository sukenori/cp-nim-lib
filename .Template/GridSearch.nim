when not declared(LIBRARY_GRIDSEARCH):
  const LIBRARY_GRIDSEARCH = true
  include "/workspaces/AtCoder-Nim/.Library/.Template/Template.nim"

  ##- **Pos**: tuple[h, w: int]
  ##    - グリッド座標を表す型エイリアス
  type Pos* = tuple[h, w: int]
  ##- **Grid[T]**: object
  ##    - 2次元配列を平坦化して保持する高速アクセス構造体
  type Grid*[T] = object
    data: seq[T]
    h*, w*: int
  ##- **initGrid(h, w, val)**
  ##    - h × w の Grid[T] を val で初期化
  proc initGrid*[T](h, w: int, val: T): Grid[T] =
    Grid[T](data: newSeqWith(h * w, val), h: h, w: w)
  ##- **seq[seq[T]].toGrid**
  ##    - 二次元配列を Grid[T] に変換（平坦化）
  func toGrid*[T](data: seq[seq[T]]): Grid[T] =
    let h = data.len
    let w = if h > 0: data[0].len else: 0
    var flat = newSeq[T](h * w)
    for y in 0 ..< h:
      for x in 0 ..< w:
        flat[y * w + x] = data[y][x]
    Grid[T](data: flat, h: h, w: w)
  ##- **seq[string].toGrid**
  ##    - 文字列配列を Grid[char] に変換（平坦化）
  func toGrid*(data: seq[string]): Grid[char] =
    let h = data.len
    let w = if h > 0: data[0].len else: 0
    var flat = newSeqOfCap[char](h * w)
    for s in data:
      for c in s:
        flat.add(c)
    Grid[char](data: flat, h: h, w: w)
  ##- **Grid[T].idx(h, w) / Grid[T].idx(p: Pos)**
  ##    - (h,w) 座標を平坦化インデックスに変換 `O(1)`
  func idx*[T](g: Grid[T], h, w: int): int {.inline.} =
    h * g.w + w
  func idx*[T](g: Grid[T], p: Pos): int {.inline.} =
    p.h * g.w + p.w
  ##- **Grid[T].pos(i: int)**
  ##    - 平坦化インデックスを (h, w) 座標に変換 `O(1)`
  func pos*[T](g: Grid[T], i: int): (int, int) {.inline.} =
    (i div g.w, i mod g.w)
  ##- **Grid[T].toSeq**: seq[seq[T]]
  ##    - グリッドを二次元配列に変換（新規割り当て）
  func toSeq*[T](g: Grid[T]): seq[seq[T]] =
    result = newSeqWith(g.h, newSeq[T](g.w))
    for y in 0 ..< g.h:
      for x in 0 ..< g.w:
        result[y][x] = g.data[y * g.w + x]
  proc `$`*[T](g: Grid[T]): string =
    var res = newSeq[string]()
    for y in 0 ..< g.h:
      var line = newSeq[string]()
      for x in 0 ..< g.w:
        line.add($g[y][x])
      res.add(line.join(" "))
    return res.join("\n")
  const
    dir4* = [(-1, 0), (0, 1), (1, 0), (0, -1)]
    dir8* = [(-1, 0), (-1, 1), (0, 1), (1, 1), (1, 0), (1, -1), (0, -1), (-1, -1)]
  type
    NeighborSearcher*[Grid, Elem] = object
      start: Pos
      use8: bool
      hasLimit: bool
      H, W: int
      hasSkip: bool
      grid*: Grid
      skipVal: Elem
  ##- **neighbors(p)**
  ##    - 座標 p の近傍探索イテレータを生成 (Method Chain)
  ##    - デフォルト: 4近傍, 範囲制限なし
  # 使用例:
  # for (nh, nw) in (r, c).neighbors.inside(H, W): ...
  proc neighbors*(p: Pos): NeighborSearcher[void, int] =
    result.start = p
    result.use8 = false
    result.hasLimit = false
    result.hasSkip = false
  ##- **ns.asDir8**
  ##    - 8近傍探索に切り替え
  proc asDir8*[G, T](ns: NeighborSearcher[G, T]): NeighborSearcher[G, T] =
    result = ns
    result.use8 = true
  ##- **ns.inside(H, W)**
  ##    - グリッド範囲内 (0..H-1, 0..W-1) に制限
  proc inside*[G, T](ns: NeighborSearcher[G, T], H, W: int): NeighborSearcher[G, T] =
    result = ns
    result.hasLimit = true
    result.H = H
    result.W = W
  ##- **ns.on(grid)**
  ##    - グリッドコンテナ（seq[string]やmatrix）を紐付け
  ##    - サイズ情報の自動取得と、skip機能のための参照保持を行う
  template on*[T](ns: NeighborSearcher[void, int], container: T): untyped =
    type ContainerType = T
    type ElemType = typeof(container[0][0]) 
    var newNs: NeighborSearcher[ptr ContainerType, ElemType]
    newNs.start = ns.start
    newNs.use8 = ns.use8
    newNs.hasLimit = true
    newNs.H = container.h
    newNs.W = container.w
    newNs.grid = unsafeAddr container
    newNs
  ##- **ns.skip(val)**
  ##    - 特定の値（壁 '#' など）を持つマスをスキップ
  ##    - 事前に `.on(grid)` が必要
  proc skip*[G, T](ns: NeighborSearcher[G, T], val: T): NeighborSearcher[G, T] =
    result = ns
    result.hasSkip = true
    result.skipVal = val
  ##- **ns.skip(grid, val)**
  ##    - `.on(grid).skip(val)` のショートカット
  template skip*[G, T](ns: NeighborSearcher[G, T], grid: typed, val: typed): untyped =
    ns.on(grid).skip(val)
  iterator items*[G, T](ns: NeighborSearcher[G, T]): Pos =
    if ns.use8:
      for d in dir8:
        let nh = ns.start.h + d[0]
        let nw = ns.start.w + d[1]
        if ns.hasLimit:
          if nh < 0 or nh >= ns.H or nw < 0 or nw >= ns.W: continue
        if ns.hasSkip:
          when G isnot void:
            if ns.grid[][nh][nw] == ns.skipVal: continue
        yield (nh, nw)
    else:
      for d in dir4:
        let nh = ns.start.h + d[0]
        let nw = ns.start.w + d[1]
        if ns.hasLimit:
          if nh < 0 or nh >= ns.H or nw < 0 or nw >= ns.W: continue
        if ns.hasSkip:
          when G isnot void:
            if ns.grid[][nh][nw] == ns.skipVal: continue
        yield (nh, nw)
  ##- **findPos(grid, target)**
  ##    - grid内から target を探し、最初の座標 (h, w) を返す。見つからない場合は (-1, -1)
  proc findPos*(grid: seq[string], target: char): Pos =
    for h, row in grid:
      let w = row.find(target)
      if w != -1: return (h, w)
    return (-1, -1)
  proc findPos*[T](grid: seq[seq[T]], target: T): Pos =
    for h, row in grid:
      let w = row.find(target)
      if w != -1: return (h, w)
    return (-1, -1)
  ##- **findAll(grid, target)**
  ##    - grid内から target を全て探し、座標リスト seq[Pos] を返す
  proc findAll*(grid: seq[string], target: char): seq[Pos] =
    for h, row in grid:
      for w, c in row:
        if c == target: result.add((h, w))
  proc findAll*[T](grid: seq[seq[T]], target: T): seq[Pos] =
    for h, row in grid:
      for w, val in row:
        if val == target: result.add((h, w))
  ##- **expandGrid(grid, fillVal, padding)**
  ##    - grid の周囲に fillVal を padding個 詰めて拡張する（番兵法用）
  proc expandGrid*(grid: seq[string], fillVal: char = '#', padding: int = 1): seq[string] =
    let h = grid.len
    let w = if h > 0: grid[0].len else: 0
    let width = w + padding * 2
    let tb = fillVal.repeat(width)
    result = newSeqOfCap[string](h + padding * 2)
    for _ in 1..padding: result.add(tb)
    let padStr = fillVal.repeat(padding)
    for row in grid:
      result.add(padStr & row & padStr)
    for _ in 1..padding: result.add(tb)
  proc expandGrid*[T](grid: seq[seq[T]], fillVal: T, padding: int = 1): seq[seq[T]] =
    let h = grid.len
    let w = if h > 0: grid[0].len else: 0
    let width = w + padding * 2
    let tb = newSeqWith(width, fillVal)
    result = newSeqOfCap[seq[T]](h + padding * 2)
    for _ in 1..padding: result.add(tb)
    let padSeq = newSeqWith(padding, fillVal)
    for row in grid:
      result.add(padSeq & row & padSeq)
    for _ in 1..padding: result.add(tb)
  template assignOrAdd(dest: var Pos, p: Pos) = dest = p
  template assignOrAdd(dest: var seq[Pos], p: Pos) = dest.add(p)
  ##- **scan(grid, 'S', sPos, 'G', gPos, 'X', walls...)**
  ##    - グリッドを一回走査し、指定された文字の座標を取得するマクロ
  ##    - 変数が seq[Pos] 型なら add し、Pos 型なら代入する
  # 使用例:
  # var start, goal: Pos
  # var jewels: seq[Pos]
  # grid.scan('S', start, 'G', goal, 'J', jewels)
  macro scan*(grid: typed, args: varargs[untyped]): untyped =
    assert args.len mod 2 == 0
    let charVal = ident("c")
    let hVal = ident("h")
    let wVal = ident("w")
    let caseStmt = nnkCaseStmt.newTree(charVal)
    for i in countup(0, args.len - 1, 2):
      let targetChar = args[i]
      let destVar = args[i+1]
      caseStmt.add nnkOfBranch.newTree(
        targetChar,
        newCall(
          bindSym("assignOrAdd"), 
          destVar, 
          nnkTupleConstr.newTree(hVal, wVal)
        )
      )
    caseStmt.add nnkElse.newTree(newStmtList(nnkDiscardStmt.newTree(newEmptyNode())))
    result = quote do:
      block:
        let H = `grid`.len
        let W = if H > 0: `grid`[0].len else: 0
        for `hVal` in 0 ..< H:
          for `wVal` in 0 ..< W:
            let `charVal` = `grid`[`hVal`][`wVal`]
            `caseStmt`