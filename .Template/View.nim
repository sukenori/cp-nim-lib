when not declared(LIBRARY_VIEW):
  const LIBRARY_VIEW = true
  include "/workspaces/AtCoder-Nim/.Library/.Template/Template.nim"

  type View1D*[T] = object
    data: ptr UncheckedArray[T]
    len*: int
    offset, step: int
    base*: int
  ##- **seq[T].view**: View1D[T]
  ##    - seqからO(1)でView1Dを生成
  func view*[T](s: var seq[T]): View1D[T] =
    if s.len == 0: return
    View1D[T](
      data: cast[ptr UncheckedArray[T]](addr s[0]),
      len: s.len,
      offset: 0,
      step: 1,
      base: 0
    )
  ##- **View1D[T][i] / View1D[T][i] = val**
  ##    - ビュー上の要素に論理インデックスiでアクセス (物理位置は i - base)
  func `[]`*[T](v: View1D[T], i: int): var T {.inline.} =
    let realIdx = i - v.base
    assert realIdx >= 0 and realIdx < v.len
    v.data[v.offset + realIdx * v.step]
  func `[]=`*[T](v: View1D[T], i: int, val: T) {.inline.} =
    let realIdx = i - v.base
    assert realIdx >= 0 and realIdx < v.len
    v.data[v.offset + realIdx * v.step] = val
  ##- **View1D[T].len**
  ##    - ビューの長さを返す
  func len*[T](v: View1D[T]): int {.inline.} = v.len
  ##- **View1D[T].shift(k)**
  ##    - 物理メモリ(offset)は動かさず、論理インデックス(base)のみずらす
  ##    - shift(1) すると、アクセスは v[1]..v[len] になる
  func shift*[T](v: View1D[T], k = 1): View1D[T] =
    result = v
    result.base += k
  ##- **View1D[T].start(s)**
  ##    - 物理的に先頭をs個切り落とす（offsetを進める）
  ##    - shiftはstartとは無関係で独立しているが、その後もshiftは維持される
  func start*[T](v: View1D[T], s: int): View1D[T] =
    assert s >= 0
    result = v
    let actual_s = if s > v.len: v.len else: s # min(s, v.len)
    result.offset += actual_s * v.step
    result.len -= actual_s
  ##- **View1D[T].size(l)**
  ##    - 長さをlに制限した部分ビュー
  func size*[T](v: View1D[T], l: int): View1D[T] =
    assert l >= 0 and l <= v.len
    result = v
    result.len = l
  ##- **View1D[T].step(k)**
  ##    - 間引き（物理ステップを変更）
  func step*[T](v: View1D[T], k: int): View1D[T] =
    result = v
    if result.len > 0:
      result.len = (result.len + k - 1) div k
    else:
      result.len = 0
    result.step *= k
  ##- **View1D[T].reverse**
  ##    - 反転ビューを返す
  ##    - shiftはreverseとは無関係で独立しているが、その後もshiftは維持される
  func reverse*[T](v: View1D[T]): View1D[T] =
    result = v
    result.offset += (v.len - 1) * v.step
    result.step = -v.step
  ##- **View1D[T].toSeq**
  ##    - 物理的に見えているデータを新規配列化 (base は無視)
  func toSeq*[T](v: View1D[T]): seq[T] =
    result = newSeq[T](v.len)
    var curr = v.offset
    for i in 0 ..< v.len:
      result[i] = v.data[curr]
      curr += v.step
  ##- **View1D[T].sort(order) / sort(cmp)**
  ##    - ビュー範囲の要素をソートし、元データへ書き戻す
  proc sort*[T](v: View1D[T], order = SortOrder.Ascending) =
    var s = v.toSeq
    s.sort(order)
    var c = v.offset
    for x in s:
      v.data[c] = x
      c += v.step
  proc sort*[T](v: View1D[T], cmp: proc(a, b: T): int) =
    var s = v.toSeq
    s.sort(cmp)
    var c = v.offset
    for x in s:
      v.data[c] = x
      c += v.step
  iterator items*[T](v: View1D[T]): T =
    var curr = v.offset
    for _ in 0 ..< v.len:
      yield v.data[curr]
      curr += v.step
  proc `$`*[T](v: View1D[T]): string = $v.toSeq
  type CircularView1D*[T] = object
    base: View1D[T]
    offset, step: int
  ##- **View1D[T].circular**
  ##    - インデックスを循環させてアクセスする1次元ビュー
  func circular*[T](v: View1D[T]): CircularView1D[T] =
    CircularView1D[T](
      base: v,
      offset: 0,
      step: 1
    )
  func `[]`*[T](cv: CircularView1D[T], i: int): var T {.inline.} =
    let idx = floorMod(cv.offset + i * cv.step, cv.base.len)
    cv.base[idx]
  func `[]=`*[T](cv: CircularView1D[T], i: int, val: T) {.inline.} =
    let idx = floorMod(cv.offset + i * cv.step, cv.base.len)
    cv.base[idx] = val
  func shift*[T](cv: CircularView1D[T], k = 1): CircularView1D[T] =
    result = cv
    result.offset -= k * cv.step
  func start*[T](cv: CircularView1D[T], s: int): CircularView1D[T] =
    result = cv
    result.offset += s * cv.step
  func step*[T](cv: CircularView1D[T], k: int): CircularView1D[T] =
    result = cv
    result.step *= k
  type View2D*[T] = object
    data: ptr UncheckedArray[T]
    h*, w*: int
    offset: int
    st_y, st_x: int
    base_y*, base_x*: int
  ##- **Grid[T].view**: View2D[T]
  ##    - GridからO(1)でView2Dを生成
  func view*[T](g: var Grid[T]): View2D[T] =
    if g.data.len == 0: return
    View2D[T](
      data: cast[ptr UncheckedArray[T]](addr g.data[0]),
      h: g.h, w: g.w,
      offset: 0,
      st_y: g.w, st_x: 1,
      base_y: 0, base_x: 0
    )
  ##- **View2D[T][i][j] / View2D[T][i][j] = val**
  ##    - 行アクセス、返されるView1Dには base_x が継承される
  ##    - 結果的にビュー上の要素アクセスとなる
  func `[]`*[T](v: View2D[T], y: int): View1D[T] {.inline.} =
    let realY = y - v.base_y
    assert realY >= 0 and realY < v.h
    View1D[T](
      data: v.data,
      len: v.w,
      offset: v.offset + realY * v.st_y,
      step: v.st_x,
      base: v.base_x
    )
  ##- **Grid[T][h][w] / Grid[T][h][j] = val**
  ##    - グリッド上の要素アクセス
  func `[]`*[T](g: var Grid[T], y: int): View1D[T] {.inline.} =
    View1D[T](
      data: cast[ptr UncheckedArray[T]](addr g.data[0]),
      len: g.w,
      offset: y * g.w,
      step: 1,
      base: 0
    )
  func `[]`*[T](g: Grid[T], y: int): View1D[T] {.inline.} =
    View1D[T](
      data: cast[ptr UncheckedArray[T]](unsafeAddr g.data[0]),
      len: g.w,
      offset: y * g.w,
      step: 1,
      base: 0
    )
  ##- **View2D[T].shift(dy, dx)**
  ##    - 物理メモリは動かさず、論理インデックスのみずらす
  func shift*[T](v: View2D[T], dy = 1, dx = 1): View2D[T] =
    result = v
    result.base_y += dy
    result.base_x += dx
  ##- **View2D[T].start(y, x)**
  ##    - 左上位置を (y, x) から開始する部分ビュー
  ##    - shiftはstartとは無関係で独立しているが、その後もshiftは維持される
  func start*[T](v: View2D[T], y: int, x: int): View2D[T] =
    assert y >= 0 and x >= 0
    result = v
    let cut_y = if y > v.h: v.h else: y
    let cut_x = if x > v.w: v.w else: x
    result.offset += cut_y * v.st_y + cut_x * v.st_x
    result.h -= cut_y
    result.w -= cut_x
  ##- **View2D[T].size(h, w)**
  ##    - ビューの高さと幅を制限した部分矩形
  func size*[T](v: View2D[T], h, w: int): View2D[T] =
    assert h <= v.h and w <= v.w
    result = v
    result.h = h
    result.w = w
  ##- **View2D[T].swapXY**
  ##    - 転置ビューを返す（h↔w, st_y↔st_x を入れ替え）
  ##    - shiftのbaseは維持
  func swapXY*[T](v: View2D[T]): View2D[T] =
    result = v
    swap(result.h, result.w)
    swap(result.st_y, result.st_x)
    swap(result.base_y, result.base_x)
  ##- **View2D[T].flipUD**
  ##    - 上下反転ビューを返す（要素はコピーしない）
  ##    - shiftのbaseは維持
  func flipUD*[T](v: View2D[T]): View2D[T] =
    result = v
    result.offset += (v.h - 1) * v.st_y
    result.st_y = -v.st_y
  ##- **View2D[T].flipLR**
  ##    - 左右反転ビューを返す（要素はコピーしない）
  ##    - shiftのbaseは維持
  func flipLR*[T](v: View2D[T]): View2D[T] =
    result = v
    result.offset += (v.w - 1) * v.st_x
    result.st_x = -v.st_x
  ##- **View2D[T].rotate90**
  ##    - 90度回転ビューを返す（h↔w, ストライド変換）
  ##    - shiftのbaseは維持
  func rotate90*[T](v: View2D[T]): View2D[T] =
    result = v
    swap(result.h, result.w)
    let old_st_y = v.st_y
    let old_st_x = v.st_x
    result.offset += (v.h - 1) * old_st_y
    result.st_y = old_st_x
    result.st_x = -old_st_y
    swap(result.base_y, result.base_x)
  ##- **View2D[T].toGrid**: Grid[T]
  ##    - 2Dビューをグリッドに新規変換（base は無視）
  func toGrid*[T](v: View2D[T]): Grid[T] =
    var flat = newSeq[T](v.h * v.w)
    var i = 0
    for y in 0 ..< v.h:
      for x in 0 ..< v.w:
        flat[i] = v[y, x]
        inc i
    Grid[T](data: flat, h: v.h, w: v.w)
  ##- **View2D[T].toSeq**: seq[seq[T]]
  ##    - 2Dビューを新規二次元配列に変換（base は無視）
  func toSeq*[T](v: View2D[T]): seq[seq[T]] =
    result = newSeqWith(v.h, newSeq[T](v.w))
    for y in 0 ..< v.h:
      for x in 0 ..< v.w:
        let rowOffset = v.offset + y * v.st_y
        for x_idx in 0 ..< v.w:
          result[y][x_idx] = v.data[rowOffset + x_idx * v.st_x]
  ##- **View2D[T].rows**
  ##    - 各行をView1Dとして遅延列挙（base は無視）
  iterator rows*[T](v: View2D[T]): View1D[T] =
    for y in 0 ..< v.h:
      yield View1D[T](
        data: v.data,
        len: v.w,
        offset: v.offset + y * v.st_y,
        step: v.st_x,
        base: v.base_x
      )
  iterator items*[T](v: View2D[T]): T =
    for y in 0 ..< v.h:
      let rowOffset = v.offset + y * v.st_y
      for x in 0 ..< v.w:
        yield v.data[rowOffset + x * v.st_x]
  proc `$`*[T](v: View2D[T]): string =
    var res = newSeq[string]()
    for row in v.rows:
      res.add($row)
    return res.join("\n")
  type CircularView2D*[T] = object
    base: View2D[T]
    y_offset, y_step: int
    x_offset, x_step: int
  func circular*[T](v: View2D[T]): CircularView2D[T] =
    CircularView2D[T](
      base: v,
      y_offset: 0, y_step: 1,
      x_offset: 0, x_step: 1
    )
  ##- **Grid[T].circular**: CircularView2D[T]
  ##    - インデックスを循環させてアクセスする2次元ビュー
  func circular*[T](g: var Grid[T]): CircularView2D[T] {.inline.} = g.view.circular
  func `[]`*[T](cv: CircularView2D[T], y: int): CircularView1D[T] {.inline.} =
    let ry = floorMod(cv.y_offset + y * cv.y_step, cv.base.h)
    CircularView1D[T](
      base: cv.base[ry],
      offset: cv.x_offset,
      step: cv.x_step
    )
  func shift*[T](cv: CircularView2D[T], dy = 0, dx = 0): CircularView2D[T] =
    result = cv
    result.y_offset -= dy * cv.y_step
    result.x_offset -= dx * cv.x_step
  func start*[T](cv: CircularView2D[T], y = 0, x = 0): CircularView2D[T] =
    result = cv
    result.y_offset += y * cv.y_step
    result.x_offset += x * cv.x_step