when not declared(LIBRARY_INDEXER):
  const LIBRARY_INDEXER = true
  include "/workspaces/AtCoder-Nim/.Library/.Template/Template.nim"

  type
    IdxMode* = enum
      Order
      Compact
    Indices*[T] = object
      val*: seq[T]
      orig*: seq[int]
      rank*: seq[int]
  ##- **openArray[T].indexer(mode = Compact)**: Indices[T]
  ##    - 配列をソートしつつインデックス変換
  ##    - Order: 重複ありモードと Compact: 重複なし（座標圧縮）モード
  ##- **Indices[T].val**: seq[T]
  ##    - （圧縮）ソート後の値の配列
  ##- **Indices[T].orig**: seq[int]
  ##    - 元インデックス（今のインデックス→元のインデックス、今そこにいるのは元のどこにいたものか）の配列
  ##- **Indices[T].rank**: seq[int]
  ##    - 順位（元のインデックス→今のインデックス、元そこにいたものはソート後何番目になったか）の配列
  # 使用例:
  # let ro = @[6,1,3,3].indexer(Order)
  # ro.val == @[1,3,3,6]  ： ソート後の値
  # ro.orig == @[1,2,3,0]  ： 元のインデックス（今のインデックス→元のインデックス）
  # ro.rank == @[3,0,1,2]  ： 各要素の順位（元のインデックス→今のインデックス）
  # let rc = @[6,1,3,3].indexer
  # rc.val == @[1,3,6]  ： ソート後の値
  # rc.rank == @[2,0,1,1]  ： 各要素の順位（元のインデックス→今のインデックス）
  proc indexer*[T](a: openArray[T], mode = Compact): Indices[T] =
    result.orig = newSeq[int](a.len)
    result.rank = newSeq[int](a.len)
    case mode
    of Order:
      var pairs = newSeqOfCap[(T, int)](a.len)
      for i, x in a: pairs.add((x, i))
      pairs.sort
      result.val = newSeq[T](a.len)
      result.orig = newSeq[int](a.len)
      for r, (v, origIdx) in pairs:
        result.val[r] = v
        result.orig[r] = origIdx
        result.rank[origIdx] = r
    of Compact:
      result.val = a.toSeq.sorted.deduplicate(isSorted = true)
      for i, x in a:
        result.rank[i] = result.val.lowerBound(x)
  ##- **Indices[T].rankOf(val)**: int
  ##    - 値 val に対応する順位を返す (見つからなければ -1)
  proc rankOf*[T](c: Indices[T], val: T): int =
    let r = c.val.lowerBound(val)
    if r < c.val.len and c.val[r] == val: r else: -1