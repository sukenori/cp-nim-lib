when not declared(LIBRARY_BISECT):
  const LIBRARY_BISECT = true
  include "/workspaces/AtCoder-Nim/.Library/.Template/Template.nim"

  type Bisect = object
    first, last, count: int
  ##- **openArray[T].less/lessEqual/greater/greaterEqual(x)**: Bisect
  ##    - ソート済み配列に対して条件を満たす範囲の先頭/末尾/要素の個数を返す
  ##- **Bisect.first**: int
  ##    - 条件を満たす範囲の先頭のインデックス（該当する要素がない場合 -1）
  ##- **Bisect.last**: int
  ##    - 条件を満たす範囲の末尾のインデックス（該当する要素がない場合 -1）
  ##- **Bisect.count**: int
  ##    - 条件を満たす範囲の要素の個数
  func bisect(l, r: int): Bisect =
    result.count = max(0, r - l)
    if result.count > 0:
      result.first = l
      result.last = r - 1
    else:
      result.first = -1
      result.last = -1
  func less[T](a: openArray[T], x: T): Bisect =
    bisect(0, a.lowerBound(x))
  func lessEqual[T](a: openArray[T], x: T): Bisect =
    bisect(0, a.upperBound(x))
  func greaterEqual[T](a: openArray[T], x: T): Bisect =
    bisect(a.lowerBound(x), a.len)
  func greater[T](a: openArray[T], x: T): Bisect =
    bisect(a.upperBound(x), a.len)
  func first(res: Bisect): int {.inline.} = res.first
  func last(res: Bisect): int {.inline.} = res.last