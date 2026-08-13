when not declared(LIBRARY_BIT):
  const LIBRARY_BIT = true
  include "/workspaces/AtCoder-Nim/.Library/.Template/Template.nim"

  type BIT*[T] = object
    n: int
    data: seq[T]
  ##- **initBIT(n)**
  ##    - サイズ n のBITを初期化（全要素 0）
  proc initBIT*[T](n: int): BIT[T] =
    result.n = n
    result.data = newSeq[T](n + 1)
  ##- **toBIT(arr)**
  ##    - 配列からBITを構築 `O(N log N)`
  proc toBIT*[T](arr: openArray[T]): BIT[T] =
    result = initBIT[T](arr.len)
    for i, x in arr:
      result.add(i, x)
  ##- **bit.add(i, x)**
  ##    - i番目 (0-based) の要素に x を加算 `O(log N)`
  proc add*[T](self: var BIT[T], i: int, x: T) =
    var idx = i + 1
    while idx <= self.n:
      self.data[idx] += x
      idx += idx and -idx
  ##- **bit.sum(i)**
  ##    - 区間 [0, i] (閉区間) の総和を計算 `O(log N)`
  proc sum*[T](self: BIT[T], i: int): T =
    var idx = i + 1
    while idx > 0:
      result += self.data[idx]
      idx -= idx and -idx
  ##- **bit.sum(l..r)**
  ##    - 区間 [l, r] (閉区間) の総和を計算 `O(log N)`
  proc sum*[T](self: BIT[T], slice: HSlice[int, int]): T =
    let l = slice.a
    let r = slice.b
    if l > r: return 0.T
    return self.sum(r) - self.sum(l - 1)
  ##- **bit.lowerBound(w)**
  ##    - `sum(0..x) >= w` となる最小のxを求める (全ての値が非負である前提)
  proc lowerBound*[T](self: BIT[T], w: T): int =
    if w <= 0: return 0
    var x = 0
    var k = 1
    while k * 2 <= self.n: k *= 2
    var curW = w
    while k > 0:
      if x + k <= self.n and self.data[x + k] < curW:
        curW -= self.data[x + k]
        x += k
      k = k div 2
    return x