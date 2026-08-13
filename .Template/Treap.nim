when not declared(LIBRARY_TREAP):
  const LIBRARY_TREAP = true

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

  var xorShiftState: uint32 = 2463534242'u32
  proc nextRand(): uint32 {.inline.} =
    var x = xorShiftState
    x = x xor (x shl 13)
    x = x xor (x shr 17)
    x = x xor (x shl 5)
    xorShiftState = x
    return x
  type NodeId = int32
  type
    TreapNode[T; isSorted: static[bool]] = object
      l, r: NodeId
      priority: uint32
      size: int32
      val: T
      when not isSorted:
        rev: bool
    Treap*[T; isSorted, isMulti: static[bool]] = object
      root: NodeId
      nodes: seq[TreapNode[T, isSorted]]
  proc size[T, S, M](self: Treap[T, S, M], t: NodeId): int32 {.inline.} =
    return if t == 0: 0 else: self.nodes[t].size
  proc update[T, S, M](self: var Treap[T, S, M], t: NodeId) {.inline.} =
    if t != 0:
      self.nodes[t].size = 1 + self.size(self.nodes[t].l) + self.size(self.nodes[t].r)
  proc newNode[T, S, M](self: var Treap[T, S, M], val: T): NodeId {.inline.} =
    let idx = self.nodes.len.int32
    var node = TreapNode[T, S](
      l: 0, r: 0, priority: nextRand(), size: 1, val: val
    )
    when not S:
      node.rev = false
    self.nodes.add(node)
    return idx
  proc push[T, S, M](self: var Treap[T, S, M], t: NodeId) {.inline.} =
    when not S:
      if t != 0 and self.nodes[t].rev:
        self.nodes[t].rev = false
        swap(self.nodes[t].l, self.nodes[t].r)
        let l = self.nodes[t].l
        let r = self.nodes[t].r
        if l != 0: self.nodes[l].rev = not self.nodes[l].rev
        if r != 0: self.nodes[r].rev = not self.nodes[r].rev
  proc splitByIdx[T, S, M](self: var Treap[T, S, M], t: NodeId, k: int32): (NodeId, NodeId) =
    if t == 0: return (0, 0)
    self.push(t)
    let c = self.size(self.nodes[t].l)
    if k <= c:
      let (l, r) = self.splitByIdx(self.nodes[t].l, k)
      self.nodes[t].l = r
      self.update(t)
      return (l, t)
    else:
      let (l, r) = self.splitByIdx(self.nodes[t].r, k - c - 1)
      self.nodes[t].r = l
      self.update(t)
      return (t, r)
  proc splitByValLower[T, S, M](self: var Treap[T, S, M], t: NodeId, val: T): (NodeId, NodeId) =
    if t == 0: return (0, 0)
    if self.nodes[t].val < val:
      let (l, r) = self.splitByValLower(self.nodes[t].r, val)
      self.nodes[t].r = l
      self.update(t)
      return (t, r)
    else:
      let (l, r) = self.splitByValLower(self.nodes[t].l, val)
      self.nodes[t].l = r
      self.update(t)
      return (l, t)
  proc splitByValUpper[T, S, M](self: var Treap[T, S, M], t: NodeId, val: T): (NodeId, NodeId) =
    if t == 0: return (0, 0)
    if self.nodes[t].val <= val:
      let (l, r) = self.splitByValUpper(self.nodes[t].r, val)
      self.nodes[t].r = l
      self.update(t)
      return (t, r)
    else:
      let (l, r) = self.splitByValUpper(self.nodes[t].l, val)
      self.nodes[t].l = r
      self.update(t)
      return (l, t)
  proc merge[T, S, M](self: var Treap[T, S, M], l, r: NodeId): NodeId =
    if l == 0: return r
    if r == 0: return l
    self.push(l)
    self.push(r)
    if self.nodes[l].priority > self.nodes[r].priority:
      self.nodes[l].r = self.merge(self.nodes[l].r, r)
      self.update(l)
      return l
    else:
      self.nodes[r].l = self.merge(l, self.nodes[r].l)
      self.update(r)
      return r
  proc initTreap*[T](isSorted, isMulti: static[bool], capacity: int = 200000): Treap[T, isSorted, isMulti] =
    result.nodes = newSeqOfCap[TreapNode[T, isSorted]](capacity + 1)
    # 0番目はnilダミー
    result.nodes.add(TreapNode[T, isSorted]()) 
    result.root = 0
  ##- **List / Set / MultiSet**
  ##    - **List**: インデックスによる操作が可能な動的配列 (Insert/Delete/Access: `O(log N)`). 区間反転(`reverse`)に対応
  ##    - **Set**: 重複なし順序付き集合 (`O(log N)`)
  ##    - **MultiSet**: 重複あり順序付き集合 (`O(log N)`)
  type
    List*[T] = Treap[T, false, false]     # isSorted=false
    Set*[T] = Treap[T, true, false]       # isSorted=true, isMulti=false
    MultiSet*[T] = Treap[T, true, true]   # isSorted=true, isMulti=true
  ##- **initList(capacity)**
  ##    - 空のListを初期化
  proc initList*[T](capacity: int = 200000): List[T] = initTreap[T](false, false, capacity)
  ##- **initSet(capacity)**
  ##    - 空のSetを初期化
  proc initSet*[T](capacity: int = 200000): Set[T] = initTreap[T](true, false, capacity)

  ##- **initMultiSet(capacity)**
  ##    - 空のMultiSetを初期化
  proc initMultiSet*[T](capacity: int = 200000): MultiSet[T] = initTreap[T](true, true, capacity)
  ##- **len**
  ##    - 要素数を返す
  proc len*[T, S, M](self: Treap[T, S, M]): int =
    self.size(self.root).int
  ##- **clear**
  ##    - 全要素を削除（メモリ確保領域は残る）
  proc clear*[T, S, M](self: var Treap[T, S, M]) =
    self.root = 0
    self.nodes.setLen(1)
  proc toSeqImpl[T, S, M](self: var Treap[T, S, M], t: NodeId, res: var seq[T]) =
    if t == 0: return
    self.push(t)
    self.toSeqImpl(self.nodes[t].l, res)
    res.add(self.nodes[t].val)
    self.toSeqImpl(self.nodes[t].r, res)
  ##- **toSeq**
  ##    - 現在の順序で要素を配列化して返す
  proc toSeq*[T, S, M](self: var Treap[T, S, M]): seq[T] =
    result = newSeqOfCap[T](self.len)
    self.toSeqImpl(self.root, result)
  template calcCap(n: int): int = max(n, 200000)
  ##- **toList(arr)**
  ##    - 配列からListを構築 `O(N log N)`
  proc toList*[T](arr: openArray[T]): List[T] =
    result = initList[T](calcCap(arr.len))
    for v in arr:
      # 末尾追加の最適化（Mergeを使わずRight Spineに追加）ができるが
      # ここは汎用Insert(idx)を使う
      result.insert(result.len, v)
  ##- **toSet(arr)**
  ##    - 配列からSetを構築 `O(N log N)`
  proc toSet*[T](arr: openArray[T]): Set[T] =
    result = initSet[T](calcCap(arr.len))
    for v in arr: result.incl(v)
  ##- **toMultiSet(arr)**
  ##    - 配列からMultiSetを構築 `O(N log N)`
  proc toMultiSet*[T](arr: openArray[T]): MultiSet[T] =
    result = initMultiSet[T](calcCap(arr.len))
    for v in arr: result.incl(v)
  ##- **list.insert(idx, val)**
  ##    - **List専用**: 指定インデックス idx に値 val を挿入 `O(log N)`
  proc insert*[T](self: var List[T], idx: int, val: T) =
    let k = idx.int32
    let (l, r) = self.splitByIdx(self.root, k)
    let newNode = self.newNode(val)
    self.root = self.merge(self.merge(l, newNode), r)
  ##- **list.delete(idx)**
  ##    - **List専用**: 指定インデックス idx の要素を削除 `O(log N)`
  proc delete*[T](self: var List[T], idx: int) =
    let k = idx.int32
    let (l, r_part) = self.splitByIdx(self.root, k)
    let (target, r) = self.splitByIdx(r_part, 1)
    self.root = self.merge(l, r)
  ##- **list.reverse(slice)**
  ##    - **List専用**: 指定区間 [l..r] を反転 `O(log N)`
  # 使用例: list.reverse(1..3)
  proc reverse*[T](self: var List[T], slice: HSlice[int, int]) =
    let l_idx = slice.a.int32
    let r_idx = slice.b.int32 + 1
    if l_idx >= r_idx: return
    let (l_part, r_part) = self.splitByIdx(self.root, r_idx)
    let (ll, target) = self.splitByIdx(l_part, l_idx)
    if target != 0:
      self.nodes[target].rev = not self.nodes[target].rev
    self.root = self.merge(self.merge(ll, target), r_part)
  ##- **list[i] / list[i] = val**
  ##    - **List専用**: インデックスアクセス `O(log N)`
  proc `[]`*[T](self: var List[T], idx: int): T =
    var t = self.root
    var k = idx.int32
    while true:
      self.push(t)
      let c = self.size(self.nodes[t].l)
      if k == c: return self.nodes[t].val
      if k < c:
        t = self.nodes[t].l
      else:
        t = self.nodes[t].r
        k -= (c + 1)
  ##- **list[i] / list[i] = val**
  ##    - **List専用**: インデックスアクセス `O(log N)`
  proc `[]=`*[T](self: var List[T], idx: int, val: T) =
    var t = self.root
    var k = idx.int32
    while true:
      self.push(t)
      let c = self.size(self.nodes[t].l)
      if k == c:
        self.nodes[t].val = val
        return
      if k < c:
        t = self.nodes[t].l
      else:
        t = self.nodes[t].r
        k -= (c + 1)
  ##- **lowerBound(val)**
  ##    - **Set/MultiSet**: val以上の要素が現れる最初のインデックスを返す `O(log N)`
  ##    - `val` が存在しない場合は `self.len` を返す
  proc lowerBound*[T, S, M](self: Treap[T, S, M], val: T): int =
    var t = self.root
    if t == 0: return 0
    var ret = 0
    while t != 0:
      if self.nodes[t].val >= val:
        t = self.nodes[t].l
      else:
        ret += self.size(self.nodes[t].l) + 1
        t = self.nodes[t].r
    return ret
  ##- **upperBound(val)**
  ##    - **Set/MultiSet**: valより大きい要素が現れる最初のインデックスを返す `O(log N)`
  proc upperBound*[T, S, M](self: Treap[T, S, M], val: T): int =
    var t = self.root
    if t == 0: return 0
    var ret = 0
    while t != 0:
      if self.nodes[t].val > val:
        t = self.nodes[t].l
      else:
        ret += self.size(self.nodes[t].l) + 1
        t = self.nodes[t].r
    return ret
  func less[T, M](s: Treap[T, true, M], x: T): Bisect =
    bisect(0, s.lowerBound(x))
  func lessEqual[T, M](s: Treap[T, true, M], x: T): Bisect =
    bisect(0, s.upperBound(x))
  func greaterEqual[T, M](s: Treap[T, true, M], x: T): Bisect =
    bisect(s.lowerBound(x), s.len)
  func greater[T, M](s: Treap[T, true, M], x: T): Bisect =
    bisect(s.upperBound(x), s.len)
  ##- **set[idx]**
  ##    - **Set/MultiSet**: ソート順で idx 番目(0-based)の要素を取得 `O(log N)`
  proc `[]`*[T, S, M](self: var Treap[T, S, M], idx: int): T =
    var t = self.root
    var k = idx.int32
    while true:
      let c = self.size(self.nodes[t].l)
      if k == c: return self.nodes[t].val
      if k < c:
        t = self.nodes[t].l
      else:
        t = self.nodes[t].r
        k -= (c + 1)
  ##- **incl(val)**
  ##    - **Set/MultiSet**: 要素を追加 `O(log N)`
  ##    - Setの場合は既存なら何もしない。MultiSetの場合は重複して追加する
  proc incl*[T, S, M](self: var Treap[T, S, M], val: T) =
    when M:
      let (l, r) = self.splitByValUpper(self.root, val)
      let newNode = self.newNode(val)
      self.root = self.merge(self.merge(l, newNode), r)
    else:
      let (l, r_ge) = self.splitByValLower(self.root, val)
      let (eq, r) = self.splitByValUpper(r_ge, val)
      if eq != 0:
        self.root = self.merge(self.merge(l, eq), r)
      else:
        let newNode = self.newNode(val)
        self.root = self.merge(self.merge(l, newNode), r)
  ##- **excl(val)**
  ##    - **Set/MultiSet**: 要素を削除 `O(log N)`
  ##    - 該当要素が存在しなければ何もしない。MultiSetの場合、1つだけ削除する
  proc excl*[T, S, M](self: var Treap[T, S, M], val: T) =
    let (l, r_part) = self.splitByValLower(self.root, val)
    let (target, r) = self.splitByValUpper(r_part, val)
    if target == 0: # Not found
      self.root = self.merge(l, r)
    else:
      when M:
        let remL = self.nodes[target].l
        let remR = self.nodes[target].r
        let mergedRem = self.merge(remL, remR)
        self.root = self.merge(self.merge(l, mergedRem), r)
      else:
        self.root = self.merge(l, r)
  ##- **exclAll(val)**
  ##    - **MultiSet専用**: 指定した値の要素を全て削除 `O(log N)`
  proc exclAll*[T](self: var MultiSet[T], val: T) =
    let (l, r_part) = self.splitByValLower(self.root, val)
    let (_, r) = self.splitByValUpper(r_part, val)
    self.root = self.merge(l, r)
  ##- **contains(val)**
  ##    - **Set/MultiSet**: 値の存在判定 `O(log N)`
  proc contains*[T, S, M](self: Treap[T, S, M], val: T): bool =
    if self.root == 0: return false
    var t = self.root
    while t != 0:
      if self.nodes[t].val == val: return true
      if self.nodes[t].val > val: t = self.nodes[t].l
      else: t = self.nodes[t].r
    return false
  ##- **count(val)**
  ##    - **Set/MultiSet**: 指定した値の個数を返す `O(log N)`
  proc count*[T, S, M](self: Treap[T, S, M], val: T): int =
    return self.upperBound(val) - self.lowerBound(val)
  iterator items*[T, S, M](self: Treap[T, S, M]): T =
    var stack: seq[tuple[t: NodeId, flipIn: bool]]
    var t = self.root
    var flip = false

    while t != 0 or stack.len > 0:
      if t != 0:
        when S:
          stack.add((t, false))
          t = self.nodes[t].l
        else:
          let eff = flip xor self.nodes[t].rev
          stack.add((t, flip))
          t = (if eff: self.nodes[t].r else: self.nodes[t].l)
          flip = eff
      else:
        let (node, inFlip) = stack.pop()
        when S:
          yield self.nodes[node].val
          t = self.nodes[node].r
        else:
          let eff = inFlip xor self.nodes[node].rev
          yield self.nodes[node].val
          t = (if eff: self.nodes[node].l else: self.nodes[node].r)
          flip = eff

  type
    Affine*[T] = object
      a, b: T
    AffineSegNode*[T] = object
      sum, min, max: T
      sz: int
  proc `*`*[T](x: Affine[T], y: T): Affine[T] = Affine[T](a: x.a * y, b: x.b * y)
  proc `*`*[T](y: T, x: Affine[T]): Affine[T] = Affine[T](a: y * x.a, b: y * x.b)
  proc `+`*[T](x: Affine[T], y: T): Affine[T] = Affine[T](a: x.a, b: x.b + y)
  proc `+`*[T](y: T, x: Affine[T]): Affine[T] = Affine[T](a: x.a, b: y + x.b)
  proc `-`*[T](x: Affine[T], y: T): Affine[T] = Affine[T](a: x.a, b: x.b - y)
  proc `-`*[T](y: T, x: Affine[T]): Affine[T] = Affine[T](a: -x.a, b: y - x.b)
  proc `-`*[T](x: Affine[T]): Affine[T] = Affine[T](a: -x.a, b: -x.b)
  type AffineSegTree*[T] = object
    n, size, log: int
    data: seq[AffineSegNode[T]]
    lazy: seq[Affine[T]]
  proc op[T](a, b: AffineSegNode[T]): AffineSegNode[T] {.inline.} =
    result.sum = a.sum + b.sum
    result.min = min(a.min, b.min)
    result.max = max(a.max, b.max)
    result.sz = a.sz + b.sz
  proc e[T](): AffineSegNode[T] {.inline.} =
    result.sum = 0
    result.sz = 0
    when T is SomeFloat:
      result.min = Inf; result.max = -Inf
    else:
      result.min = T.high; result.max = T.low
  proc mapping[T](f: Affine[T], s: AffineSegNode[T]): AffineSegNode[T] {.inline.} =
    if s.sz == 0: return s
    result.sz = s.sz
    result.sum = s.sum * f.a + f.b * T(s.sz)
    let v1 = s.min * f.a + f.b
    let v2 = s.max * f.a + f.b
    if f.a >= 0:
      result.min = v1; result.max = v2
    else:
      result.min = v2; result.max = v1
  proc composition[T](f, g: Affine[T]): Affine[T] {.inline.} =
    result.a = f.a * g.a
    result.b = f.a * g.b + f.b
  proc id[T](): Affine[T] {.inline.} =
    Affine[T](a: 1, b: 0)
  ##- **initAffineSegTree(v)**
  ##    - 配列 v で初期化。サイズは 2の冪乗に拡張される
  proc initAffineSegTree*[T](v: seq[T]): AffineSegTree[T] =
    let n = v.len
    var log = 0
    while (1 shl log) < n: log.inc
    let size = 1 shl log
    result = AffineSegTree[T](n: n, size: size, log: log)
    result.data = newSeqWith(2 * size, e[T]())
    result.lazy = newSeqWith(size, id[T]())
    for i in 0 ..< n:
      result.data[size + i] = AffineSegNode[T](sum: v[i], min: v[i], max: v[i], sz: 1)
    for i in countdown(size - 1, 1):
      result.data[i] = op(result.data[2 * i], result.data[2 * i + 1])
  ##- **toAffineSegTree(v)**
  ##    - 配列 v から AffineSegTree を構築
  proc toAffineSegTree*[T](v: openArray[T]): AffineSegTree[T] =
    let n = v.len
    var log = 0
    while (1 shl log) < n: log.inc
    let size = 1 shl log
    result = AffineSegTree[T](n: n, size: size, log: log)
    result.data = newSeqWith(2 * size, e[T]())
    result.lazy = newSeqWith(size, id[T]())
    for i in 0 ..< n:
      result.data[size + i] = AffineSegNode[T](sum: v[i], min: v[i], max: v[i], sz: 1)
    for i in countdown(size - 1, 1):
      result.data[i] = op(result.data[2 * i], result.data[2 * i + 1])
  proc len*[T](self: AffineSegTree[T]): int = self.n
  proc update[T](self: var AffineSegTree[T], k: int) {.inline.} =
    self.data[k] = op(self.data[2 * k], self.data[2 * k + 1])
  proc allApply[T](self: var AffineSegTree[T], k: int, f: Affine[T]) {.inline.} =
    self.data[k] = mapping(f, self.data[k])
    if k < self.size:
      self.lazy[k] = composition(f, self.lazy[k])
  proc push[T](self: var AffineSegTree[T], k: int) {.inline.} =
    if self.lazy[k] == id[T](): return
    self.allApply(2 * k, self.lazy[k])
    self.allApply(2 * k + 1, self.lazy[k])
    self.lazy[k] = id[T]()
  ##- **st.set(i, x) / st[i] = x**
  ##    - 点更新: i 番目の要素を x に設定 `O(log N)`
  proc set*[T](self: var AffineSegTree[T], p: int, x: T) =
    var p = p + self.size
    for i in countdown(self.log, 1): self.push(p shr i)
    self.data[p] = AffineSegNode[T](sum: x, min: x, max: x, sz: 1)
    for i in 1 .. self.log: self.update(p shr i)
  ##- **st.get(i) / st[i]**
  ##    - 点取得: i 番目の要素を取得 `O(log N)`
  proc get*[T](self: var AffineSegTree[T], p: int): T =
    var p = p + self.size
    for i in countdown(self.log, 1): self.push(p shr i)
    return self.data[p].sum
  proc toSeq*[T](self: var AffineSegTree[T]): seq[T] =
    result = newSeq[T](self.n)
    for i in 0 ..< self.n:
      result[i] = self.get(i)
  proc applyImpl[T](self: var AffineSegTree[T], a, b: int, f: Affine[T], k, l, r: int) =
    if b <= l or r <= a: return
    if a <= l and r <= b:
      self.allApply(k, f)
      return
    self.push(k)
    let mid = (l + r) div 2
    self.applyImpl(a, b, f, 2 * k, l, mid)
    self.applyImpl(a, b, f, 2 * k + 1, mid, r)
    self.update(k)
  ##- **st.apply(l..r, val)**
  ##    - 区間アフィン更新 `O(log N)`
  ##    - `val` が `Affine[T]` 型: $x \leftarrow val.a \times x + val.b$
  ##    - `val` が `T` 型: 区間代入 $x \leftarrow val$ ($0 \times x + val$)
  ##    - ブロック `st.apply(l..r): expr`: `it` (単位元) に対する操作として記述
  template apply*[T](self: var AffineSegTree[T], slice: HSlice[int, int], expr: untyped) =
    when compiles((let _ : Affine[T] = expr)):
      self.applyImpl(slice.a, slice.b + 1, expr, 1, 0, self.size)
    elif compiles((let _ : T = expr)):
      self.applyImpl(slice.a, slice.b + 1, Affine[T](a: 0, b: expr), 1, 0, self.size)
    else:
      block:
        let it {.inject.} = Affine[T](a: 1, b: 0)
        let f = expr
        self.applyImpl(slice.a, slice.b + 1, f, 1, 0, self.size)
  proc queryRec[T](self: var AffineSegTree[T], a, b: int, k, l, r: int): AffineSegNode[T] =
    if b <= l or r <= a: return e[T]()
    if a <= l and r <= b: return self.data[k]
    self.push(k)
    let mid = (l + r) div 2
    return op(self.queryRec(a, b, 2 * k, l, mid), self.queryRec(a, b, 2 * k + 1, mid, r))
  type SegProxy*[T; Mode: static int] = object
    tree: ptr AffineSegTree[T]
  ##- **st.sum[l..r] / st.min[l..r] / st.max[l..r]**
  ##    - 区間取得 `O(log N)`
  ##    - `sum`: 総和, `min`: 最小値, `max`: 最大値
  proc sum*[T](self: var AffineSegTree[T]): SegProxy[T, 0] = result.tree = addr self
  proc min*[T](self: var AffineSegTree[T]): SegProxy[T, 1] = result.tree = addr self
  proc max*[T](self: var AffineSegTree[T]): SegProxy[T, 2] = result.tree = addr self
  proc `[]`*[T, M](proxy: SegProxy[T, M], slice: HSlice[int, int]): T =
    let res = proxy.tree[].queryRec(slice.a, slice.b + 1, 1, 0, proxy.tree[].size)
    when M == 0: return res.sum
    elif M == 1: return res.min
    else: return res.max
  proc `[]`*[T](self: var AffineSegTree[T], p: int): T = self.get(p)
  proc `[]=`*[T](self: var AffineSegTree[T], p: int, val: T) = self.set(p, val)