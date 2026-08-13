when not declared(Library_Implicit_Treap):
  const Library_Implicit_Treap = true
  import random, rationals, macros, sequtils, algorithm

  type
    Operation[V] = proc(val_a, val_b: V): V
    IdentityOp[V] = proc(): V
    Composition[L] = proc(newLazy, oldLazy: L): L
    IdentityComp[L] = proc(): L
    Mapping[V, L] = proc(val: V, lazy: L): V
    CompareOp[V] = proc(val_a, val_b: V): int
  type
    LazyState[L] = object
      lazy: L
      reverse: bool
    NilState = object
    ImplicitNode[V, S] = ref object
      val: V
      priority: int
      size: int
      accum: V
      state: S
      l, r: ImplicitNode[V, S]

  proc nodeUpdate[V, S](
      node: ImplicitNode[V, S],
      op: Operation[V], idOp: IdentityOp[V]
  ) =
    if node == nil: return
    let l_size = if node.l != nil: node.l.size else: 0
    let r_size = if node.r != nil: node.r.size else: 0
    node.size = 1 + l_size + r_size
    let l_accum = if node.l != nil: node.l.accum else: idOp()
    let r_accum = if node.r != nil: node.r.accum else: idOp()
    node.accum = op(op(l_accum, node.val), r_accum)
  proc propagate[V, S, L](
      node: ImplicitNode[V, S],
      comp: Composition[L], idComp: IdentityComp[L],
      map: Mapping[V, L]
  ) =
    when S is NilState: discard
    elif S is LazyState[L]:
      if node == nil: return
      if node.state.reverse:
        swap(node.l, node.r)
        if node.l != nil: node.l.state.reverse = not node.l.state.reverse
        if node.r != nil: node.r.state.reverse = not node.r.state.reverse
        node.state.reverse = false
      if node.state.lazy != idComp():
        if node.l != nil:
          node.l.val = map(node.l.val, node.state.lazy)
          node.l.accum = map(node.l.accum, node.state.lazy)
          node.l.state.lazy = comp(node.state.lazy, node.l.state.lazy)
        if node.r != nil:
          node.r.val = map(node.r.val, node.state.lazy)
          node.r.accum = map(node.r.accum, node.state.lazy)
          node.r.state.lazy = comp(node.state.lazy, node.r.state.lazy)
        node.state.lazy = idComp()

  proc splitByIndex[V, S, L](
      node: ImplicitNode[V, S],
      op: Operation[V], idOp: IdentityOp[V],
      comp: Composition[L], idComp: IdentityComp[L],
      map: Mapping[V,L],
      idx: int
  ): (ImplicitNode[V, S], ImplicitNode[V, S]) =
    if node == nil:
      return (nil, nil)
    propagate(node, comp, idComp, map)
    let l_size = if node.l != nil: node.l.size else: 0
    if idx <= l_size:
      let (l, r) = splitByIndex(node.l, op, idOp, comp, idComp, map, idx)
      node.l = r
      nodeUpdate(node, op, idOp)
      return (l, node)
    else:
      let (l, r) = splitByIndex(node.r, op, idOp, comp, idComp, map, idx - l_size - 1)
      node.r = l
      nodeUpdate(node, op, idOp)
      return (node, r)
  proc splitByVal[V, S, L](
      node: ImplicitNode[V, S],
      op: Operation[V], idOp: IdentityOp[V],
      comp: Composition[L], idComp: IdentityComp[L],
      map: Mapping[V, L],
      cmp: CompareOp[V],
      val: V
  ): (ImplicitNode[V, S], ImplicitNode[V, S]) =
    if node == nil:
      return (nil, nil)
    propagate(node, comp, idComp, map)
    if cmp(node.val, val) < 0:
      let (l, r) = splitByVal(node.r, op, idOp, comp, idComp, map, cmp, val)
      node.r = l
      nodeUpdate(node, op, idOp)
      return (node, r)
    else:
      let (l, r) = splitByVal(node.l, op, idOp, comp, idComp, map, cmp, val)
      node.l = r
      nodeUpdate(node, op, idOp)
      return (l, node)
  proc mergeTreap[V, S, L](
      op: Operation[V], idOp: IdentityOp[V],
      comp: Composition[L], idComp: IdentityComp[L],
      map: Mapping[V,L],
      l, r: ImplicitNode[V, S]
  ): ImplicitNode[V, S] =
    if l == nil: return r
    if r == nil: return l
    propagate(l, comp, idComp, map)
    propagate(r, comp, idComp, map)
    if l.priority > r.priority:
      l.r = mergeTreap(op, idOp, comp, idComp, map, l.r, r)
      nodeUpdate(l, op, idOp)
      return l
    else:
      r.l = mergeTreap(op, idOp, comp, idComp, map, l, r.l)
      nodeUpdate(r, op, idOp)
      return r

  type
    ImplicitTreap[V, S, L] = object
      root: ImplicitNode[V, S]
      op: Operation[V]
      idOp: IdentityOp[V]
      comp: Composition[L]
      idComp: IdentityComp[L]
      map: Mapping[V,L]
      cmp: CompareOp[V]
      isSorted: bool
      isMulti: bool
  proc initImplicitTreap[V, S, L](
      op: Operation[V], idOp: IdentityOp[V],
      comp: Composition[L], idComp: IdentityComp[L],
      map: Mapping[V, L],
      cmp: CompareOp[V],
      isMulti: bool
  ): ImplicitTreap[V, S, L] =
    result.op = op; result.idOp = idOp
    result.comp = comp; result.idComp = idComp
    result.map = map
    result.cmp = cmp
    result.isMulti = isMulti
    result.root = nil

  proc len[V, S, L](self: ImplicitTreap[V, S, L]): int =
    if self.root == nil: 0 else: self.root.size
  proc lowerBound[V, S, L](self: var ImplicitTreap[V, S, L], val: V): int =
    result = self.len
    var
      idx = 0
      node = self.root
    while node != nil:
      propagate(node, self.comp, self.idComp, self.map)
      let l_size = if node.l != nil: node.l.size else: 0
      if self.cmp(node.val, val) >= 0:
        result = idx + l_size
        node = node.l
      else:
        idx += l_size + 1
        node = node.r
  proc upperBound[V, S, L](self: var ImplicitTreap[V, S, L], val: V): int =
    result = self.len
    var
      idx = 0
      node = self.root
    while node != nil:
      propagate(node, self.comp, self.idComp, self.map)
      let l_size = if node.l != nil: node.l.size else: 0
      if self.cmp(node.val,val) > 0:
        result = idx+l_size
        node = node.l
      else:
        idx += l_size + 1
        node = node.r

  proc createNode[V, S, L](self: var ImplicitTreap[V, S, L], val: V): ImplicitNode[V, S] =
    result = ImplicitNode[V, S](
      val: val,
      priority: rand(int.high),
      size: 1,
      accum: val,
      state: when S is LazyState[L]: 
              LazyState[L](lazy: self.idComp(), reverse: false) 
            else: 
              NilState(),
      l: nil, r: nil
    )
  proc insertByIndex[V, S, L](self: var ImplicitTreap[V, S, L], idx: int, val: V) =
    var (l, r) = splitByIndex(self.root, self.op, self.idOp, self.comp, self.idComp, self.map, idx)
    let newNode = self.createNode(val)
    l = mergeTreap(self.op, self.idOp, self.comp, self.idComp, self.map, l, newNode)
    self.root = mergeTreap(self.op, self.idOp, self.comp, self.idComp, self.map, l, r)
  proc deleteByIndex[V, S, L](self: var ImplicitTreap[V, S, L], idx: int) =
    var (l, r) = splitByIndex(self.root, self.op, self.idOp, self.comp, self.idComp, self.map, idx + 1)
    var (ll, _) = splitByIndex(l, self.op, self.idOp, self.comp, self.idComp, self.map, idx)
    self.root = mergeTreap(self.op, self.idOp, self.comp, self.idComp, self.map, ll, r)
  proc insertByVal[V, S, L](self: var ImplicitTreap[V, S, L], val: V) =
    let idx = self.lowerBound(val)
    if not self.isMulti:
      if idx < self.len and self[idx] == val.toUnAutoVal:
        return
    self.insertByIndex(idx, val)
  proc deleteByVal[V, S, L](self: var ImplicitTreap[V, S, L], val: V) =
    let idx = self.lowerBound(val)
    if idx < self.len and self[idx] == val.toUnAutoVal:
      self.deleteByIndex(idx)

  proc queryRange[V, S, L](self: var ImplicitTreap[V, S, L], slice: HSlice[int, int]): V =
    let
      l_idx = slice.a
      r_idx = slice.b + 1
    if l_idx >= r_idx: return self.idOp()
    var (l_part, r_part) = splitByIndex(self.root, self.op, self.idOp, self.comp, self.idComp, self.map, r_idx)
    var (ll_part, target) = splitByIndex(l_part, self.op, self.idOp, self.comp, self.idComp, self.map, l_idx)
    result = if target != nil: target.accum else: self.idOp()
    let merged_l = mergeTreap(self.op, self.idOp, self.comp, self.idComp, self.map, ll_part, target)
    self.root = mergeTreap(self.op, self.idOp, self.comp, self.idComp, self.map, merged_l, r_part)

  type
    AutoVal[T] = object
      val: T
      when compiles(default(T) + default(T)):
        sum: T
        size: int
      when compiles(T.inf):
        min: T
        max: T
  proc `<`[T](a, b: AutoVal[T]): bool =
    a.val < b.val
  proc toAutoVal[T](v: T): AutoVal[T] =
    result.val = v
    when compiles(default(T) + default(T)):
      result.sum = v
      result.size = 1
    when compiles(T.inf):
      result.min = v
      result.max = v
  template toUnAutoVal[T](v: T): auto =
    when T is AutoVal:
      v.val
    else:
      v
  proc autoOp[T](x, y: AutoVal[T]): AutoVal[T] =
    when compiles(default(T) + default(T)):
      result.sum = x.sum + y.sum
      result.size = x.size + y.size
    when compiles(T.inf):
      result.min = min(x.min, y.min)
      result.max = max(x.max, y.max)
  proc idAutoOp[T](): AutoVal[T] =
    when compiles(default(T) + default(T)):
      result.sum = T.default
      result.size = 0
    when compiles(T.inf):
      result.min = T.inf
      result.max = -T.inf
  type
    AffineMap[T] = object
      when compiles(default(T) * default(T)):
        a: T
        b: T
  proc compAffine[T](newLazy, oldLazy: AffineMap[T]): AffineMap[T] =
    when compiles(default(T) * default(T)):
      result.a = newLazy.a * oldLazy.a
      result.b = newLazy.a * oldLazy.b + newLazy.b
  proc idCompAffine[T](): AffineMap[T] =
    when compiles(default(T) * default(T)):
      result.a = 1
      result.b = 0
  proc mapAutoOp[T](v: AutoVal[T], f: AffineMap[T]): AutoVal[T] =
    when compiles(default(T) * default(T)):
      if v.size == 0: return v
      result.val = v.val * f.a + f.b
      result.sum = v.sum * f.a + v.size * f.b
      result.size = v.size
      when compiles(T.inf):
        if f.a >= 0:
          result.min = if v.min == T.inf: T.inf else: v.min * f.a + f.b
          result.max = if v.max == -T.inf: -T.inf else: v.max * f.a + f.b
        else:
          result.min = if v.max == T.inf: T.inf else: v.max * f.a + f.b
          result.max = if v.min == -T.inf: -T.inf else: v.min * f.a + f.b
  proc autoValCmp[T](a, b: AutoVal[T]): int =
    return system.cmp(a.val, b.val)

  type
    AggProxy[T, Mode] = object
      ImplicitTreapPtr: ptr T 
    SumProxy = object
    MinProxy = object
    MaxProxy = object
  proc sum[V, S, L](self: var ImplicitTreap[V, S, L]): AggProxy[ImplicitTreap[V, S, L], SumProxy] =
    result.ImplicitTreapPtr = addr(self)
  proc min[V, S, L](self: var ImplicitTreap[V, S, L]): AggProxy[ImplicitTreap[V, S, L], MinProxy] =
    result.ImplicitTreapPtr = addr(self)
  proc max[V, S, L](self: var ImplicitTreap[V, S, L]): AggProxy[ImplicitTreap[V, S, L], MaxProxy] =
    result.ImplicitTreapPtr = addr(self)
  proc `[]`[T](proxy: AggProxy[T, SumProxy], slice: Slice[int]): auto =
    return proxy.ImplicitTreapPtr[].queryRange(slice).sum
  proc `[]`[T](proxy: AggProxy[T, MinProxy], slice: Slice[int]): auto =
    return proxy.ImplicitTreapPtr[].queryRange(slice).min
  proc `[]`[T](proxy: AggProxy[T, MaxProxy], slice: Slice[int]): auto =
    return proxy.ImplicitTreapPtr[].queryRange(slice).max
  converter toAllSum[T](proxy: AggProxy[T, SumProxy]): auto =
    return proxy.ImplicitTreapPtr[].queryRange(0 ..< proxy.ImplicitTreapPtr[].len).sum
  converter toAllMin[T](proxy: AggProxy[T, MinProxy]): auto =
    return proxy.ImplicitTreapPtr[].queryRange(0 ..< proxy.ImplicitTreapPtr[].len).min
  converter toAlleMax[T](proxy: AggProxy[T, MaxProxy]): auto =
    return proxy.ImplicitTreapPtr[].queryRange(0 ..< proxy.ImplicitTreapPtr[].len).max
  proc applyRangeImpl[V, S, L](self: var ImplicitTreap[V, S, L], slice: Slice[int], f: L) =
    let (l, r) = (slice.a, slice.b)
    if l > r or l >= self.len: return
    var (l_part, r_part) = splitByIndex(self.root, self.op, self.idOp, self.comp, self.idComp, self.map, r + 1)
    var (ll_part, target) = splitByIndex(l_part, self.op, self.idOp, self.comp, self.idComp, self.map, l)
    if target != nil:
      target.state.lazy = self.comp(f, target.state.lazy)
      target.val = self.map(target.val, f)
      target.accum = self.map(target.accum, f)
    let merged_l = mergeTreap(self.op, self.idOp, self.comp, self.idComp, self.map, ll_part, target)
    self.root = mergeTreap(self.op, self.idOp, self.comp, self.idComp, self.map, merged_l, r_part)
  proc `*`*[T](m: AffineMap[T], v: T): AffineMap[T] =
    result.a = m.a * v
    result.b = m.b * v
  proc `*`*[T](v: T, m: AffineMap[T]): AffineMap[T] =
    result.a = v * m.a
    result.b = v * m.b
  proc `+`*[T](m: AffineMap[T], v: T): AffineMap[T] =
    result.a = m.a
    result.b = m.b + v
  proc `+`*[T](v: T, m: AffineMap[T]): AffineMap[T] =
    result.a = m.a
    result.b = v + m.b
  proc `-`*[T](m: AffineMap[T], v: T): AffineMap[T] =
    result.a = m.a
    result.b = m.b - v
  proc `-`*[T](v: T, m: AffineMap[T]): AffineMap[T] =
    result.a = -m.a
    result.b = v - m.b
  proc `-`*[T](m: AffineMap[T]): AffineMap[T] =
    result.a = -m.a
    result.b = -m.b
  template applyRange[V, S, L](self: var ImplicitTreap[V, S, L], slice: Slice[int], expr: untyped) =
    when compiles((var _: L = expr)):
      self.applyRangeImpl(slice, expr)
    elif compiles((var _: typeof(self.idComp.a) = expr)):
      block:
        type T = typeof(self.idComp.a)
        let
          val = expr
          f = AffineMap[T](a: 0.T, b: val)
        self.applyRangeImpl(slice, f)
    else:
      block:
        type T = typeof(self.idComp.a)
        let
          it {.inject.} = AffineMap[T](a: 1.T, b: 0.T)
          f = expr
        self.applyRangeImpl(slice, f)

  proc reverseRange[V, S, L](self: var ImplicitTreap[V, S, L], slice: HSlice[int, int]) =
    let
      l_idx = slice.a
      r_idx = slice.b + 1
    if l_idx >= r_idx: return
    var (l_part, r_part) = splitByIndex(self.root, self.op, self.idOp, self.comp, self.idComp, self.map, r_idx)
    var (ll_part, target) = splitByIndex(l_part, self.op, self.idOp, self.comp, self.idComp, self.map, l_idx)
    when S is LazyState[L]:
      if target != nil:
        target.state.reverse = not target.state.reverse
    let merged_l = mergeTreap(self.op, self.idOp, self.comp, self.idComp, self.map, ll_part, target)
    self.root = mergeTreap(self.op, self.idOp, self.comp, self.idComp, self.map, merged_l, r_part)
  
  proc `[]`[V, S, L](self: ImplicitTreap[V, S, L], i: int): auto =
    var mutableSelf = self.mutable
    var (l_part, r_part) = splitByIndex(mutableSelf.root, mutableSelf.op, mutableSelf.idOp, mutableSelf.comp, mutableSelf.idComp, mutableSelf.map, i + 1)
    var (ll_part, target) = splitByIndex(l_part, mutableSelf.op, mutableSelf.idOp, mutableSelf.comp, mutableSelf.idComp, mutableSelf.map, i)
    result = target.val.toUnAutoVal
    let merged_l = mergeTreap(mutableSelf.op, mutableSelf.idOp, mutableSelf.comp, mutableSelf.idComp, mutableSelf.map, ll_part, target)
    mutableSelf.root = mergeTreap(mutableSelf.op, mutableSelf.idOp, mutableSelf.comp, mutableSelf.idComp, mutableSelf.map, merged_l, r_part)
  proc `[]`[V, S, L](self: ImplicitTreap[V, S, L], i: BackwardsIndex): auto =
    var mutableSelf = self.mutable
    return mutableSelf[mutableSelf.len - int(i)]
  iterator items[V, S, L](self: ImplicitTreap[V, S, L]): auto =
    var mutableSelf = self.mutable
    for i in 0 ..< mutableSelf.len:
      yield mutableSelf[i]
  proc toSeq[V, S, L](self: ImplicitTreap[V, S, L]): auto =
    var mutableSelf = self.mutable
    type T = typeof(mutableSelf.root.val.toUnAutoVal)
    result = newSeqOfCap[T](mutableSelf.len)
    for i in 0 ..< mutableSelf.len:
      result.add(mutableSelf[i])
  proc `$`[V, S, L](self: ImplicitTreap[V, S, L]): string =
    var mutableSelf = self.mutable
    return $(mutableSelf.toSeq())
  proc toImplicitTreap[V, S, L](
      self: var ImplicitTreap[V, S, L],
      arr: openArray[V]
  ): ImplicitNode[V, S] =
    let n = arr.len
    if n == 0: return nil
    if n == 1:
      return self.createNode(arr[0])  
    let
      mid = n div 2
      l_root = toImplicitTreap(self, arr[0 ..< mid])
      r_root = toImplicitTreap(self, arr[mid ..^ 1])
    return mergeTreap(self.op, self.idOp, self.comp, self.idComp, self.map, l_root, r_root)

  proc `==`[V, S, L](a, b: var ImplicitTreap[V, S, L]): bool =
    if a.len != b.len: return false
    return a.toSeq == b.toSeq
  proc `<`[V, S, L](a, b: var ImplicitTreap[V, S, L]): bool =
    return a.toSeq < b.toSeq
  proc `<=`[V, S, L](a, b: var ImplicitTreap[V, S, L]): bool =
    return not (b < a)

  proc count[V, S, L](self: var ImplicitTreap[V, S, L], val: auto): int =
    let valNode = when V is AutoVal: val.toAutoVal else: val
    if not self.isSorted:
      result = 0
      let target = valNode.toUnAutoVal
      for item in self:
        if item == target:
          inc result
    else:
      return self.upperBound(valNode) - self.lowerBound(valNode)
  proc contains[V, S, L](self: var ImplicitTreap[V, S, L], val: auto): bool =
    let valNode = when V is AutoVal: val.toAutoVal else: val
    if not self.isSorted:
      let target = valNode.toUnAutoVal
      for item in self:
        if item == target:
          return true
      return false
    else:
      let idx = self.lowerBound(valNode)
      if idx >= self.len: return false
      return self[idx] == valNode.toUnAutoVal

  type
    list[T] = ImplicitTreap[AutoVal[T], LazyState[AffineMap[T]], AffineMap[T]]
  proc initList[T](): list[T] =
    result = initImplicitTreap[AutoVal[T], LazyState[AffineMap[T]], AffineMap[T]](
      autoOp[T], idAutoOp[T],
      compAffine[T], idCompAffine[T],
      mapAutoOp[T],
      autoValCmp[T],
      isMulti = true
    )
    result.isSorted = false

  proc newList[T](len: int = 0, default: T = default(T)): list[T] =
    result = initList[T]()
    if len > 0:
      var arr = newSeq[AutoVal[T]](len)
      let defVal = default.toAutoVal
      for i in 0 ..< len:
        arr[i] = defVal
      result.root = result.toImplicitTreap(arr)
  template newListWith(len_val: int, init_expr: untyped): untyped =
    block:
      type T = typeof((block:
        var it {.inject.} = 0
        init_expr
      ))
      var
        res = initList[T]()
        arr = newSeq[AutoVal[T]](len_val)
      for i in 0 ..< len_val:
        let it {.inject.} = i
        arr[i] = toAutoVal(init_expr)
      if len_val > 0:
        res.root = res.toImplicitTreap(arr)
      res
  type InitList = object
  const List = InitList()
  template makeList[T](len: int; init: T): auto =
    newListWith(len, init)
  template makeList(len: int; init: typedesc): auto =
    newList[init](len)
  macro `[]`(s: InitList, args: varargs[untyped]): untyped =
    if args.len == 1 and args[0].kind != nnkExprColonExpr:
      return newCall(newTree(nnkBracketExpr, ident("makeList"), args[0]))
    result = newCall(ident("makeList"), args[^1][0], args[^1][1])
    for i in countdown(args.len - 2, 0):
      result = newCall(ident("makeList"), args[i], result)

  proc toList[T](source: seq[T]): list[T] =
    result = initList[T]()
    if source.len == 0: return
    var arr = newSeq[AutoVal[T]](source.len)
    for i in 0 ..< source.len:
      arr[i] = source[i].toAutoVal
    result.root = result.toImplicitTreap(arr)

  type
    eagerList[T] = ImplicitTreap[AutoVal[T], NilState, AffineMap[T]]
  proc initEagerList[T](): eagerList[T] =
    result = initImplicitTreap[AutoVal[T], NilState, AffineMap[T]](
      autoOp[T], idAutoOp[T],
      compAffine[T], idCompAffine[T],
      mapAutoOp[T],
      autoValCmp[T],
      isMulti = true
    )
    result.isSorted = false

  proc newEagerList[T](len: int = 0, default: T = default(T)): eagerList[T] =
    result = initEagerList[T]()
    if len > 0:
      var arr = newSeq[AutoVal[T]](len)
      let defVal = default.toAutoVal
      for i in 0 ..< len:
        arr[i] = defVal
      result.root = result.toImplicitTreap(arr)
  template newEagerListWith(len_val: int, init_expr: untyped): untyped =
    block:
      type T = typeof((block:
        var it {.inject.} = 0
        init_expr
      ))
      var
        res = initEagerList[T]()
        arr = newSeq[AutoVal[T]](len_val)
      for i in 0 ..< len_val:
        let it {.inject.} = i
        arr[i] = toAutoVal(init_expr)
      if len_val > 0:
        res.root = res.toImplicitTreap(arr)
      res
  type InitEagerList = object
  const EagerList = InitEagerList()
  template makeEagerList[T](len: int; init: T): auto =
    newEagerListWith(len, init)
  template makeEagerList(len: int; init: typedesc): auto =
    newEagerList[init](len)
  macro `[]`*(s: InitEagerList, args: varargs[untyped]): untyped =
    if args.len == 1 and args[0].kind != nnkExprColonExpr:
      return newCall(newTree(nnkBracketExpr, ident("makeEagerList"), args[0]))
    result = newCall(ident("makeEagerList"), args[^1][0], args[^1][1])
    for i in countdown(args.len - 2, 0):
      result = newCall(ident("makeEagerList"), args[i], result)

  proc toEagerList[T](source: seq[T]): eagerList[T] =
    result = initEagerList[T]()
    if source.len == 0: return
    var arr = newSeq[AutoVal[T]](source.len)
    for i in 0 ..< source.len:
      arr[i] = source[i].toAutoVal
    result.root = result.toImplicitTreap(arr)

  proc addFirst[T, S, L](self: var ImplicitTreap[AutoVal[T], S, L], v: T) =
    let newNode = self.createNode(v.toAutoVal)
    self.root = mergeTreap(self.op, self.idOp, self.comp, self.idComp, self.map, newNode, self.root)
  proc addLast[T, S, L](self: var ImplicitTreap[AutoVal[T], S, L], v: T) =
    let newNode = self.createNode(v.toAutoVal)
    self.root = mergeTreap(self.op, self.idOp, self.comp, self.idComp, self.map, self.root, newNode)
  proc popFirst[T, S, L](self: var ImplicitTreap[AutoVal[T], S, L]): T {.discardable.} =
    result = self[0]
    var (l, r) = splitByIndex(self.root, self.op, self.idOp, self.comp, self.idComp, self.map, 1)
    self.root = r
  proc popLast[T, S, L](self: var ImplicitTreap[AutoVal[T], S, L]): T {.discardable.} =
    let n = self.len
    result = self[n - 1]
    var (l, r) = splitByIndex(self.root, self.op, self.idOp, self.comp, self.idComp, self.map, n - 1)
    self.root = l
  proc peekFirst[T, S, L](self: var ImplicitTreap[AutoVal[T], S, L]): T =
    return self[0]
  proc peekLast[T, S, L](self: var ImplicitTreap[AutoVal[T], S, L]): T =
    return self[self.len - 1]
  proc `[]=`[T, S, L](self: var ImplicitTreap[AutoVal[T], S, L], i: int, v: T) =
    self.deleteByIndex(i)
    self.insertByIndex(i, v.toAutoVal)
  proc `[]=`[T, S, L](self: var ImplicitTreap[AutoVal[T], S, L], i: BackwardsIndex, v: T) =
    self[self.len - int(i)] = v
  proc insert[T, S, L](self: var ImplicitTreap[AutoVal[T], S, L], i: int, v: T) =
    self.insertByIndex(i, v.toAutoVal)
  proc delete[T, S, L](self: var ImplicitTreap[AutoVal[T], S, L], i: int) =
    self.deleteByIndex(i)

  type
    Set[T] = ImplicitTreap[AutoVal[T], NilState, AffineMap[T]]
  proc initSet[T](): Set[T] =
    result = initImplicitTreap[AutoVal[T], NilState, AffineMap[T]](
      autoOp[T], idAutoOp[T],
      compAffine[T], idCompAffine[T],
      mapAutoOp[T],
      autoValCmp[T],
      isMulti = false
    )
    result.isSorted = true

  proc toSet[T](source: seq[T]): Set[T] =
    result = initSet[T]()
    if source.len == 0: return
    var arr = source
    arr.sort()
    let dedup = deduplicate(arr, isSorted = true)
    var autoArr = newSeq[AutoVal[T]](dedup.len)
    for i in 0 ..< dedup.len:
      autoArr[i] = dedup[i].toAutoVal
    result.root = result.toImplicitTreap(autoArr)

  type
    MultiSet[T] = ImplicitTreap[AutoVal[T], NilState, AffineMap[T]]
  proc initMultiSet[T](): MultiSet[T] =
    result = initImplicitTreap[AutoVal[T], NilState, AffineMap[T]](
      autoOp[T], idAutoOp[T],
      compAffine[T], idCompAffine[T],
      mapAutoOp[T],
      autoValCmp[T],
      isMulti = true
    )
    result.isSorted = true

  proc toMultiSet[T](source: seq[T]): MultiSet[T] =
    result = initMultiSet[T]()
    if source.len == 0: return
    var arr = source
    arr.sort()
    var autoArr = newSeq[AutoVal[T]](arr.len)
    for i in 0 ..< arr.len:
      autoArr[i] = arr[i].toAutoVal
    result.root = result.toImplicitTreap(autoArr)

  proc incl[T, S, L](self: var ImplicitTreap[AutoVal[T], S, L], v: T) =
    self.insertByVal(v.toAutoVal)
  proc excl[T, S, L](self: var ImplicitTreap[AutoVal[T], S, L], v: T) =
    let val = v.toAutoVal
    if self.count(v) > 0:
      self.deleteByVal(val)

  type
    OpUnion = object
    OpIntersection = object
    OpDifference = object
    OpSymmetricDifference = object
  proc setOpSeqRaw[T, OpTag](a, b: seq[T], isMulti: bool): seq[T] =
    var
      i = 0
      j = 0
    let
      n = a.len
      m = b.len
    result = newSeqOfCap[T](n + m)
    while i < n and j < m:
      let cmpRes = system.cmp(a[i], b[j])
      if cmpRes < 0:
        when OpTag is OpUnion or OpTag is OpDifference or OpTag is OpSymmetricDifference:
          result.add(a[i])
        i += 1
      elif cmpRes > 0:
        when OpTag is OpUnion or OpTag is OpSymmetricDifference:
          result.add(b[j])
        j += 1
      else:
        when OpTag is OpUnion:
          result.add(a[i])
          if isMulti: result.add(b[j])
        elif OpTag is OpIntersection:
          result.add(a[i])
        i += 1
        j += 1
    while i < n:
      when OpTag is OpUnion or OpTag is OpDifference or OpTag is OpSymmetricDifference:
        result.add(a[i])
      i += 1
    while j < m:
      when OpTag is OpUnion or OpTag is OpSymmetricDifference:
        result.add(b[j])
      j += 1
  proc union[T, S1, L1, S2, L2](a: var ImplicitTreap[AutoVal[T], S1, L1], b: var ImplicitTreap[AutoVal[T], S2, L2]): ImplicitTreap[AutoVal[T], NilState, AffineMap[T]] =
    let isMulti = a.isMulti
    result = if isMulti: initMultiSet[T]() else: initSet[T]()
    let
      seqA = a.toSeq
      seqB = b.toSeq
    if isMulti:
      var arr = seqA & seqB
      arr.sort()
      var autoArr = newSeq[AutoVal[T]](arr.len)
      for i in 0 ..< arr.len:
        autoArr[i] = arr[i].toAutoVal
      result.root = result.toImplicitTreap(autoArr)
    else:
      let merged = setOpSeqRaw[T, OpUnion](seqA, seqB, false)
      var autoArr = newSeq[AutoVal[T]](merged.len)
      for i in 0 ..< merged.len:
        autoArr[i] = merged[i].toAutoVal
      result.root = result.toImplicitTreap(autoArr)
  proc `|`[T, S1, L1, S2, L2](a: var ImplicitTreap[AutoVal[T], S1, L1], b: var ImplicitTreap[AutoVal[T], S2, L2]): auto = 
    union(a, b)
  proc intersection[T, S1, L1, S2, L2](a: var ImplicitTreap[AutoVal[T], S1, L1], b: var ImplicitTreap[AutoVal[T], S2, L2]): auto =
    let isMulti = a.isMulti
    result = if isMulti: initMultiSet[T]() else: initSet[T]()
    let merged = setOpSeqRaw[T, OpIntersection](a.toSeq, b.toSeq, isMulti)
    var autoArr = newSeq[AutoVal[T]](merged.len)
    for i in 0 ..< merged.len:
      autoArr[i] = merged[i].toAutoVal
    result.root = result.toImplicitTreap(autoArr)
  proc `&`[T, S1, L1, S2, L2](a: var ImplicitTreap[AutoVal[T], S1, L1], b: var ImplicitTreap[AutoVal[T], S2, L2]): auto = 
    intersection(a, b)
  proc difference[T, S1, L1, S2, L2](a: var ImplicitTreap[AutoVal[T], S1, L1], b: var ImplicitTreap[AutoVal[T], S2, L2]): auto =
    let isMulti = a.isMulti
    result = if isMulti: initMultiSet[T]() else: initSet[T]()
    let merged = setOpSeqRaw[T, OpDifference](a.toSeq, b.toSeq, isMulti)
    var autoArr = newSeq[AutoVal[T]](merged.len)
    for i in 0 ..< merged.len:
      autoArr[i] = merged[i].toAutoVal
    result.root = result.toImplicitTreap(autoArr)
  proc `-`[T, S1, L1, S2, L2](a: var ImplicitTreap[AutoVal[T], S1, L1], b: var ImplicitTreap[AutoVal[T], S2, L2]): auto = 
    difference(a, b)
  proc symmetricDifference[T, S1, L1, S2, L2](a: var ImplicitTreap[AutoVal[T], S1, L1], b: var ImplicitTreap[AutoVal[T], S2, L2]): auto =
    let isMulti = a.isMulti
    result = if isMulti: initMultiSet[T]() else: initSet[T]()
    let merged = setOpSeqRaw[T, OpSymmetricDifference](a.toSeq, b.toSeq, isMulti)
    var autoArr = newSeq[AutoVal[T]](merged.len)
    for i in 0 ..< merged.len:
      autoArr[i] = merged[i].toAutoVal
    result.root = result.toImplicitTreap(autoArr)
  proc `^`[T, S1, L1, S2, L2](a: var ImplicitTreap[AutoVal[T], S1, L1], b: var ImplicitTreap[AutoVal[T], S2, L2]): auto = 
    symmetricDifference(a, b)

  type MapElem[K, V] = tuple[key: K, val: V]
  proc mapElemCmp[K, V](a, b: AutoVal[MapElem[K, V]]): int =
    let c = system.cmp(a.val.key, b.val.key)
    if c != 0: return c
    return system.cmp(a.val.val, b.val.val)

  type
    Map[K, V] = ImplicitTreap[AutoVal[MapElem[K, V]], NilState, AffineMap[MapElem[K, V]]]
  proc initMap[K, V](): Map[K, V] =
    result = initImplicitTreap[AutoVal[MapElem[K, V]], NilState, AffineMap[MapElem[K, V]]](
      autoOp[MapElem[K, V]], idAutoOp[MapElem[K, V]],
      compAffine[MapElem[K, V]], idCompAffine[MapElem[K, V]],
      mapAutoOp[MapElem[K, V]],
      mapElemCmp[K, V],
      isMulti = false
    )
    result.isSorted = true

  proc toMap[K, V](source: seq[(K, V)]): Map[K, V] =
    result = initMap[K, V]()
    if source.len == 0: return
    var autoArr = newSeq[AutoVal[MapElem[K, V]]](source.len)
    for i, (k, v) in source:
      autoArr[i] = (key: k, val: v).toAutoVal
    autoArr.sort(result.cmp) 
    result.root = result.toImplicitTreap(autoArr)

  type
    MultiMap[K, V] = ImplicitTreap[AutoVal[MapElem[K, V]], NilState, AffineMap[MapElem[K, V]]]
  proc initMultiMap[K, V](): MultiMap[K, V] =
    result = initImplicitTreap[AutoVal[MapElem[K, V]], NilState, AffineMap[MapElem[K, V]]](
      autoOp[MapElem[K, V]], idAutoOp[MapElem[K, V]],
      compAffine[MapElem[K, V]], idCompAffine[MapElem[K, V]],
      mapAutoOp[MapElem[K, V]],
      mapElemCmp[K, V],
      isMulti = true
    )
    result.isSorted = true

  proc toMultiMap[K, V](source: seq[(K, V)]): MultiMap[K, V] =
    result = initMultiMap[K, V]()
    if source.len == 0: return
    var autoArr = newSeqOfCap[AutoVal[MapElem[K, V]]](source.len)
    for item in source:
      autoArr.add((key: item[0], val: item[1]).toAutoVal)
    autoArr.sort(result.cmp)
    result.root = result.toImplicitTreap(autoArr)

  proc lowerBoundByKey[K, V](self: var ImplicitTreap[AutoVal[MapElem[K, V]], NilState, AffineMap[MapElem[K, V]]], key: K): int =
    result = self.len
    var idx = 0
    var node = self.root
    while node != nil:
      propagate(node, self.comp, self.idComp, self.map)
      let l_size = if node.l != nil: node.l.size else: 0
      if system.cmp(node.val.val.key, key) >= 0:
        result = idx + l_size
        node = node.l
      else:
        idx += l_size + 1
        node = node.r
  proc upperBoundByKey[K, V](self: var ImplicitTreap[AutoVal[MapElem[K, V]], NilState, AffineMap[MapElem[K, V]]], key: K): int =
    result = self.len
    var idx = 0
    var node = self.root
    while node != nil:
      propagate(node, self.comp, self.idComp, self.map)
      let l_size = if node.l != nil: node.l.size else: 0
      if system.cmp(node.val.val.key, key) > 0:
        result = idx + l_size
        node = node.l
      else:
        idx += l_size + 1
        node = node.r
  proc keyRange[K, V](self: var ImplicitTreap[AutoVal[MapElem[K, V]], NilState, AffineMap[MapElem[K, V]]], key: K): Slice[int] =
    let l = self.lowerBoundByKey(key)
    let r = self.upperBoundByKey(key)
    return l ..< r

  proc add[K, V](self: var MultiMap[K, V], key: K, val: V) =
    self.insertByVal((key: key, val: val).toAutoVal)
  proc `[]=`[K, V](self: var Map[K, V], key: K, val: V) =
    let rng = self.keyRange(key)
    if rng.len > 0:
      self.deleteByIndex(rng.a)
    self.insertByVal((key: key, val: val).toAutoVal)
  proc `[]`[K, V](self: var Map[K, V], key: K): V =
    let rng = self.keyRange(key)
    if rng.len == 0: return
    return self[rng.a].val
  proc contains[K, V](self: var Map[K, V], key: K): bool =
    return self.keyRange(key).len > 0
  iterator rangeItems[K, V](self: var Map[K, V], keySlice: HSlice[K, K]): MapElem[K, V] =
    let
      l = self.lowerBoundByKey(keySlice.a)
      r = self.upperBoundByKey(keySlice.b)
    for i in l ..< r:
      yield self[i]
