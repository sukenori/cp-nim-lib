when not declared(LIBRARY_TEMPLATE):
  const LIBRARY_TEMPLATE = true
  {.warning[UnusedImport]: off.}
  import math, lenientops, bitops, strutils, nre, parseutils, sequtils, algorithm, sets, tables, deques, heapqueue, macros, random, os
  import sugar except dump

  template inf(T: typedesc[int]): int = 10 ^ 18
  template inf(T: typedesc[float]): float = 1e18

  # ordDiff： 基準との ord の差を返す（引数を入れれば基準になる）
  proc ordDiff(x: char): int {.inline.} =
    case x
    of 'a'..'z': x.ord - 'a'.ord
    of 'A'..'Z': x.ord - 'A'.ord
    of '0'..'9': x.ord - '0'.ord
    else: x.ord
  proc ordDiff(x, base: char): int {.inline.} =
    x.ord - base.ord

  # ceilDiv： Nim では負数の定義がないので定義変更（ceil/floor も ceilDiv/floorDiv も右／左を返す）
  template ceilDiv[T: SomeSignedInt](a, b: T): T =
    -floorDiv(-a, b)

  # isqrt： 非負整数に切り捨てる sqrt
  proc isqrt(n: int): int {.inline.} =
    var
      x = n
      nx = (x + 1) div 2
    while x > nx:
      x = nx
      nx = (x + n div x) div 2
    return x

  proc chMin[T](a: var T, b: T): bool {.discardable, inline.} =
    if a > b:
      a = b
      return true
    else:
      return false
  proc chMax[T](a: var T, b: T): bool {.discardable, inline.} =
    if a < b:
      a = b
      return true
    else:
      return false

  # フィールドが2つ、3つの tuple 演算
  proc `+`*[T](a, b: (T, T)): (T, T) {.inline.} = (a[0] + b[0], a[1] + b[1])
  proc `+`*[T](a, b: (T, T, T)): (T, T, T) {.inline.} = (a[0] + b[0], a[1] + b[1], a[2] + b[2])
  proc `-`*[T](a, b: (T, T)): (T, T) {.inline.} = (a[0] - b[0], a[1] - b[1])
  proc `-`*[T](a, b: (T, T, T)): (T, T, T) {.inline.} = (a[0] - b[0], a[1] - b[1], a[2] - b[2])
  proc `*`*[T](a: (T, T), k: T): (T, T) {.inline.} = (a[0] * k, a[1] * k)
  proc `*`*[T](a: (T, T, T), k: T): (T, T, T) {.inline.} = (a[0] * k, a[1] * k, a[2] * k)
  proc `div`*[T](a: (T, T), k: T): (T, T) {.inline.} = (a[0] div k, a[1] div k)
  proc `div`*[T](a: (T, T, T), k: T): (T, T, T) {.inline.} = (a[0] div k, a[1] div k, a[2] div k)
  proc `mod`*[T](a: (T, T), k: T): (T, T) {.inline.} = (a[0] mod k, a[1] mod k)
  proc `mod`*[T](a: (T, T, T), k: T): (T, T, T) {.inline.} = (a[0] mod k, a[1] mod k, a[2] mod k)

  # Seq[d1, d2, ... : init（型／初期値）]
  type InitSeq = object
  const Seq = InitSeq()
  template makeSeq[T](len: int, init: T): auto = newSeqWith(len, init)
  template makeSeq(len: int, init: typedesc): auto = newSeq[init](len)
  macro `[]`(s: InitSeq, args: varargs[untyped]): untyped =
    if args.len == 1 and args[0].kind != nnkExprColonExpr:
      return newCall(newTree(nnkBracketExpr, ident("newSeq"), args[0]))
    result = newCall(ident("makeSeq"), args[^1][0], args[^1][1])
    for i in countdown(args.len - 2, 0):
      result = newCall(ident("makeSeq"), args[i], result)

  # 配列に演算を定義
  template declareVectorOp(op) =
    proc op*[T](x, y: openArray[T]): seq[T] {.inline.} =
      assert x.len == y.len
      result = newSeq[T](x.len)
      for i in 0 ..< x.len: result[i] = op(x[i], y[i])
    proc op*[T](x: openArray[T], y: T): seq[T] {.inline.} =
      result = newSeq[T](x.len)
      for i in 0 ..< x.len: result[i] = op(x[i], y)
    proc op*[T](x: T, y: openArray[T]): seq[T] {.inline.} =
      result = newSeq[T](y.len)
      for i in 0 ..< y.len: result[i] = op(x, y[i])
  declareVectorOp(`+`)
  declareVectorOp(`-`)
  declareVectorOp(`*`)
  declareVectorOp(`div`)
  declareVectorOp(`mod`)

  # 配列に大小を定義
  proc `<`[T](a, b: openArray[T]): bool =
    for i in 0 ..< min(a.len, b.len):
      if a[i] < b[i]: return true
      if a[i] > b[i]: return false
    return a.len < b.len
  proc `<=`[T](a, b: openArray[T]): bool =
    return not (b < a)
  proc `>`[T](a, b: openArray[T]): bool =
    return b < a
  proc `>=`[T](a, b: openArray[T]): bool =
    return not (a < b)

  # sequtils のテンプレートにスライスをオーバーロード
  template collectIt(s: untyped; body: untyped): untyped =
    collect(newSeq):
      for it {.inject.} in s:
        body
  template mapIt(s: untyped; op: untyped): untyped =
    collectIt(s): (op)
  template filterIt*(s: untyped; pred: untyped): untyped =
    collectIt(s):
      if (pred): it
  template allIt(s: untyped; pred: untyped): bool =
    block:
      var f = true
      for it {.inject.} in s:
        if not (pred):
          f = false
          break
      f
  template anyIt(s: untyped; pred: untyped): bool =
    not allIt(s, not (pred))
  template countIt(s: untyped; pred: untyped): int =
    block:
      var c = 0
      for it {.inject.} in s:
        if (pred):
          inc c
      c

  # <.. <..<： 開区間・半開区間のスライス
  type OpenSlice*[T] = object
    a*, b*: T
    openLeft*, openRight*: bool
  func `<..`*[T](a, b: T): OpenSlice[T] =
    OpenSlice[T](a: a, b: b, openLeft: true, openRight: false)
  func `<..<`*[T](a, b: T): OpenSlice[T] =
    OpenSlice[T](a: a, b: b, openLeft: true, openRight: true)
  func `..<`*(a, b: float): OpenSlice[float] =
    OpenSlice[float](a: a, b: b, openLeft: false, openRight: true)
  proc contains*[T](r: OpenSlice[T], x: T): bool =
    (if r.openLeft: x > r.a else: x >= r.a) and
    (if r.openRight: x < r.b else: x <= r.b)
  proc isEmpty*[T](r: OpenSlice[T]): bool {.inline.} =
    r.a > r.b or
    (r.a == r.b and (r.openLeft or r.openRight))
  iterator items*[T: Ordinal](r: OpenSlice[T]): T =
    if not r.isEmpty:
      let lo = if r.openLeft: succ(r.a) else: r.a
      let hi = if r.openRight: pred(r.b) else: r.b
      for x in lo .. hi:
        yield x
  proc toClosed*[T: Ordinal](r: OpenSlice[T]): Slice[T] =
    if r.isEmpty:
      return high(T) .. low(T)
    let lo = if r.openLeft: succ(r.a) else: r.a
    let hi = if r.openRight: pred(r.b) else: r.b
    lo .. hi

  # (a .. b, step): ステップありのイテレータ（a < b なら dec する）
  iterator items(t: (HSlice[int, int], int)): int =
    let (slice, step) = t
    if slice.a <= slice.b:
      for i in countup(slice.a, slice.b, step):
        yield i
    else:
      for i in countdown(slice.a, slice.b, step):
        yield i
  func toSeq*(t: (HSlice[int, int], int)): seq[int] =
    let (slice, step) = t
    let n = abs(slice.b - slice.a) div step + 1
    result = newSeqOfCap[int](n)
    if slice.a <= slice.b:
      for i in countup(slice.a, slice.b, step):
        result.add(i)
    else:
      for i in countdown(slice.a, slice.b, step):
        result.add(i)

  # 直積イテレータ： for i,j,k,.. in prod(a, b, c,..):
  func rangeOf(n: int): Slice[int] {.inline.} = 0 ..< n
  func rangeOf(s: Slice[int]): Slice[int] {.inline.} = s
  macro prod*(x: ForLoopStmt): untyped =
    expectKind x, nnkForStmt
    let call = x[^2]
    let body = x[^1]
    let loopVars = x[0 ..< x.len - 2]
    let dims = call[1 ..< call.len]
    doAssert loopVars.len == dims.len
    result = body
    for idx in countdown(dims.len - 1, 0):
      let v = loopVars[idx]
      let d = dims[idx]
      result = quote do:
        for `v` in rangeOf(`d`):
          `result`
  # 組み合わせイテレータ： for i,j,k,.. in comb(n):
  func combLo(n: int): int {.inline.} = 0
  func combHi(n: int): int {.inline.} = n
  func combLo(s: Slice[int]): int {.inline.} = s.a
  func combHi(s: Slice[int]): int {.inline.} = s.b + 1
  macro comb*(x: ForLoopStmt): untyped =
    expectKind x, nnkForStmt
    let call = x[^2]
    let body = x[^1]
    let loopVars = x[0 ..< x.len - 2]
    let n = call[1]
    result = body
    for idx in countdown(loopVars.len - 1, 0):
      let v = loopVars[idx]
      let lo =
        if idx == 0: quote do: combLo(`n`)
        else:
          let prevVar = loopVars[idx - 1]
          quote do: (`prevVar` + 1)
      result = quote do:
        for `v` in `lo` ..< combHi(`n`):
          `result`

  # forElse 節内に break を設置、break しなかった場合その後の do: 節を実行
  proc replaceBreak*(n: NimNode, label: NimNode): NimNode =
    if n.kind in {nnkForStmt, nnkWhileStmt}:
      return n
    if n.kind == nnkBreakStmt and (n.len == 0 or n[0].kind == nnkEmpty):
      return newTree(nnkBreakStmt, label)
    result = copyNimNode(n)
    for child in n:
      result.add(replaceBreak(child, label))
  macro forElse*(loopExpr, body, elseBody: untyped): untyped =
    var i, s: NimNode
    if loopExpr.kind == nnkInfix and loopExpr[0].eqIdent("in"):
      i = loopExpr[1]
      s = loopExpr[2]
    else:
      error("Syntax error. Expected: forElse i in range:", loopExpr)
    let successLabel = genSym(nskLabel, "successLabel")
    let modifiedBody = replaceBreak(body, successLabel)
    result = quote do:
      block `successLabel`:
        for `i` in `s`:
          `modifiedBody`
        `elseBody`

  macro reduceOf(i, s, body, combine: untyped): untyped =
    let fnSym = genSym(nskProc, "reduceFn")
    let accSym = genSym(nskVar, "acc")
    let firstSym = genSym(nskVar, "first")
    let vSym = genSym(nskLet, "v")
    result = quote do:
      block:
        proc `fnSym`(`i`: typeof(`s`.a)): auto =
          `body`
        var `firstSym` = true
        var `accSym`: typeof(`fnSym`(`s`.a))
        for `i` in `s`:
          let `vSym` = `fnSym`(`i`)
          if `firstSym`:
            `accSym` = `vSym`
            `firstSym` = false
          else:
            `accSym` = `combine`(`accSym`, `vSym`)
        `accSym`
  # sumOf(i, range, expr): T
  template sumOf(i, s, body: untyped): untyped =
    reduceOf(i, s, body, `+`)
  # minOf(i, range, expr): T
  template minOf(i, s, body: untyped): untyped =
    reduceOf(i, s, body, min)
  # maxOf(i, range, expr): T
  template maxOf(i, s, body: untyped): untyped =
    reduceOf(i, s, body, max)
  # countOf(i, range, pred): int
  template countOf(i, s, body: untyped): untyped =
    sumOf(i, s, (if body: 1 else: 0))

  # loop(n)
  template loop(loopCnt: int, body: untyped) =
    for _ in 1 .. loopCnt:
      body

  # query(Q): op id: body
  macro query*(countExpr: typed, body: untyped): untyped =
    let countVar = genSym(nskVar, "q_count")
    let typeVar = genSym(nskVar, "q_type")
    let caseStmt = newTree(nnkCaseStmt, typeVar)
    let commonStmts = newStmtList()
    for node in body:
      if node.kind in {nnkCall, nnkCommand} and node[0].kind == nnkIdent and node[0].strVal == "op":
        let queryId = node[1]
        let queryBody = node[2]
        caseStmt.add(newTree(nnkOfBranch, queryId, queryBody))
      else:
        commonStmts.add(node)
    caseStmt.add(newTree(nnkElse, newStmtList(newTree(nnkDiscardStmt, newEmptyNode()))))
    result = quote do:
      var `countVar` = `countExpr`
      while `countVar` > 0:
        dec `countVar`
        var `typeVar`: int
        input(`typeVar`)
        `caseStmt`
        `commonStmts`

  # mutable(x)： const / immutable な値を可変参照に変換
  template mutable[T](x: T): var T =
    cast[ptr T](x.unsafeAddr)[]

  # int/string/float.input
  proc getcharUnlocked(): cint {.header: "<stdio.h>", importc: "getchar_unlocked".}
  proc validChar(): cint =
    while true:
      result = getcharUnlocked()
      if result notin {8 .. 13, 32}: break
  proc input(x: var int) =
    var
      ch = validChar()
      sgn = 1
    if ch == 45:
      sgn = -1
      ch = getcharUnlocked()
    x = 0
    while ch in 48 .. 57:
      x = x * 10 + (ch - 48)
      ch = getcharUnlocked()
    x *= sgn
  proc input(T: typedesc[int]): int =
    result.input
  proc input(x: var string) =
    var ch = validChar()
    x = ""
    while ch > 32:
      x.add(ch.char)
      ch = getcharUnlocked()
  proc input(T: typedesc[string]): string =
    result.input
  proc input(x: var float) =
    x = string.input.parseFloat
  proc input(T: typedesc[float]): float =
    result.input
  # seq[int].input： サイズの決まった seq[T] 全体を標準入力から読み込み
  proc input[T](s: var seq[T]) =
    for i in 0 ..< s.len:
      s[i].input
  # T.input(diff)： 入力値に diff を足した値を返す
  proc input*(T: typedesc[int], diff: int): int {.inline.} =
    result = T.input + diff
  # tuple.input： seq を並べたタプルへの並列読み込み
  macro input(t: tuple, diff: static[int] = 0): untyped =
    let
      len = newDotExpr(t[0], ident("len"))
      i = ident("i")
    var body = newStmtList()
    for s in t:
      let term = newTree(nnkBracketExpr, s, i)
      body.add newCall("input", term)
      if diff != 0:
        body.add newCall("inc", term, newLit(diff))
    result = quote do:
      for `i` in 0 ..< `len`: `body`

  template asYesNo(body: untyped): untyped =
    echo if body: "Yes" else: "No"

  template echoFloat(v: float) =
    echo v.formatFloat(ffDecimal, 20)

  # dump
  proc debugPassThrough[T](x: T, label: string = ""): T {.inline, discardable.} =
    when defined(debug):
      let prefix = if label.len > 0: label & " = " else: "\x1b[31m[DUMP]\x1b[0m "
      stderr.writeLine(prefix & $x)
    return x
  macro dump*(args: varargs[untyped]): untyped =
    when defined(debug):
      var line: NimNode = nil
      for a in args:
        let label = a.toStrLit
        let piece = quote do:
          `label` & " = " & $(`a`)
        if line == nil:
          line = piece
        else:
          line = quote do:
            `line` & "\t" & `piece`
      result = quote do:
        stderr.writeLine(`line`)
    else:
      result = newStmtList()

  # ランダムケース（test/case-caseIdx.in）の生成
  when defined(gen):

    var buf*: string = ""
    proc line*[T](x: T) =
      buf.add($x)
      buf.add('\n')
    proc row*[T](xs: openArray[T]) =
      for i, x in xs:
        if i > 0:
          buf.add(' ')
        buf.add($x)
      buf.add('\n')
    proc rows*[T](xss: openArray[seq[T]]) =
      for xs in xss:
        row(xs)

    proc rand*(r: Slice[int]): int =
      assert r.a <= r.b, "rand: empty integer range"
      random.rand(r)
    proc rand*(r: Slice[char]): char =
      assert r.a <= r.b, "rand: empty char range"
      char(random.rand(ord(r.a) .. ord(r.b)))
    proc rand*(r: Slice[float]): float =
      assert r.a <= r.b, "rand: empty float range"
      r.a + random.rand(1.0) * (r.b - r.a)
    proc rand*(r: OpenSlice[int]): int =
      assert not r.isEmpty, "rand: empty integer range"
      random.rand(r.toClosed())
    proc rand*(r: OpenSlice[char]): char =
      assert not r.isEmpty, "rand: empty char range"
      let c = r.toClosed()
      char(random.rand(ord(c.a) .. ord(c.b)))
    proc rand*(r: OpenSlice[float]): float =
      assert not r.isEmpty, "rand: empty float range"
      while true:
        result = r.a + random.rand(1.0) * (r.b - r.a)
        if result < r.b:
          return

    type RandOpt* = enum
      unique
      inc
      dec
      directed
      connected
      acyclic
      noMultipleEdge
      noSelfLoop
      simple
    proc checkSeqOpts(opts: set[RandOpt]) =
      assert not (inc in opts and dec in opts), "randSeq: inc and dec cannot be specified together"
    proc sortSeq[T](xs: var seq[T], opts: set[RandOpt]) =
      if inc in opts:
        xs.sort(SortOrder.Ascending)
      elif dec in opts:
        xs.sort(SortOrder.Descending)

    # randSeqFlat 重複ありで n 回引く
    proc sampleWithReplacement[T](n: int, pick: proc(): T): seq[T] =
      result = newSeq[T](n)
      for i in 0 ..< n:
        result[i] = pick()
    proc sampleUnique[T](n: int, pool: seq[T], errMsg: string): seq[T] =
      assert pool.len >= n, errMsg
      var p = pool
      shuffle(p)
      p[0 ..< n]
    proc randSeqFlat*(n: int, r: Slice[int], opts: set[RandOpt] = {}): seq[int] =
      checkSeqOpts(opts)
      assert n >= 0, "randSeq: negative length"
      if unique in opts:
        result = sampleUnique(n, toSeq(r.a .. r.b), "randSeq: range too small for unique")
      else:
        result = sampleWithReplacement(n, () => rand(r))
      result.sortSeq(opts)
    proc randSeqFlat*(n: int, r: OpenSlice[int], opts: set[RandOpt] = {}): seq[int] =
      let c = r.toClosed()
      assert c.a <= c.b, "randSeq: empty integer range"
      randSeqFlat(n, c, opts)
    proc randSeqFlat*(n: int, r: Slice[float] | OpenSlice[float], opts: set[RandOpt] = {}): seq[float] =
      checkSeqOpts(opts)
      assert unique notin opts, "randSeq[float]: unique is unsupported"
      assert n >= 0, "randSeq: negative length"
      result = newSeq[float](n)
      for i in 0 ..< n:
        result[i] = rand(r)
      result.sortSeq(opts)
    proc randSeqFlat*(n: int, r: Slice[char], opts: set[RandOpt] = {}): seq[char] =
      checkSeqOpts(opts)
      assert n >= 0, "randSeq: negative length"
      if unique in opts:
        result = sampleUnique(n, toSeq(r.a .. r.b), "randSeq: range too small for unique")
      else:
        result = sampleWithReplacement(n, () => rand(r))
      result.sortSeq(opts)
    proc randSeqFlat*(n: int, r: OpenSlice[char], opts: set[RandOpt] = {}): seq[char] =
      let c = r.toClosed()
      assert c.a <= c.b, "randSeq: empty char range"
      randSeqFlat(n, c, opts)

    # randSeqPoolFlat 候補をシャッフルして先頭 n 個を取る
    proc poolOf*(c: char): seq[char] =
      @[c]
    proc poolOf*(r: Slice[char]): seq[char] =
      toSeq(r.a .. r.b)
    proc poolOf*(r: OpenSlice[char]): seq[char] =
      let c = r.toClosed()
      assert c.a <= c.b, "poolOf: empty char range"
      poolOf(c)
    proc poolOf*(s: string): seq[string] =
      assert s.len == 1, "poolOf(string): string must have length 1"
      @[s]
    proc charRangeToStrings(lo, hi: int): seq[string] =
      assert lo <= hi, "poolOf: empty string range"
      result = newSeq[string](hi - lo + 1)
      for i in 0 ..< result.len:
        result[i] = $char(lo + i)
    proc poolOf*(r: Slice[string]): seq[string] =
      assert r.a.len == 1 and r.b.len == 1,
        "poolOf(string range): endpoints must have length 1"
      charRangeToStrings(ord(r.a[0]), ord(r.b[0]))
    proc poolOf*(r: OpenSlice[string]): seq[string] =
      assert r.a.len == 1 and r.b.len == 1,
        "poolOf(string range): endpoints must have length 1"
      let lo = if r.openLeft: ord(r.a[0]) + 1 else: ord(r.a[0])
      let hi = if r.openRight: ord(r.b[0]) - 1 else: ord(r.b[0])
      charRangeToStrings(lo, hi)
    proc randSeqPoolFlat*[T](n: int, pools: openArray[seq[T]], opts: set[RandOpt] = {}): seq[T] =
      checkSeqOpts(opts)
      assert n >= 0, "randSeq: negative length"
      var pool: seq[T] = @[]
      for p in pools:
        pool.add(p)
      assert pool.len > 0 or n == 0, "randSeq: empty candidate pool"
      if unique in opts:
        var seen: HashSet[T]
        var distinctPool: seq[T] = @[]
        for x in pool:
          if x notin seen:
            seen.incl(x)
            distinctPool.add(x)
        result = sampleUnique(n, distinctPool, "randSeq: candidate pool too small for unique")
      else:
        result = sampleWithReplacement(n, () => pool[random.rand(0 ..< pool.len)])
      result.sortSeq(opts)

    # randSeq[d1,d2,..: min .. max, {unique： 重複しない／inc： 広義単調増加／dec： 広義単調減少（uniqueと一緒に指定すれば狭義）}]
    type InitRandSeq = object
    const randSeq* = InitRandSeq()
    macro `[]`*(r: InitRandSeq, args: varargs[untyped]): untyped =
      var colonPos = -1
      for i, arg in args:
        if arg.kind == nnkExprColonExpr:
          assert colonPos == -1, "randSeq: ':' must appear exactly once"
          colonPos = i
      assert colonPos >= 0, "randSeq: use randSeq[d1, d2, ...: range[, options]]"
      var dims: seq[NimNode] = @[]
      for i in 0 ..< colonPos:
        dims.add(args[i])
      let colonArg = args[colonPos]
      dims.add(colonArg[0])
      assert dims.len >= 1, "randSeq: at least one dimension is required"
      var ranges: seq[NimNode] = @[colonArg[1]]
      var opts = newTree(nnkCurly)
      for i in colonPos + 1 ..< args.len:
        if args[i].kind == nnkCurly:
          opts = args[i]
        else:
          ranges.add(args[i])
      var statements = newStmtList()
      var dimVars: seq[NimNode] = @[]
      for dim in dims:
        let dimVar = genSym(nskLet, "dim")
        dimVars.add(dimVar)
        statements.add(newLetStmt(dimVar, dim))
      var total = dimVars[0]
      for i in 1 ..< dimVars.len:
        total = newTree(nnkInfix, ident"*", total, dimVars[i])
      let flat = genSym(nskLet, "flat")
      let pos = genSym(nskVar, "pos")
      var flatCall: NimNode
      if ranges.len == 1:
        flatCall = newCall(
          ident"randSeqFlat",
          total,
          ranges[0],
          opts
        )
      else:
        var poolItems: seq[NimNode] = @[]
        for valueRange in ranges:
          poolItems.add(newCall(ident"poolOf", valueRange))
        let pools = newTree(
          nnkPrefix,
          ident"@",
          newTree(nnkBracket, poolItems)
        )
        flatCall = newCall(
          ident"randSeqPoolFlat",
          total,
          pools,
          opts
        )
      statements.add(newLetStmt(flat, flatCall))
      statements.add(newVarStmt(pos, newLit(0)))
      var value = quote do:
        block:
          let x = `flat`[`pos`]
          inc `pos`
          x
      for i in countdown(dimVars.high, 0):
        value = newCall(ident"newSeqWith", dimVars[i], value)
      statements.add(value)
      result = newTree(nnkBlockStmt, newEmptyNode(), statements)

    # randString[n: '(', ')']
    proc charsToString(cs: openArray[char]): string =
      result = newString(cs.len)
      for i, c in cs:
        result[i] = c
    type InitRandString = object
    const randString* = InitRandString()
    macro `[]`*(r: InitRandString, args: varargs[untyped]): untyped =
      assert args.len >= 1, "randString: arguments are required"
      assert args[0].kind == nnkExprColonExpr, "randString: use randString[length: char[, char or range...]]"
      let length = args[0][0]
      var options: seq[NimNode] = @[args[0][1]]
      for i in 1 ..< args.len:
        assert args[i].kind != nnkCurly, "randString: set literals are unsupported"
        options.add(args[i])
      var poolItems: seq[NimNode] = @[]
      proc addOption(node: NimNode) =
        case node.kind
        of nnkCharLit:
          poolItems.add(node)
        of nnkInfix:
          assert node.len == 3 and node[0].eqIdent(".."), "randString: each option must be a char or char range"
          assert node[1].kind == nnkCharLit and node[2].kind == nnkCharLit, "randString: range endpoints must be char literals"
          let first = char(node[1].intVal)
          let last = char(node[2].intVal)
          assert first <= last, "randString: invalid char range"
          for c in first .. last:
            poolItems.add(newLit(c))
        else:
          assert false, "randString: each option must be a char or char range"
      for option in options:
        addOption(option)
      assert poolItems.len > 0, "randString: at least one character is required"
      let pool = newTree(nnkBracket, poolItems)
      result = quote do:
        block:
          let choices = `pool`
          var s = newStringOfCap(`length`)
          for _ in 0 ..< `length`:
            s.add(choices[rand(choices.high)])
          s

    # randMap[H, W: '.', {('#', 5), ('S', 1), ('G', 1)}]
    proc randMapImpl*(h, w: int, base: char, marks: openArray[(char, int)]): seq[string] =
      assert h >= 0 and w >= 0, "randMap: negative dimension"
      let n = h * w
      var cells = newSeqWith(n, base)
      var order = toSeq(0 ..< n)
      shuffle(order)
      var pos = 0
      for (ch, count) in marks:
        assert count >= 0, "randMap: negative count"
        assert pos + count <= n, "randMap: too many marks"
        for _ in 0 ..< count:
          cells[order[pos]] = ch
          inc pos
      result = newSeq[string](h)
      for i in 0 ..< h:
        result[i] = charsToString(cells[i * w ..< (i + 1) * w])
    type InitRandMap = object
    const randMap* = InitRandMap()
    macro `[]`*(r: InitRandMap, args: varargs[untyped]): untyped =
      assert args.len == 3, "randMap: use randMap[height, width: base, {(char, count), ...}]"
      assert args[1].kind == nnkExprColonExpr, "randMap: ':' is required between width and base"
      assert args[2].kind == nnkCurly, "randMap: marks must be {(char, count), ...}"
      let h = args[0]
      let w = args[1][0]
      let base = args[1][1]
      var markItems: seq[NimNode] = @[]
      for mark in args[2]:
        markItems.add(mark)
      let marks = newTree(
        nnkPrefix,
        ident"@",
        newTree(nnkBracket, markItems)
      )
      result = newCall(ident"randMapImpl", h, w, base, marks)

    # randTree[N, {directed： 有向木}]
    # randTree[2 .. N]
    # （1-indexed、スターグラフ： 10%、パスグラフ： 10%、完全二分木： 10%、ランダム親接続： 70% で構成）
    proc randomAttachmentTree(order: seq[int]): seq[(int, int)] =
      for i in 1 ..< order.len:
        result.add((order[i], order[random.rand(0 ..< i)]))  
    proc randTreeImpl*(n: int, opts: set[RandOpt] = {}): seq[(int, int)] =
      assert n >= 1, "randTree: n must be positive"
      let shape = random.rand(0 .. 9)
      var labels = toSeq(1 .. n)
      shuffle(labels)
      result = newSeqOfCap[(int, int)](n - 1)
      let edges =
        if shape >= 3:
          randomAttachmentTree(labels)
        else:
          var e = newSeqOfCap[(int, int)](n - 1)
          for child in 2 .. n:
            let parent =
              if shape == 0:
                1
              elif shape == 1:
                child - 1
              else:
                child div 2
            e.add((labels[child - 1], labels[parent - 1]))
          e
      for pair in edges:
        let v = pair[0]  # child
        let u = pair[1]  # parent
        if directed in opts:
          result.add((u, v))
        elif random.rand(0 .. 1) == 0:
          result.add((u, v))
        else:
          result.add((v, u))
      shuffle(result)
    proc randTreeImpl*(valueRange: Slice[int] | OpenSlice[int], opts: set[RandOpt] = {}): seq[(int, int)] =
      randTreeImpl(rand(valueRange), opts)
    type InitRandTree = object
    const randTree* = InitRandTree()
    macro `[]`*(r: InitRandTree, args: varargs[untyped]): untyped =
      assert args.len == 1 or args.len == 2, "randTree: use randTree[n] or randTree[n, {options}]"
      if args.len == 1:
        result = newCall(ident"randTreeImpl", args[0])
      else:
        assert args[1].kind == nnkCurly,
          "randTree: options must be a set literal"
        result = newCall(ident"randTreeImpl", args[0], args[1])

    # randGraph[N, M, {simple, connected}]
    # randGraph[2..N, N - 1 .. 2 * N, {connected}]
    # （1-indexed のグラフ、directed 有向グラフ connected 連結グラフ acyclic 閉路なし noMultipleEdge 多重辺なし noSelfLoop 自己ループなし simple 単純グラフ
    # （noMultipleEdge と noSelfLoop で simple 単純グラフ）
    # （connected は無向グラフでは連結、directed 有向グラフでは弱連結グラフ）
    # （acyclic 閉路なしは無向グラフでは森、directed 有向グラフでは DAG）
    # （connected 連結グラフと acyclic 閉路なしで m = n - 1 の木）
    proc graphKey(u, v: int, isDirected: bool): (int, int) =
      if isDirected:
        (u, v)
      else:
        (min(u, v), max(u, v))
    proc randGraphImpl*(n, m: int, opts: set[RandOpt] = {}): seq[(int, int)] =
      assert n >= 0, "randGraph: negative vertex count"
      assert m >= 0, "randGraph: negative edge count"
      let isDirected = directed in opts
      let isConnected = connected in opts
      let isAcyclic = acyclic in opts
      let forbidMultiple = noMultipleEdge in opts or simple in opts or isAcyclic
      let forbidSelfLoop = noSelfLoop in opts or simple in opts or isAcyclic
      if n == 0:
        assert m == 0, "randGraph: n == 0 requires m == 0"
        return @[]
      if isConnected:
        assert m >= n - 1, "randGraph: connected graph requires m >= n - 1"
      if isConnected and isAcyclic:
        assert m == n - 1, "randGraph: connected acyclic graph requires m == n - 1"
      if forbidMultiple:
        let maxEdges =
          if isDirected and isAcyclic:
            n * (n - 1) div 2
          elif isDirected:
            if forbidSelfLoop: n * (n - 1)
            else: n * n
          else:
            if forbidSelfLoop: n * (n - 1) div 2
            else: n * (n + 1) div 2
        assert m <= maxEdges, "randGraph: too many edges"
      result = @[]
      var used: HashSet[(int, int)]
      # トポロジカル順序 rank で DAG を作る
      var rank = newSeq[int](n + 1)
      if isDirected and isAcyclic:
        var order = toSeq(1 .. n)
        shuffle(order)
        for i, v in order:
          rank[v] = i
      # Union-Find で閉路なし無向森を作る
      var parent = newSeq[int](n + 1)
      var size = newSeq[int](n + 1)
      proc find(x: int): int =
        var y = x
        while parent[y] != y:
          y = parent[y]
        y
      proc unite(x, y: int): bool =
        var a = find(x)
        var b = find(y)
        if a == b:
          return false
        if size[a] < size[b]:
          swap(a, b)
        parent[b] = a
        size[a] += size[b]
        true
      if not isDirected and isAcyclic:
        assert m <= n - 1, "randGraph: forest requires m <= n - 1"
      # connected 連結グラフならまず木を作る
      if isConnected:
        var order = toSeq(1 .. n)
        shuffle(order)
        for pair in randomAttachmentTree(order):
          var u = pair[0]
          var v = pair[1]
          if isDirected and isAcyclic:
            if rank[u] > rank[v]:
              swap(u, v)
          elif isDirected and random.rand(0 .. 1) == 1:
            swap(u, v)
          result.add((u, v))
          used.incl(graphKey(u, v, isDirected))
          if not isDirected and isAcyclic:
            discard unite(u, v)
      var tries = 0
      while result.len < m:
        inc tries
        assert tries <= 5_000_000, "randGraph: cannot satisfy constraints"
        var u = random.rand(1 .. n)
        var v = random.rand(1 .. n)
        if forbidSelfLoop and u == v:
          continue
        if isAcyclic:
          if u == v:
            continue
          if isDirected:
            if rank[u] > rank[v]:
              swap(u, v)
          else:
            if not unite(u, v):
              continue
        let key = graphKey(u, v, isDirected)
        if forbidMultiple and key in used:
          continue
        result.add((u, v))
        used.incl(key)
      shuffle(result)
    proc randGraphImpl*(nRange, mRange: Slice[int] | OpenSlice[int],
                        opts: set[RandOpt] = {}): seq[(int, int)] =
      randGraphImpl(rand(nRange), rand(mRange), opts)
    type InitRandGraph = object
    const randGraph* = InitRandGraph()
    macro `[]`*(r: InitRandGraph, args: varargs[untyped]): untyped =
      assert args.len == 2 or args.len == 3, "randGraph: use randGraph[n, m] or randGraph[n, m, {options}]"
      if args.len == 2:
        result = newCall(ident"randGraphImpl", args[0], args[1])
      else:
        assert args[2].kind == nnkCurly, "randGraph: options must be a set literal"
        result = newCall(ident"randGraphImpl", args[0], args[1], args[2])

    # emit(N, M) で N M と横一列に出力
    # emit(A) が seq[seq[T]] なら各行で出力
    proc outputPart[T](x: T): string =
      $x
    proc outputPart[T](xs: seq[T]): string =
      xs.mapIt($it).join(" ")
    proc emitOne[T](x: T) =
      line(x)
    proc emitOne[T](xs: seq[T]) =
      row(xs)
    proc emitOne[T](xss: seq[seq[T]]) =
      rows(xss)
    proc emitOne(edges: seq[(int, int)]) =
      for (u, v) in edges:
        line($u & " " & $v)
    macro emit*(args: varargs[untyped]): untyped =
      assert args.len >= 1, "emit: at least one argument is required"
      if args.len == 1:
        return newCall(ident"emitOne", args[0])
      result = newStmtList()
      for i, arg in args:
        if i > 0:
          result.add(quote do:
            buf.add(' ')
          )
        result.add(quote do:
          buf.add(outputPart(`arg`))
        )
      result.add(quote do:
        buf.add('\n')
      )

    # emitCol(A, B, C) で Ai Bi Ci を縦に出力
    proc emitCol*[T](xs: openArray[T]) =
      for x in xs:
        line(x)
    proc emitCol*[A, B](xs: openArray[A], ys: openArray[B]) =
      assert xs.len == ys.len,
        "emitCol: length mismatch"
      for i in 0 ..< xs.len:
        line($xs[i] & " " & $ys[i])
    proc emitCol*[A, B, C](xs: openArray[A], ys: openArray[B], zs: openArray[C]) =
      assert xs.len == ys.len and ys.len == zs.len, "emitCol: length mismatch"
      for i in 0 ..< xs.len:
        line($xs[i] & " " & $ys[i] & " " & $zs[i])

    # emitMap(S) で seq[string] のグリッドマップを矩形で出力
    proc emitMap*(grid: openArray[string]) =
      for s in grid:
        line(s)

    # emitGraph(G) で重みなしグラフの、emitGraph(G, W) で重み付きグラフの辺リストを出力
    proc emitGraph*(edges: openArray[(int, int)]) =
      for (u, v) in edges:
        line($u & " " & $v)
    proc emitGraph*[W](edges: openArray[(int, int)],
                      weights: openArray[W]) =
      assert edges.len == weights.len,
        "emitGraph: edge/weight length mismatch"
      for i in 0 ..< edges.len:
        let (u, v) = edges[i]
        line($u & " " & $v & " " & $weights[i])

    # flush(n): 中の emit を test/case-caseIdx.in に書き出す
    template flush*(n: int, body: untyped): untyped =
      block:
        createDir("test")
        for caseIdx in 1 .. n:
          randomize(caseIdx)
          buf.setLen(0)
          body
          writeFile("test" / ("case-" & $caseIdx & ".in"), buf)
    template flush*(body: untyped): untyped =
      flush(1, body)