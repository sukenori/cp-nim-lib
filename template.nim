when not declared(LIBRARY_TEMPLATE):
  const LIBRARY_TEMPLATE = true
  {.warning[UnusedImport]: off.}
  import math, lenientops, bitops, strutils, nre, parseutils, sequtils, algorithm, sets, tables, deques, heapqueue, macros
  import sugar except dump

  template inf(T: typedesc[int]): int = 10 ^ 18
  template inf(T: typedesc[float]): float = 1e18

  ##- **char@('a')**
  proc `@`(x: char): int =
    case x
    of 'a'..'z': x.ord - 'a'.ord
    of 'A'..'Z': x.ord - 'A'.ord
    of '0'..'9': x.ord - '0'.ord
    else: x.ord

  template ceilDiv[T: SomeSignedInt](a, b: T): int =
    -floorDiv(-a, b)

  ##- **int.isqrt**
  ##    - floor(sqrt(n)) を返す。n>=0 を仮定
  proc isqrt(n: int): int {.inline.} =
    var
      x = n
      nx = (x + 1) div 2
    while x > nx:
      x = nx
      nx = (x + n div x) div 2
    return x

  proc chMax[T](a: var T, b: T): bool {.discardable, inline.} =
    if a < b:
      a = b
      return true
    else:
      return false
  proc chMin[T](a: var T, b: T): bool {.discardable, inline.} =
    if a > b:
      a = b
      return true
    else:
      return false

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

  ##- **tuple.toSeq / seq.toTuple(n)**
  ##    - タプル ⇔ シーケンス変換ユーティリティ
  func toSeq*[T: tuple](t: T): seq[typeof(t[0])] =
    for x in t.fields:
      result.add(x)
  func toTuple*[T](s: seq[T], N: static int): auto =
    when N == 2:
      return (s[0], s[1])
    elif N == 3:
      return (s[0], s[1], s[2])

  type InitSeq = object
  const Seq = InitSeq()
  ##- **Seq[d1, d2, ... : init]**
  ##    - 任意次元の配列を直感的に生成するDSL。右端の `init` で要素初期値/型を指定
  template makeSeq[T](len: int, init: T): auto = newSeqWith(len, init)
  template makeSeq(len: int, init: typedesc): auto = newSeq[init](len)
  macro `[]`(s: InitSeq, args: varargs[untyped]): untyped =
    if args.len == 1 and args[0].kind != nnkExprColonExpr:
      return newCall(newTree(nnkBracketExpr, ident("newSeq"), args[0]))
    result = newCall(ident("makeSeq"), args[^1][0], args[^1][1])
    for i in countdown(args.len - 2, 0):
      result = newCall(ident("makeSeq"), args[i], result)

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

  proc `<`[T](a, b: openArray[T]): bool =
    for i in 0 ..< min(a.len, b.len):
      if a[i] < b[i]: return true
      if a[i] > b[i]: return false
    return a.len < b.len
  proc `<=`[T](a, b: openArray[T]): bool =
    return not (b < a)

  template mapIt(s: untyped; op: untyped): untyped =
    collect(newSeq):
      for it {.inject.} in s:
        (op)
  template allIt(s: untyped; pred: untyped): bool =
    block:
      var f = true
      for it {.inject.} in s:
        if not (pred):
          f = false
          break
      f
  template anyIt(s: untyped; pred: untyped): bool =
    block:
      var f = false
      for it {.inject.} in s:
        if (pred):
          f = true
          break
      f
  template countIt(s: untyped; pred: untyped): int =
    block:
      var c = 0
      for it {.inject.} in s:
        if (pred):
          inc c
      c
  template filterIt*(s: untyped; pred: untyped): untyped =
    collect(newSeq):
      for it {.inject.} in s:
        if (pred):
          it

  ##- **seq[T].maxIt(expr)**: T
  ##    - s の要素のうち、keyExpr（itを使って書く）を最大化する要素を返す
  template maxIt*[T](s: openArray[T], keyExpr: untyped): T =
    var best = s[0]
    var bestKey = block:
      let it {.inject.} = best
      keyExpr
    for i in 1 ..< s.len:
      let cand = s[i]
      let candKey = block:
        let it {.inject.} = cand
        keyExpr
      if candKey > bestKey:
        best = cand
        bestKey = candKey
    best
  ##- **seq[T].minIt(expr)**: T
  ##    - s の要素のうち、keyExpr（itを使って書く）を最小化する要素を返す
  template minIt*[T](s: openArray[T], keyExpr: untyped): T =
    var best = s[0]
    var bestKey = block:
      let it {.inject.} = best
      keyExpr
    for i in 1 ..< s.len:
      let cand = s[i]
      let candKey = block:
        let it {.inject.} = cand
        keyExpr
      if candKey < bestKey:
        best = cand
        bestKey = candKey
    best

  template calcIdx*(len: int, i: int): int = i
  template calcIdx*(len: int, i: BackwardsIndex): int = len - int(i)

  ##- **iterator items(HSlice[int, int], step: int)**: int
  ##    - スライスをstep幅で反復。上昇・下降を自動判定
  func getIdx*(i: BackwardsIndex, len: int): int {.inline.} =
    len - int(i)
  func getIdx*(i: int, len: int): int {.inline.} =
    i
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

  ##- **iterator perm(h, w: int / h, w, d:int): tuple[int, int] / tuple[int, int, int]
  ##    - 0 ..< h, 0 .. <w, 0 ..< dの直積のtupleを返す
  iterator perms*(h, w: int): (int, int) =
    for i in 0 ..< h:
      for j in 0 ..< w:
        yield (i, j)
  iterator perms*(h, w, d: int): (int, int, int) =
    for i in 0 ..< h:
      for j in 0 ..< w:
        for k in 0 ..< d:
          yield (i, j, k)
  ##- **iterator perm(s1, s2: Slice[int] / s1, s2, s3: Slice[int]): tuple[int, int] / tuple[int, int, int]
  ##    - 各スライスの直積のtupleを返す
  iterator perms*(s1, s2: Slice[int]): (int, int) =
    for i in s1:
      for j in s2:
        yield (i, j)
  iterator perms*(s1, s2, s3: Slice[int]): (int, int, int) =
    for i in s1:
      for j in s2:
        for k in s3:
          yield (i, j, k)
  ##- **iterator perm(seq[T], seq[T],..): seq[T]
  ##    - 各seqの直積のseqを返す
  iterator perms[T](args: varargs[seq[T]]): seq[T] =
    var result = newSeq[T](args.len)
    var indices = newSeq[int](args.len)
    if args.len > 0 and args.allIt(it.len > 0):
      for i in 0..<args.len: result[i] = args[i][0]
      yield result
      while true:
        var i = args.len - 1
        while i >= 0 and indices[i] == args[i].len - 1:
          indices[i] = 0
          result[i] = args[i][0]
          dec i
        if i < 0: break
        indices[i] += 1
        result[i] = args[i][indices[i]]
        yield result
  ##- **iterator perm(int, int,..): seq[T]
  ##    - 各整数の0 ..< iの直積のseqを返す
  iterator perms*(dims: varargs[int]): seq[int] =
    var ranges = newSeq[seq[int]](dims.len)
    for i, d in dims: ranges[i] = toSeq(0 ..< d)
    for p in perms(ranges): yield p
  ##- **iterator perm(Slice[int], Slice[int],..): seq[[int]
  ##    - 各スライスの直積のseqを返す
  iterator perms(ranges: varargs[Slice[int]]): seq[int] =
    var result = newSeq[int](ranges.len)
    var indices = newSeq[int](ranges.len)
    var lens = newSeq[int](ranges.len)
    for i in 0..<ranges.len: lens[i] = ranges[i].len
    if ranges.len > 0 and lens.allIt(it > 0):
      for i in 0..<ranges.len: result[i] = ranges[i].a
      yield result
      while true:
        var i = ranges.len - 1
        while i >= 0 and indices[i] == lens[i] - 1:
          indices[i] = 0
          result[i] = ranges[i].a
          dec i
        if i < 0: break
        indices[i] += 1
        result[i] = ranges[i].a + indices[i]
        yield result
  ##- **iterator perm(seq[T]): seq[T]
  ##    - seqの順列全列挙を返す
  iterator perms[T](a: seq[T]): seq[T] =
    var p = @a
    p.sort()
    yield p
    while p.nextPermutation():
      yield p
  ##- **iterator combs(n: int, r: static int): tuple[int, int] / tuple[int, int, int] / seq[int]
  ##    - 0 ..< n の中から、2つ / 3つ選ぶtuple / 4つ以上選ぶseqを返す
  iterator combs*(n: int, r: static int): auto =
    when r == 2:
      for i in 0 ..< n:
        for j in i + 1 ..< n:
          yield (i, j)
    elif r == 3:
      for i in 0 ..< n:
        for j in i + 1 ..< n:
          for k in j + 1 ..< n:
            yield (i, j, k)
    elif r >= 4 and r <= n:
      if r == 0: yield newSeq[int]()
      else:
        var indices = (0..<r).toSeq
        yield indices
        while true:
          var i = r - 1
          while i >= 0 and indices[i] == n - r + i: dec i
          if i < 0: break
          indices[i] += 1
          for j in i+1 ..< r: indices[j] = indices[j-1] + 1
          yield indices
  ##- **iterator combs(Slice[int], r: static int): tuple[int, int] / tuple[int, int, int] / seq[int]
  ##    - スライスの中からr個選ぶseqを返す
  iterator combs*(s: Slice[int], r: static int): auto =
    let n_start = s.a
    let n_end = s.b
    when r == 2:
      for i in n_start .. n_end:
        for j in i + 1 .. n_end:
          yield (i, j)
    elif r == 3:
      for i in n_start .. n_end:
        for j in i + 1 .. n_end:
          for k in j + 1 .. n_end:
            yield (i, j, k)
    elif r>=4:
      for c in combs(r.toSeq, k): yield c
  ##- **iterator combs(openArray[T], r: static int): seq[[T]
  ##    - 配列の中から、r個選ぶseqを返す
  iterator combs[T](a: openArray[T], r: int): seq[T] =
    let n = a.len
    if r >= 0 and r <= n:
      if r == 0: yield newSeq[T]()
      else:
        var indices = (0..<r).toSeq
        var res = newSeq[T](r)
        for i, idx in indices: res[i] = a[idx]
        yield res
        while true:
          var i = r - 1
          while i >= 0 and indices[i] == n - r + i: dec i
          if i < 0: break
          indices[i] += 1
          for j in i+1 ..< r: indices[j] = indices[j-1] + 1
          for i, idx in indices: res[i] = a[idx]
          yield res

  proc replaceBreak*(n: NimNode, label: NimNode): NimNode =
    if n.kind in {nnkForStmt, nnkWhileStmt}:
      return n
    if n.kind == nnkBreakStmt and (n.len == 0 or n[0].kind == nnkEmpty):
      return newTree(nnkBreakStmt, label)
    result = copyNimNode(n)
    for child in n:
      result.add(replaceBreak(child, label))
  ##- **forElse(i, range, body)**
  ##    - forElseループが正常に終了したときだけElse節を実行
  macro forElse*(loopExpr: untyped, body: untyped): untyped =
    var i, s: NimNode
    if loopExpr.kind == nnkInfix and loopExpr[0].eqIdent("in"):
      i = loopExpr[1]
      s = loopExpr[2]
    else:
      error("Syntax error. Expected: forElse i in range:", loopExpr)
    var loopBody = newStmtList()
    var elseBody = newStmtList()
    var foundElse = false
    let stmtList = if body.kind == nnkStmtList: body else: newStmtList(body)
    for node in stmtList:
      if not foundElse and node.kind == nnkCall and node[0].kind == nnkIdent and node[0].strVal == "Else":
        foundElse = true
        if node.len > 1 and node[1].kind == nnkStmtList:
          for child in node[1]: elseBody.add(child)
      elif foundElse:
        elseBody.add(node)
      else:
        loopBody.add(node)
    let successLabel = genSym(nskLabel, "successLabel")
    let modifiedBody = replaceBreak(loopBody, successLabel)
    result = quote do:
      block `successLabel`:
        for `i` in `s`:
          `modifiedBody`
        `elseBody`

  ##- **loop(n)**
  ##    - n回の繰り返し処理
  template loop(loopCnt: int, body: untyped) =
    for _ in 1 .. loopCnt:
      body

  ##- **query(count)**
  ##    - count回のクエリ処理
  ##    - op id: bodyの形式で分岐処理を記述
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

  ##- **sumOf(i, range, expr)**: T
  ##    - rangeの各iに対してexprを計算し、その**合計**を返す
  macro sumOf(i, s, body: untyped): untyped =
    result = quote do:
      block:
        type T = typeof((
          block:
            var `i`: typeof(`s`.a)
            `body`
        ))
        var acc: T
        for `i` in `s`:
          acc += `body`
        acc
  ##- **minOf(i, range, expr)**: T
  ##    - rangeの各iに対してexprを計算し、その**最小値**を返す
  macro minOf(i, s, body: untyped): untyped =
    result = quote do:
      block:
        type T = typeof((
          block:
            var `i`: typeof(`s`.a)
            `body`
        ))
        var acc: T
        acc = T.inf
        var isFirst = true
        for `i` in `s`:
          let v = `body`
          if isFirst:
            acc = v
            isFirst = false
          else:
            if v < acc: acc = v
        acc
  ##- **maxOf(i, range, expr)**: T
  ##    - rangeの各iに対してexprを計算し、その**最大値**を返す
  macro maxOf(i, s, body: untyped): untyped =
    result = quote do:
      block:
        type T = typeof((
          block:
            var `i`: typeof(`s`.a)
            `body`
        ))
        var acc: T
        acc = -T.inf
        var isFirst = true
        for `i` in `s`:
          let v = `body`
          if isFirst:
            acc = v
            isFirst = false
          else:
            if v > acc: acc = v
        acc
  ##- countOf(i, range, pred): int
  ##    - rangeの各iに対してpredを評価し、真となる回数を返す
  macro countOf(i, s, body: untyped): untyped =
    result = quote do:
      block:
        var acc: int = 0
        for `i` in `s`:
          if `body`: acc.inc
        acc

  ##- **mutable(x)**: var T
  ##    - const/immutableな値を可変参照に変換
  template mutable[T](x: T): var T =
    cast[ptr T](x.unsafeAddr)[]

  ##- **int / string / float.input**
  ##    - 標準入力の読み込み
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
  ##- **seq[int].input**
  ##    - seq[T]全体を標準入力から読み込み
  proc input[T](s: var seq[T]) =
    for i in 0 ..< s.len:
      s[i].input
  proc input[T](s: var seq[seq[T]]) =
    for i in 0 ..< s.len:
      s[i].input
  ##- **T.input(diff)**: T
  ##    - 入力値にdiffを足した値を返す
  proc input*(T: typedesc[int], diff: int): int {.inline.} =
    result = T.input + diff
  ##- **tuple.input**
  ##    - タプル型の各フィールドを標準入力から読み込み
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

  template `:=`*(name, value: untyped): untyped =
    (block:
      var name = value
      name)

  template asYesNo(body: untyped): untyped =
    echo if body: "Yes" else: "No"

  template echoFloat(v: float) =
    echo v.formatFloat(ffDecimal, 20)

  proc debugPassThrough[T](x: T, label: string = ""): T {.inline, discardable.} =
    when defined(debug):
      let prefix = if label.len > 0: label & " = " else: "\x1b[31m[DUMP]\x1b[0m "
      stderr.writeLine(prefix & $x)
    return x

  template dump*(x: untyped): untyped =
    when defined(debug):
      debugPassThrough(x, astToStr(x))
  # ============================================================
  # dump用（-d:debug のみ）
  # ============================================================
  when defined(debug):
    template dump*(args: varargs[string, `$`]) =
      stderr.writeLine(args.join("  "))

  # ============================================================
  # ランダムケース生成（-d:gen 時のみ）
  # ============================================================
  when defined(gen):
    import std/[algorithm, macros, os, random, sequtils, sets, strutils]

    var buf*: string = ""

    # ----------------------------------------------------------
    # 基本出力
    # ----------------------------------------------------------
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

    # ----------------------------------------------------------
    # 開区間・半開区間
    #
    #   1<..10    : (1, 10]
    #   1..<10    : [1, 10)
    #   1<..<10   : (1, 10)
    #
    # int / char / float で使える。
    #
    #   let x = rand(1.0..<2.0)
    #   if x in 1.1<..3.14:
    #     ...
    # ----------------------------------------------------------
    type OpenSlice*[T] = object
      a*, b*: T
      openLeft*, openRight*: bool

    func `<..`*[T](a, b: T): OpenSlice[T] =
      OpenSlice[T](a: a, b: b, openLeft: true, openRight: false)

    func `..<`*(a, b: float): OpenSlice[float] =
      OpenSlice[float](a: a, b: b, openLeft: false, openRight: true)

    func `<..<`*[T](a, b: T): OpenSlice[T] =
      OpenSlice[T](a: a, b: b, openLeft: true, openRight: true)

    proc contains*[T](r: OpenSlice[T], x: T): bool =
      (if r.openLeft: x > r.a else: x >= r.a) and
      (if r.openRight: x < r.b else: x <= r.b)

    proc rand*(r: Slice[int]): int =
      random.rand(r)

    proc rand*(r: Slice[char]): char =
      char(random.rand(ord(r.a) .. ord(r.b)))

    proc rand*(r: Slice[float]): float =
      assert r.a <= r.b, "rand: empty float range"
      r.a + random.rand(1.0) * (r.b - r.a)

    proc rand*(r: OpenSlice[int]): int =
      let lo = if r.openLeft: r.a + 1 else: r.a
      let hi = if r.openRight: r.b - 1 else: r.b
      assert lo <= hi, "rand: empty integer range"
      random.rand(lo .. hi)

    proc rand*(r: OpenSlice[char]): char =
      let lo = if r.openLeft: ord(r.a) + 1 else: ord(r.a)
      let hi = if r.openRight: ord(r.b) - 1 else: ord(r.b)
      assert lo <= hi, "rand: empty char range"
      char(random.rand(lo .. hi))

    proc rand*(r: OpenSlice[float]): float =
      assert r.a < r.b, "rand: empty float range"
      r.a + random.rand(1.0) * (r.b - r.a)

    # ----------------------------------------------------------
    # オプション
    #
    # randSeq:
    #   unique, inc, dec
    #
    # randTree / randGraph:
    #   directed, connected, acyclic,
    #   noMultipleEdge, noSelfLoop, simple
    # ----------------------------------------------------------
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

    # ----------------------------------------------------------
    # randSeq の内部処理
    # ----------------------------------------------------------
    proc checkSeqOpts(opts: set[RandOpt]) =
      assert not (inc in opts and dec in opts),
        "randSeq: inc and dec cannot be specified together"

    proc sortSeq[T](xs: var seq[T], opts: set[RandOpt]) =
      if inc in opts:
        xs.sort(SortOrder.Ascending)
      elif dec in opts:
        xs.sort(SortOrder.Descending)

    proc randSeqFlat*(n: int, r: Slice[int],
                      opts: set[RandOpt] = {}): seq[int] =
      checkSeqOpts(opts)
      assert n >= 0, "randSeq: negative length"

      if unique in opts:
        assert r.b - r.a + 1 >= n,
          "randSeq: range too small for unique"

        var pool = toSeq(r.a .. r.b)
        shuffle(pool)
        result = pool[0 ..< n]
      else:
        result = newSeq[int](n)
        for i in 0 ..< n:
          result[i] = rand(r)

      result.sortSeq(opts)

    proc randSeqFlat*(n: int, r: OpenSlice[int],
                      opts: set[RandOpt] = {}): seq[int] =
      let lo = if r.openLeft: r.a + 1 else: r.a
      let hi = if r.openRight: r.b - 1 else: r.b
      assert lo <= hi, "randSeq: empty integer range"
      randSeqFlat(n, lo .. hi, opts)

    proc randSeqFlat*(n: int, r: Slice[float],
                      opts: set[RandOpt] = {}): seq[float] =
      checkSeqOpts(opts)
      assert unique notin opts,
        "randSeq[float]: unique is unsupported"
      assert n >= 0, "randSeq: negative length"

      result = newSeq[float](n)
      for i in 0 ..< n:
        result[i] = rand(r)

      result.sortSeq(opts)

    proc randSeqFlat*(n: int, r: OpenSlice[float],
                      opts: set[RandOpt] = {}): seq[float] =
      checkSeqOpts(opts)
      assert unique notin opts,
        "randSeq[float]: unique is unsupported"
      assert n >= 0, "randSeq: negative length"

      result = newSeq[float](n)
      for i in 0 ..< n:
        result[i] = rand(r)

      result.sortSeq(opts)

    proc randSeqFlat*(n: int, r: Slice[char],
                      opts: set[RandOpt] = {}): seq[char] =
      checkSeqOpts(opts)
      assert n >= 0, "randSeq: negative length"

      if unique in opts:
        assert ord(r.b) - ord(r.a) + 1 >= n,
          "randSeq: range too small for unique"

        var pool = toSeq(r.a .. r.b)
        shuffle(pool)
        result = pool[0 ..< n]
      else:
        result = newSeq[char](n)
        for i in 0 ..< n:
          result[i] = rand(r)

      result.sortSeq(opts)

    proc randSeqFlat*(n: int, r: OpenSlice[char],
                      opts: set[RandOpt] = {}): seq[char] =
      let lo = if r.openLeft: char(ord(r.a) + 1) else: r.a
      let hi = if r.openRight: char(ord(r.b) - 1) else: r.b
      assert ord(lo) <= ord(hi), "randSeq: empty char range"
      randSeqFlat(n, lo .. hi, opts)

    proc poolOf*(c: char): seq[char] =
      @[c]

    proc poolOf*(r: Slice[char]): seq[char] =
      toSeq(r.a .. r.b)

    proc poolOf*(r: OpenSlice[char]): seq[char] =
      let lo = if r.openLeft: ord(r.a) + 1 else: ord(r.a)
      let hi = if r.openRight: ord(r.b) - 1 else: ord(r.b)
      assert lo <= hi, "poolOf: empty char range"

      result = newSeq[char](hi - lo + 1)
      for i in 0 ..< result.len:
        result[i] = char(lo + i)

    proc poolOf*(s: string): seq[string] =
      assert s.len == 1,
        "poolOf(string): string must have length 1"
      @[s]

    proc poolOf*(r: Slice[string]): seq[string] =
      assert r.a.len == 1 and r.b.len == 1,
        "poolOf(string range): endpoints must have length 1"

      let lo = ord(r.a[0])
      let hi = ord(r.b[0])
      assert lo <= hi, "poolOf: empty string range"

      result = newSeq[string](hi - lo + 1)
      for i in 0 ..< result.len:
        result[i] = $char(lo + i)

    proc poolOf*(r: OpenSlice[string]): seq[string] =
      assert r.a.len == 1 and r.b.len == 1,
        "poolOf(string range): endpoints must have length 1"

      let lo = if r.openLeft: ord(r.a[0]) + 1 else: ord(r.a[0])
      let hi = if r.openRight: ord(r.b[0]) - 1 else: ord(r.b[0])
      assert lo <= hi, "poolOf: empty string range"

      result = newSeq[string](hi - lo + 1)
      for i in 0 ..< result.len:
        result[i] = $char(lo + i)

    proc randSeqPoolFlat*[T](n: int, pools: openArray[seq[T]],
                            opts: set[RandOpt] = {}): seq[T] =
      checkSeqOpts(opts)
      assert n >= 0, "randSeq: negative length"

      var pool: seq[T] = @[]
      for p in pools:
        pool.add(p)

      assert pool.len > 0 or n == 0,
        "randSeq: empty candidate pool"

      if unique in opts:
        var seen: HashSet[T]
        var distinctPool: seq[T] = @[]

        for x in pool:
          if x notin seen:
            seen.incl(x)
            distinctPool.add(x)

        assert distinctPool.len >= n,
          "randSeq: candidate pool too small for unique"

        shuffle(distinctPool)
        result = distinctPool[0 ..< n]
      else:
        result = newSeq[T](n)
        for i in 0 ..< n:
          result[i] = pool[random.rand(0 ..< pool.len)]

      result.sortSeq(opts)

    # ----------------------------------------------------------
    # randSeq DSL
    #
    #   randSeq[5: 1..10]
    #   randSeq[5: 1..10, {unique, inc}]
    #   randSeq[3, 3: 1..9, {unique}]
    #   randSeq[2, 3, 4: 1..100]
    #
    # charを渡せば seq[char]、
    # stringを渡せば seq[string]。
    #
    #   randSeq[5: 'a'..'z', 'A'..'Z']
    #   randSeq[5: "a".."z"]
    #
    # unique/inc/dec は多次元でも全要素に適用される。
    # ----------------------------------------------------------
    type InitRandSeq = object

    const randSeq* = InitRandSeq()

    macro `[]`*(r: InitRandSeq, args: varargs[untyped]): untyped =
      var colonPos = -1

      for i, arg in args:
        if arg.kind == nnkExprColonExpr:
          assert colonPos == -1,
            "randSeq: ':' must appear exactly once"
          colonPos = i

      assert colonPos >= 0,
        "randSeq: use randSeq[d1, d2, ...: range[, options]]"

      var dims: seq[NimNode] = @[]
      for i in 0 ..< colonPos:
        dims.add(args[i])

      let colonArg = args[colonPos]
      dims.add(colonArg[0])

      assert dims.len >= 1,
        "randSeq: at least one dimension is required"

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

    # ----------------------------------------------------------
    # randString
    #
    #   randString[10: 'a'..'z']
    #   randString[10: 'a'..'z', 'A'..'Z', '0'..'9']
    #   randString[10: '(', ')']
    #   randString[rand(1..5): "A".."Z"]
    # ----------------------------------------------------------
    proc charsToString(cs: openArray[char]): string =
      result = newString(cs.len)
      for i, c in cs:
        result[i] = c

    type InitRandString = object

    const randString* = InitRandString()

    macro `[]`*(r: InitRandString, args: varargs[untyped]): untyped =
      assert args.len >= 1,
        "randString: arguments are required"

      assert args[0].kind == nnkExprColonExpr,
        "randString: use randString[length: char[, char or range...]]"

      let length = args[0][0]
      var options: seq[NimNode] = @[args[0][1]]

      for i in 1 ..< args.len:
        assert args[i].kind != nnkCurly,
          "randString: set literals are unsupported"
        options.add(args[i])

      var poolItems: seq[NimNode] = @[]

      proc addOption(node: NimNode) =
        case node.kind
        of nnkCharLit:
          poolItems.add(node)

        of nnkInfix:
          assert node.len == 3 and node[0].eqIdent(".."),
            "randString: each option must be a char or char range"

          assert node[1].kind == nnkCharLit and node[2].kind == nnkCharLit,
            "randString: range endpoints must be char literals"

          let first = char(node[1].intVal)
          let last = char(node[2].intVal)

          assert first <= last,
            "randString: invalid char range"

          for c in first .. last:
            poolItems.add(newLit(c))

        else:
          assert false,
            "randString: each option must be a char or char range"

      for option in options:
        addOption(option)

      assert poolItems.len > 0,
        "randString: at least one character is required"

      let pool = newTree(nnkBracket, poolItems)

      result = quote do:
        block:
          let choices = `pool`
          var s = newStringOfCap(`length`)

          for _ in 0 ..< `length`:
            s.add(choices[rand(choices.high)])

          s

    # ----------------------------------------------------------
    # randMap
    #
    #   randMap[H, W: '.', {('#', 5), ('S', 1), ('G', 1)}]
    #
    # base以外の記号は、互いに異なるランダム位置に置かれる。
    # ----------------------------------------------------------
    proc randMapImpl*(h, w: int, base: char,
                      marks: openArray[(char, int)]): seq[string] =
      assert h >= 0 and w >= 0,
        "randMap: negative dimension"

      let n = h * w
      var cells = newSeqWith(n, base)
      var order = toSeq(0 ..< n)
      shuffle(order)

      var pos = 0

      for (ch, count) in marks:
        assert count >= 0,
          "randMap: negative count"
        assert pos + count <= n,
          "randMap: too many marks"

        for _ in 0 ..< count:
          cells[order[pos]] = ch
          inc pos

      result = newSeq[string](h)

      for i in 0 ..< h:
        result[i] = charsToString(cells[i * w ..< (i + 1) * w])

    type InitRandMap = object

    const randMap* = InitRandMap()

    macro `[]`*(r: InitRandMap, args: varargs[untyped]): untyped =
      assert args.len == 3,
        "randMap: use randMap[height, width: base, {(char, count), ...}]"

      assert args[1].kind == nnkExprColonExpr,
        "randMap: ':' is required between width and base"

      assert args[2].kind == nnkCurly,
        "randMap: marks must be {(char, count), ...}"

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

    # ----------------------------------------------------------
    # randTree
    #
    # 1-indexed。
    #
    # star:   10%
    # path:   10%
    # binary: 10%
    # random: 70%
    #
    #   randTree[N]
    #   randTree[N, {directed}]
    #   randTree[2..N, {directed}]
    # ----------------------------------------------------------
    proc randTreeImpl*(n: int,
                      opts: set[RandOpt] = {}): seq[(int, int)] =
      assert n >= 1,
        "randTree: n must be positive"

      let shape = random.rand(0 .. 9)

      var labels = toSeq(1 .. n)
      shuffle(labels)

      result = newSeqOfCap[(int, int)](n - 1)

      for child in 2 .. n:
        let parent =
          if shape == 0:
            1
          elif shape == 1:
            child - 1
          elif shape == 2:
            child div 2
          else:
            random.rand(1 ..< child)

        let u = labels[parent - 1]
        let v = labels[child - 1]

        if directed in opts:
          result.add((u, v))
        elif random.rand(0 .. 1) == 0:
          result.add((u, v))
        else:
          result.add((v, u))

      shuffle(result)

    proc randTreeImpl*(valueRange: Slice[int],
                      opts: set[RandOpt] = {}): seq[(int, int)] =
      randTreeImpl(rand(valueRange), opts)

    proc randTreeImpl*(valueRange: OpenSlice[int],
                      opts: set[RandOpt] = {}): seq[(int, int)] =
      randTreeImpl(rand(valueRange), opts)

    type InitRandTree = object

    const randTree* = InitRandTree()

    macro `[]`*(r: InitRandTree, args: varargs[untyped]): untyped =
      assert args.len == 1 or args.len == 2,
        "randTree: use randTree[n] or randTree[n, {options}]"

      if args.len == 1:
        result = newCall(ident"randTreeImpl", args[0])
      else:
        assert args[1].kind == nnkCurly,
          "randTree: options must be a set literal"
        result = newCall(ident"randTreeImpl", args[0], args[1])

    # ----------------------------------------------------------
    # randGraph
    #
    # 頂点番号は1-indexed。
    #
    # connected:
    #   無向グラフでは連結。
    #   有向グラフでは弱連結。
    #
    # acyclic:
    #   無向グラフでは森。
    #   有向グラフではDAG。
    #
    # connected と acyclic を同時指定した場合、
    # m == n - 1 の木になる。
    #
    #   randGraph[N, M]
    #   randGraph[N, M, {simple, connected}]
    #   randGraph[2..N, N - 1 .. 2 * N, {connected}]
    # ----------------------------------------------------------
    proc graphKey(u, v: int, isDirected: bool): (int, int) =
      if isDirected:
        (u, v)
      else:
        (min(u, v), max(u, v))

    proc randGraphImpl*(n, m: int,
                        opts: set[RandOpt] = {}): seq[(int, int)] =
      assert n >= 0, "randGraph: negative vertex count"
      assert m >= 0, "randGraph: negative edge count"

      let isDirected = directed in opts
      let isConnected = connected in opts
      let isAcyclic = acyclic in opts
      let forbidMultiple = noMultipleEdge in opts or simple in opts or isAcyclic
      let forbidSelfLoop = noSelfLoop in opts or simple in opts or isAcyclic

      if n == 0:
        assert m == 0,
          "randGraph: n == 0 requires m == 0"
        return @[]

      if isConnected:
        assert m >= n - 1,
          "randGraph: connected graph requires m >= n - 1"

      if isConnected and isAcyclic:
        assert m == n - 1,
          "randGraph: connected acyclic graph requires m == n - 1"

      if forbidMultiple:
        let maxEdges =
          if isDirected:
            if forbidSelfLoop:
              n * (n - 1)
            else:
              n * n
          else:
            if forbidSelfLoop:
              n * (n - 1) div 2
            else:
              n * (n + 1) div 2

        assert m <= maxEdges,
          "randGraph: too many edges"

      result = @[]

      var used: HashSet[(int, int)]

      # DAG用のトポロジカル順序。
      var rank = newSeq[int](n + 1)
      if isDirected and isAcyclic:
        var order = toSeq(1 .. n)
        shuffle(order)
        for i, v in order:
          rank[v] = i

      # 無向森用Union-Find。
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
        for i in 1 .. n:
          parent[i] = i
          size[i] = 1

      # connectedなら、まずランダムな木を作る。
      if isConnected:
        var order = toSeq(1 .. n)
        shuffle(order)

        for i in 1 ..< n:
          var u = order[i]
          var v = order[random.rand(0 ..< i)]

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

        assert tries <= 5_000_000,
          "randGraph: cannot satisfy constraints"

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

    proc randGraphImpl*(nRange, mRange: Slice[int],
                        opts: set[RandOpt] = {}): seq[(int, int)] =
      randGraphImpl(rand(nRange), rand(mRange), opts)

    proc randGraphImpl*(nRange, mRange: OpenSlice[int],
                        opts: set[RandOpt] = {}): seq[(int, int)] =
      randGraphImpl(rand(nRange), rand(mRange), opts)

    type InitRandGraph = object

    const randGraph* = InitRandGraph()

    macro `[]`*(r: InitRandGraph, args: varargs[untyped]): untyped =
      assert args.len == 2 or args.len == 3,
        "randGraph: use randGraph[n, m] or randGraph[n, m, {options}]"

      if args.len == 2:
        result = newCall(ident"randGraphImpl", args[0], args[1])
      else:
        assert args[2].kind == nnkCurly,
          "randGraph: options must be a set literal"
        result = newCall(ident"randGraphImpl", args[0], args[1], args[2])

    # ----------------------------------------------------------
    # 出力
    #
    # emit(N, M, X)
    # emit(A)             # 配列は横一行
    # emit(M)             # 行列は各行を出力
    # emit(G)             # 辺リスト
    #
    # emitCol(A)
    # emitCol(A, B)
    # emitCol(A, B, C)
    #
    # emitGraph(G)
    # emitGraph(G, W)
    # ----------------------------------------------------------
    proc outputPart[T](x: T): string =
      $x

    proc outputPart[T](xs: seq[T]): string =
      xs.mapIt($it).join(" ")

    proc emitOne[T](x: T) =
      line(x)

    proc emitOne[T](xs: seq[T]) =
      row(xs)

    proc emitOne(xs: seq[string]) =
      for s in xs:
        line(s)

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

    proc emitCol*[T](xs: openArray[T]) =
      for x in xs:
        line(x)

    proc emitCol*[A, B](xs: openArray[A], ys: openArray[B]) =
      assert xs.len == ys.len,
        "emitCol: length mismatch"

      for i in 0 ..< xs.len:
        line($xs[i] & " " & $ys[i])

    proc emitCol*[A, B, C](
        xs: openArray[A],
        ys: openArray[B],
        zs: openArray[C]
    ) =
      assert xs.len == ys.len and ys.len == zs.len,
        "emitCol: length mismatch"

      for i in 0 ..< xs.len:
        line($xs[i] & " " & $ys[i] & " " & $zs[i])

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

    # ----------------------------------------------------------
    # flush
    #
    # flush(10):
    #   ...
    #
    # test/case-1.in ～ test/case-10.in に書き出す。
    # 各ケースは caseIdx をシードにするため再現可能。
    # ----------------------------------------------------------
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