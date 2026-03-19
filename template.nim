when not declared(LIBRARY_TEMPLATE):
  const LIBRARY_TEMPLATE = true
  {.warning[UnusedImport]: off.}
  import math, lenientops, bitops, strutils, nre, parseutils, sequtils, algorithm, sets, tables, deques, heapqueue, macros
  import sugar except dump

  template inf(T: typedesc[int]): int = 10 ^ 18
  template inf(T: typedesc[float]): float = 1e18

  ##- **bitアクセス: x[i], x[i] = b**
  ##    - 整数xのi番目ビットを取得/設定 (0/1)。範囲外は未定義
  proc `[]`(x, i: int): int = x shr i and 1
  proc `[]=`(x: var int, i, y: int): void =
    if y == 1: x = x or (1 shl i)
    elif y == 0: x = x and not (1 shl i)
  template count(x: int): int = x.countSetBits

  ##- **char@('a')**
  ##    - 'a' からの0-index相対値
  proc `@`(x: char, a = 'a'): int = x.ord - a.ord
  proc parseInt(x: char): int = ($x).parseInt

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
      let dumpTag = "\x1b[31m[dump]\x1b[0m"
      let prefix = if label.len > 0:
          dumpTag & " " & label & " = "
        else:
          dumpTag & " "
      stderr.writeLine(prefix & $x)
    return x
  template dump*(x: untyped): untyped =
    block:
      let val = x
      when defined(debug):
        debugPassThrough(val, astToStr(x))
      else:
        val
