when not declared(LIBRARY_MODINT):
  const LIBRARY_MODINT = true

  type ModInt*[M: static[int]] = object
    v*: int

  var dynamic_mod_value {.used.}: int = 998244353

  template getMod[M: static[int]](t: typedesc[ModInt[M]]): int =
    when M > 0: M
    else: dynamic_mod_value

  ##- **initMod(m)**
  ##    - 動的modの値を m に設定
  proc initMod*(m: int) = dynamic_mod_value = m

  proc initMint*[M: static[int]](n: int): ModInt[M] {.inline.} =
    let m = ModInt[M].getMod()
    var v = n
    if v < 0: v = v mod m + m
    elif v >= m: v = v mod m
    ModInt[M](v: v)

  ##- **a.toInt**
  ##    - ModInt を素の int に変換（暗黙/明示の両対応）
  proc toInt*[M](a: ModInt[M]): int {.inline.} = a.v
  converter toIntConverter*[M](a: ModInt[M]): int {.inline.} = a.v

  proc `+`*[M](a, b: ModInt[M]): ModInt[M] {.inline.} =
    let m = ModInt[M].getMod()
    var res = a.v + b.v
    if res >= m: res -= m
    ModInt[M](v: res)

  proc `-`*[M](a, b: ModInt[M]): ModInt[M] {.inline.} =
    let m = ModInt[M].getMod()
    var res = a.v - b.v
    if res < 0: res += m
    ModInt[M](v: res)

  proc `*`*[M](a, b: ModInt[M]): ModInt[M] {.inline.} =
    ModInt[M](v: (a.v * b.v) mod ModInt[M].getMod())

  ##- **a.pow(p)**
  ##    - a^p を計算 (繰り返し二乗法) `O(log p)`
  proc pow*[M](a: ModInt[M], p: int): ModInt[M] =
    var base = a; var exp = p; result = ModInt[M](v: 1)
    while exp > 0:
      if (exp and 1) != 0: result = result * base
      base = base * base; exp = exp shr 1

  ##- **inv(a)**
  ##    - a の逆元を返す (フェルマーの小定理) ※Modは素数前提
  proc inv*[M](a: ModInt[M]): ModInt[M] {.inline.} = a.pow(ModInt[M].getMod() - 2)

  proc `/`*[M](a, b: ModInt[M]): ModInt[M] {.inline.} = a * b.inv()

  proc `+=`*[M](a: var ModInt[M], b: ModInt[M]) {.inline.} = a = a + b
  proc `-=`*[M](a: var ModInt[M], b: ModInt[M]) {.inline.} = a = a - b
  proc `*=`*[M](a: var ModInt[M], b: ModInt[M]) {.inline.} = a = a * b
  proc `/=`*[M](a: var ModInt[M], b: ModInt[M]) {.inline.} = a = a / b

  proc `+`*[M](a: ModInt[M], b: int): ModInt[M] {.inline.} = a + initMint[M](b)
  proc `-`*[M](a: ModInt[M], b: int): ModInt[M] {.inline.} = a - initMint[M](b)
  proc `*`*[M](a: ModInt[M], b: int): ModInt[M] {.inline.} = a * initMint[M](b)
  proc `/`*[M](a: ModInt[M], b: int): ModInt[M] {.inline.} = a / initMint[M](b)
  proc `+`*[M](a: int, b: ModInt[M]): ModInt[M] {.inline.} = initMint[M](a) + b
  proc `-`*[M](a: int, b: ModInt[M]): ModInt[M] {.inline.} = initMint[M](a) - b
  proc `*`*[M](a: int, b: ModInt[M]): ModInt[M] {.inline.} = initMint[M](a) * b
  proc `/`*[M](a: int, b: ModInt[M]): ModInt[M] {.inline.} = initMint[M](a) / b

  proc `$`*[M](a: ModInt[M]): string = $a.v

  proc getFactTable[M: static[int]](): var seq[int] =
    var table {.global.}: seq[int]
    return table

  proc getInvFactTable[M: static[int]](): var seq[int] =
    var table {.global.}: seq[int]
    return table

  proc prepareFactImpl[M: static[int]](n: int) =
    var ft = getFactTable[M]()
    if ft.len > n: return
    if ft.len == 0:
      getFactTable[M]() = @[1, 1]; getInvFactTable[M]() = @[1, 1]
    ft = getFactTable[M](); var ift = getInvFactTable[M]()
    let needed = n + 1
    if ft.len < needed:
      let start = max(2, ft.len)
      ft.setLen(needed); ift.setLen(needed)
      var val = ModInt[M](v: ft[start-1])
      for i in start .. n: val *= i; ft[i] = val.v
      var invVal = ModInt[M](v: ft[n]).inv()
      ift[n] = invVal.v
      for i in countdown(n-1, start): invVal *= (i + 1); ift[i] = invVal.v
      getFactTable[M]() = ft; getInvFactTable[M]() = ift

  proc getFact[M: static[int]](n: int): ModInt[M] =
    prepareFactImpl[M](n); return ModInt[M](v: getFactTable[M]()[n])

  proc getInvFact[M: static[int]](n: int): ModInt[M] =
    prepareFactImpl[M](n); return ModInt[M](v: getInvFactTable[M]()[n])

  # ========================================
  # 動的Mod (dmint)
  # ========================================
  type dmint* = ModInt[0]

  ##- **n.toDmint**
  ##    - 動的modの ModInt に変換
  converter toDmint*(n: int): dmint {.inline.} = initMint[0](n)

  ##- **dfact(n) / dinvFact(n)**
  ##    - 動的modでの n! と (n!)^{-1} を返す
  proc dfact*(n: int): dmint = getFact[0](n)
  proc dinvFact*(n: int): dmint = getInvFact[0](n)

  ##- **dModCombination(n,k) / dModPermutation(n,k) / dModHomogeneous(n,k)**
  ##    - 動的modでの nCk, nPk, nHk を返す（kが範囲外なら0）
  proc dModCombination*(n, k: int): dmint =
    if k < 0 or k > n: return dmint(v: 0)
    return dfact(n) * dinvFact(k) * dinvFact(n-k)

  proc dModPermutation*(n, k: int): dmint =
    if k < 0 or k > n: return dmint(v: 0)
    return dfact(n) * dinvFact(n-k)

  proc dModHomogeneous*(n, k: int): dmint =
    if n == 0 and k == 0: return dmint(v: 1)
    return dModCombination(n + k - 1, k)

  # ========================================
  # 静的Mod (mint)
  # ========================================
  template defineMintLogic(M_VAL: static[int]) =
    ##- **mint**
    ##    - 法 M_VAL の ModInt 型エイリアス
    type mint* {.inject.} = ModInt[M_VAL]

    ##- **n.toMint**
    ##    - int を法 M_VAL で正規化して mint に変換
    converter toMint*(n: int): mint {.inline, inject.} = initMint[M_VAL](n)

    proc prepareFact*(n: int) {.inject.} = prepareFactImpl[M_VAL](n)

    ##- **n.fact / invFact**
    ##    - 法 M_VAL での n! と (n!)^{-1} を返す
    proc fact*(n: int): mint {.inject.} = getFact[M_VAL](n)
    proc invFact*(n: int): mint {.inject.} = getInvFact[M_VAL](n)

    ##- **modCombination(n,k) / modPermutation(n,k) / modHomogeneous(n,k)**
    ##    - 静的modでの nCk, nPk, nHk を返す（kが範囲外なら0）
    proc modCombination*(n, k: int): mint {.inject.} =
      if k < 0 or k > n: return mint(v: 0)
      return fact(n) * invFact(k) * invFact(n-k)

    proc modPermutation*(n, k: int): mint {.inject.} =
      if k < 0 or k > n: return mint(v: 0)
      return fact(n) * invFact(n-k)

    proc modHomogeneous*(n, k: int): mint {.inject.} =
      if n == 0 and k == 0: return mint(v: 1)
      return modCombination(n + k - 1, k)

  ##- **initMod998244353 / initMod1000000007**
  ##    - 代表的な法をmint環境として初期化（階乗APIも生成）
  template initMod998244353* = defineMintLogic(998244353)
  template initMod1000000007* = defineMintLogic(1000000007)
