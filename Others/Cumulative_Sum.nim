when not declared(CUMULATIVE_SUM):
  const CUMULATIVE_SUM = true
  import sequtils

  # --- 共通ヘルパー ---
  template calcIdx(len: int, i: int): int = i
  template calcIdx(len: int, i: BackwardsIndex): int = len - int(i)

  # --- 1次元累積和 (CumSum) ---

  type
    CumSum*[T] = object
      data: seq[T]

  proc initCumSumImpl*[T, U](arr: seq[U]): CumSum[T] =
    var data = newSeq[T](arr.len + 1)
    data[0] = default(T)
    for i in 0 ..< arr.len:
      when compiles(T(arr[i])):
        data[i + 1] = data[i] + T(arr[i])
      else:
        {.error: "Cannot convert " & $U & " to " & $T.}
    result.data = data

  proc initCumSum*[T](arr: seq[T]): CumSum[T] = initCumSumImpl[T, T](arr)
  template initCumSum*[T](arr: seq): auto = initCumSumImpl[T, typeof(arr[0])](arr)

  proc `[]`*[T](cs: CumSum[T], slice: HSlice[int, int]): T =
    let l = slice.a
    let r = slice.b
    return cs.data[r + 1] - cs.data[l]

  proc `[]`*[T](cs: CumSum[T], slice: HSlice[int, BackwardsIndex]): T =
    let len = cs.data.len - 1
    let l = slice.a
    let r = calcIdx(len, slice.b)
    return cs.data[r + 1] - cs.data[l]

  proc `[]`*[T](cs: CumSum[T], slice: HSlice[BackwardsIndex, BackwardsIndex]): T =
    let len = cs.data.len - 1
    let l = calcIdx(len, slice.a)
    let r = calcIdx(len, slice.b)
    return cs.data[r + 1] - cs.data[l]


  # --- 1次元 Imos法 (Imos1D) ---

  type
    Imos1D*[T] = object
      diff: seq[T]
      len: int

  proc initImos1D*[T](len: int): Imos1D[T] =
    result.len = len
    result.diff = newSeq[T](len + 1)

  proc add*[T](imos: var Imos1D[T], slice: HSlice, val: T) =
    let l = calcIdx(imos.len, slice.a)
    let r = calcIdx(imos.len, slice.b)
    if l <= r and l < imos.len:
      imos.diff[l] += val
      if r + 1 < imos.diff.len:
        imos.diff[r + 1] -= val

  proc build*[T](imos: Imos1D[T]): CumSum[T] =
    var data = newSeq[T](imos.len + 1)
    var currentVal = default(T)
    data[0] = default(T)
    for i in 0 ..< imos.len:
      currentVal += imos.diff[i]
      data[i + 1] = data[i] + currentVal
    result.data = data


  # --- 2次元累積和 (CumSum2D) ---
  # 内部データを1次元配列にフラット化

  type
    CumSum2D*[T] = object
      data: seq[T]
      h*, w*: int

  # インデックス計算ヘルパー
  template idx(cs: CumSum2D, y, x: int): int = y * (cs.w + 1) + x

  proc initCumSum2DImpl*[T, U](grid: seq[seq[U]]): CumSum2D[T] =
    let h = grid.len
    let w = if h > 0: grid[0].len else: 0
    
    # フラットな配列を一括確保 (ゼロ初期化される)
    var data = newSeq[T]((h + 1) * (w + 1))
    
    # インデックス計算用: 幅は w + 1
    let stride = w + 1
    
    for i in 0 ..< h:
      let rowOffset = (i + 1) * stride
      let prevRowOffset = i * stride
      for j in 0 ..< w:
        when compiles(T(grid[i][j])):
          let val = T(grid[i][j])
          # data[i+1][j+1] = data[i][j+1] + data[i+1][j] - data[i][j] + val
          data[rowOffset + j + 1] = 
            data[prevRowOffset + j + 1] + 
            data[rowOffset + j] - 
            data[prevRowOffset + j] + val
        else:
          {.error: "Cannot convert " & $U & " to " & $T.}
    
    result.data = data
    result.h = h
    result.w = w

  # 低レベル初期化: 既にフラット化されたグリッドデータ(サイズ h*w)から構築
  proc initCumSum2DFromFlat*[T](flatData: seq[T], h, w: int): CumSum2D[T] =
    var data = newSeq[T]((h + 1) * (w + 1))
    let stride = w + 1
    for i in 0 ..< h:
      let rowOffset = (i + 1) * stride
      let prevRowOffset = i * stride
      let srcRowOffset = i * w
      for j in 0 ..< w:
        let val = flatData[srcRowOffset + j]
        data[rowOffset + j + 1] = 
          data[prevRowOffset + j + 1] + 
          data[rowOffset + j] - 
          data[prevRowOffset + j] + val
    result.data = data
    result.h = h
    result.w = w

  proc initCumSum2D*[T](grid: seq[seq[T]]): CumSum2D[T] = initCumSum2DImpl[T, T](grid)
  template initCumSum2D*[T](grid: seq[seq]): auto = initCumSum2DImpl[T, typeof(grid[0][0])](grid)

  # 区間和取得
  proc queryRect[T](cs: CumSum2D[T], y1, y2, x1, x2: int): T =
    let stride = cs.w + 1
    # cs.data[y2 + 1][x2 + 1] - cs.data[y1][x2 + 1] - cs.data[y2 + 1][x1] + cs.data[y1][x1]
    let p1 = (y2 + 1) * stride + (x2 + 1)
    let p2 = y1 * stride + (x2 + 1)
    let p3 = (y2 + 1) * stride + x1
    let p4 = y1 * stride + x1
    return cs.data[p1] - cs.data[p2] - cs.data[p3] + cs.data[p4]

  proc `[]`*[T](cs: CumSum2D[T], ySlice: HSlice, xSlice: HSlice): T =
    let y1 = calcIdx(cs.h, ySlice.a)
    let y2 = calcIdx(cs.h, ySlice.b)
    let x1 = calcIdx(cs.w, xSlice.a)
    let x2 = calcIdx(cs.w, xSlice.b)
    return queryRect(cs, y1, y2, x1, x2)

  # [][] 用プロキシ
  type
    CumSum2DrowProxy*[T] = object
      cs: ptr CumSum2D[T]
      y1, y2: int

  template `[]`*[T](inst: CumSum2D[T], ySlice: HSlice): auto =
    let y1 = calcIdx(inst.h, ySlice.a)
    let y2 = calcIdx(inst.h, ySlice.b)
    CumSum2DrowProxy[T](cs: unsafeAddr(inst), y1: y1, y2: y2)

  proc `[]`*[T](proxy: CumSum2DrowProxy[T], xSlice: HSlice): T =
    let x1 = calcIdx(proxy.cs[].w, xSlice.a)
    let x2 = calcIdx(proxy.cs[].w, xSlice.b)
    return queryRect(proxy.cs[], proxy.y1, proxy.y2, x1, x2)


  # --- 2次元 Imos法 (Imos2D) ---
  # 内部データを1次元配列にフラット化

  type
    Imos2D*[T] = object
      diff: seq[T] # フラット化した差分配列
      h, w: int

  proc initImos2D*[T](h, w: int): Imos2D[T] =
    result.h = h
    result.w = w
    # 累積和計算時に番兵が必要になるため (h+1)*(w+1) で確保しておくと計算が楽
    result.diff = newSeq[T]((h + 1) * (w + 1))

  proc add*[T](imos: var Imos2D[T], ySlice: HSlice, xSlice: HSlice, val: T) =
    let y1 = calcIdx(imos.h, ySlice.a)
    let y2 = calcIdx(imos.h, ySlice.b)
    let x1 = calcIdx(imos.w, xSlice.a)
    let x2 = calcIdx(imos.w, xSlice.b)
    
    if y1 <= y2 and x1 <= x2 and y1 < imos.h and x1 < imos.w:
      let stride = imos.w + 1
      # diff[y1][x1] += val
      imos.diff[y1 * stride + x1] += val
      # diff[y1][x2 + 1] -= val
      imos.diff[y1 * stride + (x2 + 1)] -= val
      # diff[y2 + 1][x1] -= val
      imos.diff[(y2 + 1) * stride + x1] -= val
      # diff[y2 + 1][x2 + 1] += val
      imos.diff[(y2 + 1) * stride + (x2 + 1)] += val

  # 構築: Imos2D -> CumSum2D
  # Imosの復元とCumSumの構築を行う
  proc build*[T](imos: Imos2D[T]): CumSum2D[T] =
    # 作業用配列として imos.diff のコピーを作成し、in-placeで復元を行う
    var d = imos.diff 
    let h = imos.h
    let w = imos.w
    let stride = w + 1
    
    # 1. 横方向累積 (差分解消)
    for i in 0 ..< h:
      let rowOffset = i * stride
      for j in 0 ..< w:
        # d[i][j+1] += d[i][j]
        d[rowOffset + j + 1] += d[rowOffset + j]
    
    # 2. 縦方向累積 (差分解消 -> ここで各マスの値 "A[i][j]" が確定)
    #    かつ、これをそのまま "1次元配列" として initCumSum2DFromFlat に渡す準備をする
    #    d配列は (h+1)*(w+1) サイズで、各行の末尾(w+1列目)と最終行(h+1行目)は番兵または0になっているはず
    
    # フラットな「値」の配列を作る
    var restored = newSeq[T](h * w)
    for j in 0 ..< w:
      for i in 0 ..< h:
        # d[i+1][j] += d[i][j]
        d[(i + 1) * stride + j] += d[i * stride + j]
        
        # 復元された値を保存
        restored[i * w + j] = d[i * stride + j]

    # 3. 2次元累積和構築
    # 復元された値の配列から累積和オブジェクトを作る
    return initCumSum2DFromFlat(restored, h, w)
