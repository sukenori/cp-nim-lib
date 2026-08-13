when not declared(LIBRARY_MEMOIZED):
  const LIBRARY_MEMOIZED = true
  include "/workspaces/AtCoder-Nim/.Library/.Template/Template.nim"

  ##- **{.memoized.}**
  ##    - メモ化するプロシージャ。結果をグローバルテーブルにキャッシュ
  macro memoized*(procDef: untyped): untyped =
    let procName = procDef[0]
    let params = procDef[3]
    let returnType = params[0]
    let cacheName = genSym(nskVar, "memo_" & procName.strVal & "_cache")
    var keyConstr = newTree(nnkPar)
    for i in 1 ..< params.len:
      let param = params[i]
      let paramNames = param[0 .. ^3]
      for name in paramNames:
        keyConstr.add(name)
    var keyTypeConstr = newTree(nnkPar)
    for i in 1 ..< params.len:
      let param = params[i]
      let paramType = param[^2]
      for _ in 0 ..< param.len - 2:
        keyTypeConstr.add(paramType)
    let originalBody = procDef.body
    let newBody = quote do:
      let key = `keyConstr`
      if `cacheName`.hasKey(key):
        return `cacheName`[key]
      `originalBody`
      `cacheName`[key] = result
    procDef.body = newBody
    let cacheDecl = quote do:
      var `cacheName` = initTable[`keyTypeConstr`, `returnType`]()
    result = newStmtList()
    result.add(cacheDecl)
    result.add(procDef)