include "/workspaces/AtCoder-Nim/.Library/template.nim"

let
  N, M = int.input
  X = Seq[N: int.input]
var b: Table[int, int]
loop M:
  let C, Y = int.input
  b[C] = Y

type
  State = tuple[times: int, counter: int]
  Value = tuple[money: int]
  Node = tuple[state: State, value: Value]
let
  maxTimes = N + 1
  maxCounter = N + 1
  maxIdx = maxTimes * maxCounter
proc idx(state: State): int = state.times * maxCounter + state.counter
let startNode: Node = (state: (times: 0, counter: 0), value: (money: 0))

iterator transition(state: State): tuple[nextState: State, weight: Value] =
  if state.times == N: discard
  else:
    yield (
      nextState: (times: state.times + 1, counter: state.counter + 1),
      weight: (money: X[state.times] + b.getOrDefault(state.counter + 1))
    )
    yield (
      nextState: (times: state.times + 1, counter: 0),
      weight: (money: 0)
    )

var
  visited = Seq[maxIdx: bool] 
  cumMemo = Seq[maxIdx: (money: -int.inf)]
proc `+`(a, b: Value): Value =
  (money: a.money + b.money)
proc `<`(a, b: Value): bool =
  a.money < b.money
proc update(currCumVal: var Value; weight, nextCumVal: Value) =
  if currCumVal.money < weight.money + nextCumVal.money:
    currCumVal = (money: weight.money + nextCumVal.money)
proc memoizedDFS(state: State): Value =
  if visited[state.idx]: return cumMemo[state.idx]
  visited[state.idx] = true
  var isEnd = true
  for (nextState, weight) in transition(state):
    isEnd = false
    cumMemo[state.idx].update(weight, memoizedDFS(nextState))
  if isEnd: cumMemo[state.idx] = Value.default
  return cumMemo[state.idx]
echo (startNode.value + memoizedDFS(startNode.state)).money