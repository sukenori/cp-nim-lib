#グループ分け全列挙
var s:HashSet[seq[seq[int]]]
proc r(i:int,v:seq[seq[int]])=
  if i==N: s.incl(v); return
  for j in 0..<v.len:
    var vi=v; vi[j].add(A[i]); r(i+1,vi)
  var vi=v; vi.add(@[A[i]]); r(i+1,vi)
r(0,newSeq[seq[int]]())