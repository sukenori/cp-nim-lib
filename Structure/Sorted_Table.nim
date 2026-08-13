type
  SortedTable[K,V] {.importcpp:"std::map",header:"<map>"}=object
  SortedTableIt[K,V] {.importcpp:"std::map<'*0,'*1>::const_iterator"}=object
  SortedTableRevIt[K,V] {.importcpp:"std::map<'*0,'*1>::const_reverse_iterator"}=object

# コンストラクタ
proc initSortedTable[K,V]():SortedTable[K,V] {.importcpp:"std::map<'*0,'*1>()",constructor}

# イテレータ操作
template defIt(TIt:typedesc)=
  proc beginIt[K,V](t:SortedTable[K,V]):SortedTableIt[K,V] {.importcpp:"#.begin()"}
  proc endIt[K,V](t:SortedTable[K,V]):SortedTableIt[K,V] {.importcpp:"#.end()"}
  proc rbeginIt[K,V](t:SortedTable[K,V]):SortedTableRevIt[K,V] {.importcpp:"#.rbegin()"}
  proc next[K,V](it:TIt[K,V],n:int):TIt[K,V] {.importcpp:"std::next(#,#)"}
  proc prev[K,V](it:TIt[K,V],n:int):TIt[K,V] {.importcpp:"std::prev(#,#)"}
  proc distance[K,V](a,b:TIt[K,V]):int {.importcpp: "std::distance(#,#)"}
  proc `++`[K,V](it:var TIt[K,V]) {.importcpp:"(++#)"}
  proc `==`[K,V](a,b:TIt[K,V]):bool {.importcpp:"#==#"}
  proc `*`[K,V](it:TIt[K,V]):(K,V) {.importcpp:"(*#)"}
  proc key[K,V](it:TIt[K,V]):K {.importcpp:"#->first"}
  proc val[K,V](it:TIt[K,V]):V {.importcpp:"#->second"}
defIt(SortedTableIt)
defIt(SortedTableRevIt)

# メソッド
proc `[]=`[K,V](t:var SortedTable[K,V],k:K,v:V) {.importcpp:"#[@]=@"}
proc `[]`[K,V](t:SortedTable[K,V],k:K):V {.importcpp:"#[@]"}
proc erase[K,V](t:var SortedTable[K,V],k:K):int {.importcpp:"#.erase(@)"}
proc size[K,V](t:SortedTable[K,V]):int {.importcpp:"#.size()"}
proc count[K,V](t:SortedTable[K,V],k:K):int {.importcpp:"#.count(@)"}
proc empty[K,V](t:SortedTable[K,V]):bool {.importcpp:"#.empty()"}

proc find[K,V](t:SortedTable[K,V],k:K):SortedTableIt[K,V] {.importcpp:"#.find(@)"}
proc lower_bound[K,V](t:SortedTable[K,V],k:K):SortedTableIt[K,V] {.importcpp:"#.lower_bound(@)"}
proc upper_bound[K,V](t:SortedTable[K,V],k:K):SortedTableIt[K,V] {.importcpp:"#.upper_bound(@)"}
proc keys[K,V](t:SortedTable[K,V]):seq[K]=
  var it=t.beginIt; for _ in 0..<t.size(): result.add(it.key); ++it
proc values[K,V](t:SortedTable[K,V]):seq[V]=
  var it=t.beginIt; for _ in 0..<t.size(): result.add(it.val); ++it
proc pairs[K,V](t: SortedTable[K,V]): seq[(K,V)] =
  var it=t.beginIt; for _ in 0..<t.size(): result.add((it.key,it.val)); ++it

#使用法
var t=initSortedTable[int,int]()

t[k]=v
t.erase(k)
t.size()
t.count(k) #1なら存在する、0なら存在しない
t.empty :bool
t.find(a)
t.lower_bound(a)
t.upper_bound(a)
t.keys
t.values
t.pairs