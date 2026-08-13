type
  SortedSet[T] {.importcpp:"std::set",header:"<set>"}=object
  SortedSetIt[T] {.importcpp:"std::set<'*0>::const_iterator",header:"<set>"}=object
  SortedSetRevIt[T] {.importcpp:"std::set<'*0>::const_reverse_iterator",header:"<set>"}=object
#コンストラクタ
proc initSortedSet[T]():SortedSet[T] {.importcpp:"std::set<'*0>()"}

#イテレータ操作
template defIt(TIt:typedesc)=
  proc beginIt[T](s:SortedSet[T]):SortedSetIt[T] {.importcpp:"#.begin()"}
  proc endIt[T](s:SortedSet[T]):SortedSetIt[T] {.importcpp:"#.end()"} #末尾の次
  proc rbeginIt[T](s:SortedSet[T]):SortedSetRevIt[T] {.importcpp:"#.rbegin()"} #末尾からの逆
  proc next[T](it:TIt[T],n:int):TIt[T] {.importcpp:"std::next(#,#)",header:"<iterator>"}
  proc prev[T](it:TIt[T],n:int):TIt[T] {.importcpp:"std::prev(#,#)",header:"<iterator>"}
  proc distance[T](a,b: TIt[T]): int {.importcpp: "std::distance(#,#)", header:"<iterator>"}
  proc `==`[T](a,b:TIt[T]):bool {.importcpp:"#==#"}
  proc `!=`[T](a,b:TIt[T]):bool {.importcpp:"#!=#"}
  proc `*`[T](it:TIt[T]):T {.importcpp:"(*#)"}
defIt(SortedSetIt)
defIt(SortedSetRevIt)

#メソッド
proc insert[T](s:var SortedSet[T],v:T) {.importcpp:"#.insert(@)"}
proc erase[T](s:var SortedSet[T],v:T):int {.importcpp:"#.erase(@)"}
proc size[T](s:SortedSet[T]):int {.importcpp:"#.size()"}
proc count[T](s:SortedSet[T],v:T):int {.importcpp:"#.count(@)"}
proc empty[T](s:SortedSet[T]):bool {.importcpp:"#.empty()"}
proc find[T](s:SortedSet[T],v:T):SortedSetIt[T] {.importcpp: "#.find(@)"}
proc lower_bound[T](s:SortedSet[T],v:T):SortedSetIt[T] {.importcpp: "#.lower_bound(@)"}
proc upper_bound[T](s:SortedSet[T],v:T):SortedSetIt[T] {.importcpp: "#.upper_bound(@)"}

#使用法
var s=initSortedSet[int]()

s.insert(a)
s.erase(a)
s.size()
s.count() #1なら存在する、0なら存在しない
s.empty() :bool
s[a]
s.find(a)
s.lower_bound(a)
s.upper_bound(a)