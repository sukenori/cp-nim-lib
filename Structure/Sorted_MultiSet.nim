type
  SortedMultiSet[T] {.importcpp:"std::multiset",header:"<set>"}=object
  SortedMultiSetIt[T] {.importcpp:"std::set<'*0>::const_iterator",header:"<set>"}=object
  SortedMultiSetRevIt[T] {.importcpp:"std::set<'*0>::const_reverse_iterator",header:"<set>"}=object
#コンストラクタ
proc initSoretdMultiSet[T]():SortedMultiSet[T] {.importcpp:"std::multiset<'*0>()"}

#イテレータ操作
template defIt(TIt:typedesc)=
  proc beginIt[T](s:SortedMultiSet[T]):SortedMultiSetIt[T] {.importcpp:"#.begin()"}
  proc endIt[T](s:SortedMultiSet[T]):SortedMultiSetIt[T] {.importcpp:"#.end()"} #末尾の次
  proc rbeginIt[T](s:SortedMultiSet[T]):SortedMultiSetRevIt[T] {.importcpp:"#.rbegin()"} #末尾からの逆
  proc next[T](it:TIt[T],n:int):TIt[T] {.importcpp:"std::next(#,#)",header:"<iterator>"}
  proc prev[T](it:TIt[T],n:int):TIt[T] {.importcpp:"std::prev(#,#)",header:"<iterator>"}
  proc distance[T](a,b: TIt[T]): int {.importcpp: "std::distance(#,#)", header:"<iterator>"}
  proc `==`[T](a,b:TIt[T]):bool {.importcpp:"#==#"}
  proc `!=`[T](a,b:TIt[T]):bool {.importcpp:"#!=#"}
  proc `*`[T](it:TIt[T]):T {.importcpp:"(*#)"}
defIt(SortedMultiSetIt)
defIt(SortedMultiSetRevIt)

#メソッド
proc insert[T](s:var SortedMultiSet[T],v:T) {.importcpp:"#.insert(@)"}
proc erase[T](s:var SortedMultiSet[T],v:T):int {.importcpp:"#.erase(@)"} #
proc size[T](s:SortedMultiSet[T]):int {.importcpp:"#.size()"}
proc count[T](s:SortedMultiSet[T],v:T):int {.importcpp:"#.count(@)"}
proc empty[T](s:SortedMultiSet[T]):bool {.importcpp:"#.empty()"}
proc find[T](s:SortedMultiSet[T],v:T):SortedMultiSetIt[T] {.importcpp: "#.find(@)"}
proc lower_bound[T](s:SortedMultiSet[T],v:T):SortedMultiSetIt[T] {.importcpp: "#.lower_bound(@)"}
proc upper_bound[T](s:SortedMultiSet[T],v:T):SortedMultiSetIt[T] {.importcpp: "#.upper_bound(@)"}