type trie=ref object
  t:Table[char,trie]
  c:int
var
  t:trie=new(trie)
  a=0
for i in 1..N:
  let S=nextString()
  var tj=t
  for Sj in S:
    if tj.t.hasKey(Sj): a+=tj.t[Sj].c; tj.t[Sj].c+=1
    else:
      tj.t[Sj]=trie(t:initTable[char,trie](),c:1)
    tj=tj.t[Sj]
echo a