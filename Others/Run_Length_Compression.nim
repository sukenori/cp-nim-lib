var c= @[(k:S[0],v:0)]
#Echode
for Si in S:
  if c[^1].k==Si: c[^1].v+=1
  else: c.add((Si,1))
#Decode
var a:string
for (k,v) in c: a&=k.repeat(v)
echo a