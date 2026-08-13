#実数
proc f(m:int):float=
var
  l=
  r=
while r-l>pow(10,-6.0):
  let
    ml=(l*2+r)/3
    mr=(l+r*2)/3
  if f(ml)>f(mr): l=ml
  else: r=mr
echo f(r)

#整数
proc f(m:int):float=
var
  l=
  r=
while r-l>2:
  let
    ml=(l*2+r) div 3
    mr=(l+r*2) div 3
  if f(ml)>f(mr): l=ml
  else: r=mr
echo (l..r).toSeq.mapIt(f(it)).min