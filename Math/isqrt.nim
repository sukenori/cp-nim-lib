proc isqrt(n:int):int=
  var
    x=n
    nx=(x+1) div 2
  while x>nx: x=nx; nx=(x+n div x) div 2
  return x