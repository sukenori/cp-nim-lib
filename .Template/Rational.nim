when not declared(LIBRARY_RATIONAL):
  const LIBRARY_RATIONAL = true
  {.warning[UnusedImport]: off.}
  import rationals
  include "/workspaces/AtCoder-Nim/.Library/.Template/Template.nim"

  template inf(T: typedesc[Rational[int]]): Rational[int] = int.inf.toRational
  template inf(T: typedesc[Rational[float]]): Rational[float] = float.inf.toRational