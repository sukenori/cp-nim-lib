var
  s,m,a=0
#sは累積和、mは累積和の最小値、aが連続区間最大値
for i in 0..<N:
  s+=A[i]
  m.min=s
  a.max=s-m