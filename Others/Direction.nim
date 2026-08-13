import atcoder/extra/other/direction
for (nh,nw) in (h,w).neighbor(dir4,(0..<H,0..<W)): #dir8

for (dh,dw) in [(-1,0),(0,1),(1,0),(0,-1)]:
  let (nh,nw)=(h+dh,w+dw)
  if nh in 0..<H and nw in 0..<W and 

#Sentinel
var m=newSeqWith(H,"#"&nextString()&"#")
for i in [0,H+1]: m.insert("#".repeat(W+2),i)

#Rotate/flip
proc rr(i,j,k:int):(int,int)=
  if k==0: return (i,j)
  rr(N-1-j,i,k-1)
#k回左回転した座標が出てくる：(ni,nj)は「右回転（right rotate）後に(i,j)になる座標を元の座標で表現すると何か」

proc lr(i,j,k:int):(int,int)=
  if k==0: return (i,j)
  lr(j,N-1-i,k-1)
#k回右回転した座標が出てくる：(ni,nj)は「左回転（left rotate）後に(i,j)になる座標を元の座標で表現すると何か」

proc hf(i,j,k:int):(int,int)=
  if k==0: return (i,j)
  hf(-i,j,k-1)
#k回左右反転（horizontal flip）した座標が出てくる

proc vf(i,j,k:int):(int,int)=
  if k==0: return (i,j)
  vf(i,-j,k-1)
#k回上下反転（vertical flip）した座標が出てくる

proc md(i,j,k:int):(int,int)=
  if k==0: return (i,j)
  l(j,N-1-i,k-1)
#k回y=x反転（主対角線反転）（main-diagonal flip）した座標が出てくる

proc md(i,j,k:int):(int,int)=
  if k==0: return (i,j)
  l(j,N-1-i,k-1)
#k回y=-x反転（副主対角線反転）（anti-diagonal flip）した座標が出てくる

let (ni,nj)=f(i,j,k)