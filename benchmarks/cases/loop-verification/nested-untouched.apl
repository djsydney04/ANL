fn main()->i64 ensures(r)r==7;{
 let mut x=7;let snap=x;let mut i=0;
 while(i<2) invariant i>=0 && i<=2; invariant x==snap;{
 let mut j=0;while(j<2) invariant j>=0 && j<=2; invariant i>=0 && i<2; invariant x==snap; {j=j+1;}
 i=i+1;}x}