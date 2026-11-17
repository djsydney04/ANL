fn main()->i64 ensures(result) result==4;
{let mut x=0;while({x=x+1;x<4}) invariant 0<=x; invariant x<=3; {} x}
