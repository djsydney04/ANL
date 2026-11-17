fn main()->i64 ensures(result) result==2;
{let mut x=0;while(x<2) invariant true; {x=x+1;} x}
