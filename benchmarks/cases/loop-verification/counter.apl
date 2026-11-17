fn count(n:i64)->i64
requires 0<=n;
requires n<=1000;
ensures(result) result==n;
{let mut i=0;while(i<n) invariant 0<=i; invariant i<=n; {i=i+1;} i}
fn main()->i64 {count(1000)}
