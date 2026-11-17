fn inc(x:i64)->i64 requires x>=-1000 && x<=1000;ensures(r)r==x+3;{x+3}
fn twice(x:i64)->i64 requires x>=-900 && x<=900;ensures(r)r==2*x+6;{inc(x)+inc(x)}
fn f(x:i64)->i64 requires x>=-100 && x<=100;ensures(r)r==4*x+18;{twice(twice(x))}
