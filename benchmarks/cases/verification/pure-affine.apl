fn f(x:i64)->i64 requires x>=-1000 && x<=1000;ensures(r)r==3*x+7;{3*x+7}
