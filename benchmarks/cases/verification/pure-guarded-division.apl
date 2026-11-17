fn f(x:i64)->i64 requires x>=-100 && x<=100;ensures(r)(x==0 && r==7)||(x!=0 && r==100/x);{if x==0 {7}else{100/x}}
