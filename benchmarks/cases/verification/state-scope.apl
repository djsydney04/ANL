fn f(a:i64,b:i64)->i64 requires a>=0 && a<=10;requires b>=0 && b<=10;ensures(r)r==(a+3)*100+b+2;{let mut x=a;let mut y=b;x={let local=3;y=y+2;x+local};x*100+y}
