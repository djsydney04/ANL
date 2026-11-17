fn pack(a:i64,b:i64,c:i64)->i64 requires a>=0 && a<=100 && b>=0 && b<=100 && c>=0 && c<=100;ensures(r)r==100*(a+1)+10*b+c;{let mut a=a;a=a+1;100*a+10*b+c}
fn f(x:i64)->i64 requires x>=0 && x<=10;ensures(r)r==12202*x+22505;{let mut v=x;let r=pack({v=v+1;v},{v=v*2;v},{v=v+3;v});r*100+v}
