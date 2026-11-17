fn f(p:bool,a:i64)->i64 requires a>=-100 && a<=100;ensures(r)(p && r==11*a+3)||(!p && r==11*a+5);{let mut x=a;let old=x;if {x=x+1;p}{x=x+2;}else{x=x+4;};old*10+x}
