Control.Print.printLength:=1000;
Control.Print.printDepth:=1000;
Control.Print.linewidth:=1000;


val t1="LAMBDA abc[(P Z)]"
val ans1=fromString(t1)
val tt1= t1=toString(fromString(t1))

val t2 = "(ITE <T,LAMBDA x[x],LAMBDA x[LAMBDA y[Z]]>)"
val ans2=fromString(t2)
val tt2= t2=toString(fromString(t2));

val t3 = "(ITE <T,(LAMBDA x[x] Z),(LAMBDA x[LAMBDA y[Z]] Z)>)"
val ans3=fromString(t3)
val tt3= t3=toString(fromString(t3));

val t4 = "((S Z) Z)"
val ans4=fromString(t4)
val tt4= t4=toString(fromString(t4));

val t5 = "(Z Z)"
val ans5=fromString(t5)
val tt5= t5=toString(fromString(t5));

val t6 = "(P Z)"
val ans6=fromString(t6)
val tt6= t6=toString(fromString(t6));

val t7 = "(LAMBDA x[x] T)"
val ans7=fromString(t7)
val tt7= t7=toString(fromString(t7));

val t8 = "(LAMBDA x[(LAMBDA y[x] T)] F)"
val ans8=fromString(t8)
val tt8= t8=toString(fromString(t8));

val t9 = "(LAMBDA x[(LAMBDA y[y] LAMBDA y[x])] F)"
val ans9=fromString(t9)
val tt9= t9=toString(fromString(t9));

val t10 = "((LAMBDA x[x] LAMBDA x[x]) F)"
val ans10=fromString(t10)
val tt10= t10=toString(fromString(t10));

val t11 = "((LAMBDA x[LAMBDA y[x]] x) (w w))"
val ans11=fromString(t11)
val tt11= t11=toString(fromString(t11));

val t12 = "LAMBDA LAMBDA LAMBDA (GTZ Z)[T][T][(S Z)]"
val ans12=fromString(t12)
val tt12= t12=toString(fromString(t12));

val t13 = "(LAMBDA LAMBDA LAMBDA (GTZ Z)[T][T][(S Z)] LAMBDA LAMBDA LAMBDA (GTZ Z)[T][T][(S Z)])"
val ans13=fromString(t13)
val tt13= t13=toString(fromString(t13));


val FINAL_ANS = tt1 andalso tt2 andalso tt3 andalso tt4 andalso tt5 andalso tt6 andalso tt7 andalso tt8 andalso tt9 andalso tt10 andalso tt11 andalso tt12 andalso tt13 
