include "Q1c-forall2rec.dfy"
include "Q1d-rec2forall.dfy"
lemma palin3(a:string,b:string) 
ensures recPalin(a) && recPalin(b) ==> recPalin(a+b+a)
{ 
    // if (|a| > 0) {
    //     assert [a[0]] + a[1..] == a;
    //     assert [a[0]] + (a[1..] + b + a) == ([a[0]] + a[1..]) + b + a;
    // } else if (|b| > 0) {
    //     assert [b[0]] + b[1..] == b;
    //     assert (a + [b[0]]) + b[1..] + a == a + ([b[0]] + b[1..]) + a;
    // }
    // if(|a| > 1) {
    //     rec2forall(a[1..(|a|-1)]);
    // }
    forall2rec(a);
    forall2rec(b);
    rec2forall(a);
    rec2forall(b);
    forall2rec(a+b+a);
    
}