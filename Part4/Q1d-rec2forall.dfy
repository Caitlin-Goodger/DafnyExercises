
include "Q1a-forallPalin.dfy"
include "Q1b-recPalin.dfy"
lemma rec2forall(a : string) 
ensures recPalin(a) ==> forallPalin(a) { 
    if(|a| > 1) {
        rec2forall(a[1..(|a|-1)]);
    }
}