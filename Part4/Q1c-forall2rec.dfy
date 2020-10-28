include "Q1a-forallPalin.dfy"
include "Q1b-recPalin.dfy"
lemma forall2rec(a : string)
ensures forallPalin(a) ==> recPalin(a) { }