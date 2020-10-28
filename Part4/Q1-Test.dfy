include "Q1a-forallPalin.dfy"
include "Q1b-recPalin.dfy"
include "Q1c-forall2rec.dfy"
include "Q1d-rec2forall.dfy"

method tests(a : string) {
  forall2rec(a);
  rec2forall(a);
  assert forallPalin(a) ==> recPalin(a);
  assert recPalin(a) ==> forallPalin(a);
}