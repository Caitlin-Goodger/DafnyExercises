// Do not modify or submit this file
include "Q2a-diffSeq.dfy"
include "Q2b-diffComplete.dfy"
include "Q2c-diffImp.dfy"
include "Q2d-maxDiff.dfy"

method Main() {
  var a1:seq<int> := [1,2,3,4,5] ;
  var diffS := diffSeq(a1);
  print(diffS);
  print("\n");
  var iny1:= diffImp(a1);
  var diff1:= maxDiff(iny1);
  print a1[..], "  diffImp(a1)= ", iny1, "  maxDiff(diffImp(a1))= " ,diff1,"\n";
  var a:seq<int> := [10,2,30,4,3];
  var iny:= diffImp(a);
  var diff:= maxDiff(iny);
  print a[..], "  diffImp(a)= ", iny, "  maxDiff(diffImp(a))= " ,diff,"\n";
  var m:int := maxDiff(iny[..]);
}