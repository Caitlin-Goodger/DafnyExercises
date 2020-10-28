include "Q2a-diffSeq.dfy"

// in diffImp it is best to iterate in opposite order as diffSeq
method diffImp(a:seq<int>) returns (r:seq<int>)
 decreases 0
 requires |a| > 0
 ensures |r| == |a| -1
 ensures forall i:int :: 0 <= i <|r| ==> r[i] == a[i] - a[i+1]
 ensures diffSeq(a) == r 
 {
     var dif := diffSeq(a);
     var i := 0;
     r:= [];
     while i < |a|-1 
     decreases |a|-1-i
     invariant i <= |a|-1
     invariant i == |r|
     invariant forall j:int :: 0 <= j <|r| ==> r[j] == a[j] - a[j+1] 
     invariant forall j:int :: 0 <= j <|r| ==> r[j] == dif[j];
     {
         r := r + [a[i] - a[i+1]];
         i := i+1;
     }
     

     assert forall j:int :: 0 <= j <|r| ==> r[j] == a[j] - a[j+1];
     assert |r| == |a| -1;
 }


