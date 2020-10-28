include "Q2a-diffSeq.dfy"

lemma diffComplete(s:seq<int>, r:seq<int>) 
  requires |s| > 0 
  //requires diffSeq(s) == r  
  requires |r| +1 == |s|
  requires forall i:int :: 0 <= i <|r| ==> r[i] == s[i] - s[i+1]
  ensures diffSeq(s) == r  
  {
    if |s| == 1 {
      
    } else {
      diffComplete(s[1..],r[1..]);
    }
  }

  