
function method diffSeq(s:seq<int>) :(r:seq<int>) 
  requires |s| > 0 
  ensures |r| == |s| -1
  ensures forall i:int :: 0 <= i <|r| ==> r[i] == s[i] - s[i+1]
  //ensures diffSeq(s) == r
  { 
    if |s| == 1 then [] else [s[0]-s[1]] + diffSeq(s[1..])
    
  }