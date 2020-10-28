function method maxDiff(s:seq<int>) : int 
  requires |s| > 0
  { 
    if |s| == 1 then absolute(s[0]) else if absolute(maxDiff(s[1..])) > absolute(s[0]) then absolute(maxDiff(s[1..])) else absolute(s[0])
  }

  function method absolute(s:int) : (r:int) 

  { 
    if s < 0 then -s else s
  }