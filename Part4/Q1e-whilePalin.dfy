include "Q1a-forallPalin.dfy"
method whilePalin(a:string) returns (r : bool) 
  ensures r == forallPalin(a) { 

    var i := 0;
    r := true;
    if (|a| < 2) {
      return true;
    }

    while ( i < (|a|/2)) 
    decreases (|a|/2) -i 
    invariant 0 <= i <= (|a|/2)
    invariant r == forall x :: 0 <= x < i ==> a[x] == a[|a|-1-x]{
      if(a[i] != a[|a|-1-i]) {
        r := false;
      }
      i := i+1;
    }



  }