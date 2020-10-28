include "Q4a-value.dfy"

method valueI(n : Number) returns (r : nat)
  decreases 0
  ensures r == value(n) 
  
  {

    r := 0;
    var i:nat := |n|;

    while (i != 0) 
    decreases i 
    invariant i <= |n|
    invariant r == value(n[i..]) 
    {
        i := i -1;
        r := r * BASE + n[i];
    }

   }


  //  method Main() {
  //    var g:= [1,6,5,4];
  //    var h := valueI(g);
  //    print (h);


  //  }