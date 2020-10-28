include "Numsupport.dfy"

function method value(n : Number) : (r : nat) { 
    if n == [] then 0 else n[0] + BASE * value(n[1..])
 }
