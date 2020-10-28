include "Q4a-value.dfy"

function method add(a : Number, b : Number) : (r : Number)
  requires |a| == |b|
  ensures value(r) == value(a) + value(b) 
  { 

  // var t := value(a) + value(b);
  // [t]

  }

  // function method addition(a :Digit, b :Digit ) : (r:Number) {
  //   var add := a + b;
  //   if add >= BASE then [1,(add-BASE)] else [add]
  // }

//   method Main() {
//     var n := [9,6,4,5];
//     var w := [2,4,3,4];
//     var j := add(n,w);
//     print(j);

// }
