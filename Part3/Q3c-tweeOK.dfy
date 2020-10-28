include "Tweesupport.dfy"
include "Q3b-toSet.dfy"

predicate method tweeOK(t : Twee)
{ 
    match t
    case Empty => true
    case Node(value,left,right) => 
    var leftValues := toSet(left);
    var rightValues := toSet(right);
    var l:= (set x | x in leftValues && x < value) == leftValues;
    var r:= (set x | x in rightValues && x > value) == rightValues;
    if l && r then tweeOK(left) && tweeOK(right) else false
}

// function method getValue(t : Twee) : (r:seq<int>) {
//     match t 
//      case Empty => []
//      case Node(value,left,right) => getValue(left) + [value] + getValue(right)
// }

// method Main() {
//     var g := Node(5,Node(3,Node(2,Empty,Empty),Node(4,Empty,Empty)),Node(8,Node(6,Empty,Empty),Node(7,Empty,Empty)));
//     var h := Node(5,Node(3,Node(2,Empty,Empty),Node(4,Empty,Empty)),Node(8,Node(6,Empty,Empty),Node(9,Empty,Empty)));
//     var m := Node(5,Node(1,Empty,Empty),Empty);
//     var r := tweeOK(m);
//     print(r);
// }