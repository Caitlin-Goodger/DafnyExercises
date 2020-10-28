include "Tweesupport.dfy"


function method toSet(t : Twee) : (r : set<int> )
{ 
    match t 
    case Empty => {}
    case Node(value,left,right) =>  {value} + toSet(left) +  toSet(right)

}

// method Main() {
//      var g := Node(1,Node(2,Empty,Node(3,Empty,Empty)),Node(5,Empty,Empty));
//      var t := toSet(g);
//      print(t);
//  }