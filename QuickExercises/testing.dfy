// datatype List<T> = Nil | Cons(head: T, tail: List<T>)

// function method first<T>(l : List<T>) : T
//   requires l.Cons? 
// {  
    
// }
  
// lemma firstIsFirst(x : int){
//     assert first(Cons(x,Nil)) == x;
// }


// datatype List<T> = Nil | Cons(head: T, tail: List<T>)

// function method second<T>(l : List<T>) : T
// requires l.Cons?
// requires l.tail.Cons?
// {
//   l.tail.head
// }

// lemma secondIsSecond(x : int, y : int){
//     assert second(Cons(x,Cons(y, Nil))) == y;
// }

// datatype Option<T> = None | Some(value: T)
//   //see https://en.wikipedia.org/wiki/Option_type

// datatype List<T> = Nil | Cons(head: T, tail: List<T>)


// function method secondOpt<T>(l : List<T>) : Option<T>
//   //https://www.youtube.com/watch?v=dg_lDj_wV7c
//   //look ma no preconditions!
// {  
// if l.Cons? && l.tail.Cons? then Some(l.tail.head) else None
// }

// lemma secondIsSecondOpt(x : int, y : int){
//     assert secondOpt(Cons(x,Cons(y, Nil))) == Some(y);
//     assert secondOpt(Cons(y, Nil)) == None;
//     assert secondOpt<int>(Nil) == None;
// }

/* Read sections 4.0, to 4.4 of the book.
   Implement  cMatchString and cIfString functions to satisfy the assert
statments in the Main method.
It may help to test the output of your functions by printing their output.
   The cMatchString method should make use of match (and not if)
   The cIfString method should make use of if (and not match)

   YOU WILL NEED both techniques later */

// datatype Color = Red | Blue |  Named(name: string)

// function method cIfString (c:Color) : string{
//   if c == Red then "Red" else 
//   if c == Blue then "Blue" else 
//   if c.Named? then c.name else "No"
// }

// function method cMatchString(c:Color) :string {
//  cIfString(c)
// }

// method Main() {
//     assert forall c:Color :: cIfString(c) == cMatchString(c);
//     assert cIfString(Red) == "Red";
//     assert cIfString(Blue) == "Blue";
//     assert cIfString(Named("pingu")) == "pingu";
//     assert cIfString(Named("seally")) == "seally";
// }
   
  
// datatype Tree = Leaf | Node(left: Tree, right: Tree)
// function method Size(t: Tree): nat
// {
//   if t.Node? then Size(t.left) + Size(t.right) else 1
// }
    
    
// method Main() {
//   var tl:Tree := Leaf;
//   var tc:Tree := Node(Node(Leaf, Leaf),Leaf);
//   assert Size(tl) == 1;
//   assert Size(tc) == 3;
//   print "  ",Size(tl),"  ",Size(tc), "\n";

// }


// /* Read sections 4.0, to 4.5 of the book.
//   Implement the noNamedColor predicate to satisfy the
// assert statements in Main. */

// datatype Color = Red | Blue |  Named(name: string)
// datatype Tree<T> = Leaf(data: T)
//                  | Node(left: Tree<T>, right: Tree<T>)
// predicate noNamedColor(t:Tree<Color>)
//   {
//     if t.Leaf? then if t.data == Red then true else if t.data == Blue then true else false else 
//     if t.Node? then if noNamedColor(t.left) && noNamedColor(t.right) then true else false else false
//   }
// method Main() {
//     var t0 := Node(Node(Leaf(Red),Leaf(Blue)), Leaf(Red));
//     assert noNamedColor(t0) == true;
//     var t1 := Node(Leaf(Red),Leaf(Blue));
//     assert noNamedColor(t1) == true;
//     var t2 := Node(Node(Leaf(Red),Leaf(Blue)), Leaf(Named("pingu")));
//     assert noNamedColor(t2) == false;
//     var t3 := Node(Leaf(Named("pingu")), Node(Leaf(Red),Leaf(Blue)));
//     assert noNamedColor(t3) == false;
// }


// /* Read sections 4.0, to 4.5 of the book.
//   Implement the cNC function to specify the containsNamedColor method.
//   The result must satisfy the assert statements in Main. */

// datatype Color = Red | Blue |  Named(name: string)
// datatype Tree<T> = Leaf(data: T)
//                  | Node(left: Tree<T>, right: Tree<T>)
// /* A solution is to first match on the casses of the tree. This allows you
// to intorduce a parameter variable for the Color on the Leaf.
// Then if the color variable is of typ Named you can use the
// label name to extract the string. */
// function cNC(t:Tree<Color>) :set<string>
//      {
//        var sofar:set<string> := {};
//     if t.Leaf? then

//      var c:Color := t.data;
//     if c.Named?  then sofar+{c.name} else sofar
//      else if t.Node? then sofar + cNC(t.left) + cNC(t.right) else sofar
//      }

// method containsNamedColor(t:Tree<Color>) returns (r: set<string>)
//     decreases t
//     ensures r == cNC(t)
//  {
//     var sofar:set<string> := {};
//     if t.Leaf? {

//      var c:Color := t.data;
//     if c.Named?  {sofar:= sofar+{c.name};}
//     } else {
//         var tmp:set<string> := containsNamedColor(t.left);
//         var tmp2:set<string> := containsNamedColor(t.right);
//         sofar := tmp + tmp2 ;}

//     return sofar;
// }


// method Main() {
//     var t0 := Node(Node(Leaf(Red),Leaf(Blue)), Leaf(Red));
//     var tmp:set<string>  := containsNamedColor(t0) ;
//     assert tmp == {};
//     var t2 := Node(Node(Leaf(Red),Leaf(Blue)), Leaf(Named("pingu")));
//     var tmp2:set<string>  := containsNamedColor(t2) ;
//     assert tmp2 == {"pingu"};
//     var t3 := Node(Leaf(Named("pingu")),
//               Node(Leaf(Named("david")),Leaf(Named("james"))));
//     var tmp3:set<string>  := containsNamedColor(t3) ;
//     print tmp3, "\n";
//     assert tmp3 == {"pingu","david","james"};


// }

// /*  read Rise4fun ~ tutorial ~ set
//     Dafny +  , set union
//     Dafny *  , set intersection
//     Dafny -  , set diference
//     Dafny subset or eq ,  <=     {1} <= {1,2}
//     Dafny subset , <
// */
// // Think what the method does and then
// // add an accurate contract for the setbuilder method
// method  setbuilder(s: set<int>, t: set<int>) returns (r: set<int>)
// requires (1 !in s) && (2 !in s)
// ensures r <= {3}
// {
//      r := (s - t);
//      r := r*{1,2,3,4};
//      r := r*{5,1,2,3};
// }

// // This is simply a test process
// // it is used to prevernt silly postconditions like "ensures true"
// method tester(ss: set<int>, tt: set<int>)
// {
//     var c:set<int> := {0,3,4,5};
//     var r:set<int> := setbuilder((ss*c), tt);
//     print r;
//     //assert r <= {3,4};
//     var cc:set<int> := {0,3,4,5};
//     var rr:set<int> := setbuilder((ss*cc), tt);
//     print r;
//     //assert rr <= {0,3};
// }

// method Main () {
//   var tmp12:set<int> := {0,3,4,5,6,8};
//   var c:set<int> := {0,4,5};

//   tester(tmp12,c);

// }

// /* You need only understand how the program behaves. You can ignore
// the details of the proof. But in case you are interested not
// the loop invariant a< 0 ==> b==bx  is needed although
// the loop can never in entered what a< 0 */

// method foo(a:int, b:int) returns (r:int)
//   ensures a > 0 ==> r == a +b
//   ensures a < 0 ==> r == b
// {
//   var tmp:int := a;
//   var bx:int := b;
//   //assert a < 0 ==> b==bx;
//   while (tmp > 0 )
//    decreases tmp
//    invariant tmp < 0 ==> b==bx
//        // Note loop never executed when tmp<0 (or a<0)
//     invariant  a>0 ==> tmp >= 0
//     invariant (tmp +bx == a +b)
//   {
//       tmp := tmp -1;
//       bx:= bx +1;
//   }
//   //assert a < 0 ==> b==bx;
//  r := bx;
// }
// /*omitted*/

// method seqSum(input:seq<nat>) returns (r:nat)
// {
//     r :=0; 
//     var i:nat := 0;
//     while (i<|input|)
//      decreases |input| -i
//     {
//         r:= r+input[i];
//         i := i+1;
//     }
// }

// method longAddition(a : nat, b : nat)  returns (r : nat)
//   ensures r == a + b 
// {
//  var ax := a;
//  var bx := b;

//  while (ax > 0)
//   // needs one decreases and one invariant
// decreases ax
//    invariant ax +bx == a +b
//     {
//       ax := ax - 1; 
//       bx := bx + 1;
//       print "ax=",ax," bx=",bx,"\n";
//     } 
//     r := bx;
// }

// method Main() {  
//    var v := longAddition(4,3);
//    print "done\n";
// }

// method Main() {
// var guard := true;
// var inv := true;

// while (guard) 

// //needs one decreases and one invariant...

// invariant inv
// decreases guard

//   {
//       assert inv;
//       inv := false;
//       guard := false;
//       inv := true;
//       assert inv;
//   }

// assert (!guard);
// assert inv;
// }

// /*   while Guard  invariant Inv {}
//     Remember the Guard
//         Inv /\ not Guard  ==> ensures
// */
// datatype Floor = Dirty | Mopped
// method  cleaner(corridor: seq<Floor>) returns (r: seq<Floor>)
// ensures |corridor| == |r|
// {
//    r:=[];
//    var i := |corridor|;

//    while i >0
//    // one decreases and TWO invariant clauses
//   decreases i 
//   invariant |r| + i == |corridor|
//   invariant 0<=i<=|corridor|

//    {
//       r := r + [Mopped];
//       i := i -1;
//    }
// }

// /* Recursive specification Iterative implementation
// the ensures clause establishes that the implementation
// satisfies the specification.  */
// datatype List = Nil | Cons(head:nat, tail:List)
// function sumNum(l:List) :nat
// decreases l
// {
//     match l
//        case Nil => 0
//        case Cons(h,t) => h + sumNum(t)
// }
// method sumNumImp(l:List) returns (r:nat)
// ensures r == sumNum(l)
// {
//     r := 0;
//     var lin:List := l;
//     while (lin.Cons?)
//     // add Both a decreases and an invariant clause
    
//       decreases lin
//       invariant r == sumNum(l) - sumNum(lin)
//     {
//         r := r + lin.head;
//         lin := lin.tail;
//     }
// }
   
//    /* factorial  DO NOT USE INTEGER DIVISION */
// function method fact(n:nat) : nat
// decreases n
// { if n == 0 then 1 else n* fact(n-1)  }
// method factorial(n:nat) returns (r:nat)
//   ensures r == fact(n) /* DO NOT USE INTEGER DIVISION */
// {
//   var x := n;
//   r := 1;
//   while x > 0
//     decreases x
//     invariant r * fact(x) == fact(n)
//   {
//     r := r * x;
//     x := x - 1;
//   }
// }
// method Main() {
//     var f4:nat := factorial(4);
//     print "4 ", fact(4)," ", f4 , "\n";
//     var f5:nat := factorial(5);
//     print "5 ", fact(5)," ", f5 , "\n";
// }


// predicate isFilledArray(a:array<int>, start : int, step : int)
// reads a
// {
//  forall j :: 0 <= j < a.Length ==> a[j] == start + (j * step)
// }

// method fillArray(length : nat, start : int, step : int)  returns (a : array<int>)
//   ensures isFilledArray(a,start,step)
//   ensures a.Length == length
// {
//  var i : nat := 0;
//  a := new int[length];
//  while (i < length ) 
//  decreases length - i 
//  invariant 0 <= i <= length
//  invariant forall j :: 0 <= j < i ==> a[j] == start + (j * step) {
//     a[i] := start + (i*step);
//     i := i+1;
//  }
    
// }

// /* cut and paste question into VS code then paste answer into window
// Zipping two lists of ints. The invartiants for this are tricky but
// DON'T PANIC remember range invariant then correctness invariant   */
// function method sumSeqs(a:seq<int>, b:seq<int>) : seq<int>
//   decreases a
//   requires |a| == |b|
// {
//    if a == [] then [] else
//       [a[0]+b[0]] + sumSeqs(a[1..],b[1..])
// }

// /* this either this lemma is important, or we're really really mean*/
// lemma soWhat() ensures sumSeqs([],[]) == [] {}

// method sumSeqImp(a:seq<int>, b:seq<int>)  returns (r : seq<int>)
// requires |a| == |b|
// ensures r == sumSeqs(a,b)
// {
//  var i: int := |a|;
//  var arr: array := new int[|a|];
//  while (i >= 1)
//    decreases i - 1
//    invariant 0 <= i <= |a|;
//    invariant arr[i ..] == sumSeqs(a[i ..], b[i ..])
//  {
//    i := i - 1;
//    arr[i] := a[i] + b[i];
//  }

//  r := arr[..];

// }
// method Main() {
//     var testa:seq<int> := [1,2,3,4];
//     var testb:seq<int> := [1,2,3,4];
//     var resab := sumSeqs(testa,testb);
//     var resabI := sumSeqImp(testa,testb);
//     assert resabI == resab;
//     print resab," ", resabI,"\n";
// }

// method Main() {  
//   var myArray := fillArray(5,2,3);
//   print myArray," ",myArray[0]," ",myArray[1]," ",myArray[2]," ",myArray[3]," ",myArray[4]," ","\n";
// }

// predicate isArraySum(a:array<int>, b:array<int>, r:array<int>)
//   requires a.Length == b.Length == r.Length
//   reads a, b, r
//  {
//       forall j :: 0 <= j < r.Length ==> r[j] == a[j] + b[j] 
// }

// method sumArrays(a:array<int>, b:array<int>)  returns (r : array<int>)
//   requires a.Length == b.Length
//   ensures a.Length == b.Length == r.Length
//   ensures isArraySum(a,b,r)
// {
//  var i : nat := 0;
//  r := new int[a.Length];
//  while (i < a.Length )

// //needs decreases plus two invariants
   // decreases a.Length - i
   // invariant 0<=i<=a.Length
   // invariant forall j :: 0 <= j < i ==> r[j] == a[j] + b[j] 
//     {
//      r[i] := a[i] + b[i];
//      i := i + 1;
//     } 
// }

// /* This is easier to do in VS code!
// write an  Iterative implementation  and verify it by adding loop invariants */
// datatype List = Nil | Cons(head:nat, tail:List)
// function method multNum(l:List) :nat /* recusrive specification */
// decreases l
// {
//     match l
//        case Nil => 1
//        case Cons(h,t) => h * multNum(t)
// }
// method multNumImp(l:List) returns (r:nat)
// requires l.Cons?
// ensures r == multNum(l)   /* this is statically verified for any example */
// {
//     var i : int := 0;
//     r := 1;
//     var temp:List:= l;
//     while (temp.Cons?) 
//     decreases temp
//     invariant 0<= i{
//        i := i+1;
//        r := r*temp.head;
//        temp := temp.tail;
//     }
// }
// method Main() {
//    print "main \n";
//    var l:List := Cons(2,Cons(3,Nil));
//    var n:nat := multNum(l);
//    var nm:nat := multNumImp(l);
//    assert n ==nm;  /* this is statically verified (checked) for the single example */
//    print l,"  ", n, " ",nm, "\n";
// }

// method FPP(tory : bool, labour: bool) 
//  requires ( (tory || labour) && !(tory && labour) ) 
//  ensures (tory || labour)  {}

// datatype Party = Green | Labour | Nzf | Maori | Tory | Act | ToP

//  method Main()
//   {
//     var mmp : multiset<Party> := multiset{Labour, Labour, Green, Maori, 
//                         Act, Tory, Labour, Tory};
//     print (mmp),"\n";
//     var tally := map party | party in mmp :: 5;
//     print tally, "\n";
//   }

// function set_union<T>(a: set<T>, b : set<T>): (res: set<T>)
//    ensures forall x | x in res :: x in a || x in b
//    ensures forall x | x in a :: x in res
//    ensures forall x | x in b :: x in res
// { (set x | x in a+b :: x)}

// method Main() {
//   var myMap := map["apple" := 3, "pear" := 5, "banana" := 4];
//   print myMap, "\n";

//  //insert "tomato" into the map with value 5
//   var yourMap := myMap["tomato" := 5];
//   print yourMap, "\n";
//   assert yourMap == map["apple" := 3, "tomato" := 5, "pear" := 5, "banana" := 4]
// }

// method Main() {
//   var myMap :=  map["apple" := 3, "tomato" := 5, "pear" := 5, "banana" := 4];
//   print myMap, "\n";

// //check that tomato is in the map's set of keys
// //hint - look up
// //https://ecs.wgtn.ac.nz/Courses/SWEN324_2020T2/DafnyResources#StackOverflow
//   var your := "tomato" in myMap.Keys;
//   print your, "\n";
//   assert your;
// }

// method Main() {
//   var myMap :=  map["apple" := 3, "tomato" := 5,  "banana" := 4];
//   print myMap, "\n";

// //double each map entry

// //hint - look up the Dafny quick refeerence, or/and 
// //https://ecs.wgtn.ac.nz/Courses/SWEN324_2020T2/DafnyResources#StackOverflow
//   var yourMap := map x : string | x in myMap.Keys :: myMap[x] * 2;
//   print yourMap, "\n";
//   assert yourMap ==  map["apple" := 6, "tomato" := 10,  "banana" := 8];
// }

// method Main() {
//   var myMap :=  map["apple" := 3, "tomato" := 5,  "banana" := 4];
//   print myMap, "\n";

// //remove tomato from my map

// //hint - look up the Dafny quick refeerence, or/and 
// //https://ecs.wgtn.ac.nz/Courses/SWEN324_2020T2/DafnyResources#StackOverflow
//   var yourMap := map x : string | x in myMap.Keys && x != "tomato" :: myMap[x];
//   print yourMap, "\n";
//   assert yourMap ==  map["apple" := 3, "banana" := 4];
// }

// datatype List<T> = Nil | Cons(car : T, cdr : List<T>)

// function method toSequence<T>(l : List<T>) : seq<T> {
//   match l
//     case Nil => []
//     case Cons(car,cdr) => [car] + toSequence(cdr)
// }

// //complete this funciton so it doubles every element of the list
// function method double(l : List<real>) : List<real>
//   ensures 
//     (var input := toSequence(l);
//      var output := toSequence(double(l));
//      (|output| == |input|) && 
//      forall i :: 0 <= i < |input| ==> output[i] == 2.0 * input[i])
//   {
//   match l
//     case Nil => Nil
//     case Cons(car,cdr) => Cons(car*2.0,double(cdr))

//   }




// datatype List<T> = Nil | Cons(car : T, cdr : List<T>)

// function method toSequence<T>(l : List<T>) : seq<T> {
//   match l
//     case Nil => []
//     case Cons(car,cdr) => [car] + toSequence(cdr)
// }


// //complete this function so that it replaces elemth element of the list 
// function method replace<T(==)>(l : List<T>, elem : nat, other : T) : List<T>
//   requires elem < |toSequence(l)|
//   ensures toSequence(replace(l,elem,other)) ==
//      toSequence(l)[..elem] + [other] + toSequence(l)[(elem+1)..]
// {
//   match l
//     case Nil => Nil
//     case Cons(car,cdr) => if elem == 0 then Cons(other,cdr) else Cons(car,replace(cdr,elem-1,other))
// }


// lemma replace1() {
//   assert replace( Cons("000", Cons("111", Cons("222", Nil))), 1, "999") ==
//     Cons("000", Cons("999", Cons("222", Nil)));
// }

// datatype List<T> = Nil | Cons(car : T, cdr : List<T>)

// function method toSequence<T>(l : List<T>) : seq<T> {
//   match l
//     case Nil => []
//     case Cons(car,cdr) => [car] + toSequence(cdr)
// }

// //complete this function so that it returns the list without its elemth element 
// function method delete<T(==)>(l : List<T>, elem : nat) : List<T>
//   requires elem < |toSequence(l)|
//   ensures toSequence(delete(l,elem)) == toSequence(l)[..elem] + toSequence(l)[(elem+1)..]
// {
//   match l
//     case Nil => Nil
//     case Cons(car,cdr) => if elem == 0 then cdr else Cons(car,delete(cdr,elem-1))
// }

// lemma delete1() {
//   assert delete( Cons("000", Cons("111", Cons("222", Nil))), 1) ==
//     Cons("000", Cons("222", Nil));
// }

// datatype List<T> = Nil | Cons(car : T, cdr : List<T>)

// function length<T>(l : List<T>) : nat 
//   { match l
//      case Nil => 0
//      case Cons(_, cdr) => 1 + length(cdr) }

// //find the length of the list using a while...
// method lengthW<T>(list:  List<T>) returns (r : nat)
//  ensures r == length(list) {
//     var l := list;
//     r := 0;
   //  while l.Cons? 
   //  decreases l
   //  {
   //     r := r+1;
   //     l:= l.cdr;
   //  }
//  }

// datatype Tree = Leaf(value : int) | Node(left : Tree, right: Tree) 

// const myTree := Node(Node(Leaf(20),Leaf(3)),Node(Leaf(7),Leaf(-2)));

// //sum the leaves in the Tree - with a while!
// method sumWhile(tree : Tree) returns (r : int)
//  ensures r == sumLeaves(tree)
// {
//    //these variables might get you started
//    r := 0;
//    var todo := [tree];
//    ghost var chips := allNodes(todo);

//    while [???]

// }

// //primitive recusive version, LeafByNiggle!
// function method sumLeaves(t : Tree) : int 
// /*omitted*/


// //number of nodes in the tree
// function method size(t : Tree) : nat 
// /*omitted*/

// //I needed this function
// function  allNodes(l : seq<Tree>) : nat
// {
//   if (l == []) 
//     then 0 
//     else size(l[0]) + allNodes(l[1..])
// }

// //And this one too
// function  allSum(l : seq<Tree>) : int
// {
//   if (l == []) 
//     then 0 
//     else sumLeaves(l[0]) + allSum(l[1..])
// }

// datatype List<T> = Nil | Cons(car : T, cdr : List<T>)

// function length<T>(l : List<T>) : nat 
//   { match l
//      case Nil => 0
//      case Cons(_, cdr) => 1 + length(cdr) }

// //find the length of the list using a while...
// method lengthW<T>(list:  List<T>) returns (r : nat)
//  ensures r == length(list) {
//     var l := list;
//     r := 0;
//     while l.Cons?
//     decreases l 
//     invariant r == length(list)-length(l){
//        r := r +1;
//        l:= l.cdr;
//     }
//  }

//  datatype Tree = Leaf(value : int) | Node(left : Tree, right: Tree) 

// const myTree := Node(Node(Leaf(20),Leaf(3)),Node(Leaf(7),Leaf(-2)));

// //sum the leaves in the Tree - primitive recursively
// function method sumLeaves(t : Tree) : int 
// {
// if t.Leaf? then t.value else sumLeaves(t.left) + sumLeaves(t.right)

// }

// //The niggle is an oracle that has been 
// /*omitted*/


// method Main() {
//     print myTree,"\n";
//     print sumLeaves(myTree),"\n";
//     assert sumLeaves(myTree) == 28;
// }

//datatype List<T> = Nil | Cons(car : T, cdr : List<T>)

// function method filterByFilter(list: List<int>) : (r: List<int>)
//  ensures positives(r)
// {
// match list
//     case Nil => true
//     case Cons(a,d) => if (a<0) then filterByFilter(d) else Cons(a,filterByFilter(d)
// }

// predicate positives(list : List<int>) {
//   match list
//     case Nil => Nil
//     case Cons(a,d) => if (a<0) then false else positives(d)
// }

// function method  length<T>(l : List<T>) : nat 
//   { match l
//      case Nil => 0
//      case Cons(_, cdr) => 1 + length(cdr) }

// method Main()
// {    
//     var myList := Cons(1,Cons(-2,Cons(3,Cons(4,Nil))));
//     var filtered := filterByFilter(myList);
//     print filtered, "\n";
//     assert length(filtered) == 3;
//     assert positives(filtered);
//     assert filtered == Cons(1,Cons(3,Cons(4,Nil)));
// }
      

// function method filterByTail(list: List<int>, acc : List<int>) : (r: List<int>)
//  ensures positives(r)
// match list
//     case Nil => Nil
//     case Cons(a,d) => if (a<0) then filterByTail(d,acc) else Cons(a,filterByTail(d,acc)
// }

// predicate positives(list : List<int>) {
//   match list
//     case Nil => true
//     case Cons(a,d) => if (a<0) then false else positives(d)
// }

// function method  length<T>(l : List<T>) : nat 
//   { match l
//      case Nil => 0
//      case Cons(_, cdr) => 1 + length(cdr) }

// method Main()
// {    
//     var myList := Cons(1,Cons(-2,Cons(3,Cons(4,Nil))));
//     var filtered := filterByTail(myList, Nil);
//     print filtered, "\n";
//     assert length(filtered) == 3;
//     assert positives(filtered);
//}

// /* This is easier to do in VS code!
// write an  Iterative implementation  and verify it by adding loop invariants */
// datatype List = Nil | Cons(head:nat, tail:List)
// function method multNum(l:List) :nat /* recusrive specification */
// decreases l
// {
//     match l
//        case Nil => 1
//        case Cons(h,t) => h * multNum(t)
// }
// method multNumImp(l:List) returns (r:nat)
// requires l.Cons?
// ensures r == multNum(l)   /* this is statically verified for any example */
// {
//    r := multNum(l);
// }
// method Main() {
//    print "main \n";
//    var l:List := Cons(2,Cons(3,Nil));
//    var n:nat := multNum(l);
//    var nm:nat := multNumImp(l);
//    assert n ==nm;  /* this is statically verified (checked) for the single example */
//    print l,"  ", n, " ",nm, "\n";
// }

// datatype List<T> = Nil | Cons(car : T, cdr : List<T>)

// method filterByWhile(list: List<int>) returns (r: List<int>)
//  ensures positives(r)
// {
//     r := Nil;
//     var l := list; 
   //  while l.Cons?
   //  decreases l
   //  invariant positives(r){
   //    if (l.car >= 0) {
   //       r := Cons(l.car,r);
   //    }
   //    l := l.cdr;
   //  }
// }


// predicate positives(list : List<int>) {
//   match list
//     case Nil => true
//     case Cons(a,d) => if (a<0) then false else positives(d)
// }

// function method  length<T>(l : List<T>) : nat 
//   { match l
//      case Nil => 0
//      case Cons(_, cdr) => 1 + length(cdr) }

// method Main()
// {    
//     var myList := Cons(1,Cons(-2,Cons(3,Cons(4,Nil))));
//     var filtered := filterByWhile(myList);
//     print filtered, "\n";
//     assert positives(filtered);
// }

// datatype Tree = Leaf(value : int) | Node(left : Tree, right: Tree) 

// const myTree := Node(Node(Leaf(20),Leaf(3)),Node(Leaf(7),Leaf(-2)));

// //sum the leaves in the Tree - with a while!
// method sumWhile(tree : Tree) returns (r : int)
//  ensures r == sumLeaves(tree)
// {
//    //these variables might get you started
//    r := 0;
//    var todo := [tree];
//    ghost var chips := allNodes(todo);

//    while todo != [] 
//    decreases chips 
//    invariant chips == allNodes(todo)
//    invariant allSum(todo) + r == sumLeaves(tree){
//       var t := todo[0];

//       if(t.Leaf?) {
//          r := r + t.value;
//          todo := todo[1..];
//       } else {
//          todo:= [t.left,t.right] + todo[1..];
//       }
//       chips := chips -1;
//   }

// }

// //primitive recusive version, LeafByNiggle!
// function method sumLeaves(t : Tree) : int {
//    match t
//    case Leaf(v) => v
//    case Node(l,r) => sumLeaves(l) + sumLeaves(r)
// }
// /*omitted*/


// //number of nodes in the tree
// function method size(t : Tree) : nat 
// /*omitted*/ {
//    match t 
//    case Leaf(v) => 0
//    case Node(l,r) => 1 + sumLeaves(l) + sumLeaves(r)
// }

// //I needed this function
// function  allNodes(l : seq<Tree>) : nat
// {
//   if (l == []) 
//     then 0 
//     else size(l[0]) + allNodes(l[1..])
// }

// //And this one too
// function  allSum(l : seq<Tree>) : int
// {
//   if (l == []) 
//     then 0 
//     else sumLeaves(l[0]) + allSum(l[1..])
// }

// method Main() {
//  var a := 1;
//  var b := 2;
//  var c := 3;

//  var fuel := 999;

//  while (fuel > 0) 
//     decreases fuel
//     invariant a != b
//     invariant a != c
//     invariant b !=c
//     {

//         var tmp := a;
//         a := b;
//         b := c;
//         c := tmp;

//         fuel := fuel - 1;
//     }
//   assert a != b;
// } 

// //This question inspired by Alistair Donaldson:
// //
// // Software Verification Using k-Induction
// //Alastair F Donaldson, Leopold Haller, Daniel Kroening, Philipp Rümmer
// //International Static Analysis Symposium 2011
        

// class window {
//     var fi:int;
//     constructor(){fi:=0;}
//     function double(i:int):int
//     reads this
//     { 2*i +fi}
// }

// /* Visual studio gives a good error message*/
// /* Visual studio gives a good error message*/
// class picture {
//     var fi:int;
//     constructor(){fi:=0;}
//     method double(i:int) returns (r:int)
//      modifies this
//     { fi:= i;
//     r:= 2*1;}
// }

// /* Write the getter getFi() so that the class verifies */
// class covid2m {
//     var fi:int;
//     constructor() ensures fi == 0 {fi:=0;}
    
//     function method getFi() : int 
//     reads this{
//        fi
//     }
// }

// method Main() {
//     var co:covid2m := new covid2m();
//     print "co.fi = ", co.getFi();
//     assert co.getFi() == 0;
// }

// /* Write  setFi() so that the class verifies
//     remember my body is private! */
// class covidElbowBumps {
//     var fi:int;
//     constructor() ensures fi == 0 {fi:=0;}
    
//     method setFi(i:int) 
//     modifies this
//     ensures fi == i{
//         fi := i;
//     }

//     method testFi(j:int) returns (r:bool)
//     ensures (r == (fi==j))  {
//         print "fi ",fi,"   j ",j,"\n";
//         r := (fi==j);
//     }
// }

// method Main() {
//     var co:covidElbowBumps := new covidElbowBumps();
//     co.setFi(6);
//     var tmp:bool := co.testFi(6);
//     print tmp,"\n";
//     assert tmp;
// }

// /* Write  append2Store so that the class verifies
//     remember my body is private AND
//     old(x) in the post condition  referes to the value of x in the pre state*/
// class classyOne {
//     var store:string;
//     constructor() ensures store == "" {store:="";}

//     method append2Store(t:string) 
//     modifies this 
//     ensures store == old(store) + t{
//         store := store + t;
//     }
//     method testStore(t:string) returns (r:bool)
//     ensures (r == (store == t))  {
//         print "store ",store,"   t ",t,"\n";
//         r := (store==t);
//     }
// }

// method Main() {
//     var clOne:classyOne := new classyOne();
//     clOne.append2Store("pingu");
//     var tp:bool := clOne.testStore("pingu");
//     clOne.append2Store("robby");
//     var tmp:bool := clOne.testStore("pingurobby");
//     print tmp,"\n";
//     assert tp && tmp;
// }     

// /* Write  the constructor, getStore  AND setStore
//     remember what you have learnt in previous exercises */
// class classyTwo {
//     var store:nat;

//      constructor() ensures store == 0 {store:=0;}

//     function method getStore() : nat 
//     reads this{
//        store
//     }

//     method setStore(i:nat) 
//     modifies this
//     ensures store == i{
//         store := i;
//     }

// }
// method Main() {
//     var clTwo:classyTwo := new classyTwo();
//     var n:nat := clTwo.getStore();
//     assert (n == 0);
//     clTwo.setStore(6);
//     assert (clTwo.getStore()== 6);
//     print "clTwo ", clTwo.getStore(), "\n";
// }

// class Stack {
//    const values : array<int>;
//    const capacity : nat;
//    var size : nat;
// //this simple stack of integers needs an (anonymous) constructor!
//    constructor (i: nat)
//    ensures capacity == i
//    ensures size == 0
//    ensures values.Length == i
//    ensures forall k :: 0<= k < i ==> values[k] == 0{
//        capacity := i;
//        size := 0;
//        values := new int[i](l => 0);

//    }
// }

// method Main() {
//    var s := new Stack(10);
//    assert s.capacity == 10;
//    assert s.values.Length == s.capacity;
//    assert s.size == 0;
//   assert s.values[..] == [0,0,0,0,0,0,0,0,0,0];
// }   

// class Stack {
//    const values : array<int>;
//    const capacity : nat;
//    var size : nat;
//       constructor(capacity_ : nat) 
// /*omitted*/
//    method push(i : int) 
//  /*omitted*/

//    function method top() : (r : int) 
//       reads values
//    requires values.Length > 0 {
//    values[0]
//    }
// }


// method VerifyStack(s : Stack, i : int, j : int)
//  modifies s, s.values
//  requires 0 <= s.size < (s.values.Length - 2)
//  requires s.values.Length == s.capacity
//  requires s.size == 0
//   {
//   s.push(i);
//   assert s.size == 1 + old(s.size);
//   var v := s.top();
//   assert s.size == 1 + old(s.size);
//   assert v == i;
//   }

class Stack {
   const values : array<int>;
   const capacity : nat;
   var size : nat;
      constructor(capacity_ : nat) 
/*omitted*/

//you need to define
   method push(i : int) 
   modifies this, values
   requires size < values.Length
   requires size < capacity
   ensures size <= capacity
   ensures values[old(size)] == i
   ensures size == old(size) +1
   {
      values[size] := i;
      size := size + 1;
   }


   method pop() returns (r : int)
   modifies this, values
   requires 0 < size < values.Length
   requires size < capacity
   ensures size == old(size) -1
   ensures r == values[old(size)]{
      r := values[size];
      size := size -1;
   }    

}

method VerifyStack(s : Stack, i : int, j : int)
 modifies s, s.values
 requires 0 <= s.size < (s.values.Length - 2)
 requires s.values.Length == s.capacity
 requires s.size == 0
  {
  s.push(i);
  s.push(j);
  var v := s.pop();
  assert v == j;
  v := s.pop();
  assert v == i;
}

