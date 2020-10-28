datatype List<T> = Nil | Cons(car : T, cdr : List<T>)

datatype Option<T> = None | Some(value: T)

datatype MinMax<T> = MinMax(min : T, max : T)




function method foot<T>(l : List<T>) : T 
requires l.Cons?
decreases l
{
   match l {
      case Cons(car, cdr) => if cdr.Cons? then foot(cdr) else car
   }

}


 function method footOpt<T>(l : List<T>) : Option<T> 
 decreases l{
    match l {
      case Nil => None
      case Cons(car, cdr) => if cdr.Cons? then footOpt(cdr) else Some(car)
   }
 }

 function method minMaxOpt(l : List<int>) : Option<MinMax<int>> 
 decreases l{
    match l {
      case Nil => None
      case Cons(car, cdr) => 
         var r:Option<MinMax<int>> := minMaxOpt(cdr);
         match r {
            case None => Some(MinMax(car,car))
            case Some(value) => 
               var m:MinMax<int> := value;
               if car < m.min then Some(MinMax(car,m.max)) else
               if car > m.max then Some(MinMax(m.min,car)) else Some(m)
         }
         
   }
 }

 predicate sorted(l : List<int>) 
 decreases l{
    match l {
       case Nil => true
       case Cons(car, cdr) => 
         var r:List<int> := cdr;
         if r.Cons? then car <= r.car && sorted(cdr) else true
    }
 }

 function method merge(a : List<int>, b : List<int>) : List<int> 
 requires sorted(a)
 requires sorted(b)
 decreases a 
 decreases b
 {
    match a {
       case Nil => b
       case Cons(car, cdr) => 
         match b {
            case Nil => a
            case Cons(car2, cdr2) => 
               if car <= car2 then Cons(car, merge(cdr,b)) else 
               if car2 < car then Cons(car2,merge(a,cdr2)) else Nil
         }
    }
 }




lemma mergeIsMerge()
   ensures merge(Cons(2,Nil),Cons(1,Cons(3,Nil))) == 
                   Cons(1,Cons(2,Cons(3,Nil)))
{}

lemma mergeIsSorted(a : List<int>, b : List<int> )
   requires sorted(a)
   requires sorted(b)
   ensures sorted(merge(a,b)) 
{}

method Main () {
   //var t := sorted(Cons(77,Cons(5, Cons(51, Nil))));
   //var p := sorted(Cons(1, Cons(1, Nil)));
   var m := merge(Cons(1, Nil), Cons(1, Nil));
   print m;
}



