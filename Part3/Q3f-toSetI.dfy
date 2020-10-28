include "Tweesupport.dfy"
include "Q3a-tweeSize.dfy"
include "Q3d-contains.dfy"

method toSetI(t:Twee) returns (r:set<int>)
  decreases 0
  ensures r == toSet(t) { 
    r := {};
   var todo := [t];
   ghost var chips := allNodes(todo);

   while todo != [] 
   decreases chips 
   invariant chips == allNodes(todo)
   invariant allSum(todo) + r == toSet(t){
      var t := todo[0];

      if(t.Node?) {
         r := r + {t.value};
         todo:= [t.left,t.right] + todo[1..];
         
      } else {
         todo := todo[1..];
      }
      chips := chips -1;
    
   }
  }

function  allNodes(l : seq<Twee>) : nat
{
  if (l == []) 
    then 0 
    else tweeSize(l[0]) + allNodes(l[1..])
}

//And this one too
function  allSum(l : seq<Twee>) : set<int>
{
  if (l == []) 
    then {} 
    else toSet(l[0]) + allSum(l[1..])
}
        

