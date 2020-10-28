include "OptionSupport.dfy"
class Table<Data> {

  ghost var M: map<int, Data>
  ghost var Repr: set<object>

  const keys : array<int>
  const values : array<Option<Data>>
  var size : nat
  const capacity : nat


  predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr 
    ensures Valid() ==> keys.Length == values.Length
    ensures Valid() ==> size <= keys.Length
    ensures Valid() ==> capacity == keys.Length
    {  
      // this in Repr && values in Repr && keys in Repr && size <= values.Length && values.Length == keys.Length && capacity == values.Length 
      //  && forall i::0<=i<size ==>keys[i] in M.Keys && size == |M.Keys|
      this in Repr && values in Repr && keys in Repr && size <= values.Length && values.Length == keys.Length && capacity == values.Length
    }

  constructor ()
    ensures Valid() && fresh(Repr)
    ensures M == map[] 
    ensures size == 0
    ensures capacity ==5
    ensures values.Length == capacity
    ensures keys.Length == capacity
    ensures keys.Length == values.Length
    //ensures forall i:nat::i<values.Length ==>values[i] ==None
    ensures forall i:nat::i<size ==>keys[i] in M
    ensures |M.Keys| == 0;
    { 

      M := map[];
      size := 0;
      capacity := 5;
      values := new Option<Data>[5];
      keys := new int[5];
      Repr := {this,values,keys};
    }

  method Lookup(key: int) returns (r : Option<Data>)
    requires Valid()
    ensures Valid() 
    ensures key in M ==> r == Some(M[key])
    ensures key !in M ==> r == None
    {

      //ghost var h := key in M;
      
      r := None;
      var i := 0;

      //ghost var h := key in M;
      while (i < size) 
      decreases size -i
      invariant 0 <= i <= size
      {
        
        if (keys[i] == key) {
            r := values[i];
            return r;
        }


        i :=i+1;
      }
      return r;

    }

  method Add(key: int, value: Data)
    requires Valid()
    requires key !in M // remove for part e)
    requires size < capacity // remove for part g)
    modifies Repr 
    ensures Valid()
    ensures fresh(Repr - old(Repr))
    ensures M == old(M)[key := value]
    ensures forall i ::0 <i <size-1 ==> keys[i] == old(keys[i])
    ensures forall i ::0 <i <size-1 ==> values[i] == old(values[i]) { 
      keys[size] := key;
      values[size] := Some(value);
      size := size +1;
      M := M[key:=value];
      //Repr := {this,values,keys};

    }

  method Remove(key: int)
    requires Valid()
    requires key in M
    requires size > 0
    modifies Repr
    ensures size >= 0
    ensures Valid() 
    ensures  fresh(Repr - old(Repr))
    ensures M == old(map k | k in M && k != key :: M[k]) 
    { 

      var i := 0;

      while (i < size) 
      decreases size -i
      invariant 0 <= i <= size
      {
        if (keys[i] == key) {
            var j := i; 
            while( j < size -1) 
            decreases size -1 -j 
            modifies keys, values{
              keys[j] := keys[j+1];
              values[j] := values[j+1];
              j := j +1;
            }
            size := size - 1;
            break;
        }


        i :=i+1;
      }
      
      
      //M := M[key:=value];
      M := map x : int | x in M.Keys && x != key :: M[x];
    }
}


