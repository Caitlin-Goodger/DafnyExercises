datatype Dictionary<K(==),V> = 
    Nil |
    Bucket(key : K, value : V, next : Dictionary<K,V> )


function method toMap<K(==),V>(dict : Dictionary<K,V>) : map<K,V>  {

   match dict {
    case Nil => map[]
    case Bucket(key,value,next) =>
      toMap(next)[key := value]
  }
}


 function method insert<K(==),V>(k : K, v : V, dict : Dictionary<K,V>) :  Dictionary<K,V> {
  Bucket(k,v,dict)
 }


 function method lookup<K(==),V>(k : K, dict : Dictionary<K,V>) :  V 
  requires dict.Bucket? 
  decreases dict {
   match dict {
     case Bucket(key,value,next) => 
     if key == k then value else 
     if next.Bucket? then lookup(k,next) else value
   }
 }

 predicate method contains<K(==),V>(k : K, dict : Dictionary<K,V>) 
 decreases dict {
   match dict {
     case Nil => false
     case Bucket(key,value,next) => 
     if key == k then true else contains(k,next)
   }
 }


lemma lookupInsert(k : string, j : string,
                   v :int,  w: int,  d : Dictionary<string,int>)
  requires j != k
  ensures lookup(k,insert(k,v,d)) == v
  ensures contains(k,insert(k,v,d))
  ensures lookup(k,insert(k,v,insert(k,w,d))) == v
  ensures lookup(k,insert(j,w,insert(k,v,d))) == v
{}



 predicate noDupKeys<K(==),V>(dict : Dictionary<K,V>) {
   noDupKey(dict)
 }

 predicate method noDupKey<K(==),V>(dict : Dictionary<K,V>) 
 decreases dict{
   match dict {
     case Nil => true
     case Bucket(key,value,next) =>
      if contains(key,next) then false else noDupKey(next)
   }
 }


 function method cull<K(==),V>(dict : Dictionary<K,V>) : Dictionary<K,V>  
 ensures culling(dict) {
   var r:= rD({},dict);
   if noDupKey(r) then r else Nil
 }

predicate method culling<K(==),V>(dict : Dictionary<K,V>)  {
   var r:= rD({},dict);
   true
 }


function method rD<K(==),V>(k : set<K>, dict : Dictionary<K,V>) :  Dictionary<K,V>
decreases dict {
  match dict {
    case Nil => dict
    case Bucket(key,value,next) =>
      var r:= key in k;
      var kS:set<K> := k + {key};
      if r then rD(k,next) else Bucket(key,value,rD(kS,next))
  }
 }
 lemma cullPreservesMappings<K(==),V>(dict: Dictionary<K, V>)
    ensures toMap(cull(dict)) == toMap(dict) { }

lemma cullRemovesDuplicates<K,V>(d : Dictionary<K,V>) 
  ensures noDupKeys<K,V>( cull(d) )
{}


  
  method Main () {
  var dict := Bucket("key1", 1, Bucket("key2", 2, Bucket("key3", 0, Bucket("key2", 9, Nil))));
  var t:= toMap(cull(dict)) == toMap(dict) ;
  var g := toMap(cull(dict));
   var d := toMap(dict); 
  // var m := contains("key154", g);
   //var h := noDupKeys(dict);
   print g;
   print "\n";
   print d;
   print "\n";
  print t;
  print "\n";
}