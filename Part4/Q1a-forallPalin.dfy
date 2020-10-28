predicate method forallPalin (a : string) {
  forall x :: 0 <= x < (|a|/2) ==> a[x] == a[|a|-1-x] }