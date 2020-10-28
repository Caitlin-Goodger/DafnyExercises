predicate method recPalin(a : string) {
  if |a| <2 then true else if a[0] == a[|a|-1] then recPalin(a[1..|a|-1]) else false }