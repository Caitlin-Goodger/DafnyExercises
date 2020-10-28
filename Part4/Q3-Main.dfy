include "OptionSupport.dfy"
include "Q3.dfy"

method Main() {
  var t := new Table<string>();
  assert t.size == 0;
  t.Add(1,"Foo");
  var foo := t.Lookup(1);
  assert foo == Some("Foo");
  t.Add(2, "Bar");
  foo := t.Lookup(1);
  assert foo == Some("Foo");
  t.Add(1,"Hemi");
  t.Add(3,"Moana");
  foo := t.Lookup(1);
  assert foo == Some("Hemi");
  assert t.size == 3;
}