datatype Timer = Timer( hh : nat, mm : nat, sec : nat)

function method tick ( t: Timer) : Timer 
 {
  if t.sec == 0 then if t.mm == 0 then if t.hh ==0 then Timer(t.hh,59,59) else Timer(t.hh-1,59,59) else Timer(t.hh,t.mm-1,59) else Timer(t.hh,t.mm,t.sec-1)
  
} 

method countdown(start : Timer)
decreases sum(start) {
  
  print start;
  print "\n";
  if(sum(start) == 0) {
    return;
  }
  countdown(tick(start));
}

function method sum(t : Timer) : nat {
  (t.hh*60*60) + (t.mm*60) + t.sec
}

method Main() {
  //printCalendar(100, Date(Wednesday, 1, Jan));
  countdown(Timer(0,1,12));
}
