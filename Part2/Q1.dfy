datatype Day = Monday | Tuesday | Wednesday | 
               Thursday | Friday | Saturday | Sunday

datatype Month = Jan | Feb | Mar | Apr | May | Jun  | Jul | Aug | Sep | Oct | Nov | Dec

datatype Date = Date(day : Day, date : nat, month : Month)

 function method nextDay(d : Day) : Day {
  match d {
    case Monday => Tuesday
    case Tuesday => Wednesday
    case Wednesday => Thursday
    case Thursday => Friday
    case Friday => Saturday
    case Saturday => Sunday
    case Sunday => Monday
    }

 }

  function method nextMonth(m : Month) : Month {
    match m {
    case Jan => Feb
    case Feb => Mar
    case Mar => Apr
    case Apr => May
    case May => Jun
    case Jun => Jul
    case Jul => Aug
    case Aug => Sep
    case Sep => Oct
    case Oct => Nov
    case Nov => Dec
    case Dec => Jan

    }
  }

  function method nextDate(d : Date) : Date {
    var da := d.day;
    var dt := d.date;
    var mon := d.month;
    var newmon := Jan;
    if mon == Jan && dt == 31 then Date(nextDay(da), 1, nextMonth(mon)) else 
    if mon == Feb && dt == 29 then Date(nextDay(da), 1, nextMonth(mon)) else
    if mon == Mar && dt == 31 then Date(nextDay(da), 1, nextMonth(mon)) else 
    if mon == Apr && dt == 30 then Date(nextDay(da), 1, nextMonth(mon)) else 
    if mon == May && dt == 31 then Date(nextDay(da), 1, nextMonth(mon)) else 
    if mon == Jun && dt == 30 then Date(nextDay(da), 1, nextMonth(mon)) else 
    if mon == Jul && dt == 31 then Date(nextDay(da), 1, nextMonth(mon)) else 
    if mon == Aug && dt == 31 then Date(nextDay(da), 1, nextMonth(mon)) else
    if mon == Sep && dt == 30 then Date(nextDay(da), 1, nextMonth(mon)) else 
    if mon == Oct && dt == 31 then Date(nextDay(da), 1, nextMonth(mon)) else 
    if mon == Nov && dt == 30 then Date(nextDay(da), 1, nextMonth(mon)) else 
    if mon == Dec && dt == 31 then Date(nextDay(da), 1, nextMonth(mon)) else 
    Date(nextDay(da), dt+1, mon) 
  }

  method printCalendar(len : nat, d : Date) {
    if (len <= 0) {
      return;
    }
    print d;
    print "\n";
    printCalendar(len-1,nextDate(d));
  }



method Main() {
  printCalendar(100, Date(Wednesday, 1, Jan));
  //var dt:Day := Saturday;
  //var d := nextDay(dt);
  //var test := nextDate(Date(Monday,29,Feb));

  //print d;
  //print test;
}



