abstract sig User{}
sig TaxiDriver extends User{}
sig Passenger extends User{}

sig TaxiCab{
	pass: some Passenger,
	driver: one TaxiDriver
}

abstract sig TaxiStatus{}
sig Available extends TaxiStatus{}
sig NotAvailable extends TaxiStatus{}

sig Queue{}

sig Zone{
	queues: one Queue
}

sig City{
	zones: set Zone
}{#zones >=1}

sig Request{
	pass: some Passenger,
	driver: one TaxiDriver,
 	taxi: one TaxiCab
}

sig Reservation{
	pass: some Passenger,
	driver: one TaxiDriver,
 	taxi: one TaxiCab,
	resTime: Int,
	appointmentTime: Int
} 

fact noSameQueueInTwoZones {
	no q:Queue | some disj z1,z2: Zone | q in z1.queues and q in z2.queues
}

fact noSamePassangerInTwoTaxis{
	no p: Passenger | some disj tc1,tc2: TaxiCab | p in tc1.pass and p in tc2.pass
} 

fact noReservationAfter2Hours{
	no r:Reservation | r.appointmentTime >=2+r.resTime
}

pred RequestATaxi[r:Request, p:Passenger,d:TaxiDriver, t:TaxiCab]{
	r.pass=p and
	r.driver = d and
	r.taxi= t
}

pred show(){#Zone>1 and #Queue>1}
run show

run RequestATaxi for 5 

