abstract sig User{}

abstract sig Notify{
	resID: Reservation,
	notifyID: String,
	message: String,
	waitingTime: String,
	cabID: TaxiCab
}

abstract sig Reservation{
	reservationID: String,
	reservationTime: Int,
	startTime: Int,
	endTime: String,
	startPoint: String,
	destinationPoint: String,
}

abstract sig DriverStatus{
	status: one String
}

sig Guest extends User{}

sig Passenger extends User{
	name: one String,
	surname: one String,
	telephoneNumber: one String,
	emailAddress: one String,
	userID: one String,
	password: one String
}

sig TaxiDriver extends User{
	name: one String,
	surname: one String,
	emailAddress: one String,
	telephoneNumber: one String,
	username: one String,
	password: one String,
	licenseID: one String,
	driverStatus: one DriverStatus
}

sig TaxiCab{
	cabID: String,
	maxPassenger: Int
}

sig City{
	name: String,
	cap: String,
	state: String
}

sig Zone{
	address: String,
	queueNumber: Int
}

sig Queue{
	queueID: Int
}

sig Notification{
	notifyID: Notify,
	passenger: Passenger
}

fact StartEndDiffrent{
	all r:Reservation| not ( r.startPoint=r.destinationPoint)
}

fact OnePassengerMaxTakeUp{
	no disj p1,p2:Passenger, t:TaxiCab | t.cabID=p1.userID and t.cabID=p2.userID and p1.userID=p2.userID
}


fact noEmptyLocation{
	all r : Reservation | (#r.destinationPoint=1) 
}

fact noDoubleIDNotify{
	no disj n1,n2:Notify | n1.notifyID = n2.notifyID
}

fact noDoublePassenger{
	no disj p1,p2:Passenger | (p1.userID=p2.userID)
}

fact noEmptyNotification{
	all n:Notify | (#n.message=1)
}

fact noEmptyTime{
	all r:Reservation | (#r.startTime=1) and (#r.endTime=1)
}

assert noDoublePassenger{
	no disj p1,p2:Passenger | p1.userID=p2.userID
}

check noDoublePassenger for 5

assert addNewPassenger{
	all p,p1,p2: Passenger | (p not in p1) and addNewPassenger[p, p1,p2] implies (p in p2) 
}
check addNewPassenger for 5

assert NoLessTwoHours{
	no  r:Reservation|(r.startTime-r.reservationTime>2)
}
check  NoLessTwoHours

assert OnlyRegisteredUser{
	no r : Reservation, p:Passenger | (p.userID=r.reservationID)
}
check OnlyRegisteredUser

pred show(){}
run show for 30

pred addNewPassenger(p,p1,p2:Passenger){
	p.userID not in p1.userID implies p.userID=p2.userID
}
run addNewPassenger for 5

pred noLessTwoHours(r:Reservation){
	r.startTime-r.reservationTime>2
}
run noLessTwoHours for 5
