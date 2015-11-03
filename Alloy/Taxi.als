sig Customer{
userID: Int,
userName: String,
userPhoneNumber: Int,
userEmail: String,
request: one Request,
orderStatus: one OrderStatus
}

sig RegisteredUser{
name: one String,
surname: one String,
mail: one String,
dateOfBirth: one String,
username: one String,
password: one String
}

sig Driver{
driverID: Int,
driverPhoneNumber: Int,
driverEmail: String,
driverLicenseNumber: Int,
moving: one Moving,
request: one Request
}

sig Request{
requestID:String,
requestTime:String,
requestStatus:String,
requestEstimateTimeOfArrival:String,
moving: one Moving,
orderStatus: one OrderStatus
}

sig OrderStatus{
offered:String,
received: String,
accepted: String,
pickUp: String,
cancelled: String,
failed: String
}


sig Moving{
startLocation: String,
endLocation: String,
endNumber: String,
estimateTimeOfDriving: String,
startTime: Int,
endTime: Int
}

sig Zone{
zoneID:Int,
nameOfDistrict:String,
request: one Request
}

sig DriverStatus{
Free: String,
Busy: String,
OffDuty: String,
driver: one Driver
}

sig TaxiCab{
licenseNumber:Int,
maxPassengers:Int,
driverID:Int,
driver: one Driver,
customer: one Customer
}

sig TimeDate{
day: one Int,
month: one Int,
year: one Int,
hours: one Int,
minutes: one Int, 
}

sig Reservation{
Location: one String,
day: one Int,
month: one Int,
hours: one Int,
minutes: one Int,
}

sig Cancelbooking extends Driver{}

sig Requests extends Driver{}

sig RequestID extends Request{} 

fact OneUserMaxTakeUps{
	all u : Customer | (some t : TaxiCab | t.customer=u)
}

fact NoEmptyLocation{
	all m : Moving | (#m.endLocation=1) and (#m.endNumber=1)
}

fact noDoubleUser{
	no disj u1,u2:RegisteredUser | (u1.mail=u2.mail) and (u1.username=u2.username)
}

fact TaxiDriverCancel{
	all r : Request | (some c: Cancelbooking | c.request=r)
}

fact NotifyTaxiDriver{
	all r : Request | (some c: Cancelbooking | c.request=r)
}

fact OneCodeUser{
	all r : RequestID | (one c : Customer | c.request = r) 
}


fact StartEndDiffrent{
	all m:Moving | not ( m.startLocation=m.endLocation )
}

fact noEmptyTime{
	all t:TimeDate | (t.hours=1) and (t.minutes=1)
}


fact noEmptyDate{
	all d: TimeDate | (d.day=1) and (d.month=1) and (d.year=1)
}

fact MinTwoHours{
all r:Reservation| (r.hours>=2) and(r.minutes>=2)

}

assert OnlyRegisteredUser{
	no r : Request | (no c : Customer | c.request=r)
}
check OnlyRegisteredUser



assert CancelBookingDriver{
	all o : OrderStatus, r1, r2: Request | (o in r1.requestID) and DeleteOrder[o,r1,r2] implies (o not in r2.requestID)
	//all o1 : OrderStatus, o2 : OrderStatus| (o1=o2.cancelled)

}
check CancelBookingDriver


assert NoLessTwoHours{
	no  r:Reservation|(r.hours>2)
}
check  NoLessTwoHours

assert AddBookingDriver{
	all o : OrderStatus, r1, r2: Request | (o in r1.requestID) and AddBooking[o,r1,r2] implies (o not in r2.requestID)
	//all o1 : OrderStatus, o2 : OrderStatus| (o1=o2.cancelled)
}
check CancelBookingDriver


pred show(){
#RegisteredUser=1
#Customer=1
#Request=1
#Driver=1
}
run show for 10


pred DeleteOrder(o:OrderStatus, r1,r2:Request){
	r2.requestID=r1.requestID-o
}
run DeleteOrder for 5

pred AddBooking(o:OrderStatus, r1,r2:Request){
	o not in r1.requestID implies r2.requestID=r1.requestID+o
}
run AddBooking for 5
