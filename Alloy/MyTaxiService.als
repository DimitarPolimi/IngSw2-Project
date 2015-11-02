sig Customer{
userID: Int,
userName: String,
userPhoneNumber: Int,
userEmail: String,
request: one Request
}

sig RegisteredUser{
name: one String,
surname: one String,
mail: one String,
dateOfBirth: one String,
username: one String,
password: one String
}

//sig Visitor extends User{} 

sig Driver{
driverID: Int,
driverPhoneNumber: Int,
driverEmail: String,
driverLicenseNumber: Int
}

sig Request{
requestID:Int,
requestTime:Int,
requestStatus:Int,
requestEstimateTimeOfArrival:String
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
estimateTimeOfDriving: String,
startTime: Int,
endTime: Int
}

sig Zone{
zoneID:Int,
nameOfDistrict:String
}

sig DriverStatus{
Free: String,
Busy: String,
OffDuty: String
}

sig TaxiCab{
licenseNumber:Int,
maxPassengers:Int,
driverID:Int,
customer: some Customer
}

sig Cancelbooking extends Driver{}

sig Requests extends Driver{}

sig RequestID extends Request{} 

fact OneUserMaxTakeUps{
	all u : Customer | (some t : TaxiCab | t.customer=u)
}

fact NoEmptyLocation{
	all m : Moving | (#m.endLocation=1) //and (#m.endNumber=1)
}

fact noDoubleUser{
	no disj u1,u2:RegisteredUser | (u1.mail=u2.mail) and (u1.username=u2.username)
}

fact TaxiDriverCancel{
	all r : Request | (some c: Cancelbooking | c.requestID=r)
}

fact NotifyTaxiDriver{
	all r : Request | (some c: Cancelbooking | c.requestID=r)
}

fact OneCodeUser{
	all r : RequestID | (one c : Customer | c.requestID = r) 
}

assert OnlyRegisteredUser{
	no r : Request | (no c : Customer | c.request=r)
}

check OnlyRegisteredUser


pred show{
#RegisteredUser=1
#Customer=1
#Request=1
#Driver=1
}
run show for 10

