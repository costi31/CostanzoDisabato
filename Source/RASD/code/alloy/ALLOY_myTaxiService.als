module myTaxiService

/**** Initial Comment at this model ****/
/*** The model is based on the UML class diagram shown in previous chapter and it tries to validate it. There is a little difference. The data and the time are modelled as integer numbers representing a timestamp from a certain initial date that are not relevant in this model. The reason for this choice is to use the available functionalities of Alloy. A second note on the model is the following: a driver can only wait for a ride or drive. Hence, the workshifts are not modelled   ***/
/*** Important Observation: the Integer defined by Alloy has the maximum value equal to 7, so this is a limit to our model ***/


/*** CLASS DECLARATION ***/

abstract sig Ride {
	/** Timestamp for departure and arrival time **/
	departure : one Int,
	arrival : lone Int,	
	/** Relations**/
	startingPosition : one Position,
	destination : one Position, 
	customer : one User,
	driver : lone Driver
} { departure > 0 && arrival > 0}

sig ZerotimeRide extends Ride {
}

sig FutureRide extends Ride {
}

/** By definition Zerotime and Future are a partition of abstract class Ride **/

sig CabCompany {}

sig User {
	email : one GenericEmail,
	-- password : one GenericText,
	-- name : one GenericText,
	-- surname : one GenericText,
	-- birthday : one Date,
	-- cityOfResidence : lone GenericText,
	taxCode : one GenericText,
	/** Relations**/
	currentPosition : lone Position,
	alert : set Alert	
}

sig Driver extends User {
	cabCarCode: one GenericText,
	-- cabCompany : one cabCompany,
	/** Relations**/
	currentArea : lone Area
}

sig Position {
	-- GPSCoordinates : one Float
	-- city : lone GenericText,
	-- street : lone GenericText,
	-- civicNumber : lone Integer
	area : one Area
}

sig Area {
	-- name : one GenericText
	/** Relations**/
	availableDrivers: set Driver	
}

sig Alert {
	-- receiver : one User,
	-- message : one GenericText,
	-- date : lone Date,
	-- time : lone Time
}

/** The current time **/
one sig CurrentTime {
	current : one Int
} { current > 0}

sig GenericText {}

sig GenericEmail {}

/** Definition of Boolean type **/
abstract sig Boolean {}

one sig True extends Boolean {}

one sig False extends Boolean {}

/** Note: The commented attributes are not relevant in this model **/

/*** DEFINITION OF THE CONSTRAINTS ***/

-- the tax code is unique
fact taxCodeUnicity {
	no disj u1 , u2 : User | u1.taxCode = u2.taxCode
}

-- the email is unique
fact emailUnicity {
	no disj u1 , u2 : User | u1.email = u2.email
}

-- the cabCarCode is unique
fact cabCarCodeUnique {
	no disj d1 , d2 : Driver | d1.cabCarCode = d2.cabCarCode
}

-- the driver exists for a zerotime ride
fact driverExistence {
	all ztr : ZerotimeRide | #ztr.driver = 1
}

-- the driver and the customer are two different people
fact differentDriverAndCustomer {
	no r : Ride | r.customer = r.driver
}

-- the cabman can drive at most one rides at the same time
fact taxiDriverUbiquity {
	no disj r1 , r2 : Ride | r1.departure >= r2.departure && r1.departure =< r2.arrival && r1.driver = r2.driver
}

-- an user cannot be on two rides at the same time
fact userUbiquity {
	no disj r1 , r2 : Ride | r1.departure >= r2.departure && r1.departure =< r2.arrival && (r1.customer = r2.customer || r1.customer = r2.driver || r1.driver = r2.customer)
}

-- correctness of time : the departure is before the arrival (at least one unit of time)
fact noBackTime {
	no r : Ride | r.departure >= r.arrival
}

-- a zerotime ride is already departed
fact correctnessOfZeroTime {
	all ztr : ZerotimeRide | ztr.departure =< CurrentTime.current
}

-- a zerotime ride has always an arrival time
fact zerotimeRideAlwaysArrive {
	all ztr : ZerotimeRide | #ztr.arrival = 1
}

-- a future ride is after now
/** Note that in the statechart diagram, 10 minutes before the departure, a future ride becomes zerotime and it is managed **/
fact correctnessOfFuture {
	all fr : FutureRide | fr.departure > CurrentTime.current
}

-- no ride is cyclic (or null): the starting position is different from the destination
fact noSelfRide {
	no r : Ride | r.startingPosition = r.destination
}

-- if the cabman is driving or traveling he isn't in any queue
fact waitOrWork {
	all d : Driver | ( driverBusy [d] = True || driverTraveling[d] = True ) implies no a : Area | d.currentArea = a
}

-- if the cabman is not driving or traveling he is in a queue
fact waitOrWork2 {
	all d : Driver | driverBusy[d] = False && driverTraveling[d] = False implies one a : Area | d.currentArea = a
}

-- The driver is into the correct queue
fact driverInCorrectArea {
	all d : Driver , a : Area | d in a.availableDrivers <=> d.currentArea = a
}

/*** FUNCTIONS ***/

-- Return true if a ride is in progress
fun nowRide [r : Ride] : one Boolean {
	( CurrentTime.current >= r.departure && CurrentTime.current =< r.arrival ) implies {True} else {False}
}

-- Return true if a driver is working
fun driverBusy [d : Driver] : one Boolean {
	( some r : Ride | nowRide [r] = True && r.driver = d ) implies {True} else {False}
}

-- Return true if a driver is traveling as customer
fun driverTraveling [d : Driver] : one Boolean {
	( some r : Ride | nowRide [r] = True && r.customer = d ) implies {True} else {False}
}

/*** ASSERTIONS AND PREDICATES ***/

-- A driver is always into a queue. It is a false assertion and we want to proof it.
assert driversInTheQueue {
	all d : Driver | one a : Area | d in a.availableDrivers
}

check driversInTheQueue for 5 but exactly 3 Area , 2 FutureRide, exactly 3 Driver

-- A person that is on a zerotime ride can have booked a future ride (defined as the opposite assertion to find a counterexample)
assert multipleReservation {
	no u : User | some ztr : ZerotimeRide , fr : FutureRide | ztr.customer = u && fr.customer = u
}

check multipleReservation for 5

-- A driver who is now working (driving) is not customer of any other ride
assert noUbiquity {
	all d : Driver | ( driverBusy [d] = True ) implies no r : Ride | 
	( nowRide[r] = True && r.customer = d )
}

check noUbiquity for 5

pred noDriverAsCustomer () {
	no d : Driver | some r : Ride | r.customer = d
	#ZerotimeRide = 2
	#FutureRide = 1
	#Driver = 2
	#User = 5
	#Area = 3
	one a : Area | a.availableDrivers != none
}

run noDriverAsCustomer for 5

pred show () {
	#ZerotimeRide = 2
	#FutureRide > 1
	#Driver = 2
	#User > 3
}

run show for 4
