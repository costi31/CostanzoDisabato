module meteoCal

/*** Class declaration ***/

sig GenericText{}

sig User {
	email: one GenericText,
	favourites: set User
x

sig Event {
	creator: one User,
	partecipants: set User,
	--where: one GenericText,
	--when: one GenericData,
	--wfi: one WeatherForecast
}

sig Invitation {
	recipient: one User,
	object: one Event
	--- the sender can be recovered from the event
}

sig Calendar{
	owner: one User,
	events: set Event,
    alerts: set Alert
}  

sig Alert{
	reference: one Event,
}

-- there are also other attributes but are not relevants for this representation

/*** DEFINITION OF THE CONSTRAINTS ***/

--each email has to be unique
fact emailUnicity{
	no disj u1, u2: User | u1.email = u2.email
}
--each  user has only one calendar
fact calendarUnicity{ 
	no disj c1, c2: Calendar | c1.owner = c2.owner
}
--each user must have a calendar
fact oneUserOneCalendar { 
	no u: User | all c: Calendar| u != c.owner
}
--an user cannot have himself as favourite
fact noSelfFavorite{
	no u: User | u in u.favourites 
}
--an event is in the calendar  only if the owner is the organizer or a  partecipant
fact noFloatingEvent{
	all e: Event | all c: Calendar | e in c.events iff c.owner in e.partecipants or c.owner = e.creator--u in e.partecipants implies e in c.events and c.owner = u
}
--all the events are contaned in calendars
fact noEventOutOfCalendar	{
	all e: Event | some c: Calendar | e in c.events
}
--an user cannot have two favourites who are the same user
fact noDoubleFavouries{
	all u1, u2, u3: User | u2 in u1.favourites and u3 in u1.favourites implies u2 != u3
}
--a person cannot be invited twice
fact noDoubleInvitation { 
	all u: User | no disj i1, i2: Invitation | i1.recipient = u and i2.recipient = u and i1.object = i2.object
}
-- only the organizer of an event can invite to that event
fact onlyOrganizerCanInvite {
	all e: Event | no i: Invitation | e.creator = i.recipient and i.object = e
}
 --each partecipanr had to be invited previously
fact aPartecipantHadAnInvite {
	all e: Event | all p: e.partecipants | one i: Invitation | p = i.recipient and i.object = e 
}
--all the alerts are contaned in calendars
fact noAlertOutOfCalendar	{
	all a:Alert | some c: Calendar | a in c.alerts
}
--all the alerts in a calendar are only on the events in the calendar
fact alertsOnlyOnMyEvents{
	all c:Calendar | all a:c.alerts | a.reference in c.events 
}
-- each organizer has in his calednar the events that he creates
fact organizerEvent {
	all e: Event | one c: Calendar | c.owner = e.creator and e in c.events
}




/*** FUNCTION ***/

-- invitations returns the set of invitations of which the event passed as param is the object
fun invitation [e: Event]: set Invitation {
	{i:Invitation | e = i.object}
}
-- organizedEvents returns the set of events whose creator is the same as the param
fun organizedEvents[u: User] : set Event {
	{e: Event | e.creator = u}
}
--partecipantEvents returns the set of events in which the user passed as param is partecipant
fun partecipantEvents[u: User] : set Event {
	{e: Event | u in e.partecipants}
}


/*** ASSERTION ***/
--nobody can invite himself
assert noSelfInvitation{ 
	no i: Invitation | i.recipient = i.object.creator
}
check noSelfInvitation for 3 
--nobody can partecpiate an event without a previous invitation
assert noSneakInEvent {
	all e: Event | #e.partecipants <= #invitation[e]  
}
check noSneakInEvent for 3 
--all the events in the calendare are there because the owner of the calendar is either
-- the organizer or a partecipant
assert noGhostEvent {
	all c: Calendar | #c.events = #organizedEvents[c.owner] + #partecipantEvents[c.owner]
}
check noGhostEvent for 3 

/*** PREDICATES ***/
--is a way to ensure a number of significant entities
pred showEvent {
	#User > 1 and #Event > 2
}
run showEvent for 4

pred show {

}
run show {} for 3 
