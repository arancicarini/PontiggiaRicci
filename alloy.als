open util/integer
open util/boolean

//signatures
abstract sig Client{
automatedSos: one Bool
}
sig User extends Client{
fiscalCode: one String,
status: one UserStatus,
thirdpartiesallowed: String -> Data,
inDangerOfLife : Time -> one Bool,
IsUnderAssistance: Time -> one Bool,
Thresholds: one Int
}

sig UserStatus{
active: Bool
}
sig ThirdParty extends Client{
email: one String,
alerts: set Int,
datareceived: set Data,
groupeddatareceived: set Data,
timeofLife: one Int
}{
#alerts > -1
#datareceived > -1
timeofLife > -1
}

sig Alert{
 data: one Data,
status: one EmergencyStatus,
alertID: one Int
}{
alertID > 0
}

sig EmergencyStatus{
handling: Bool
}

abstract sig Request{
requestID: Int,
requester:String,
time: Time,
parameters: Parameters
}
{
requestID > 0
}
sig IndividualRequest extends Request{
identifier: one String
}
sig GroupRequest extends Request{
//qua bisognerà per forza aggiungere qualcosa
}

sig Data{
identifier: lone String,
parameters: one Parameters,
healthValues: one Int,
location: one Location,
time: one Time

}

//this is completely useless for the alloy analysis
sig HealthValue{
heartRate: one Int,
pression: one Int,
bloodSaturation: one Int,
bodyTemperature: one Int,
}

sig Location{
latitude: one Int,
longitude: one Int
}


sig Parameters{
}


sig Time{
day: one Int,
month: one String,
year: one Int,
hour: one Int,
minute: one Int,
second: one Int
}{
 day > 0 and day < 32
 hour > -1 and hour < 25
minute > -1 and minute < 61
second > -1 and second < 61
}

sig Datapool{
data: set Data
}


//facts

//requests must regard subscribed users
fact IndivdualRequestmustRegardAsubscribedUser{
  all r1: IndividualRequest |  IsSubscribedtoData4Help[r1.identifier]
}

//data must regard subscribed users
fact DataMustRegardSubscribedUser{
all d1: Data |  IsSubscribedtoData4Help[d1.identifier]
}

//there can't be requests with the same id
fact RequestsAreUnique{
no disjoint req1, req2 : Request | req1.requestID = req2.requestID
}

//requests must have requesterString corresponding to existing Third parties
fact CorrectRequestsID{
all r1: Request | one t1: ThirdParty | r1.requester = t1.email
}

//third parties must have ids corresponding to unique alerts
fact CorrectAlertsID{
all t1: ThirdParty | all number: t1.alerts | one al: Alert | number = al.alertID
}



//there are no users with the same fiscal code
fact FiscalCodeeIsUnique{
no disjoint u1,u2: User | u1.fiscalCode = u2.fiscalCode
}

//there are no third parties with the same email (at the same time )
fact EmailsAreUnique{
no disjoint t1,t2: ThirdParty | t1.email = t2.email && t1.timeofLife = t2.timeofLife
}

//there are no two health values regarding the same user of the same dateTime
fact NoSameTimeSameUserData{
all disj d1,d2: Data | d1.identifier = d2.identifier implies d1.time != d2.time
}

//ottengo solo i dati richiesti
pred existsassociatedRequest[t1:ThirdParty, d:Data ]{
some req:IndividualRequest | (req.parameters = d.parameters and req.requester = t1.email)
}
fact Onlyrequested{
all t1:ThirdParty | all d1:t1.datareceived | existsassociatedRequest[t1,d1]
}

pred existsgroupedsassociatedRequest[t1:ThirdParty, d:Data ]{
some req:GroupRequest | (req.parameters = d.parameters and req.requester = t1.email)
}

fact Onlygroupedrequested{
all t1:ThirdParty | all d1:t1.groupeddatareceived | existsgroupedsassociatedRequest[t1,d1]
}

//al tempo zero i dati ricevuti sono zero
fact Zeroatthefirst{
all t1:ThirdParty | t1.timeofLife = 0 implies (t1.datareceived = none and t1.groupeddatareceived = none)
}

//in un datapool ci stanno solo dati di un parametro
fact Datapoolwithonlyoneparameter{
all datapool: Datapool | no d1,d2:Data | (d1.parameters != d2.parameters and d1 in datapool.data and d2 in datapool.data)
}

//third parties e utenti non possono avere lo stesso identificato
fact ThirdPartiesandUsersDosjointed{
all t1:ThirdParty, u1:User | t1.email != u1.fiscalCode
}

// useful preds
pred IsSubscribedtoData4Help[u:String]{
one u1:User | u = u1.fiscalCode
}

//this implies the previous
pred IsSubscribedtoAutomatedSos[u:String]{

 one u1:User |  u = u1.fiscalCode and  isTrue[u1.automatedSos]
}


//if a user is active or inactive
pred IsActive[u:String]{
 one u1:User |  u = u1.fiscalCode and  isTrue[u1.status.active]
}


//Data4Help
//accessingtoindividualData
pred accessToIndividualData[u1, u1': User, req: IndividualRequest, t1, t1': ThirdParty, d1: Data]  {
//preconditions
d1 not in t1.datareceived
req.requester = t1.email
req.identifier = u1.fiscalCode
d1.identifier = u1.fiscalCode
t1.email -> d1 not in u1.thirdpartiesallowed
d1.parameters = req.parameters
//postconditions
d1 in t1'.datareceived
t1'.email -> d1 in u1'.thirdpartiesallowed
}


//refusingaccesstoindividualData
pred refuseAccessToindividualData[u1, u1': User, req: IndividualRequest, t1, t1': ThirdParty, d1: Data] {
//preconditions
d1 not in t1.datareceived
req.requester = t1.email
req.identifier = u1.fiscalCode
d1.identifier = u1.fiscalCode
t1.email -> d1 not in u1.thirdpartiesallowed
d1.parameters = req.parameters
//postconditions
d1 not in t1'.datareceived
t1'.email -> d1 not in u1'.thirdpartiesallowed
}

//cananonymizedata
pred accesstoAnonymizedData[t1,t1': ThirdParty, req: GroupRequest, datapool: Datapool]{
# datapool.data.identifier > 3
req.requester = t1.email
//in datapool there are all and only data 
all d1:datapool.data | d1.parameters = req.parameters
no d1:Data | d1.parameters= req.parameters and d1 not in datapool.data
//all data are not known by the third party (assumption for simplicity)
all d1:datapool.data | d1 not in t1.groupeddatareceived
all d1:datapool.data | d1 in t1'.groupeddatareceived 
}

//cannotanonymizeData
pred noaccesstoAnonymizedData[t1,t1': ThirdParty, req: GroupRequest, datapool: Datapool]{
# datapool.data.identifier < 4
req.requester = t1.email
//in datapool there are all and only data 
all d1:datapool.data | d1.parameters = req.parameters
no d1:Data | d1.parameters= req.parameters and d1 not in datapool.data
//all data are not known by the third party (assumption for simplicity)
all d1:datapool.data | d1 not in t1.groupeddatareceived
all d1:datapool.data | d1 not in t1'.groupeddatareceived
}


//requirements
fact AccessToIndividualData {
all u1, u1': User, req: IndividualRequest, t1, t1': ThirdParty, d1: Data |(
(d1 not in t1.datareceived) and
(req.requester = t1.email) and
(req.identifier = u1.fiscalCode) and
(d1.identifier = u1.fiscalCode) and
(t1.email -> d1 not in u1.thirdpartiesallowed) and
(d1.parameters = req.parameters)) implies
(d1 in t1'.datareceived and
(t1'.email -> d1 in u1'.thirdpartiesallowed))
}


//refusingaccesstoindividualData
fact RefuseAccessToindividualData{
all u1, u1': User, req: IndividualRequest, t1, t1': ThirdParty, d1: Data |(
(d1 not in t1.datareceived) and
(req.requester = t1.email) and
(req.identifier = u1.fiscalCode) and
(d1.identifier = u1.fiscalCode) and
(t1.email -> d1 not in u1.thirdpartiesallowed) and
(d1.parameters = req.parameters)) implies
((d1 not in t1'.datareceived) and
(t1'.email -> d1 not in u1'.thirdpartiesallowed))
}


fact AccesstoAnonymizedData{
all t1,t1': ThirdParty, req: GroupRequest, datapool: Datapool |
((# datapool.data.identifier > 3) and
req.requester = t1.email and
//in datapool there are all and only data of the same parameters
(all d1:datapool.data | d1.parameters = req.parameters) and
(no d1:Data | d1.parameters= req.parameters and d1 not in datapool.data) 
and t1.email = t1'.email and t1'.timeofLife > t1.timeofLife) implies
(all d1:datapool.data | (d1 in t1'.groupeddatareceived and d1.identifier = "Nobody"))
}


fact NoaccesstoAnonymizedData{
all t1,t1': ThirdParty, req: GroupRequest, datapool: Datapool | 
(# datapool.data.identifier < 4 and
req.requester = t1.email and
//in datapool there are all and only data of the same parameters
(all d1:datapool.data | d1.parameters = req.parameters) and
(no d1:Data | d1.parameters= req.parameters and d1 not in datapool.data) 
and t1.email = t1'.email and t1'.timeofLife > t1.timeofLife)implies
(all d1:datapool.data | d1 not in t1'.groupeddatareceived)
}


//assertions
assert PrivacyIsProtected{
all t1:ThirdParty | all d1: t1.groupeddatareceived | d1.identifier = "Nobody"
}

assert PrivacyIsProtected2{
all t1:ThirdParty | all d1: t1.datareceived | (d1.identifier  != "Nobody"  <=> ( one u1:User | t1.email -> d1 in u1.thirdpartiesallowed))
}

//an interesting predicate
pred AllowThirdPartiesToGetData{
all t1:ThirdParty | (t1.datareceived != none and t1.groupeddatareceived != none)
}



//AutomatedSos
//facts
//a user with no automatedSos service  is never in danger of life 
fact DangerOfLifeonlyisAutomatedSos{
all u1:User, t1:Time | ( (t1 -> True in  u1.inDangerOfLife) implies isTrue[u1.automatedSos]
)}

//a third party can handle alerts only if he is subscribed to AutomatedSOS
fact HandleOnlyIFSubscribed{
all t1: ThirdParty | ((some number: Int | number in t1.alerts)  implies  isTrue[t1.automatedSos])
}

//There can't be alerts with the same id
fact AlertsIDAreunique{
no disjoint al1, al2 : Alert | al1.alertID = al2.alertID
}

//there are alerts only if the user is active
fact IfNonActiveThereareNoEmergencies{
all al:Alert | IsActive[al.data.identifier]
}


//there can't be contemporary emergencies for the same user
fact NocontemporaryEmergenciesForTheSameUSer{
all disj al1, al2: Alert | al1.data.identifier = al2.data.identifier implies al1.data.time != al2.data.time
}

//whenever a user is in danger of life, health values go below trehsholds (for that time)
fact DangerOfLife{
all t1:Time, u1:User | ( (t1->True in u1.inDangerOfLife)  <=> (one d1:Data | (d1.time = t1 and  d1.identifier = u1.fiscalCode and d1.healthValues < u1.Thresholds)))
}

//an alert is created only if healthvalues are under thresholds
fact AlertCreation{
all al1: Alert |  one u1:User | al1.data.healthValues < u1.Thresholds
}

//an alert is created if healthvalues are under thresholds 
fact AlertCreation2{
all d1:Data | (  (one u1:User | (u1.fiscalCode = d1.identifier and d1.healthValues < u1.Thresholds))  implies  (one al1:Alert | al1.data = d1))
}


// an alert is marked as "handling" if and only if there is exactly one third party which is handling it
fact ExactlyOneHandling{
all al1: Alert | (isTrue[al1.status.handling] <=>  (one t1: ThirdParty |  al1.alertID in t1.alerts))
}


//there are no alerts market as not handling (which means, there is always a third party which handles the request)
fact AllAlertsAreHandled{
all al1:Alert | isTrue[al1.status.handling]
}

//when a third party handles an alert, the user is provided with medical assistance (we don't care how)
fact ProvideMedicalAssistance{
all t1:ThirdParty, al1:Alert | ( (al1.alertID in t1.alerts) implies (all u1:User | ((u1.fiscalCode = al1.data.identifier) implies ( al1.data.time -> True in u1.IsUnderAssistance))))
}

assert HandleEmergency{
all t1:Time, u1:User | ( ( (t1->True) in u1.inDangerOfLife) implies (t1 -> True in u1.IsUnderAssistance))
}


//commands
check HandleEmergency for 5 but  exactly 10 String, 5 Int






