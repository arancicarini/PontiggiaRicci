open util/integer
open util/boolean

//signatures
abstract sig Client{
automatedSos: one Bool
}
//all the cross product where the first element is a Int or a Time are intended to model the time instances ( both in User and ThirdParty)
sig User extends Client{
fiscalCode: one String,
status: one UserStatus,
thirdpartiesallowed: Int -> (String -> Data), 
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
datareceived: Int -> set Data, 
groupeddatareceived: Int -> set Data 
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
time: Int,
parameters: one Parameters
}
{
requestID > 0
time > 0
}

sig IndividualRequest extends Request{
identifier: one String
}
sig GroupRequest extends Request{
}

sig Data{
identifier: lone String,
parameters: one Parameters,
healthValues: one Int,
time: one Time,
anon : one Bool
}

sig Parameters{
}

//this class is not redudant: we use this when we want to state two different  instants of time, while int fields are used when
//we want also to ORDER instants of time
sig Time{
}




//facts
//requests must regard subscribed users
fact IndivdualRequestmustRegardAsubscribedUser{
  all r1: IndividualRequest |  IsSubscribedtoData4Help[r1.identifier]
}
//Notworequestsatthesametime
fact NoContemporary{
no disj req1, req2: Request | req1.requester = req2.requester and req1.time = req2.time
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

//there are no users with the same fiscal code
fact FiscalCodeeIsUnique{
no disjoint u1,u2: User | (u1.fiscalCode = u2.fiscalCode)
}

//there are no third parties with the same email 
fact EmailsAreUnique{
no disjoint t1,t2: ThirdParty | (t1.email = t2.email )
}



//there are no two health values regarding the same user of the same dateTime
fact NoSameTimeSameUserData{
all disj d1,d2: Data | d1.identifier = d2.identifier implies d1.time != d2.time
}

//if the thid party has something, he has asked for the data before [done with a pred]
pred existsassociatedRequest[t1:ThirdParty, d:Data, num:Int ]{
some req:IndividualRequest | (req.identifier = d.identifier and req.requester = t1.email and req.time < num)
}
fact Onlyrequested{
all t1:ThirdParty, num:Int,  d:Data | ( (num -> d in t1.datareceived)  implies existsassociatedRequest[t1,d, num])
}

//if the thid party has something, he has asked for the data before [done with a pred]
pred existsgroupedsassociatedRequest[t1:ThirdParty, d:Data, num:Int]{
some req:GroupRequest | (req.parameters = d.parameters and req.requester = t1.email and req.time < num)
}
fact Onlygroupedrequested{
all t1:ThirdParty,d1:Data,num:Int | (num -> d1 in t1.groupeddatareceived) implies existsgroupedsassociatedRequest[t1,d1, num]
}




//third parties e utenti non possono avere lo stesso identificativo
fact ThirdPartiesandUsersDosjointed{
all t1:ThirdParty, u1:User | t1.email != u1.fiscalCode
}

//TIME MODELLING
// all'istante zero non ci sono tuple
fact ZeroFirstUser{
all u1:User | all number:Int  | all s:String | all d:Data | ( ((number -> (s -> d)) in u1.thirdpartiesallowed) implies (number > 0 ) )
}

//se in un istante si inserisce una tupla, questa resterà inserita anche in tutti gli istanti successivi
fact InvariantUser{
all u1:User | all number:Int  | all s:String | all d:Data | ( ((number -> (s -> d)) in u1.thirdpartiesallowed) implies (all num:Int | (num>number) implies(num -> (s -> d)) in u1.thirdpartiesallowed))
}

//all'instante Zero non ci sono tuple
fact ZeroFirstDataReceived{
all t1:ThirdParty | all number:Int  |  all d:Data | ( ((number -> d) in t1.datareceived) implies (number > 0 ))
}

//se in un istante si inserisce una tupla, questa resterà inserita anche in tutti gli istanti successivi
fact InvariantDataReceived{
all t1:ThirdParty | all number:Int  |  all d:Data | ( ((number -> d) in t1.datareceived) implies (all num:Int | (num>number)implies((num -> d) in t1.datareceived)))
}

//all'istante Zero non ci sono tuple
fact ZeroFirstgroupedDataReceived{
all t1:ThirdParty | all number:Int  |  all d:Data | ( ((number -> d) in t1.groupeddatareceived) implies (number > 0 ))
}

//se in un istante si inserisce una tupla, questa resterà inserita anche in tutti gli istanti successivi
fact InvariantgroupedDataReceived{
all t1:ThirdParty | all number:Int  |  all d:Data | ( ((number -> d) in t1.groupeddatareceived) implies (all num:Int | (num>number)implies((num -> d) in t1.groupeddatareceived)))
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
//modeling requests
//request to a single user's data
fact AccessToIndividualData {
all u1: User, req: IndividualRequest, t1: ThirdParty, d1: Data|(
one num:Int | (
(req.time=num) and 
d1 not in t1.datareceived[num]) and
(req.requester = t1.email) and
(req.identifier = u1.fiscalCode) and (d1.identifier = u1.fiscalCode) and
(num -> (t1.email -> d1) not in u1.thirdpartiesallowed)  and
(d1.parameters = req.parameters) 
and (  
(all number:Int| ( (number > num) implies 
(d1 in t1.datareceived[number] and
(number -> (t1.email -> d1) in u1.thirdpartiesallowed))))
or
(all number:Int| ( (number > num) implies 
(d1  not in t1.datareceived[number] and
(number -> (t1.email -> d1) not  in u1.thirdpartiesallowed))))))
}

sig Datapool {
data:some Data
}

// in a datapool there are all and only the data which match the parameters
fact AlltheSameParameter{
all datapool:Datapool | no d1,d2:Data | d1.parameters != d2.parameters and d1 in datapool.data and d2 in datapool.data
}

fact AllTheParameter{
all datapool:Datapool | no d1,d2:Data | d1.parameters = d2.parameters and d1 in datapool.data and d2 not in datapool.data
}


//se in questo istante ci sei e nel precedente no è perchè ho appena fatto la richiesta che è andata a buon fine
//fact JustRequested{
//all t1:ThirdParty,  d1:Data, num1, num2:Int | ( (num1 -> d1 not in t1.groupeddatareceived) and ( num2 -> d1 in  t1.groupeddatareceived ) and num2 = num1 +1 ) <=> ( 
//(one req:Request |  (req.requester = t1.email and req.time = num1 and req.parameters = d1.parameters)))
//}


//Anonymize when possible if requested data about groups of clients
//Hp: 3 rappresenta la soglia
fact AccesstoAnonymizedData{
all p1: Parameters, t1: ThirdParty, num:Int,  pool:Datapool|(
one req: GroupRequest| (
req.time = num 
//and (all d1:Data | ((d1 in pool.data) implies (d1 not in ThirdParty.groupeddatareceived[num])))
 and req.requester = t1.email  
and (all d1:Data | d1 in pool.data implies d1.parameters = p1) 
and  req.parameters=p1
and 
(
      (     (#(pool.data)  > 2) and   all number:Int | (number > num implies  ((all d1:Data | d1 in pool.data implies  d1 in t1.groupeddatareceived[number] ) and  (all d1:Data | d1 in pool.data implies d1.identifier = "nobody") ))
      )
or 
      (    (#(pool.data) <3) and   all number:Int | (number > num  implies (all d1:Data | d1 in pool.data implies d1 not in t1.groupeddatareceived[number]))
	  )
)
)
)


}



//assertions checking that privacy is always respected
//"Nobody" is a constant used to model whene the fiscal code is anonymized
assert PrivacyIsProtected{
all t1:ThirdParty, num:Int | all d1: t1.groupeddatareceived[num] | d1.identifier = "nobody"
}

assert PrivacyIsProtected2{
all t1:ThirdParty, num:Int,  d1: Data | ( (num->d1 in t1.datareceived) implies one u1:User | (num -> (t1.email -> d1) in u1.thirdpartiesallowed))
}

//an interesting predicate: we want to be sure that the third parties are able to receive data in our modelling
pred AllowThirdPartiesToGetData{
some t1:ThirdParty | some num:Int | (t1.datareceived[num] != none and t1.groupeddatareceived[num] != none)
}



//AutomatedSos
//facts
//a user with no automatedSos service  is never in danger of life ( in our modelling)
fact DangerOfLifeonlyisAutomatedSos{
all u1:User, t1:Time | ( (t1 -> True in  u1.inDangerOfLife) implies isTrue[u1.automatedSos]
)}

//a third party can handle alerts only if he is subscribed to AutomatedSOS
fact HandleOnlyIfSubscribed{
all t1: ThirdParty | ((some number: Int | number in t1.alerts)  implies  isTrue[t1.automatedSos])
}

//There can't be  two alerts with the same id
fact AlertsIDAreunique{
no disjoint al1, al2 : Alert | al1.alertID = al2.alertID
}

//third parties must have ids in its relation corresponding to unique alerts (consistency of alertID)
fact CorrectAlertsID{
all t1: ThirdParty | all number: t1.alerts | one al: Alert | number = al.alertID
}

//there are alerts only if the user is active (again: an assumption of our modeling)
fact IfNonActiveThereareNoEmergencies{
all al:Alert | IsActive[al.data.identifier]
}


//there can't be two contemporary emergencies for the same user
fact NocontemporaryEmergenciesForTheSameUSer{
all disj al1, al2: Alert | al1.data.identifier = al2.data.identifier implies al1.data.time != al2.data.time
}

//whenever a user is in danger of life, health values go below trehsholds (just for that time)
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


//there are no alerts marked as not handling (which means, there is always a third party which handles the request)
fact AllAlertsAreHandled{
all al1:Alert | isTrue[al1.status.handling]
}

//when a third party handles an alert, the user is provided with medical assistance (we don't care how, it's out of our control)
fact ProvideMedicalAssistance{
all t1:ThirdParty, al1:Alert | ( (al1.alertID in t1.alerts) implies (all u1:User | ((u1.fiscalCode = al1.data.identifier) implies ( al1.data.time -> True in u1.IsUnderAssistance))))
}


//the main goal of AutoMatedSos
assert HandleEmergency{
all t1:Time, u1:User | ( ( (t1->True) in u1.inDangerOfLife) implies (t1 -> True in u1.IsUnderAssistance))
}


//commands
run AllowThirdPartiesToGetData  for 4 but  exactly 6 String,  4 Int









