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
inDangerOfLife : Int -> one Bool,
IsUnderAssistance: Int -> one Bool,
thresholds: one Int
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
identifier: one String,
accepted: one Bool 
}
sig GroupRequest extends Request{
}

sig Data{
identifier: String,
parameters: one Parameters,
healthValues: one Int,
time: one Int,
}

sig Parameters{
}

//TO DO LIST
// riscrivere i fact aiutandosi con dei pred per rendere il tutto più leggibile
//modellizzare la creazione di data
//guardare quaderno principles
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

fun getTheUser[identifier:String]: one User{
 { u1:User | u1.fiscalCode = identifier}
}

fun getTheThirdParty[identifier:String]: one ThirdParty{
{t1:ThirdParty | t1.email = identifier}
}


//facts
//requests must regard subscribed users
fact IndivdualRequestmustRegardAsubscribedUser{
  all r1: IndividualRequest |  IsSubscribedtoData4Help[r1.identifier]
}
//Notworequestsatthesametimebythesamethirdaprty
fact NoContemporary{
no disjoint req1, req2: Request | req1.requester = req2.requester and req1.time = req2.time
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
no disj d1,d2: Data | d1.identifier = d2.identifier and d1.time = d2.time
}

//a user can give permission only for his data
fact OnlyMyData{
all u1:User, d1:Data, num:Int, s:String|  (d1 in u1.thirdpartiesallowed[num][s] implies d1.identifier = u1.fiscalCode)
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

//a third party can't receive data from the future
fact NotFromTheFuture{
all t1:ThirdParty, d1:Data, num:Int | d1 in t1.datareceived[num] implies d1.time < num
}

fact GroupedNotFromTheFuture{
all t1:ThirdParty, d1:Data, num:Int | d1 in t1.groupeddatareceived[num] implies d1.time< num
}


//The user can't allow the third party to receive future data
fact NoAllowForTheFuture{
all u1:User, d1:Data, num:Int, s:String|  (d1 in u1.thirdpartiesallowed[num][s] implies d1.time < num)
}

//MODELLING REQUESTS
//if a request is successfull, the user involved in the request has give his permission
fact SuccesfullIndividualRequestUser{
all req1:IndividualRequest | isTrue[req1.accepted] <=>  (all d1:Data | (d1.identifier = req1.identifier and d1.parameters = req1.parameters) <=> ((req1.time +1) -> ( req1.requester  -> d1 ) in  getTheUser[d1.identifier].thirdpartiesallowed))
}

//if a request is successfull, the following instant of time the third party has all his datas
fact SuccessfullIndividualRequestThirdParty{
all req1:IndividualRequest | isTrue[req1.accepted] <=>  (all d1:Data | (d1.identifier = req1.identifier and d1.parameters = req1.parameters) <=> (req1.time +1) -> d1 in  getTheThirdParty[req1.requester].datareceived)
}

//devo inserire d1.time < req.time e invece sopra no perchè .....
fun GetTheMatchingNumberofUsers[req:GroupRequest]: one Int{
{ #{s1:String | some d1:Data | d1.time <= req.time and d1.parameters = req.parameters and s1 = d1.identifier}}
}

fact SuccessfullGroupedRequestThirdParty{
all req1: GroupRequest | GetTheMatchingNumberofUsers[req1] > 2 <=> (all d1:Data | (d1.time <= req1.time and d1.parameters = req1.parameters) <=> (req1.time +1) -> d1 in  getTheThirdParty[req1.requester].groupeddatareceived)
}





//assertions checking that privacy is always respected
assert PrivacyIsProtected{
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
all u1:User, t1: Int | ( (t1 -> True in  u1.inDangerOfLife) implies isTrue[u1.automatedSos]
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
all t1:Int, u1:User | ( (t1->True in u1.inDangerOfLife)  <=> (one d1:Data | (d1.time = t1 and  d1.identifier = u1.fiscalCode and d1.healthValues < u1.thresholds)))
}

//an alert is created only if healthvalues are under thresholds
fact AlertCreation{
all al1: Alert |  one u1:User | al1.data.healthValues < u1.thresholds
}

//an alert is created if healthvalues are under thresholds 
fact AlertCreation2{
all d1:Data | (  (one u1:User | (u1.fiscalCode = d1.identifier and d1.healthValues < u1.thresholds))  implies  (one al1:Alert | al1.data = d1))
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


//the main goal of AutomatedSos
assert HandleEmergency{
all t1:Int, u1:User | ( ( (t1->True) in u1.inDangerOfLife) implies (t1 -> True in u1.IsUnderAssistance))
}


//commands
check PrivacyIsProtected for 4  but  exactly 5 String,  4  Int









