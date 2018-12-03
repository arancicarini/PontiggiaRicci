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
thirdpartiesallowed: Int -> (ThirdParty -> Data), 
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
parameters: one Parameters,
accepted: one Bool 
}
{
requestID > 0
time > 0
}

sig IndividualRequest extends Request{
identifier: one String,
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
all u1:User, d1:Data, num:Int, t1:ThirdParty|  (d1 in u1.thirdpartiesallowed[num][t1] implies d1.identifier = u1.fiscalCode)
}

//third parties e utenti non possono avere lo stesso identificativo
fact ThirdPartiesandUsersDosjointed{
all t1:ThirdParty, u1:User | t1.email != u1.fiscalCode
}

//TIME MODELLING
// all'istante zero non ci sono tuple
fact ZeroFirstUser{
all u1:User | all number:Int  | all s:ThirdParty | all d:Data | ( ((number -> (s -> d)) in u1.thirdpartiesallowed) implies (number > 0) )
}

//se in un istante si inserisce una tupla, questa resterà inserita anche in tutti gli istanti successivi
fact InvariantUser{
all u1:User | all number:Int  | all s:ThirdParty | all d:Data | ( ((number -> (s -> d)) in u1.thirdpartiesallowed) implies (all num:Int | (num>number) implies(num -> (s -> d)) in u1.thirdpartiesallowed))
}

//all'instante Zero non ci sono tuple
fact ZeroFirstDataReceived{
all t1:ThirdParty | all number:Int  |  all d:Data | ( ((number -> d) in t1.datareceived) implies (number > 0))
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
all u1:User, d1:Data, num:Int, s:ThirdParty|  (d1 in u1.thirdpartiesallowed[num][s] implies d1.time < num)
}

//MODELLING REQUESTS
//if the thid party has something, he has asked for the data before [done with a pred]
pred existsassociatedRequest[t1:ThirdParty, d:Data, num:Int ]{
one req:IndividualRequest | req.identifier = d.identifier and req.requester = t1.email and req.time = num and isTrue[req.accepted] and req.parameters = d.parameters and d.time <= req.time
}
pred notexistsassociatedRequest[t1:ThirdParty, d:Data, num:Int ]{
no req:IndividualRequest | req.identifier = d.identifier and req.requester = t1.email and req.time = num and isTrue[req.accepted] and req.parameters = d.parameters and d.time <= req.time
}
fact Onlyrequested{
all t1:ThirdParty, num:Int,  d:Data |  num -> d in t1.datareceived <=>
 (  
	((notexistsassociatedRequest[t1,d, num-1]) and ((num -1) -> d in t1.datareceived))   or  
	( existsassociatedRequest[t1,d, num-1] and (num -1) -> d not in t1.datareceived)
)
}

//if a user has given his permission, he has been asked for it before[done with a pred]
fact Onlyifrequested{
all u1:User, num:Int,  d:Data, t1:ThirdParty |  num ->t1-> d in u1.thirdpartiesallowed <=>
 (  ((not existsassociatedRequest[t1,d, num-1]) and ((num -1) ->t1-> d in u1.thirdpartiesallowed))   or  
	( existsassociatedRequest[t1,d, num-1] and (num -1) ->t1-> d not in u1.thirdpartiesallowed)
)
}

//if the thid party has something, he has asked for the data before [done with a pred]
pred existsgroupedsassociatedRequest[t1:ThirdParty, d:Data, num:Int]{
one req:GroupRequest | (req.parameters = d.parameters and req.requester = t1.email and req.time = (num) and isTrue[req.accepted] and d.time <= req.time)
}
pred notexistsgroupedsassociatedRequest[t1:ThirdParty, d:Data, num:Int]{
no req:GroupRequest | (req.parameters = d.parameters and req.requester = t1.email and req.time = (num) and isTrue[req.accepted] and d.time <= req.time)
}
fact Onlygroupedrequested{
all t1:ThirdParty,d1:Data,num:Int | num -> d1 in t1.groupeddatareceived <=> 
 (  (  notexistsgroupedsassociatedRequest[t1,d1, num-1] and (num -1) -> d1 in t1.groupeddatareceived)   or  
	(existsgroupedsassociatedRequest[t1,d1, num-1] and (num -1) -> d1 not in t1.groupeddatareceived) 
)
}

//a grouped request is accepted only if the number of data involving the request is more than 2 (arbitrary number for 1000)
//fact OnlyifAnonymous{
//all req1:GroupRequest | isTrue[req1.accepted] <=>


//assertions checking that privacy is always respected
assert PrivacyIsProtected{
all t1:ThirdParty, num:Int,  d1: Data | ( (num->d1 in t1.datareceived) <=> (one u1:User | (num -> (t1 -> d1) in u1.thirdpartiesallowed)))
}

//an interesting predicate: we want to be sure that the third parties are able to receive data in our modelling
pred AllowThirdPartiesToGetData{
some t1:ThirdParty | some num:Int | (t1.datareceived[num] != none and t1.groupeddatareceived[num] != none)
}

//pred GetData

//commands
run AllowThirdPartiesToGetData  for 5 but  exactly 5 String,  5 Int
