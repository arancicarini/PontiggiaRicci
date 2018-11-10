open util/integer
open util/boolean

//signatures
abstract sig Client{
AutomatedSos: one Bool
}
sig User extends Client{
fiscalCode: one String,
status: one UserStatus
}

sig UserStatus{
active: Bool
}

sig ThirdParty extends Client{
email: one Int,
requests: set Request,
alerts: set Alert
}

sig Alert{
 data: one Data,
status: one EmergencyStatus
}

sig EmergencyStatus{
handling: Bool
}

abstract sig Request{}
sig IndividualRequest extends Request{
identifier: one String
}
sig GroupRequest extends Request{
//qua bisognerà per forza aggiungere qualcosa
}

abstract sig Data{
identifier: one String,
information: one PersonalInformation
}
sig HealthValue extends Data{
userIdentifier: one String,
heartRate: one Int,
pression: one Int,
bloodSaturation: one Int,
bodyTemperature: one Int,
time: one Time
}
sig Location extends Data{
latitude: one Int,
longitude:  one Int
} 
 sig PersonalInformation{
information: some AtomicInformation
}

sig AtomicInformation{}

sig Time{
day: one String,
month: one String,
year: one Int,
hour: one Int,
minute: one Int,
second: one Int
}

//facts
pred IndivdualRequestmustRegardAsubscribedUser{
  all r1: IndividualRequest |  IsSubscribedtoData4Help[r1.identifier]
}

fact DataMustRegardSubscribedUser{
all d1: Data |  IsSubscribedtoData4Help[d1.identifier]
}

fact EmergenciesmustRegardASubscribedUSer{
all em1: Alert | IsSubscribedtoAutomatedSos[em1.data.identifier]
}

fact NocontemporaryEmergenciesForTheSameUSer

fact FiscalCodeeIsUnique{
no disjoint u1,u2: User | u1.fiscalCode = u2.fiscalCode
}

//pred
pred IsSubscribedtoData4Help[u:String]{
one u1:User | u = u1.fiscalCode
}

//quest'ultimo implica il precedente
pred IsSubscribedtoAutomatedSos[u:String]{

 one u1:User |  u = u1.fiscalCode and  isTrue[u1.AutomatedSos]
}






//commands

run   IsSubscribedtoData4Help for  2 but exactly 3 String

// non ci sono due health values realtivi allo stesso utente dello stesso dateTime

//ogni emergency deve essere relativa ad un utente registrato

// non possono esserci contemporaneamente due emergenze dello stesso utente

// non possono esserci emergenze attive rispetto ad un utente non attivo

//i gruppi di data devono comprendere più di mille

//se sono meno di mille 

//una alert deve essere gestita
