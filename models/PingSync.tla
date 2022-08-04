------------------------------ MODULE PingSync ------------------------------

(*


+-------------+                       +-----------------+
|             |                       |                 |
|             |                       |                 |
| Server      |-------network---------+   Client        +
|             |                       |                 |
|             |                       |                 |
+------+------+                       +-----------------+


This is an algorithm to change network 

A server receives a request to change network settings but
then it needs to have a timeout and revert to old settings
if the new settings can't get a ping.


*)

EXTENDS Naturals
--------------------------------------------------

(* -------------------------------------------------- *)
(* Constants *)
(* -------------------------------------------------- *)


CONSTANTS TimeLimit, MaxTime


(* -------------------------------------------------- *)
(* Variables *)
(* -------------------------------------------------- *)


VARIABLES server, time

vars == << server, time >> 



(* -------------------------------------------------- *)
(* Sets *)
(* -------------------------------------------------- *)

NetworkState == { "Active", "InActive" } 
NetworkProfile == { "N1","N2"}
Status ==  {"Connected", "Unconnected", "Timeout"}
Messages == {"None", "Ping","Pong", "Change"}

Time == {t \in Nat: t < (TimeLimit + MaxTime) }

(* -------------------------------------------------- *)
(* Tuples / Records  *)
(* -------------------------------------------------- *)

Server == [ state : NetworkState ,
           profile : NetworkProfile,          
           status : Status,
           message : Messages ]
           

(* -------------------------------------------------- *)
(* Specification  *)
(* -------------------------------------------------- *)

Init ==
  /\ server = [ state |-> "Active" ,
                profile |-> "N1",
                status |-> "Connected",
                message |-> "None" ] 
  /\ time = 0


MessageChangeRequest ==
  /\ server.message = "Change"
  /\ server.state = "Active"
  /\ server.status = "Connected"
  /\ time' = time + 1
  /\ server' = [server EXCEPT !.state = "InActive",
                                !.status = "Unconnected",
                                !.message = "None",
                              !.profile = "N2" ]


(* The server is still inactive but the network connection is back *)
(* We ping out to see if we can count it as active *)

MessagePingRequest == 
  /\ server.message = "None"
  /\ server.state = "InActive"
  /\ server.status = "Connected"
  /\ time' = time + 1
  /\ server' = [server EXCEPT !.message = "Ping"] 




(* The server is still inactive but the network *)
(* connection is back *)
(* We see a Pong and so set the connection active *)
MessagePongRequest ==
  /\ server.message = "Ping"
  /\ server.state = "InActive"
  /\ server.status = "Connected"
  /\ time' = time + 1
  /\ server' = [server EXCEPT !.message = "Pong",
                              !.state = "Active"  ] 

MessageTimeout ==
  /\ server.state = "InActive" 
  /\ server.status # "Timeout"
  /\ time >= TimeLimit
  /\ time < TimeLimit + MaxTime  
  /\ time' = time + 1
  /\ server' = [server EXCEPT !.status = "Timeout"  ]

MessageResponseToTimeout ==
  /\ server.state  = "InActive" 
  /\ server.status = "Timeout"
  /\ time' = time + 1    
  /\ server' = [server EXCEPT !.profile = "N1",
                              !.state = "Active",   
                              !.status = "Unconnected",  
                              !.message = "None"  ]    
  
MessageResponseToChange == 
     \/ MessageChangeRequest 
     \/ MessagePingRequest
     \/ MessagePongRequest
     \/ MessageTimeout
     \/ MessageResponseToTimeout  
  
MessageInitiateChange ==
  /\ server.message = "None"
  /\ server.state = "Active"
  /\ server.status = "Connected"
  /\ time' = time + 1
  /\ server' = [server EXCEPT !.message = "Change" ]

WorldConnectOrNo ==
  /\ server.status = "Unconnected"
  /\ LET Connection == CHOOSE c \in Status :
                                   c \in {"Unconnected","Connected"}
     IN /\  server' = [server EXCEPT !.status = Connection]
        /\  time' = time + 1
  
WorldActions ==
  \/  WorldConnectOrNo

  
Next == UNCHANGED vars 
      \/ MessageResponseToChange
      \/ (MessageInitiateChange /\ time < TimeLimit)
      \/ WorldConnectOrNo  

NoMessagesProp == [][server.status = "Unconnected" =>
                    server'.message = "None" ]_vars

EventualPong == <>(server.message = "Pong") 

SometimesTimeout == (time >= TimeLimit) ~>  (server.state = "Timeout")

  
Properties == NoMessagesProp /\
                EventualPong /\
                SometimesTimeout


TypeOK == server \in Server
    /\         time \in Time   



SPEC == Init
 /\ ( [][Next]_vars ) 
 /\ SF_vars(Next) 
 
 


=============================================================================
\* Modification History
\* Last modified Wed Aug 03 23:33:03 CDT 2022 by scott
\* Created Fri Jul 15 20:15:56 CDT 2022 by scott
