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


CONSTANTS TimeLimit

(* -------------------------------------------------- *)
(* Variables *)
(* -------------------------------------------------- *)


VARIABLES server, time

vars == << server, time >> 



(* -------------------------------------------------- *)
(* Sets *)
(* -------------------------------------------------- *)

NetworkState == { "Active", "InActive" } 
NetworkProfile == { "Old","New"}
Status ==  {"Connected", "Unconnected"}
Messages == {"None", "Ping","Pong", "Change"}

Time == {t \in Nat: t < TimeLimit }

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
                profile |-> "Old",
                status |-> "Connected",
                message |-> "None" ] 
  /\ time = 0

Next == UNCHANGED << vars >>



(* -------------------------------------------------- *)
(* Properties  *)
(* -------------------------------------------------- *)


(*  Messages can't come in when your server is unconnected *)
NoMessagesProp == [][server.status = "Unconnected" =>
                    server'.message = "None" ]_vars




(* -------------------------------------------------- *)
(* Model Format  *)
(* -------------------------------------------------- *)

SPEC == Init
 /\ ( [][Next]_vars ) 
 /\ WF_vars(Next) 
 
 


=============================================================================
\* Modification History
\* Created Fri Jul 15 20:15:56 CDT 2022 by scott
