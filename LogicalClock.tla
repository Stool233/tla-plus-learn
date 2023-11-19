---------------------------- MODULE LogicalClock ----------------------------
EXTENDS Naturals, Sequences, TLC

(***************************************************************************)
(* The parameter N represents the number of processes.                     *)
(* The parameter maxClock is used only for model checking in order to      *)
(* keep the state space finite.                                            *)
(***************************************************************************)
CONSTANT N, maxClock


ASSUME NType == N \in Nat
ASSUME maxClockType == maxClock \in Nat

Proc == 1 .. N
Clock == Nat \ {0}
  

(*--algorithm logicalClock
variables
  clock = [p \in Proc |-> 1];
  req = [p \in Proc |-> [q \in Proc |-> 0]];
  ack = [p \in Proc |-> {}];
  network = [p \in Proc |-> [q \in Proc |-> <<>>]];
  crit = {};
  
define
  ReqMessage(c) == [type |-> "req", clock |-> c]
  AckMessage == [type |-> "ack", clock |-> 0]
  RelMessage == [type |-> "rel", clock |-> 0]

  Message == {AckMessage, RelMessage} \union {ReqMessage(c) : c \in Clock}
  
  TypeInvariant ==
    /\ clock \in [Proc -> Clock]
    /\ req \in [Proc -> [Proc -> Nat]]
    /\ ack \in [Proc -> SUBSET Proc]
    /\ network \in [Proc -> [Proc -> Seq(Message)]]
    /\ crit \in SUBSET Proc
    
  beats(p,q) ==
    \/ req[p][q] = 0
    \/ req[p][p] < req[p][q]
    \/ req[p][p] = req[p][q] /\ p < q
    
  Broadcast(s, m) ==
    [r \in Proc |-> IF s=r THEN network[s][r] ELSE Append(network[s][r], m)]
  
  
end define;



fair process proc \in Proc
begin 

  Request: 
    req[self][self] := clock[self];
    network[self] := Broadcast(self, ReqMessage(clock[self]));
    ack[self] := {self};


  Receive:
      if Proc # {self} then
          with q \in Proc \ {self}
          do 
            if  network[q][self] # << >> then
            
                with m = Head(network[q][self]), c = m.clock
                do
                  if m.type = "req" then
                    req[self][q] := c;
                    if c > clock[self] then
                      clock[self] := c + 1;
                    else
                      clock[self] := clock[self] + 1;
                    end if;
                    network[q][self] := Tail(network[q][self]) || 
                    network[self][q] := Append(network[self][q], AckMessage);
                      
                  elsif m.type = "ack" then
                     ack[self] := ack[self] \union {q};
                     network[q][self] := Tail(network[q][self]);
                  
                  elsif m.type = "rel" then
                    req[self][q] := 0;
                    network[q][self] := Tail(network[q][self]);
                  
                  end if; 
                end with;
             end if;
            
          end with;
      
      end if;
  

    
  Enter:
    if (ack[self] = Proc) /\ (  \A q \in Proc \ {self} : beats(self,q) ) then
      crit := crit \union {self};
    else
      goto Receive;
    end if;
    
    
  Exit:
    crit := crit \ {self};
    network[self] := Broadcast(self, RelMessage);
    req[self][self] := 0;
    ack[self] := {};
    goto Request;
    
      
    
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "207be3db" /\ chksum(tla) = "43df02b6")
VARIABLES clock, req, ack, network, crit, pc

(* define statement *)
ReqMessage(c) == [type |-> "req", clock |-> c]
AckMessage == [type |-> "ack", clock |-> 0]
RelMessage == [type |-> "rel", clock |-> 0]

Message == {AckMessage, RelMessage} \union {ReqMessage(c) : c \in Clock}

TypeInvariant ==
  /\ clock \in [Proc -> Clock]
  /\ req \in [Proc -> [Proc -> Nat]]
  /\ ack \in [Proc -> SUBSET Proc]
  /\ network \in [Proc -> [Proc -> Seq(Message)]]
  /\ crit \in SUBSET Proc

beats(p,q) ==
  \/ req[p][q] = 0
  \/ req[p][p] < req[p][q]
  \/ req[p][p] = req[p][q] /\ p < q

Broadcast(s, m) ==
  [r \in Proc |-> IF s=r THEN network[s][r] ELSE Append(network[s][r], m)]


vars == << clock, req, ack, network, crit, pc >>

ProcSet == (Proc)

Init == (* Global variables *)
        /\ clock = [p \in Proc |-> 1]
        /\ req = [p \in Proc |-> [q \in Proc |-> 0]]
        /\ ack = [p \in Proc |-> {}]
        /\ network = [p \in Proc |-> [q \in Proc |-> <<>>]]
        /\ crit = {}
        /\ pc = [self \in ProcSet |-> "Request"]

Request(self) == /\ pc[self] = "Request"
                 /\ req' = [req EXCEPT ![self][self] = clock[self]]
                 /\ network' = [network EXCEPT ![self] = Broadcast(self, ReqMessage(clock[self]))]
                 /\ ack' = [ack EXCEPT ![self] = {self}]
                 /\ pc' = [pc EXCEPT ![self] = "Receive"]
                 /\ UNCHANGED << clock, crit >>

Receive(self) == /\ pc[self] = "Receive"
                 /\ IF Proc # {self}
                       THEN /\ \E q \in Proc \ {self}:
                                 IF network[q][self] # << >>
                                    THEN /\ LET m == Head(network[q][self]) IN
                                              LET c == m.clock IN
                                                IF m.type = "req"
                                                   THEN /\ req' = [req EXCEPT ![self][q] = c]
                                                        /\ IF c > clock[self]
                                                              THEN /\ clock' = [clock EXCEPT ![self] = c + 1]
                                                              ELSE /\ clock' = [clock EXCEPT ![self] = clock[self] + 1]
                                                        /\ network' = [network EXCEPT ![q][self] = Tail(network[q][self]),
                                                                                      ![self][q] = Append(network[self][q], AckMessage)]
                                                        /\ ack' = ack
                                                   ELSE /\ IF m.type = "ack"
                                                              THEN /\ ack' = [ack EXCEPT ![self] = ack[self] \union {q}]
                                                                   /\ network' = [network EXCEPT ![q][self] = Tail(network[q][self])]
                                                                   /\ req' = req
                                                              ELSE /\ IF m.type = "rel"
                                                                         THEN /\ req' = [req EXCEPT ![self][q] = 0]
                                                                              /\ network' = [network EXCEPT ![q][self] = Tail(network[q][self])]
                                                                         ELSE /\ TRUE
                                                                              /\ UNCHANGED << req, 
                                                                                              network >>
                                                                   /\ ack' = ack
                                                        /\ clock' = clock
                                    ELSE /\ TRUE
                                         /\ UNCHANGED << clock, req, ack, 
                                                         network >>
                       ELSE /\ TRUE
                            /\ UNCHANGED << clock, req, ack, network >>
                 /\ pc' = [pc EXCEPT ![self] = "Enter"]
                 /\ crit' = crit

Enter(self) == /\ pc[self] = "Enter"
               /\ IF (ack[self] = Proc) /\ (  \A q \in Proc \ {self} : beats(self,q) )
                     THEN /\ crit' = (crit \union {self})
                          /\ pc' = [pc EXCEPT ![self] = "Exit"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "Receive"]
                          /\ crit' = crit
               /\ UNCHANGED << clock, req, ack, network >>

Exit(self) == /\ pc[self] = "Exit"
              /\ crit' = crit \ {self}
              /\ network' = [network EXCEPT ![self] = Broadcast(self, RelMessage)]
              /\ req' = [req EXCEPT ![self][self] = 0]
              /\ ack' = [ack EXCEPT ![self] = {}]
              /\ pc' = [pc EXCEPT ![self] = "Request"]
              /\ clock' = clock

proc(self) == Request(self) \/ Receive(self) \/ Enter(self) \/ Exit(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Proc: proc(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Proc : WF_vars(proc(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

ClockConstraint == \A p \in Proc : clock[p] <= maxClock

BoundedNetwork == \A p,q \in Proc : Len(network[p][q]) <= 3

Mutex == \A p,q \in crit : p = q

=============================================================================
\* Modification History
\* Last modified Sun Apr 16 20:56:30 CST 2023 by wengjialin
\* Created Sat Apr 15 18:25:02 CST 2023 by wengjialin
