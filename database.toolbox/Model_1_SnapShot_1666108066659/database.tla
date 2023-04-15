------------------------------ MODULE database ------------------------------
EXTENDS Integers, Sequences, TLC
CONSTANTS Data, NULL, Clients

(*--algorithm database
variables
    query = [c \in Clients |-> NULL];
    db_value \in Data;

define
    Exists(val) == val /= NULL
    RequestingClients == {c \in Clients: Exists(query[c]) /\ query[c].type = "request"}
end define;

macro request(data) begin
    query[self] := [type |-> "request"] @@ data;
end macro;

macro wait_for_response() begin
    await query[self].type = "response";
end macro;


process clients \in Clients
variables result = NULL;
begin
    Request:
        while TRUE do
            either \* read
                request([request |-> "read"]);
                Confirm:
                    wait_for_response();
                    result := query[self].result;
                    assert result = db_value;
            or \* write
                with d \in Data do
                    request([request |-> "write", data |-> d]);
                end with;
                Wait:
                    wait_for_response();
            end either;
        end while;
end process;


process database = "Database"
begin
    DB:
        with client \in RequestingClients, q = query[client] do
            if q.request = "write" then
                db_value := q.data;
            elsif q.request = "read" then
                skip;
            else 
                assert FALSE; \* What did we even pass in
            end if;
            query[client] := [type |-> "response", result |-> db_value];
        end with;
    goto DB;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "556495c6" /\ chksum(tla) = "6bf5eebc")
VARIABLES query, db_value, pc

(* define statement *)
Exists(val) == val /= NULL
RequestingClients == {c \in Clients: Exists(query[c]) /\ query[c].type = "request"}

VARIABLE result

vars == << query, db_value, pc, result >>

ProcSet == (Clients) \cup {"Database"}

Init == (* Global variables *)
        /\ query = [c \in Clients |-> NULL]
        /\ db_value \in Data
        (* Process clients *)
        /\ result = [self \in Clients |-> NULL]
        /\ pc = [self \in ProcSet |-> CASE self \in Clients -> "Request"
                                        [] self = "Database" -> "DB"]

Request(self) == /\ pc[self] = "Request"
                 /\ \/ /\ query' = [query EXCEPT ![self] = [type |-> "request"] @@ ([request |-> "read"])]
                       /\ pc' = [pc EXCEPT ![self] = "Confirm"]
                    \/ /\ \E d \in Data:
                            query' = [query EXCEPT ![self] = [type |-> "request"] @@ ([request |-> "write", data |-> d])]
                       /\ pc' = [pc EXCEPT ![self] = "Wait"]
                 /\ UNCHANGED << db_value, result >>

Confirm(self) == /\ pc[self] = "Confirm"
                 /\ query[self].type = "response"
                 /\ result' = [result EXCEPT ![self] = query[self].result]
                 /\ Assert(result'[self] = db_value, 
                           "Failure of assertion at line 34, column 21.")
                 /\ pc' = [pc EXCEPT ![self] = "Request"]
                 /\ UNCHANGED << query, db_value >>

Wait(self) == /\ pc[self] = "Wait"
              /\ query[self].type = "response"
              /\ pc' = [pc EXCEPT ![self] = "Request"]
              /\ UNCHANGED << query, db_value, result >>

clients(self) == Request(self) \/ Confirm(self) \/ Wait(self)

DB == /\ pc["Database"] = "DB"
      /\ \E client \in RequestingClients:
           LET q == query[client] IN
             /\ IF q.request = "write"
                   THEN /\ db_value' = q.data
                   ELSE /\ IF q.request = "read"
                              THEN /\ TRUE
                              ELSE /\ Assert(FALSE, 
                                             "Failure of assertion at line 55, column 17.")
                        /\ UNCHANGED db_value
             /\ query' = [query EXCEPT ![client] = [type |-> "response", result |-> db_value']]
      /\ pc' = [pc EXCEPT !["Database"] = "DB"]
      /\ UNCHANGED result

database == DB

Next == database
           \/ (\E self \in Clients: clients(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Tue Oct 18 23:46:39 CST 2022 by wengjialin
\* Created Tue Oct 18 22:45:47 CST 2022 by wengjialin
