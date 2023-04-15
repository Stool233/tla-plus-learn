------------------------------ MODULE library ------------------------------
EXTENDS Integers, TLC, Sequences
PT == INSTANCE PT

CONSTANTS Books, People, NumCopies
ASSUME NumCopies \subseteq Nat

set ++ x == set \union {x}
set -- x == set \ {x}

(*--algorithm library
variables
    library \in [Books -> NumCopies],
    reserves = [b \in Books |-> <<>>];

define
    AvailableBooks == {b \in Books: library[b] > 0}
    BorrowableBooks(p) == 
        {b \in AvailableBooks: 
            \/ reserves[b] = <<>>
            \/ p = Head(reserves[b])}
end define;


fair process persion \in People
variables
    books = {};
    wants \in SUBSET Books;
begin
    Person:
      while TRUE do
        either
            \* Checkout:
            with b \in (BorrowableBooks(self) \intersect wants) \ books do
                library[b] := library[b] - 1;
                books := books ++ b;
                wants := wants -- b;
                if reserves[b] /= <<>> /\ self = Head(reserves[b]) then
                    reserves[b] := Tail(reserves[b]);
                end if;
            end with;  
            
        or 
            \* Return:
            with b \in books do
                library[b] := library[b] + 1;
                books := books -- b;
            end with;
        or
            \* Reserve:
            with b \in {b \in Books: self \notin PT!Range(reserves[b])} do
                reserves[b] := Append(reserves[b], self);
            end with;
        or 
            \* Want
            with b \in Books \ wants do
                wants := wants ++ b;
            end with;
        end either;
      end while;
end process;    
    

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "3d3aa2b3" /\ chksum(tla) = "a036ca42")
VARIABLES library, reserves

(* define statement *)
AvailableBooks == {b \in Books: library[b] > 0}
BorrowableBooks(p) ==
    {b \in AvailableBooks:
        \/ reserves[b] = <<>>
        \/ p = Head(reserves[b])}

VARIABLES books, wants

vars == << library, reserves, books, wants >>

ProcSet == (People)

Init == (* Global variables *)
        /\ library \in [Books -> NumCopies]
        /\ reserves = [b \in Books |-> <<>>]
        (* Process persion *)
        /\ books = [self \in People |-> {}]
        /\ wants \in [People -> SUBSET Books]

persion(self) == \/ /\ \E b \in (BorrowableBooks(self) \intersect wants[self]) \ books[self]:
                         /\ library' = [library EXCEPT ![b] = library[b] - 1]
                         /\ books' = [books EXCEPT ![self] = books[self] ++ b]
                         /\ wants' = [wants EXCEPT ![self] = wants[self] -- b]
                         /\ IF reserves[b] /= <<>> /\ self = Head(reserves[b])
                               THEN /\ reserves' = [reserves EXCEPT ![b] = Tail(reserves[b])]
                               ELSE /\ TRUE
                                    /\ UNCHANGED reserves
                 \/ /\ \E b \in books[self]:
                         /\ library' = [library EXCEPT ![b] = library[b] + 1]
                         /\ books' = [books EXCEPT ![self] = books[self] -- b]
                    /\ UNCHANGED <<reserves, wants>>
                 \/ /\ \E b \in {b \in Books: self \notin PT!Range(reserves[b])}:
                         reserves' = [reserves EXCEPT ![b] = Append(reserves[b], self)]
                    /\ UNCHANGED <<library, books, wants>>
                 \/ /\ \E b \in Books \ wants[self]:
                         wants' = [wants EXCEPT ![self] = wants[self] ++ b]
                    /\ UNCHANGED <<library, reserves, books>>

Next == (\E self \in People: persion(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in People : WF_vars(persion(self))

\* END TRANSLATION 

NoDuplicateReservations ==
    \A b \in Books:
        \A i, j \in 1..Len(reserves[b]):
            i /= j => reserves[b][i] /= reserves[b][j]

TypeInvariant ==
    /\ library \in [Books -> NumCopies ++ 0]
    /\ books \in [People -> SUBSET Books]
    /\ wants \in [People -> SUBSET Books]
    /\ reserves \in [Books -> Seq(People)]
    /\ NoDuplicateReservations
    

\*Liveness == 
\*    /\ <>(\A p \in People: wants[p] = {})
Liveness == 
    \A p \in People:
        \A b \in Books:
            b \in wants[p] ~> b \notin wants[p]
            


=============================================================================
\* Modification History
\* Last modified Mon Nov 28 21:17:22 CST 2022 by wengjialin
\* Created Sat Nov 05 18:12:15 CST 2022 by wengjialin
