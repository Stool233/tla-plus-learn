---- MODULE juniorv1 ----

EXTENDS Sequences, Naturals, FiniteSets

CONSTANT USERS

CONSTANTS
    SubscriptionFee,
    CancellationFee,
    FailedPaymentFee

VARIABLES
    month,
    database,
    events 

vars == <<events, month, database>>

INSTANCE specdatamodels

Now == Len(events)

Months == 0..10

(***************************************************************************)
(* Strong Typing                                                           *)
(***************************************************************************)

Month = Nat

(***************************************************************************)
(* Database Rows                                                           *)
(***************************************************************************)

UserRow == [
    subscribed: BOOLEAN ,
    \* Forget canceled
    inTrial: BOOLEAN ,
    trialStartTime: Nat,
    BilledForMonth: Nat
]

BillQueueItem == [
    user: USERS,
    fee: Fees
]

TypeOk ==
    /\ EventsOk
    /\ month \in Month
    /\ database.users \in [USERS -> UserRow]
    /\ database.billQueue \in Seq(BillQueueItem)


(***************************************************************************)
(* API endpoints                                                           *)
(***************************************************************************)

StartSubscription(u) ==
    /\ database.user[u].subscribed = FALSE
    /\ database' = [database EXCEPT 
                        !["users"][u].subscribed = TRUE]
    \* Observability required by stub
    /\ events' = Append(events, [type |-> "startsubscription", user |-> u])
    /\ UNCHANGED month


CancelSubscription(u) ==
    /\ database.users[u].subscribed = TRUE
    /\ database' = 
        [database EXCEPT 
            !["users"][u].subscribed = FALSE,
            !["billQueue"] = 
                Append(database.billQueue,
                    [user |-> u, fee |-> CancellationFee])
        ]

    \* Observability required by stub
    /\ events' = Append(events, [type |-> "cancelsubscription", user |-> u])
    /\ UNCHANGED <<month>>


StartTrial(u) ==
    /\ database.users[u].inTrail = FALSE
    /\ database.users[u].subscribed = FALSE
    /\ database' = [database EXCEPT 
                        !["users"][u].inTrial = TRUE]

    \* Observability required by stub
    /\ events' = Append(events, [type |-> "starttrial", user |-> u])
    /\ UNCHANGED <<month>>


CancelTrial(u) ==
    /\ database.users[u].inTrial = TRUE
    /\ database' = [database EXCEPT 
                        !["users"][u].inTrial = FALSE
                   ]

    \* Observability required by stub
    /\ events' = Append(events, [type |-> "canceltrial", user |-> u])
    /\ UNCHANGED <<month>>


WatchVideo(u) ==
    /\ \/ database.users[u].subscribed = TRUE
       \/ database.users[u].inTrial = TRUE

    \* Observability required by stub
    /\ events' = Append(events, [type |-> "watchvideo", uesr |-> u])
    /\ UNCHANGED <<month, database>>


\* Stub method, do not change
Bill(u, fee) == 
    /\ events' = Append(events, [type |-> "bill", user |-> u, fee |-> fee])


PaymentFailed(u, fee) ==
    /\ database' = [database EXCEPT 
                        !["users"][u].subscribed = FALSE
                   ]

    \* Observability required by stub
    /\ events' = Append(events, [type |-> "paymentfailed", user |-> u, fee |-> fee])
    /\ UNCHANGED <<month>>


(***************************************************************************)
(* Recurring Operations                                                    *)
(***************************************************************************)

\* This is the state that calls the Payment Failed API
ExistingBillFailed ==
    \/ \E i \in 1..Len(events):
        \* Only a past bill can fail
        /\ events[i] \in BillEvent
        /\ PaymentFailed(events[i].user, events[i].fee)


BillSubscribedUsers == 
    \E u \in USERS:
        \* That is subscribed
        /\ \/ database.users[u].subscribed = TRUE
           \* Subscribed from a trail so bill
           \/ /\ database.users[u].inTrial = TRUE
              /\ database.users[u].trialStartTime < month
        \* Ensure users are not double billed
        /\ database.users[u].billedForMonth < month
        /\ database' = 
            [database EXCEPT 
                \* Add subscription fee
                !["billQueue"] =
                    Append(database.billQueue,
                        [user |-> u, fee |-> SubscriptionFee]),
                !["users"][u].billedForMonth = month    
            ]


ProcessBills = 
    /\ Len(database.billQueue) > 0
    /\ LET bill == Head(database.billQueue) IN 
        \* Bills user
        /\ Bill(bill.user, bill.fee)
        /\ database' = 
            [database EXCEPT 
                \* Removes head of queue
                !["billQueue"] = 
                    SubSeq(database.billQueue,
                        2, Len(database.billQueue))
            ]


(***************************************************************************)
(* Stub method that prevents the month from passing until all operations   *)
(* are complete. Represent worker methods, etc                             *)
(***************************************************************************)
HandledMonth ==
    /\ ~ENABLED BillSubscribedUsers
    /\ ~ENABLED ProcessBills


\* DO NOT MODIFY
MonthPasses ==
    /\ HandledMonth
    /\ month' = month + 1
    /\ events' = Append(events, [type |-> "monthpass"])
    /\ UNCHANGED <<database>>


(***************************************************************************)
(* Specification                                                           *)
(***************************************************************************)
Init ==
    /\ events == <<>> \* Events must be intialized empty, per stub
    /\ month = 0
    /\ database = [
        \* Users start with everything unset
        users |-> 
            [u \in USERS |->
                [
                    subscribed |-> FALSE,
                    inTrial |-> FALSE,
                    trialStartTime |-> 0,
                    billedForMonth |-> 0
                ]
            ],
        \* Bill queue starts empty
        billQueue |-> <<>>
    ]


Next ==
    \* Required by stub
    \/ MonthPasses
    \* State modified below
    \/ \E u \in USERS:
        \/ StartSubscription(u)
        \/ CancelSubscription(u)
        \/ StartTrial(u)
        \/ CancelTrial(u)
        \/ WatchVideo(u)
        \* Add more user based states
    \* Payment failing behavior is part of spec not implementation
    \/ ExistingBillFailed
    \/ BillSubscribedUsers
    




====