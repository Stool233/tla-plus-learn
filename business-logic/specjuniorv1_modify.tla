-------------------------------- MODULE specjuniorv1_modify --------------------------------
(***************************************************************************)
(* A single page version for easier testing                                *)
(***************************************************************************)


EXTENDS Sequences, Naturals, FiniteSets

(***************************************************************************)
(* specdatamodels.tla                                                      *)
(***************************************************************************)

(***************************************************************************)
(* An ordered event stream of every event that occurs in the system.       *)
(* All the specifications will be written based on it.                     *)
(* This is an observability value that you wouldn't have access to in the  *)
(* implementation. We'll only have the API method stubs write to it; no    *)
(* implementation may read from it. This will be enforced with code review *)
(***************************************************************************)
VARIABLE events

\* Represents every potential user in the system
CONSTANT USERS

\* Constants that should be set to single model values to allow comparisons.
\* Only equality comparisons will be made.
CONSTANTS
    SubscriptionFee,
    CancellationFee,
    FailedPaymentFee

Fees == {SubscriptionFee, CancellationFee, FailedPaymentFee}

(***************************************************************************)
(* Event Types: Describes everything that can happen in the system         *)
(***************************************************************************)

MonthPassEvent == [type : {"monthpass"}]

StartSubscriptionEvent == [type : {"startsubscription"}, user: USERS]
CancelSubscriptionEvent == [type : {"cancelsubscription"}, user: USERS]

StartTrialEvent == [type : {"starttrial"}, user: USERS]
CancelTrialEvent == [type : {"canceltrial"}, user: USERS]

WatchVideoEvent == [type : {"watchvideo"}, user: USERS]

BillEvent == [type : {"bill"}, user: USERS, fee: Fees]
PaymentFailedEvent == [type : {"paymentfailed"}, user: USERS, fee: Fees]

Event ==
    MonthPassEvent \union
    StartSubscriptionEvent \union
    CancelSubscriptionEvent \union
    StartTrialEvent \union
    CancelTrialEvent \union
    WatchVideoEvent \union
    BillEvent \union
    PaymentFailedEvent

EventsOk ==
    events \in Seq(Event)
    
VARIABLES
    month,
    database

vars == <<events, month, database>>

Now == Len(events)

Months == 0..10

(***************************************************************************)
(* Strong Typing                                                           *)
(***************************************************************************)

Month == Nat

(***************************************************************************)
(* Database Rows                                                           *)
(***************************************************************************)

UserRow == [
    subscribed: BOOLEAN,
    canceled: BOOLEAN,
    inTrial: BOOLEAN,
    trialStartTime: Nat,
    billedForMonth: Nat
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
    /\ database.users[u].subscribed = FALSE
    /\ database' = [database EXCEPT
                        !["users"][u].subscribed = TRUE
                   ]
    \* Observability required by stub
    /\ events' = Append(events, [type |-> "startsubscription", user |-> u])
    /\ UNCHANGED month


CancelSubscription(u) ==
    /\ database.users[u].subscribed = TRUE
    /\ database' = 
        [database EXCEPT
            !["users"][u].subscribed = FALSE,
            !["users"][u].canceled = TRUE,
            !["billQueue"] = 
                Append(database.billQueue, 
                    [user |-> u, fee |-> CancellationFee])
        ]
                   
    \* Observability required by stub
    /\ events' = Append(events, [type |-> "cancelsubscription", user |-> u])
    /\ UNCHANGED <<month>>

    
StartTrial(u) ==
    /\ database.users[u].inTrial = FALSE
    /\ database.users[u].subscribed = FALSE
    /\ database.users[u].canceled = FALSE
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
    /\ events' = Append(events, [type |-> "watchvideo", user |-> u])
    /\ UNCHANGED <<month, database>>

\* Stub method, do not change
Bill(u, fee) ==
    /\ events' = Append(events, [type |-> "bill", 
                                 user |-> u, 
                                 fee |-> fee])

PaymentFailed(u, fee) ==
    /\ database' = [database EXCEPT
                        !["users"][u].subscribed = FALSE
                   ]
    
    \* Observability required by stub
    /\ events' = Append(events, [type |-> "paymentfailed", 
                                 user |-> u , 
                                 fee |-> fee])
    /\ UNCHANGED <<month>>

(***************************************************************************)
(* Recurring Operations                                                    *)
(***************************************************************************)

\* This the the state that calls the Payment Failed API
ExistingBillFailed == 
    \/ \E i \in 1..Len(events):
        \* Only a past bill can fail
        /\ events[i] \in BillEvent
        /\ PaymentFailed(events[i].user, events[i].fee)


BillSubscribedUsers ==
    \E u \in USERS:
        \* That is subscribed
        /\ \/ database.users[u].subscribed = TRUE
           \* Subscribed from a trial so bill
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

ProcessBills ==
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
(* are complete. Represent worker methods, etc.                            *)
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
    /\ events = <<>> \* Events must be initialized empty, per stub
    /\ month = 0
    /\ database = [
            \* Users start with everything unset
            users |-> 
                [u \in USERS |-> 
                   [
                    subscribed |-> FALSE,
                    canceled |-> FALSE,
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

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* spec.tla                                                                *)
(***************************************************************************)

(***************************************************************************)
(* Trace requirements to specification                                     *)
(*                                                                         *)
(*  Not Traceable                                                          *)  
(*      Functional: 1,2,3,6,7,9,14                                         *)
(*      NonFunctional: 1,2,3                                               *)
(***************************************************************************)

(***************************************************************************)
(* Definitions                                                             *)
(***************************************************************************)

\* 用户u在执行到第end个事件时，处于“试用中”状态
InTrial(u, end) ==
    \E i \in 1..end:
        /\ events[i] \in StartTrialEvent \* Has started trial 存在一个开始试用事件
        /\ events[i].user = u \* 该事件的用户是u
        (*******************************************************************)
        (* 6. Start Trial endpoint request 开始试用请求                      *)
        (* 6.3 If the requesting User has never been Subscribed or In      *)
        (*     Trial, that User SHALL be In Trial                          *)
        (* 6.3 如果 请求用户之前从未订阅过或者试用过，那么该用户应该处于试用中状态    *)
        (*******************************************************************)
        /\ ~\E j \in i..end: \* And not canceled 且没有取消试用（试用过程中，如果主动订阅，也算取消了试用）
            /\ events[j] \in 
                (***********************************************************)
                (* 8. Cancel Trial endpoint request                        *)
                (* 8.2 [Partial] If the requesting User is In Trial, the   *)
                (*      User SHALL be Not Subscribed                       *)
                (***********************************************************)
                CancelTrialEvent \union 
                (***********************************************************)
                (* 2. Start Subscription endpoint request                  *)
                (* 2.2 If the requesting User is In Trial, the trial SHALL *)
                (*     end and the requesting User SHALL be Subscribed     *)
                (* 试用过程中，如果主动订阅，也算取消了试用                       *)
                (***********************************************************)
                StartSubscriptionEvent
            /\ events[j].user = u

         (*******************************************************************)
         (* 11. [Partial] When a User is In Trial at the end of the month   *)
         (*     that the trial was started, they SHALL be Subscribed        *)
         (* 当用户在试用月结束时仍处于试用状态，他们应该自动订阅                     *)
         (*******************************************************************)
        /\ ~\E j \in i..end:
            /\ events[j] \in MonthPassEvent


\* 用户u在事件i之后, 直到end时, 处于“未订阅”状态 
\* （看着像尝试订阅后，没有订阅成功、或者订阅后取消了订阅）
UnsubscribedAfterEvent(u, i, end) ==
    \E j \in i..end: \* And not unsubscribed after 
        /\ events[j] \notin MonthPassEvent \* 存在一个不是“月份过渡”的事件j
        /\ events[j].user = u \* 该事件的用户是u
        (************************************************************)
        (* Cancel Subscription endpoint request                     *)
        (* 取消订阅请求                                                *)
        (* 4.2.1 User SHALL be Not Subscribed at the end of the     *)
        (*       current month                                      *)
        (* 用户不能在当前月结束时仍处于订阅状态                           *)
        (************************************************************)
        /\ \/ /\ events[j] \in CancelSubscriptionEvent \* 事件j是“取消订阅”事件
              /\ \E k \in j..end: events[k] \in MonthPassEvent \* 事件j到end，有月份过渡事件，即这个月取消订阅后，下个月就处于未订阅状态
           (************************************************************)
           (* 16. User has payment failed                              *)
           (* 16.1 mark the User as Not Subscribed                     *)
           (* 支付失败，用户标记为未订阅                                   *)
           (************************************************************)
           \/ events[j] \in PaymentFailedEvent  \* 事件j是“支付失败”事件


\* 用户u在开始订阅后，在时间点end仍处于已订阅状态
SubscribedFromStartSubscription(u, end) ==
    (*******************************************************************)
    (* 2.4 If the requesting User is scheduled to be Not Subscribed    *)
    (*     due to cancellation, the requesting User SHALL remain       *)
    (*     Subscribed                                                  *)
    (* Implemented because a StartSubscriptionEvent after Cancel       *)
    (* undoes the cancel.                                              *)
    (*******************************************************************)
    \E i \in 1..end:
        /\ events[i] \in StartSubscriptionEvent \* Has subscribed
        /\ events[i].user = u
        /\ ~UnsubscribedAfterEvent(u, i, end)

\* 用户u在时间end即将取消订阅
AboutToCancel(u, end) ==
    \E i \in 1..end:
        /\ events[i] \in CancelSubscriptionEvent
        /\ ~\E j \in i..end:
            events[j] \in MonthPassEvent \union \* 发生取消订阅事件后，到时间点end没没有发生月份更新事件（即每月订阅确认的时间点）
                          StartSubscriptionEvent \* 发生取消订阅事件后，到时间点end没有重新发起订阅


\* 用户u在试用后，在时间点end，处于已订阅状态
SubscribedFromTrial(u, end) ==
    (*******************************************************************)
    (* 11 [Partial] When a User is In Trial at the end of the month    *)
    (*    that the trial was started, they SHALL be Subscribed         *)
    (*******************************************************************)
    \E i \in 1..end:
        /\ events[i] \in StartTrialEvent \* Has started trial 发生试用事件
        /\ events[i].user = u
        /\ ~InTrial(u, end) \* Requirement fulfilled through InTrial 在时间点end，不处于试用中状态
        /\ ~UnsubscribedAfterEvent(u, i, end) \* 从开始试用（时间点i）到时间点end，没有取消订阅（表示订阅后取消，或者订阅后支付失败）
        (************************************************************)
        (* Cancel Trial endpoint request                            *)
        (* 8.2 [Partial] If the requesting User is In Trial, the    *)
        (*     User SHALL be Not Subscribed                         *)
        (************************************************************)
        /\ ~\E j \in i..end: \* And not canceled
            /\ events[j] \in CancelTrialEvent \* 从开始试用（时间点i）到时间点end，没有取消试用
            /\ events[j].user = u
            


\* 用户u在时间点end，处于已订阅状态       
Subscribed(u, end) == 
    \/ SubscribedFromStartSubscription(u, end)  \* 手动发起订阅事件
    \/ SubscribedFromTrial(u, end) \* 试用到期后自动订阅




(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

(***************************************************************************)
(* 2 When a request is received by the Start Subscription endpoint         *)
(* 当 endpoint“开始订阅”     收到请求时  的AccessControl                       *)
(***************************************************************************)
StartSubscriptionAccessControl ==
    \A u \in USERS:
        LET authorized == ~Subscribed(u, Now) \/ AboutToCancel(u, Now) IN   \* 没有订阅，或者已经发起了取消订阅
        (*******************************************************************)
        (* 2.1: If the requesting User is Subscribed, the request SHALL    *)  
        (*      return with 409 Conflict                                   *)
        (*******************************************************************)
        \/ /\ ~authorized   \* 已订阅，不能再发起订阅
           /\ ~ENABLED StartSubscription(u)     \* ~ENABLED StartSubscription(u) 即StartSubscription为true的条件不成立，即其prime变量没法被赋值

        (*******************************************************************)
        (* 2.2 [Partial]: If the requesting User is In Trial, the trial    *)
        (*      SHALL end and the requesting User SHALL be Subscribed      *)
        (*******************************************************************)
        (*******************************************************************)
        (* 2.3: If the requesting User is Not Subscribed, the requesting   *)
        (*        User SHALL be Subscribed                                 *)
        (*******************************************************************)
        \/ /\ authorized   \* 未订阅，可以发起订阅
           /\ ENABLED StartSubscription(u)

(***************************************************************************)
(* 4 When a request is received by the Cancel Subscription endpoint        *)
(* 当 endpoint“取消订阅”     收到请求时  的AccessControl                       *)
(***************************************************************************)
CancelSubscriptionAccessControl ==
    \A u \in USERS:
        LET authorized == Subscribed(u, Now) /\ ~AboutToCancel(u, Now) IN \* 已订阅，且未发起取消订阅
        (*******************************************************************)
        (* 4.1 If the requesting User is not Subscribed, the request SHALL *)
        (*     return with 409 Conflict                                    *)
        (*******************************************************************)
        \/ /\ ~authorized  \* 未订阅，不能取消订阅
           /\ ~ENABLED CancelSubscription(u)
        (*******************************************************************)
        (* 4.2 [Partial]: If the requesting User is Subscribed, the User   *)  
        (*      SHALL ... [Cancellation Requirements]                      *)
        (*******************************************************************)
        \/ /\ authorized \* 已订阅，可以取消订阅
           /\ ENABLED CancelSubscription(u)


(***************************************************************************)
(* 6.3 [Partial] If the requesting User is has never been Subscribed,      *)
(*      or is In Trial                                                     *)
(***************************************************************************)
\* 具备试用资格
EligibleForTrial(u) ==
    ~\E i \in 1..Len(events):
        /\ events[i] \in
            StartSubscriptionEvent \union
            StartTrialEvent
        /\ events[i].user = u

(***************************************************************************)
(* 6 When a request is received by the Start Trial endpoint                *)
(* 当 endpoint “开始试用”  收到请求时 的AccessControl                          *) 
(***************************************************************************)
StartTrialAccessControl ==
    \A u \in USERS:
        (*******************************************************************)
        (* 6.1 If the requesting User is Subscribed or In Trial, the       *)
        (*     request SHALL return with 409 Conflict                      *)
        (*******************************************************************)
        (*******************************************************************)
        (* 6.2 If the requesting User has previously been Subscribed or    *)
        (*     In Trial, the request SHALL return with 409 Conflict        *)
        (*******************************************************************)   
        \/ /\ ~EligibleForTrial(u) \* 不具备试用资格
           /\ ~ENABLED StartTrial(u)
        (*******************************************************************)
        (* 6.3 If the requesting User has never been Subscribed or         *)
        (*     In Trial, that User SHALL be In Trial                       *)
        (*******************************************************************) 
        \/ /\ EligibleForTrial(u) \* 具备试用资格
           /\ ENABLED StartTrial(u)


(***************************************************************************)
(* 8 When a request is received by the Cancel Trial endpoint               *)
(* 当 endpoint “取消试用”  收到请求时 的AccessControl                          *)
(***************************************************************************)
CancelTrialAccessControl == 
    \A u \in USERS:
                 
        (*******************************************************************)
        (* 8.1 If the requesting User is not In Trial, the request SHALL   *)
        (*     return with 409 Conflict                                    *)
        (*******************************************************************) 
        \/ /\ ~InTrial(u, Now)
           /\ ~ENABLED CancelTrial(u)
                       
        (*******************************************************************)
        (* 8.2 [Partial] If the requesting User is In Trial, the User      *)
        (*     SHALL be Not Subscribed                                     *)
        (*******************************************************************) 
        \/ /\ InTrial(u, Now)
           /\ ENABLED CancelTrial(u)

(***************************************************************************)
(* 10 When a request is received by the Watch Video endpoint               *)
(* 当 endpoint “观看视频” 收到请求时 的AccessControl *)
(***************************************************************************)
WatchVideoAccessControl ==
    \A u \in USERS:
        (*******************************************************************)
        (* 10.1 If the requesting User is not In Trial or Subscribed, the  *)
        (*      request SHALL return with 409 Conflict                     *)
        (*******************************************************************)
        \/ /\ ~InTrial(u, Now) /\ ~Subscribed(u, Now)
           /\ ~ENABLED WatchVideo(u)
        (*******************************************************************)
        (* 10.2 If the requesting User is In Trial or Subscribed, the      *) 
        (*      system SHALL allow the User to Watch Video                 *)
        (*******************************************************************)
        \/ /\ InTrial(u, Now) \/ Subscribed(u, Now)     \* 试用中或者已订阅
           /\ ENABLED WatchVideo(u)

(***************************************************************************)
(* Runs a given operation between: 1 - first month for the first month（第一个事件到第一个月份过渡事件）,    *) 
(* and month i - month i + 1（第i个月份过渡事件 到 i的下一个月份过渡事件）（即两个连续的月份之间）       *)                                        
(* 可能不使用双重否定更容易理解一点，后面尝试下 *)
(***************************************************************************)
TrueForEveryUserMonth(op(_,_,_), checkFirstMonth) ==
    LET numMonthPass == Cardinality({i \in 1..Len(events): events[i]
                                                 \in MonthPassEvent}) \* 当前经过了多少个月（通过月份过渡事件的数量来确定）
    IN
    \* If checking the first month
    /\ \/ ~checkFirstMonth
       \/ /\ checkFirstMonth
        \* There does not exist 
          /\ ~\E i \in 1..Len(events):
            \* a first month
            /\ events[i] \in MonthPassEvent
            /\ ~\E j \in 1..i: events[j] \in MonthPassEvent
            \* Where the op is false for any user
            /\ \E u \in USERS: 
                ~op(u,1,i)

    \* There does not exist a pair of consecutive months
    /\ ~\E i \in 1..Len(events):
        /\ events[i] \in MonthPassEvent
        /\ \E j \in i+1..Len(events):
            \* j是i之后第一个月份过渡事件
            /\ events[j] \in MonthPassEvent
            /\ ~\E k \in (i + 2)..(j-1):          
                events[k] \in MonthPassEvent
            \* where op is not true for all users
            /\ \E u \in USERS:
                ~op(u,i,j)

(***************************************************************************)
(* 15 When a User is Billed the system SHALL call the Bill endpoint        *)
(*    of the Payment Processor.                                            *)
(* This requirement is satisfied by how requirements 4.2.2, 12 and 13      *)
(* are tested. They test that appropriate Bill message was dispatched      *)
(***************************************************************************)

(***************************************************************************)
(* 12 When a User becomes Subscribed                                       *)
(***************************************************************************)

(***************************************************************************)
(* 12.1 they shall be Billed the Subscription Fee before the end of the    *)
(*      month                                                              *)
(***************************************************************************)

SubscribedThisMonth(u, start, end) ==
    /\ ~Subscribed(u, start) 
    /\ Subscribed(u, end-1)

UserSubscribedThisMonthBilledSubscriptionFee(u, start, end) ==
    LET shouldBill == SubscribedThisMonth(u, start, end) IN
    \* Only applies if subscribed this month
    \/ ~shouldBill
    \/ /\ shouldBill
       /\ \E i \in start..end:
            /\ events[i] \in BillEvent
            /\ events[i].user = u
            /\ events[i].fee = SubscriptionFee
    

SubscribedNewUsersBilledSubscriptionFee ==
    TrueForEveryUserMonth(UserSubscribedThisMonthBilledSubscriptionFee, TRUE)

(***************************************************************************)
(* 13 When a User is Subscribed at the start of a month, they shall be     *)
(*    Billed the Subscription Fee                                          *)
(***************************************************************************)
SubscribedUserBilledThisMonth(u, start, end) ==
    LET subscribed == Subscribed(u, start) IN
    \* Only applies if subscribed at start of month
    \/ ~subscribed
    \/ /\ subscribed
       /\ \/ \E i \in start..end:
                /\ events[i] \in BillEvent
                /\ events[i].user = u
                /\ events[i].fee = SubscriptionFee
         \* If the user failed a payment this is a separate workflow
          \/ \E i \in start..end: 
                /\ events[i] \in PaymentFailedEvent
                /\ events[i].user = u


SubscribedUsersBilledStartOfMonth == 
    TrueForEveryUserMonth(SubscribedUserBilledThisMonth, FALSE)

(***************************************************************************)
(* 12.2     If the requesting User has Post Due Payments they SHALL be     *)
(*          Billed in that amount before the end of the month, and         *)
(*          Post Due Payments shall be zeroed                              *)
(* 逾期付款相关 *)
(***************************************************************************)
(***************************************************************************)
(* 16  When a callback is received to the Payment Failed endpoint for a    *)
(*     User, the system SHALL                                              *)
(*     16.2 set Post Due Payment for the User to:                          *)
(*          (failed payment amount) + CancellationFee                      *)
(***************************************************************************)

PotentialStartingEvent(u, event) == 
    /\ event \in StartSubscriptionEvent \union
                 StartTrialEvent
    /\ event.user = u

IsPaymentFailedEvent(u, event) ==
    /\ event \in PaymentFailedEvent
    /\ event.user = u
    
\* fee参数好像没用到
UserBilledForFailureBetweenRange(u, start, end, fee) ==
    \E i \in start..end:
        /\ events[i] \in BillEvent
        /\ events[i].user = u
        /\ events[i].fee = FailedPaymentFee

\* 用户在订阅后，如果有逾期付款，那么在订阅后的这个月内，用户应该按该金额收取费用，且逾期付款应该被清零
\* 逾期付款出现在付款失败后
UserBilledForPostDuePaymentsIfSubscribed(u, start, end) ==
    LET starts == {i \in 1..start: PotentialStartingEvent(u, events[i])} IN
    LET paymentFailed == {i \in 1..start:IsPaymentFailedEvent(u, events[i])} IN
    
    \A p \in paymentFailed:     \* 对于任意一个付款失败事件p

        LET resubscribedAfterFailedPayment ==
            \E i \in p..end:
                /\ i \in starts
        IN

        \/ ~resubscribedAfterFailedPayment \* 在p之后没有重新订阅的事件
        \/ /\ resubscribedAfterFailedPayment \* 在p之后有重新订阅的事件
            \* There doesn't exist a failed payment
            \* 在p之后，到end之间没有其他的付款失败事件
           /\ ~\E i \in p..end: \* 不存在一个i，i在p到end之间满足：
                \* That has a subscription directly after it
                /\ i \in starts     \* i是一个可能的订阅事件
                /\ ~\E j \in p..i:  \* 在p之后，到i之间没有其他的订阅事件
                    j \in starts   \* 
                \* Where the user was not billed for the failed payment
                /\ ~UserBilledForFailureBetweenRange(u, i, end, events[p].fee)  \* 在i到end之间，用户没有支付失败的费用                            

SubscribedUsersBilledPostDuePayements ==
    TrueForEveryUserMonth(UserBilledForPostDuePaymentsIfSubscribed, TRUE)


(***************************************************************************)
(* 4 Cancel Subscription endpoint                                          *)
(* 4.2.2  if the user is Not Subscribed at the end of the current month,   *)
(* they SHALL be Billed a Cancellation Fee                                 *)
(***************************************************************************)
UserCancelledLastMonth(u, start, end) ==
    \* start - 1 because it doesn't count cancellations that take effect
    \* at start
    /\ Subscribed(u, start-1) 
    /\ ~Subscribed(u, start)

UserCancelledLastMonthBilled(u, start, end) ==
    \* Only applies if user cancelled this month
    \/ ~UserCancelledLastMonth(u, start, end)
    \/ /\ UserCancelledLastMonth(u, start, end)
       /\ \/ \E i \in start..end:
                /\ events[i] \in BillEvent
                /\ events[i].user = u
                /\ events[i].fee = CancellationFee
          \* If the user failed a payment this is a separate workflow
          \/ \E i \in start..end: 
                /\ events[i] \in PaymentFailedEvent
                /\ events[i].user = u

CancelingUsersBilledCancelationFees ==
    TrueForEveryUserMonth(UserCancelledLastMonthBilled, FALSE)


(***************************************************************************)
(* State Constraints                                                       *)
(***************************************************************************)

EventLengthLimit ==
    Len(events) < 10


MonthLimit ==
    LET monthPassEvents == SelectSeq(events, LAMBDA x: x.type = "monthpass") 
    IN
    Len(monthPassEvents) < 5

StateLimit ==
    /\ EventLengthLimit
    /\ MonthLimit

=============================================================================
