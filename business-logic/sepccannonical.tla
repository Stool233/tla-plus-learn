---- MODULE sepccannonical ----
EXTENDS Naturals, Sequences, FiniteSets

(***************************************************************************)
(* Redeclaration of specdatamodels variables                               *)
(***************************************************************************)


VARIABLE events

CONSTANT USERS

CONSTANTS 
    SubscriptionFee,
    CancellationFee,
    FailedPaymentFee

(***************************************************************************)
(* Logic to Test                                                           *)
(* Replace stubs below with implementation. Because there is no forward    *)
(* declaration, we invert what we'd ideally like to do, which is to import *)
(* the requirements into each implementation, Our logic testing relies on  *)
(* determining if a given state is enabled or not.                         *)
(***************************************************************************)

VARIABLE database, month
INSTANCE stubs


Sepc == Init /\ [][Next]_vars


(***************************************************************************)
(* Trace requirements to specification                                     *)
(*                                                                         *)
(* Not Traceable                                                           *)
(*     Functional: 1,2,3,6,7,9,14                                          *)
(*     NonFunctional: 1,2,3                                                *)
(***************************************************************************)

\* 用户u在执行到第end个事件时，处于“试用中”状态
InTrail(u, end) ==
    \E i \in 1..end:
        /\ events[i] \in StartTrialEvent \* Has started trial 有一个开始试用事件
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
                CancelTrailEvent \union 
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

\* 用户u在在事件i之后, 直到end时, 处于“未订阅”状态 
UnsubscribedAfterEvent(u, i, end) ==
    \E j \in i..end: \* And not unsubscribed after 
        /\ events[j] \notin MonthPassEvent \* 
        /\ events[j].user = u \* 该事件的用户是u
        (************************************************************)
        (* Cancel Subscription endpoint request                     *)
        (* 取消订阅请求                                                *)
        (* 4.2.1 User SHALL be Not Subscribed at the end of the     *)
        (*       current month                                      *)
        (* 用户不能在当前月结束时仍处于订阅状态                           *)
        (************************************************************)
        /\ \/ /\ events[j] \in CancelSubscriptionEvent \* 事件i到end，有“取消订阅”事件
              /\ \E k \in j..end: events[k] \in MonthPassEvent \* 事件j到end，有月份过渡事件
           (************************************************************)
           (* 16. User has payment failed                              *)
           (* 16.1 mark the User as Not Subscribed                     *)
           (* 支付失败，用户标记为未订阅                                   *)
           (************************************************************)
           \/ events[j] \in PaymentFailedEvent  \* 事件i到end，有“支付失败”事件


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


AboutToCancel(u, end) ==
    \E i \in 1..end:
        /\ events[i] \in CancelSubscriptionEvent
        /\ ~\E j \in 1..end:
            events[j] \in MonthPassEvent \union 
                          StartSubscriptionEvent


SubscribedFromTrial(u, end) ==
    (*******************************************************************)
    (* 11 [Partial] When a User is In Trial at the end of the month    *)
    (*    that the trial was started, they SHALL be Subscribed         *)
    (*******************************************************************)
    \E i \in 1..end:
        /\ events[i] \in StartTrialEvent \* Has started trial
        /\ events[i].user = u
        /\ ~InTrail(u, end) \* Requirement fulfilled through InTrial
        /\ ~UnsubscribedAfterEvent(u, i, end)
        (************************************************************)
        (* Cancel Trial endpoint request                            *)
        (* 8.2 [Partial] If the requesting User is In Trial, the    *)
        (*     User SHALL be Not Subscribed                         *)
        (************************************************************)
        /\ ~\E j \in i..end: \* And not canceled
            /\ events[j] \in CancelTrialEvent
            /\ events[j].user = u


Subscribed(u, end) ==
    \/ SubscribedFromStartSubscription(u, end)
    \/ SubscribedFromTrial(u, end)


(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)


(***************************************************************************)
(* 2 When a request is received by the Start Subscription endpoint         *)
(***************************************************************************)
StartSubscriptionAccessControl ==
    \A u \in USERS:
        LET authorized == ~Subscribed(u, Now) \/ AboutToCancel(u, Now) IN 
        (*******************************************************************)
        (* 2.1: If the requesting User is Subscribed, the request SHALL    *)  
        (*      return with 409 Conflict                                   *)
        (*******************************************************************)
        \/ /\ ~authorized
           /\ ~ENABLED StartSubscription(u)

        (*******************************************************************)
        (* 2.2 [Partial]: If the requesting User is In Trial, the trial    *)
        (*      SHALL end and the requesting User SHALL be Subscribed      *)
        (*******************************************************************)
        (*******************************************************************)
        (* 2.3: If the requesting User is Not Subscribed, the requesting   *)
        (*        User SHALL be Subscribed                                 *)
        (*******************************************************************)
        \/ /\ authorized
           /\ ENABLED StartSubcription(u)


(***************************************************************************)
(* 4 When a request is received by the Cancel Subscription endpoint        *)
(***************************************************************************)
CancelSubscriptionAccessControl ==
    \A u \in USERS:
        LET authorized == Subscribed(u, Now) /\ ~AboutToCancel(u, Now) IN 
        (*******************************************************************)
        (* 4.1 If the requesting User is not Subscribed, the request SHALL *)
        (*     return with 409 Conflict                                    *)
        (*******************************************************************)
        \/ /\ ~authorized
           /\ ~ENABLED CancelSubscription(u)
        (*******************************************************************)
        (* 4.2 [Partial]: If the requesting User is Subscribed, the User   *)  
        (*      SHALL ... [Cancellation Requirements]                      *)
        (*******************************************************************)
        \/ /\ authorized
           /\ ENABLED CancelSubscription(u)


(***************************************************************************)
(* 6.3 [Partial] If the requesting User is has never been Subscribed,      *)
(*      or is In Trial                                                     *)
(***************************************************************************)
EligibleForTrial(u) ==
    ~\E i \in 1..Len(events):
        /\ events[i] \in 
            StartSubscriptionEvent \union 
            StartTrialEvent
        /\ evnets[i].user = u


(***************************************************************************)
(* 6 When a request is received by the Start Trial endpoint                *)
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
        \/ /\ ~EligibleForTrial(u)
           /\ ~ENABLED StartTrial(u)
        (*******************************************************************)
        (* 6.3 If the requesting User has never been Subscribed or         *)
        (*     In Trial, that User SHALL be In Trial                       *)
        (*******************************************************************) 
        \/ /\ EligibleForTrial(u)
           /\ ENABLED StartTrial(u)


(***************************************************************************)
(* 8 When a request is received by the Cancel Trial endpoint               *)
(***************************************************************************)
CancelTrialAccessControl == 
    \A u \in USERS:

        (*******************************************************************)
        (* 8.1 If the requesting User is not In Trial, the request SHALL   *)
        (*     return with 409 Conflict                                    *)
        (*******************************************************************) 
        \/ /\ ~InTrail(u, Now)
           /\ ~ENABLED CancelTrial(u)

        (*******************************************************************)
        (* 8.2 [Partial] If the requesting User is In Trial, the User      *)
        (*     SHALL be Not Subscribed                                     *)
        (*******************************************************************)
        \/ /\ InTrial(u, Now)
           /\ ENABLED CancelTrial(u)


(***************************************************************************)
(* 10 When a request is received by the Watch Video endpoint               *)
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
        \/ /\ InTrial(u, Now) \/ Subscribed(u, Now)
           /\ ENABLED WatchVideo(u)


(***************************************************************************)
(* Runs a given operation between: 1 - first month for the first month,    *) 
(* and month i - month i + 1                                               *)
(***************************************************************************)
TrueForEveryUserMonth(op(_,_,_), checkFirstMonth) ==
    LET numMonthPass == Cardinality({i \in 1..Len(events): events[i]
                                                \in MonthPassEvent})
    IN 
    \* If checking the first month
    /\ \/ ~checkFirstMonth
       \/ /\ checkFirstMonth
       \* There does not exist
          /\ ~\E i \in 1..Len(events):
            \* a first month
            /\ events[i] \in MonthPassEvent
            /\ ~\E j \in 1..i: event[j] \in MonthPassEvent
            \* Where the op is false for any user
            /\ \E u \in USERS:
                ~op(u,1,i)
    
    \* There does not exist a pair of consecutive months
    /\ ~\E i \in 1..Len(events):
        /\ events[i] \in MonthPassEvent
        /\ \E j \in i+1..Len(events):
            /\ events[j] \in MonthPassEvent
            /\ ~\E k \in (i + 2)..(j - 1):
                events[k] \in MonthPassEvent
            \* where op is not true for all users
            /\ \E u \in USERS
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
            /\ event[i] \in BillEvent
            /\ event[i].user = u
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
          \* If the user failed a payment this is a seperate workflow
          \/ \E i \in start..end:
                /\ events[i] \in PaymentFailedEvent
                /\ events[i].user = u


SubscribedUsersBilledStartOfMonth == 
    TrueForEveryUserMonth(SubscribedUserBilledThisMonth, FALSE)


(***************************************************************************)
(* 12.2     If the requesting User has Post Due Payments they SHALL be     *)
(*          Billed in that amount before the end of the month, and         *)
(*          Post Due Payments shall be zeroed                              *)
(***************************************************************************)
(***************************************************************************)
(* 16  When a callback is received to the Payment Failed endpoint for a    *)
(*     User, the system SHALL                                              *)
(*     16.2 set Post Due Payment for the User to:                          *)
(*          (failed payment amount) + CancellationFee                      *)
(***************************************************************************)

PotentailStartingEvent(u, event) ==
    /\ event \in StartSubscriptionEvent \union 
                 StartTrailEvent
    /\ event.user = u

IsPaymentFailedEvent(u, event) ==
    /\ event \in PaymentFailedEvent
    /\ event.user = u

UserBilledForFailureBetweenRange(u, start, end, fee) ==
    \E i \in start..end:
        /\ events[i] \in BillEvent
        /\ events[i].user = u
        /\ events[i].fee = FailedPaymentFee

UserBilledForPostDuePaymentsIfSubscribed(u, start, end) ==
    LET starts == {i \in 1..start: PotentailStartingEvent(u, events[i])} IN 
    LET paymentFailed == {i \in 1..start: IsPaymentFailedEvent(u, events[i])} IN 

    \A p \in paymentFailed:

        LET resubscribedAfterFailedPayment ==
            \E i \in p..end:
                /\ i \in starts
        IN 

        \/ ~resubscribedAfterFailedPayment
        \/ /\ resubscribedAfterFailedPayment
            \* There doesn't exist a failed payment
            /\ ~\E i \in p..end:
                \* That has a subscription directly after it
                /\ i \in starts
                /\ ~\E j \in p..i:
                    j \in starts
                \* Where the user was not billed for the failed payment
                /\ ~UserBilledForFailureBetweenRange(u, i, end, events[p].fee)

SubscribedUsersBilledPostDuePayments = 
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
          \* If the user failed a payment this is a separete workflow
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
    LET monthPassEvents == SelectSeq(events, LAMBDA x : x.type = "monthpass")
    IN 
    Len(monthPassEvents) < 5


StateLimit ==
    /\ EventLengthLimit
    /\ MonthLimit

====