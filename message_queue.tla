--------------------------- MODULE message_queue ---------------------------
EXTENDS TLC, Integers, Sequences
CONSTANTS MaxQueueSize

(*--algorithm message_queue

variable queue = <<>>;

define
    BoundedQueue == Len(queue) <= MaxQueueSize
end define;

process writer = "writer"
begin Write:
    while TRUE do
        queue := Append(queue, "msg");
        await Len(queue) <= MaxQueueSize;
    end while;
end process;

process reader = "reader"
variables current_message = "none";
begin Read:
    while TRUE do
        await queue /= <<>>;
        current_message := Head(queue);
        queue := Tail(queue);
    end while;
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "205e8e8c" /\ chksum(tla) = "fc83c0a7")
VARIABLE queue

(* define statement *)
BoundedQueue == Len(queue) <= MaxQueueSize

VARIABLE current_message

vars == << queue, current_message >>

ProcSet == {"writer"} \cup {"reader"}

Init == (* Global variables *)
        /\ queue = <<>>
        (* Process reader *)
        /\ current_message = "none"

writer == /\ queue' = Append(queue, "msg")
          /\ Len(queue') <= MaxQueueSize
          /\ UNCHANGED current_message

reader == /\ queue /= <<>>
          /\ current_message' = Head(queue)
          /\ queue' = Tail(queue)

Next == writer \/ reader

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Sat Aug 27 17:14:50 CST 2022 by wengjialin
\* Created Sat Aug 27 16:34:14 CST 2022 by wengjialin
