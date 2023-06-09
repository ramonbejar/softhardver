
------------------------- MODULE concurrent_buffer -------------------------
(******* Example from:
         https://levelup.gitconnected.com/debugging-concurrent-systems-with-a-model-checker-c7eee210d86f
*******)

EXTENDS Naturals, Sequences

CONSTANTS Producers,
          Consumers,
          BufCapacity,
          Data

ASSUME /\ Producers # {}
       /\ Consumers # {}
       /\ Producers \intersect Consumers = {}
       /\ BufCapacity > 0
       /\ Data # {}
----------------------------------------------------------------------------       
VARIABLES buffer, 
          waitSet
          
Participants == Producers  \union Consumers
RunningThreads == Participants \ waitSet

TypeInv == /\ buffer \in Seq(Data)
           /\ Len(buffer) \in 0..BufCapacity
           /\ waitSet \subseteq Participants
           
Notify == IF waitSet /= {}
           THEN \exists x \in waitSet : waitSet' = waitSet \ {x}
           ELSE UNCHANGED waitSet
           
NotifyAll == waitSet' = {}

Wait(t) == waitSet' = waitSet \union {t}            
---------------------------------------------------------------------------

Init == buffer = <<>> /\ waitSet = {}

Put(t,m) == IF Len(buffer) < BufCapacity
            THEN /\ buffer' = Append(buffer,m)
                 /\ Notify
            ELSE /\ Wait(t)
                 /\ UNCHANGED buffer
              
Get(t) == IF Len(buffer) > 0
            THEN /\ buffer' = Tail(buffer)
                 /\ Notify
            ELSE /\ Wait(t)
                 /\ UNCHANGED buffer              
                  
Next == \exists t \in RunningThreads : \/ t \in Producers /\ \exists m \in Data : Put(t,m)
                                       \/ t \in Consumers /\ Get(t)
Prog == Init /\ [][Next]_<< buffer , waitSet >>
-----------------------------------------------------------------------------

NoDeadlock == [](RunningThreads /= {})
THEOREM Prog => []TypeInv /\ NoDeadlock 


=============================================================================
\* Modification History
\* Last modified Thu May 18 13:58:23 CEST 2023 by ramon
\* Created Thu May 18 12:35:44 CEST 2023 by ramon
