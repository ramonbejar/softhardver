------------------------------- MODULE Add2FG -------------------------------
EXTENDS Integers

(*********--algorithm Add2FG {    

  variable x = 0 ;

  process (A = 1)
   variable ta = -1 ;
   {
    a1: ta := x;
    a2: x := ta+1 
  }

  process (B = 2)
   variable tb = -1 ;
    {
    b1: tb := x;
    b2: x := tb + 1
  }
}

*********)
\* BEGIN TRANSLATION (chksum(pcal) = "1b626abd" /\ chksum(tla) = "5ff5e3e0")
VARIABLES x, pc, ta, tb

vars == << x, pc, ta, tb >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ x = 0
        (* Process A *)
        /\ ta = -1
        (* Process B *)
        /\ tb = -1
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "a1"
                                        [] self = 2 -> "b1"]

a1 == /\ pc[1] = "a1"
      /\ ta' = x
      /\ pc' = [pc EXCEPT ![1] = "a2"]
      /\ UNCHANGED << x, tb >>

a2 == /\ pc[1] = "a2"
      /\ x' = ta+1
      /\ pc' = [pc EXCEPT ![1] = "Done"]
      /\ UNCHANGED << ta, tb >>

A == a1 \/ a2

b1 == /\ pc[2] = "b1"
      /\ tb' = x
      /\ pc' = [pc EXCEPT ![2] = "b2"]
      /\ UNCHANGED << x, ta >>

b2 == /\ pc[2] = "b2"
      /\ x' = tb + 1
      /\ pc' = [pc EXCEPT ![2] = "Done"]
      /\ UNCHANGED << ta, tb >>

B == b1 \/ b2

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == A \/ B
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

\* Invariant property:
Inv == (pc[1] = "Done") /\ (pc[2] = "Done") => (x = 2)

=============================================================================
\* Modification History
\* Last modified Wed May 17 08:50:32 CEST 2023 by ramon
\* Created Fri Feb 10 15:06:24 CET 2023 by ramon
