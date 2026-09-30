------------------------------ MODULE Peterson ------------------------------
EXTENDS Integers
CONSTANT Procs

(*********

--algorithm Peterson {
  variables flag = [i \in Procs |-> FALSE] , turn = 0 ;
  process (P \in Procs) {
    ncs: while (TRUE) {
           skip ; 
    enter: flag[self] := TRUE ; 
       e2: if (flag[1 - self]) {              
       e3:   if (self /= turn) {
       e4:     flag[self] := FALSE ;
               goto e3 
              } 
              else { goto enter }
           } ;
       cs: skip ;
     exit: flag[self] := FALSE ;
       x2: turn := 1 - self 
    }
  }
}

*********)

\* BEGIN TRANSLATION (chksum(pcal) = "c2f57458" /\ chksum(tla) = "77df21ec")
VARIABLES flag, turn, pc

vars == << flag, turn, pc >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ flag = [i \in Procs |-> FALSE]
        /\ turn = 0
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "enter"]
             /\ UNCHANGED << flag, turn >>

enter(self) == /\ pc[self] = "enter"
               /\ flag' = [flag EXCEPT ![self] = TRUE]
               /\ pc' = [pc EXCEPT ![self] = "e2"]
               /\ turn' = turn

e2(self) == /\ pc[self] = "e2"
            /\ IF flag[1 - self]
                  THEN /\ pc' = [pc EXCEPT ![self] = "e3"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << flag, turn >>

e3(self) == /\ pc[self] = "e3"
            /\ IF self /= turn
                  THEN /\ pc' = [pc EXCEPT ![self] = "e4"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "enter"]
            /\ UNCHANGED << flag, turn >>

e4(self) == /\ pc[self] = "e4"
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "e3"]
            /\ turn' = turn

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ UNCHANGED << flag, turn >>

exit(self) == /\ pc[self] = "exit"
              /\ flag' = [flag EXCEPT ![self] = FALSE]
              /\ pc' = [pc EXCEPT ![self] = "x2"]
              /\ turn' = turn

x2(self) == /\ pc[self] = "x2"
            /\ turn' = 1 - self
            /\ pc' = [pc EXCEPT ![self] = "ncs"]
            /\ flag' = flag

P(self) == ncs(self) \/ enter(self) \/ e2(self) \/ e3(self) \/ e4(self)
              \/ cs(self) \/ exit(self) \/ x2(self)

Next == (\E self \in Procs: P(self))

Spec == Init /\ [][Next]_vars /\ SF_vars(P(0)) /\ SF_vars(P(1))

\* END TRANSLATION 


MutualExclusion == ~ ((pc[0] = "cs") /\ (pc[1] = "cs"))

Liveness == \A i \in Procs : []<>(pc[i] = "cs") 

(* Q2.1: from ncs, process 0 eventually enters the critical section. *)
NcsToCs == [](pc[0] = "ncs" => <>(pc[0] = "cs"))

(* Q2.2: from ncs, process 0 eventually reaches the backoff label e4. *)
NcsToE4 == [](pc[0] = "ncs" => <>(pc[0] = "e4"))

============================================================================= 

\* Anything here.