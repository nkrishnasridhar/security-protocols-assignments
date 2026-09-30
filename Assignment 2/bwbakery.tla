------------------------------ MODULE bwbakery ------------------------------
(***************************************************************************)
(* The Black-White Bakery algorithm (Taubenfeld [2], Algorithm 2, p.62)     *)
(* modelled for N concurrent processes.  Set N <- 3 in the TLC model.       *)
(*                                                                         *)
(* Label / line correspondence with Algorithm 2:                           *)
(*                                                                         *)
(*   ncs        remainder section                                          *)
(*   e1 .. e4   doorway   (lines 1-4)                                      *)
(*   e5 .. e10  waiting   (lines 5-10)                                     *)
(*   cs         critical section (line 11)                                 *)
(*   x12, x13   exit section (lines 12-13)                                 *)
(***************************************************************************)
EXTENDS Integers

CONSTANT N                      \* number of processes; set N <- 3 in the model

Procs  == 1..N                  \* process identifiers, as in the paper's 1..n
Colors == {"black", "white"}

(* Maximum of a non-empty finite set of integers.  Used at line 3.  The set  *)
(* passed in is never empty: process self always satisfies the colour test.  *)
Max(S) == CHOOSE x \in S : \A y \in S : y <= x

(* Lexicographic order on ticket pairs.  TLA+ has no built-in ordering on    *)
(* tuples, so [a,b] < [c,d] must be defined explicitly.  This is the same    *)
(* definition given for the bakery algorithm in the week 5 lecture slides.   *)
Less(a, b, c, d) == (a < c) \/ ((a = c) /\ (b < d))

(* [a,b] >= [c,d], the comparison used in line 8 of Algorithm 2. *)
Geq(a, b, c, d) == ~ Less(a, b, c, d)

(*********

--algorithm bwbakery {

  variables
    color    \in Colors ,                     \* the single extra shared bit
    choosing =  [i \in Procs |-> FALSE] ,     \* doorway flags, initially false
    number   =  [i \in Procs |-> 0] ,         \* ticket numbers, initially 0
    mycolor  \in [Procs -> Colors] ;          \* ticket colours, initially immaterial

  process (P \in Procs)
    variables j = 1 ;                         \* the paper's loop index, process-local
  {
    ncs: while (TRUE) {
           skip ;                             \* remainder section

      e1:  choosing[self] := TRUE ;           \* line 1  -- doorway opens
      e2:  mycolor[self] := color ;           \* line 2
      e3:  number[self] := 1 + Max({ number[k] : k \in {q \in Procs : mycolor[q] = mycolor[self]} }) ;
                                              \* line 3
      e4:  choosing[self] := FALSE ;          \* line 4  -- doorway closes
           j := 1 ;                           \* line 5  -- loop initialisation

      e5:  while (j <= N) {                   \* line 5  -- for j = 1 to n

      e6:    await choosing[j] = FALSE ;      \* line 6

      e7:    if (mycolor[j] = mycolor[self]) {                                            \* line 7

      e8:      await (number[j] = 0) \/ Geq(number[j], j, number[self], self) \/ (mycolor[j] # mycolor[self]) ;
                                              \* line 8  -- same colour: lexicographic order
             } else {

      e9:      await (number[j] = 0) \/ (mycolor[self] # color) \/ (mycolor[j] = mycolor[self]) ;
                                              \* line 9  -- different colour: order set by the colour bit
             } ;

      e10:   j := j + 1 ;                     \* line 10 -- od
           } ;

      cs:  skip ;                             \* line 11 -- critical section

      x12: if (mycolor[self] = "black") {     \* line 12 -- flip the colour bit away from my ticket
             color := "white"
           } else {
             color := "black"
           } ;

      x13: number[self] := 0 ;                \* line 13 -- release the ticket
    }
  }
}

*********)
\* BEGIN TRANSLATION (chksum(pcal) = "55b9d506" /\ chksum(tla) = "89f44690")
VARIABLES color, choosing, number, mycolor, pc, j

vars == << color, choosing, number, mycolor, pc, j >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ color \in Colors
        /\ choosing = [i \in Procs |-> FALSE]
        /\ number = [i \in Procs |-> 0]
        /\ mycolor \in [Procs -> Colors]
        (* Process P *)
        /\ j = [self \in Procs |-> 1]
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "e1"]
             /\ UNCHANGED << color, choosing, number, mycolor, j >>

e1(self) == /\ pc[self] = "e1"
            /\ choosing' = [choosing EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "e2"]
            /\ UNCHANGED << color, number, mycolor, j >>

e2(self) == /\ pc[self] = "e2"
            /\ mycolor' = [mycolor EXCEPT ![self] = color]
            /\ pc' = [pc EXCEPT ![self] = "e3"]
            /\ UNCHANGED << color, choosing, number, j >>

e3(self) == /\ pc[self] = "e3"
            /\ number' = [number EXCEPT ![self] = 1 + Max({ number[k] : k \in {q \in Procs : mycolor[q] = mycolor[self]} })]
            /\ pc' = [pc EXCEPT ![self] = "e4"]
            /\ UNCHANGED << color, choosing, mycolor, j >>

e4(self) == /\ pc[self] = "e4"
            /\ choosing' = [choosing EXCEPT ![self] = FALSE]
            /\ j' = [j EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "e5"]
            /\ UNCHANGED << color, number, mycolor >>

e5(self) == /\ pc[self] = "e5"
            /\ IF j[self] <= N
                  THEN /\ pc' = [pc EXCEPT ![self] = "e6"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << color, choosing, number, mycolor, j >>

e6(self) == /\ pc[self] = "e6"
            /\ choosing[j[self]] = FALSE
            /\ pc' = [pc EXCEPT ![self] = "e7"]
            /\ UNCHANGED << color, choosing, number, mycolor, j >>

e7(self) == /\ pc[self] = "e7"
            /\ IF mycolor[j[self]] = mycolor[self]
                  THEN /\ pc' = [pc EXCEPT ![self] = "e8"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "e9"]
            /\ UNCHANGED << color, choosing, number, mycolor, j >>

e8(self) == /\ pc[self] = "e8"
            /\ (number[j[self]] = 0) \/ Geq(number[j[self]], j[self], number[self], self) \/ (mycolor[j[self]] # mycolor[self])
            /\ pc' = [pc EXCEPT ![self] = "e10"]
            /\ UNCHANGED << color, choosing, number, mycolor, j >>

e9(self) == /\ pc[self] = "e9"
            /\ (number[j[self]] = 0) \/ (mycolor[self] # color) \/ (mycolor[j[self]] = mycolor[self])
            /\ pc' = [pc EXCEPT ![self] = "e10"]
            /\ UNCHANGED << color, choosing, number, mycolor, j >>

e10(self) == /\ pc[self] = "e10"
             /\ j' = [j EXCEPT ![self] = j[self] + 1]
             /\ pc' = [pc EXCEPT ![self] = "e5"]
             /\ UNCHANGED << color, choosing, number, mycolor >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "x12"]
            /\ UNCHANGED << color, choosing, number, mycolor, j >>

x12(self) == /\ pc[self] = "x12"
             /\ IF mycolor[self] = "black"
                   THEN /\ color' = "white"
                   ELSE /\ color' = "black"
             /\ pc' = [pc EXCEPT ![self] = "x13"]
             /\ UNCHANGED << choosing, number, mycolor, j >>

x13(self) == /\ pc[self] = "x13"
             /\ number' = [number EXCEPT ![self] = 0]
             /\ pc' = [pc EXCEPT ![self] = "ncs"]
             /\ UNCHANGED << color, choosing, mycolor, j >>

P(self) == ncs(self) \/ e1(self) \/ e2(self) \/ e3(self) \/ e4(self)
              \/ e5(self) \/ e6(self) \/ e7(self) \/ e8(self) \/ e9(self)
              \/ e10(self) \/ cs(self) \/ x12(self) \/ x13(self)

Next == (\E self \in Procs: P(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

-----------------------------------------------------------------------------
(***************************************************************************)
(* Correctness properties.                                                 *)
(***************************************************************************)

(* The ticket space is bounded by {0,...,N} x {black, white}.  Algorithm 2  *)
(* does not enforce this in code -- it is a consequence of the colouring -- *)
(* so we assert it and let TLC confirm it.                                  *)
TypeOK == /\ color    \in Colors
          /\ choosing \in [Procs -> BOOLEAN]
          /\ mycolor  \in [Procs -> Colors]
          /\ number   \in [Procs -> 0..N]

(* Mutex: no two of the processes are ever in their critical sections       *)
(* (line 11 of Algorithm 2) at the same time.                               *)
Mutex == [] \A i, k \in Procs : (i # k) => ~ ((pc[i] = "cs") /\ (pc[k] = "cs"))

(* Liveness: any process that begins executing the entry code (line 1)      *)
(* eventually enters its critical section.                                  *)
Liveness == \A i \in Procs : [] ((pc[i] = "e1") => <>(pc[i] = "cs"))

-----------------------------------------------------------------------------
(***************************************************************************)
(* Fairness.                                                               *)
(*                                                                         *)
(* Active(self) collects every action of process self OUTSIDE its          *)
(* remainder section.  Fairness is imposed on Active only, never on        *)
(* ncs(self), so a process is still free to stay in -- or halt in -- its    *)
(* non-critical section for ever (Dijkstra's first criterion).             *)
(*                                                                         *)
(* FairSpec is defined below the translation on purpose: re-running         *)
(* "Translate PlusCal Algorithm" overwrites Spec but leaves this intact.    *)
(***************************************************************************)

Active(self) == \/ e1(self)  \/ e2(self) \/ e3(self) \/ e4(self) \/ e5(self)
                \/ e6(self)  \/ e7(self) \/ e8(self) \/ e9(self) \/ e10(self)
                \/ cs(self)  \/ x12(self) \/ x13(self)

FairSpec == Spec /\ \A self \in Procs : WF_vars(Active(self))

=============================================================================
