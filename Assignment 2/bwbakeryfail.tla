---------------------------- MODULE bwbakeryfail ----------------------------
(***************************************************************************)
(* Process-failure variant of the Black-White Bakery model.                *)
(*                                                                         *)
(* This module EXTENDS bwbakery and adds nothing to its PlusCal block, so  *)
(* the graded 3-process no-failure model is reused verbatim.  Failure is   *)
(* introduced purely as an extra raw-TLA+ action.                          *)
(*                                                                         *)
(* A broken-down process is parked at the control value pc[i] = "crashed". *)
(* Every action of the translated algorithm is guarded by pc[self] = L for *)
(* some label L of Algorithm 2, and "crashed" is not one of those labels,  *)
(* so a crashed process has no enabled action: it takes no further step    *)
(* for the rest of the behaviour, and its weak-fairness conjunct is        *)
(* vacuously satisfied.  No new variable is needed.                        *)
(***************************************************************************)
EXTENDS bwbakery

Crashed(i) == pc[i] = "crashed"

(* Guard restricting the model to at most one broken-down process, as the   *)
(* question asks about one failure among the three.                         *)
NoneCrashedYet == \A i \in Procs : ~ Crashed(i)

(***************************************************************************)
(* Variant A -- "clean" failure.  Lamport [1] assumes that a failed         *)
(* processor goes to its noncritical section and that reads from its memory *)
(* eventually return zero.  The failure therefore releases the ticket and   *)
(* lowers the doorway flag.                                                 *)
(***************************************************************************)
CrashZero(self) == /\ NoneCrashedYet
                   /\ pc'       = [pc       EXCEPT ![self] = "crashed"]
                   /\ choosing' = [choosing EXCEPT ![self] = FALSE]
                   /\ number'   = [number   EXCEPT ![self] = 0]
                   /\ UNCHANGED << color, mycolor, j >>

(***************************************************************************)
(* Variant B -- "frozen" failure.  The registers keep whatever they held at *)
(* the instant of the breakdown, so a ticket taken at line 3 or a doorway   *)
(* flag raised at line 1 is never released.                                 *)
(***************************************************************************)
CrashFreeze(self) == /\ NoneCrashedYet
                     /\ pc' = [pc EXCEPT ![self] = "crashed"]
                     /\ UNCHANGED << color, choosing, number, mycolor, j >>

NextZero   == Next \/ (\E self \in Procs : CrashZero(self))
NextFreeze == Next \/ (\E self \in Procs : CrashFreeze(self))

(* Fairness is unchanged from bwbakery, and is deliberately NOT placed on   *)
(* the crash actions: a failure is permitted but never forced, so runs in   *)
(* which nobody breaks down are still part of the model.                    *)
Fairness == \A self \in Procs : WF_vars(Active(self))

SpecZero   == Init /\ [][NextZero]_vars   /\ Fairness
SpecFreeze == Init /\ [][NextFreeze]_vars /\ Fairness

-----------------------------------------------------------------------------
(***************************************************************************)
(* Properties for the surviving processes.                                 *)
(***************************************************************************)

(* Mutex is stated exactly as in bwbakery: a crashed process is not in its  *)
(* critical section, so no relativisation is needed.                        *)
MutexF == [] \A i, k \in Procs : (i # k) => ~ ((pc[i] = "cs") /\ (pc[k] = "cs"))

(* Liveness, relativised to the survivors: a process that begins its entry  *)
(* code eventually reaches its critical section unless it is the process    *)
(* that breaks down.                                                        *)
LivenessF ==
  \A i \in Procs : [] ((pc[i] = "e1") => <>((pc[i] = "cs") \/ Crashed(i)))

=============================================================================
