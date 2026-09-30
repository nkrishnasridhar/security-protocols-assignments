------------------------------ MODULE Beverage ------------------------------
(* TLA+ model of the week-3 beverage machine.
   State labels are boolean variables (one-hot encoding of the four states).
   Transition actions are the named operators on the edges.
   No fairness: Spec is Init /\ [][Next]_vars only. *)

VARIABLES pay, select, coke, sprite

vars == << pay, select, coke, sprite >>

TypeOK ==
    /\ pay    \in BOOLEAN
    /\ select \in BOOLEAN
    /\ coke   \in BOOLEAN
    /\ sprite \in BOOLEAN
    /\ \/ ( pay /\ ~select /\ ~coke /\ ~sprite)
       \/ (~pay /\  select /\ ~coke /\ ~sprite)
       \/ (~pay /\ ~select /\  coke /\ ~sprite)
       \/ (~pay /\ ~select /\ ~coke /\  sprite)

Init ==
    /\ pay    = TRUE
    /\ select = FALSE
    /\ coke   = FALSE
    /\ sprite = FALSE

(* pay --insert_coin--> select *)
InsertCoin ==
    /\ pay     = TRUE
    /\ pay'    = FALSE
    /\ select' = TRUE
    /\ UNCHANGED << coke, sprite >>

(* select --tau--> coke *)
TauCoke ==
    /\ select  = TRUE
    /\ select' = FALSE
    /\ coke'   = TRUE
    /\ UNCHANGED << pay, sprite >>

(* select --tau--> sprite *)
TauSprite ==
    /\ select  = TRUE
    /\ select' = FALSE
    /\ sprite' = TRUE
    /\ UNCHANGED << pay, coke >>

(* coke --get_coke--> pay *)
GetCoke ==
    /\ coke  = TRUE
    /\ coke' = FALSE
    /\ pay'  = TRUE
    /\ UNCHANGED << select, sprite >>

(* sprite --get_sprite--> pay *)
GetSprite ==
    /\ sprite  = TRUE
    /\ sprite' = FALSE
    /\ pay'    = TRUE
    /\ UNCHANGED << select, coke >>

Next == InsertCoin \/ TauCoke \/ TauSprite \/ GetCoke \/ GetSprite

Spec == Init /\ [][Next]_vars

(* In all reachable states, if pay = TRUE then eventually coke = TRUE. *)
PayLeadsToCoke == [](pay => <>coke)

=============================================================================
