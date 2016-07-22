
Ltac Debug_Level := 0.

Tactic Notation "debug" int_or_var(level) tactic3(tac) :=
  let dl := Debug_Level in
  tryif guard dl >= level
  then tac
  else idtac.

Tactic Notation "oc" open_constr(x) := idtac.

Tactic Notation "debugif" tactic3(tac1) "then" int_or_var(level) tactic2(dtac) :=
  unshelve oc(_:True);revgoals;[tac1|debug level dtac; exact I].
