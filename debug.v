
Ltac Debug_Level := 0.

Tactic Notation "Debug" int_or_var(level) tactic3(tac) :=
  let dl := Debug_Level in
  tryif guard dl >= level
  then tac
  else idtac.

Tactic Notation "oc" open_constr(x) := idtac.

Tactic Notation "DebugIf" tactic3(tac1) "then" int_or_var(level) tactic2(dtac) :=
  let dl := Debug_Level in
  tryif guard dl >= level
  then (unshelve oc(_:True);revgoals;[tac1|dtac; exact I])
  else tac1.
