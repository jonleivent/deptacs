
(*redefine Debug_Level to activate debugging:*)
Ltac Debug_Level := 0.

(*Run tac only if Debug_Level >= level:*)
Tactic Notation "Debug" int_or_var(level) tactic3(tac) :=
  let dl := Debug_Level in
  tryif guard dl >= level
  then tac
  else idtac.

Local Tactic Notation "oc" open_constr(x) := idtac.

(*Always run tac1, but if it succeeds and Debug_Level>=level, then run dtac
even inf tac1 completely solves its goal.  Uses an open_constr with True
conclusion to run dtac (instead of an assert, for example) so that it does not
become part of the proof term.*)
Tactic Notation "DebugIf" tactic3(tac1) "then" int_or_var(level) tactic2(dtac) :=
  let dl := Debug_Level in
  tryif guard dl >= level
  then (unshelve oc(_:True);revgoals;[tac1|dtac; exact I])
  else tac1.
