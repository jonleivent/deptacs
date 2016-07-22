(* Sandbox tacticals that execute a tactic within a sandbox that will not
impact the overall proof term.  The tactics executed within can pass a value
back to the caller via their "giving" tactic argument.  The Magic sandbox also
allows the tactic to use the wave_want tactic to prove anything.  *)

Require Import utils.

Local Record Sandbox : Prop := {}.

(*see bug 4957 for why we need to redefine unify:*)
Local Tactic Notation "unify" uconstr(X) uconstr(Y) :=
  let unused := constr:(eq_refl:X=Y) in idtac.

(*tac should take a single tactic arg, and call that tactic on a value it
wants to give back to the caller:*)
Ltac sandbox_value tac :=
  lazymatch
    constr:(
      ltac:(
        let V := fresh in
        refine (let V := _ in _);
        let e := get_value V in
        let giving value := unify value e in
        let unused := constr:(ltac:(clear V;
                                   tac giving;
                                   intros; constructor)
                             : Sandbox) in
        exact e)) with
    (let _ := _ in ?R) => R end.

Local Definition Magic := forall T, T.
(*Keep Magic opaque to prevent inadvertent use:*)
Opaque Magic.

Ltac wave_wand :=
  (*use Magic, if it exists:*)
  apply (ltac:(assumption) : forall T, T).

(*Like sandbox_value, but with magical powers - tac can call wave_wand to get
whatever it wants:*)
Ltac magic_sandbox_value tac :=
  lazymatch
    constr:(
      ltac:(
        let V := fresh in
        refine (let V := _ in _);
        let e := get_value V in
        let giving value := unify value e in
        let unused := constr:(ltac:(clear V; intros ?wand;
                                   tac giving;
                                   intros; constructor)
                             : Magic -> Sandbox) in
        exact e)) with
    (let _ := _ in ?R) => R end.
