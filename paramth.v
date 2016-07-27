(*
get_paramed_type_head produces the parameterized/index-free portion of the type.
*)

Require Import utils.
Require Import sandbox.

(*Given a type functor F, produce a fully parameterized type by wrapping the
result of the inside tactic on F's body with F's parameters.  If F is 
"fun x y => P x (f y)", then this produces the type 
"forall x y, <inside (P x (f y))>"*)
Ltac wrap_typewise F inside :=
  let rec f F :=
      lazymatch type of F with
      | (forall (a : ?X), _) =>
        let a' := fresh a in
        constr:(forall (a' : X), ltac:(let R := f (F a') in exact R))
      | _ => inside F
      end in
  f F.

Ltac common_head trip :=
  lazymatch trip with
  | (?X, ?A, ?A) => X
  | (?F _, ?G1 _, ?G2 _) => common_head (F, G1, G2)
  end.

(*How to segregate a type's indexes from its non-index parameters: Make two
instances of the type with the same fresh type parameters, put one instance in
the conclusion and the other in a hyp, and case that hyp.  The hyp's indexes
don't change, but the conclusion's do.  No non-index parameters change in
either.  Compare the types of the two instances to find where the differ. *)
Ltac get_paramed_type_head_internal T giving :=
  let hT := head_of T in
  let inside C := constr:(C -> C -> True) in
  let w := wrap_typewise hT inside in
  assert w;
  [intros;
   let H := last_hyp in
   revert H;
   let H := last_hyp in
   let TH := type of H in
   (tryif case H
     then [>
           intros;
           let H' := last_hyp in
           let TH' := type of H' in
           let x := common_head (T, TH, TH') in
           giving x|..]
     else giving T);
   intros; exact I
  |].

Ltac get_paramed_type_head T :=
  sandbox_value ltac:(get_paramed_type_head_internal T).
