(*
get_paramed_type_head produces the parameterized/index-free portion of the type.
*)

Require Import utils.
Require Import sandbox.

Ltac wrap_typewise T inside :=
  let rec f T :=
      lazymatch type of T with
      | (forall (a : ?X), _) =>
        let a' := fresh a in
        constr:(forall (a' : X), ltac:(let R := f (T a') in exact R))
      | _ => inside T
      end in
  f T.

Ltac common_head trip :=
  lazymatch trip with
  | (?X, ?A, ?A) => X
  | (?F _, ?G1 _, ?G2 _) => common_head (F, G1, G2)
  end.

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
