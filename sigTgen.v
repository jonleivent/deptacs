(*

sigT_generalize_eqs: A sigT-based (instead of JMeq-based) generalize_eqs
tactic

*)

Require Import utils.
Require Import paramth.

(*Return the possibly nested sigT type needed to dependently analyze term -
only term's type's indexes are given the sigT treatment.*)
Ltac sigT_for term :=
  let T := type of term in
  let pT := get_paramed_type_head T in
  let rec f t h :=
      lazymatch t with
      | pT => h
      | ?F _ =>
        let a := fresh in
        constr:(sigT (fun a => ltac:(let h' := constr:(h a) in
                                  let r := f F h' in exact r)))
      end in
  f T pT.

(*Return the existT of the above sigT for term.*)
Ltac sigTify_term term :=
  let s := sigT_for term in
  constr:(ltac:(repeat (try exact term; eapply existT)) : s).

Ltac type_head_args T acc :=
  let pT := get_paramed_type_head T in
  let rec f T acc :=
      lazymatch T with
      | pT =>
        let Tt := type of T in
        constr:((Tt, T, acc))
      | ?F ?A => f F (A, acc)
      end in
  f T acc.

Local Definition to_be_generalized{T}(x:T) := x.

Ltac pose_over tx :=
  let rec f p :=
      lazymatch p with
      | ((forall (a : ?T), @?B a), ?Y, (?A, ?R)) =>
        let tA := pose_over T in
        let v := fresh "v0" in
        let dummy := match goal with _ => pose (v := to_be_generalized A : tA) end in
        let B' := (eval cbv beta in (B v)) in
        f (B', (Y v), R)
      | (_, ?Y, I)  => Y
      end in
  let tha := type_head_args tx I in
  f tha.

Ltac do_generalization :=
  match goal with
  | [H' := to_be_generalized ?H |- _] =>
    unfold to_be_generalized in H';
    let s' := sigTify_term H' in
    let s := sigTify_term H in
    generalize (eq_refl : s' = s);
    clearbody H'
  | [H' := to_be_generalized _ |- _] =>
    (*the remaining ones fail clearbody, hopefully aren't needed to be generalized:*)
    unfold to_be_generalized in H';
    subst H'
  end.  

Ltac sigT_generalize_eqs H :=
  let T := type of H in
  let T' := pose_over T in
  let H' := fresh H in
  pose (H' := to_be_generalized H : T');
  repeat do_generalization;
  generalize H; rename H' into H, H into H'; try clear H'.
