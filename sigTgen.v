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

Ltac reverse_args_until_target T targ acc :=
  lazymatch T with
  | targ => acc
  | ?F ?A => reverse_args_until_target F targ (A, acc)
  end.

Local Definition cloned{T}(x:T) := x.

Ltac is_already_cloned H :=
  lazymatch type of H with cloned _ => H end.

Ltac pose_clone H T :=
  let H' := fresh "gen_x" in
  let dummy := match goal with _ => pose (H' := H : cloned T) end in
  H'.

(*pose replacement copies of all index-filling args, and mark them with
cloned for later:*)
Ltac pose_clones_for_index_args T :=
  let rec f p :=
      lazymatch p with
        (*type of X......,  X, args to use*)
      | ((forall (a : ?ta), _), ?X, (?A , ?R)) =>
        (*Note: ta may differ from type of A by virtue of previous clones*)
        let A' :=
            match goal with
            | _ => is_already_cloned A (*no need to clone A more than once:*)
            | _ =>
              let ta' := pose_clones_for_index_args ta in (*recurse on ta first*)
              pose_clone A ta'
            end in
        let X' := constr:(X A') in
        let T' := type of X' in
        f (T', X', R)
      | (_, ?X, I)  => X (*returns: pt paramed with clones*)
      end in
  let pT := get_paramed_type_head T in
  let tpT := type of pT in
  let index_args := reverse_args_until_target T pT I in
  f (tpT, pT, index_args).

(*create an (possibly sigT-based) equality in the conclusion for one cloned
marked local def:*)
Ltac equate_one_clone :=
  match goal with
  | [H' := ?H : cloned _ |- _] =>
    unfold cloned in H';
    let s' := sigTify_term H' in
    let s := sigTify_term H in
    generalize (eq_refl : s' = s);
    clearbody H'
  end.

Ltac sigT_generalize_eqs H :=
  let T := type of H in
  let T' := pose_clones_for_index_args T in
  let H' := fresh H in
  pose (H' := H : cloned T');
  repeat equate_one_clone;
  generalize H;
  rename H' into H, H into H';
  try clear H'.
