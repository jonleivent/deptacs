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

Local Definition clone_of{T}(x:T) := x.

Ltac is_already_cloned H :=
  lazymatch get_value H with clone_of _ => I end.

Ltac clone H T :=
  let H' := fresh "gen_x" in
  let dummy := match goal with _ => pose (H' := clone_of H : T) end in
  H'.

(*pose replacement copies of all index-filling args, and mark them with
clone_of for later:*)
Ltac pose_clones_for_index_args T :=
  let rec f p :=
      lazymatch p with
        (*type of X......,  X, args to use*)
      | ((forall (a : ?ta), _), ?X, (?A , ?R)) =>
        (*Note: ta may differ from type of A by virtue of previous clones*)
        match goal with
        | _ =>
          (*no need to clone A more than once:*)
          let dummy := is_already_cloned A in
          let X' := constr:(X A) in
          let T' := type of X' in
          f (T', X', R)
        | _ =>
          let ta' := pose_clones_for_index_args ta in (*recurse on ta first*)
          let A' := clone A ta' in (*then clone A with the clone-indexed ta'*)
          let X' := constr:(X A') in
          let T' := type of X' in
          f (T', X', R)
        end
      | (_, ?X, I)  => X (*returns: pt paramed with clones*)
      end in
  let pT := get_paramed_type_head T in
  let tpT := type of pT in
  let args := reverse_args_until_target T pT I in
  f (tpT, pT, args).

(*create an (possibly sigT-based) equality in the conclusion for one clone_of
marked local def:*)
Ltac equate_one_clone :=
  match goal with
  | [H' := clone_of ?H |- _] =>
    unfold clone_of in H';
    let s' := sigTify_term H' in
    let s := sigTify_term H in
    generalize (eq_refl : s' = s);
    clearbody H'
  end.

Ltac sigT_generalize_eqs H :=
  let T := type of H in
  let T' := pose_clones_for_index_args T in
  let H' := fresh H in
  pose (H' := clone_of H : T');
  repeat equate_one_clone;
  generalize H;
  rename H' into H, H into H';
  try clear H'.
