
Ltac goaltype := lazymatch goal with |- ?G => G end.

Ltac last_hyp := lazymatch goal with H :_ |- _ => H end.

Ltac revert_all := repeat let H := last_hyp in revert H.

Ltac get_value H := eval cbv delta [H] in H.

Ltac head_of term :=
  lazymatch term with
  | ?F ?A => head_of F
  | _ => term
  end.

(*A helpful induction has to alter the goal to be about ctors.  Not all
induction lemmas will do this, so we should check. *)
Ltac helpful_induction H ind :=
  let G1 := goaltype in
  (tryif constr_eq ind False
    then induction H
    else induction H using ind);
  tryif (intros; let G2 := goaltype in constr_eq G1 G2)
  then fail
  else idtac.

(*Do an intro only if it is unique, else remove it:*)
Ltac uintro :=
  lazymatch goal with
  | _ : ?T |- ?T -> _ => intros _
  | _ => intros ? (*not "intro" to avoid head reduction*)
  end.

Ltac helpful_injection H := progress (injection H; repeat uintro; subst).

Ltac force_clear :=
  clear;
  repeat match goal with H :_ |- _ => clear H end.

Ltac force_subst H :=
  lazymatch type of H with
  | ?X = ?Y => first [subst X|subst Y]
  end.

Ltac is_prop :=
  let G := goaltype in
  let tG := type of G in
  constr_eq tG Prop.
