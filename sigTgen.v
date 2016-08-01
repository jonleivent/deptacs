(*

sigT_generalize_eqs: A sigT-based (instead of JMeq-based) generalize_eqs
tactic

*)

Require Import utils.
Require Import paramth.

Ltac reverse_args_upto T upto acc :=
  lazymatch T with
  | upto => acc
  | ?F ?A => reverse_args_upto F upto (A, acc)
  end.

Local Definition cloned{T}(x:T) := x.

Ltac pose_clone H T :=
  lazymatch type of H with
  | cloned _ => H (*no need to clone H more than once:*)
  | _ =>
    let H' := fresh "gen_x" in
    let dummy := match goal with _ => pose (H' := H : cloned T) end in H'
  end.

(*pose replacement copies of all args of type T up to upto (a head subterm of
T), and mark them as cloned:*)
Ltac pose_clones_for_args T upto :=
  let rec f p :=
      lazymatch p with
        (*type of X......,  X, args to use*)
      | ((forall (a : ?ta), _), ?X, (?A , ?R)) =>
        (*Note: ta may differ from type of A by virtue of previous clones*)
        let A' := pose_clone A ta in
        let X' := constr:(X A') in
        let T' := type of X' in
        f (T', X', R)
      | (_, ?X, I)  => X (*returns: pt paramed with clones*)
      end in
  let tupto := type of upto in
  let args := reverse_args_upto T upto I in
  f (tupto, upto, args).

(*Return the possibly nested sigT type needed to dependently analyze term -
only term's type's params up to the upto arg are given the sigT treatment.*)
Ltac sigT_for T upto :=
  let rec f t h :=
      lazymatch t with
      | upto => h
      | ?F _ =>
        let a := fresh in
        constr:(sigT (fun a => ltac:(let R := f F (h a) in exact R)))
      end in
  f T upto.

(*Return the existT of type sig for term.*)
Ltac sigTify_term term sig :=
  constr:(ltac:(repeat (try exact term; eapply existT)) : sig).

Ltac unbody_clones :=
  repeat
    match goal with
    | [H' := ?H : cloned ?T' |- _] =>
      unfold cloned in H';
      clearbody H'
    end.

(*generate via backtracking successively smaller heads of T*)
Ltac get_next_type_head T :=
  multimatch T with
  | _ => T
  | ?F _ => get_next_type_head F
  end.

Ltac sigT_generalize_as_needed := true.

Ltac get_type_head T :=
  lazymatch sigT_generalize_as_needed with
  | true => get_next_type_head T
  | _ => get_paramed_type_head T
  end.

(* For hyp H, with inductive type T:

1. create H', a copy of H that remains unchanged - all current references to f
in the hyps and conclusion will be redirected to H'

2. for each index arg of T, generate a new variable to replace it in the type
of H (recursively - so that the types of these new variables use the new
variables themselves)

3. create (via generalize, hence in the conclusion) a possibly nested
sigT-based equality between H' and H that carries all of the equalities
between the original index args and the new replacement variables, as well as
the equality between H' and H themselves.  These equalities can be recovered
by injection on this nested sigT-based equality, with additional use of an
inj_pair2 lemma (such as Eqdep_dec.inj_pair2_eq_dec) as needed.

Why doesn't this do more, like the JMeq-based generalize_eqs?  Because some of
the extra equalities created by generalize_eqs are there because these extra
equalities cannot be extracted from a JMeq via injection as they can from a
sigT-based equality, and because once the index args of H are filled with new
vars, nothing else is going to mutate when H is destructed.  For the purposes
of something like induction, it may make sense to put further equalities and
other things into the conclusion so that they are incorporated into the
inductive hyp, but that has nothing to do with handling type-index issues per
se.

When doing non-axiom-based dependent case analysis, such as by using
Eqdep_dec.inj_pair2_eq_dec to avoid the eq_rect_eq axiom, it is best if this
tactic does not create too many sigT-based equalities (nestings), as any such
extras may require an eqdec proof for a type which cannot be proven.  The
axiom-based schemes (such as when using JMeq-based generalize_eqs, or using
eq_rect_eq) do not have this issue as they do not require eqdec proofs.

There are two modes, based on the setting of sigT_generalize_as_needed.  If
set to true, then the tactic will rely on backtracking to determine which
indexes need to be replaced with vars.  Because this relies on backtracking,
it must be sequenced with tactics that will fail unless the sigT is nested
enough - in other words, it should not be used interactively and followed by a
".".

If set to false, then the tactic will rely on paramth's get_paramed_type_head
to determine which args are indexes directly.  This may be necessary in cases
when the conclusion is not dependent on H, but only indirectly on some of its
indexes.  However, in such cases, it is probably the case that the inversion
tactic would work directly without generalizing.

 *)
Ltac sigT_generalize_eqs H :=
  let T := type of H in
  let hT := get_type_head T in
  let T' := pose_clones_for_args T hT in
  let H' := fresh H in
  pose (H : T') as H';
  let s := sigT_for T hT in
  let e := sigTify_term H s in
  let s' := sigT_for T' hT in
  let e' := sigTify_term H' s' in
  generalize (eq_refl : e' = e);
  clearbody H';
  unbody_clones;
  rename H' into H, H into H';
  try clear H';
  unfold cloned.
