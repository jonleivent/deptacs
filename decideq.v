(*

A dependent decide equality tactic that works with or without axioms on
dependent types.

There are several modes of usage.  The default is to use typeclasses when
available, and to avoid usage of axioms.  To turn off typeclass search,
re-define the handle_sub_eqdec tactic to idtac (from its
default_handle_sub_eqdec value).  To enable axioms re-define one or more of
the tactic aliases: proof_irrelevance_alias, inj_pair2_alias and UIP_alias.
If this is done, the algorithm will prefer axioms to typeclass search, as
axiom usage will be faster and lead to smaller proof terms.  Note that
inj_pair2_alias needs some proper definition (other than False).

For typeclasses, sumbool and or are made Existing Classes, so that one can add
Existing Instances like Nat.eq_dec.  TBD: if use of Existing Class makes for
wild-goose typeclass search, we could instead use normal Class/Instance with
singleton classes.

*)

Require Import utils.
Require Import block.
Require Import debug.
Require Import paramth.
Require Import sigTgen.

Set Injection On Proofs.

(*Redefine these to their respective symbols as desired:*)

(*Valid values for proof_irrelevance_alias are:*)
(*Coq.Logic.ProofIrrelevance.proof_irrelevance*)
(*False -- disable use of proof irrelevance*)
Ltac proof_irrelevance_alias := False.

(*Valid values for inj_pair2_alias are: *)
(*Coq.Logic.Eqdep.EqdepTheory.inj_pair2  -- uses Coq.Logic.Eqdep.Eq_rect_eq.eq_rect_eq axiom*)
(*Coq.Logic.Eqdep_dec.inj_pair2_eq_dec   -- no axiom, subgoals are all eqdecs*)
(*Eqdep_em.inj_pair2_eqem                -- no axiom, subgoals are all eqems*)
Ltac inj_pair2_alias := False.

(*Coq.Logic.Eqdep.EqdepTheory.UIP        -- uses Coq.Logic.Eqdep.Eq_rect_eq.eq_rect_eq axiom*)
(*Coq.Logic.Eqdep_dec.UIP_dec            -- no axiom, subgoals are all eqdecs*)
(*Eqdep_em.UIP_em                        -- no axiom, subgoals are all eqems*)
(*False                                  -- do not use UIP*)
Ltac UIP_alias := False.

(*Note: it does not work to attempt to pick up inj_pair2 as a hint because its
application is too ambiguous in nested sigT cases, as it must infer a function.*)

Lemma eqdec_implies_eqem : forall T (a b : T), {a=b} + {a<>b} -> a=b \/ a<>b.
Proof.
  tauto.
Qed.

Hint Extern 100 (?a = ?b \/ ?a <> ?b) =>
intros; apply eqdec_implies_eqem  : typeclass_instances.

(* Why care about "eqem" (equality excluded middle) (a=b \/ a<>b) at all?  We
will be able to prove eqdec ({a=b} + {a<>b}) on most types that we can prove
eqem on, and eqded implies eqem trivially (as eqdec_implies_eqem above shows).
However, when using proof relevance, and needing a decision procedure on
proofs, it is not possible to do case analysis on any informative Props when
the goal is eqdec, but it is possible when the goal is eqem.  It is also the
case that the theorems in Eqdep_dec (inj_pair2_eq_dec and UIP_dec are used
here) only need eqem, although they currently ask for eqdec (I have a copy of
Eqdep_dec that uses eqem instead).  Hence it is possible to use eqem to get
eqdec in more cases - such as when the types of certain fields or indexes only
provide eqem.

 *)

(* The "practical theory" behind how this algorithm works:
   
For an eqdec (or eqem) goal of the form {a=b}+{a<>b} (or a=b \/ a<>b), we
start by doing induction on a using its standard induction scheme.  Then we
attempt to destruct b in each subgoal.  However...

Inductive types come in two major varieties: those with indexes and those
without.  Those with indexes will need a kind of dependent destruction (for b
above), while those without indexes won't.  Even the simplist inductive type
with indexes will need it:

  Inductive Simp : unit -> Type := simp : Simp tt.

  Goal forall u (a b : Simp u), {a=b}+{a<>b}.

  intros u a. induction a. Fail destruct b.

This is because the type of a constructor is seen by Coq as dependent on the
constructor itself even in this trivial case where there really is only one
type (Simp tt) in the type family and only one constructor for that type.

So, for such indexed types, we will generalize the conclusion over b and its
type's indexes (recursively), freeing the conclusion from the destructee.  But
first, to tie the generalized bs and indexes to the destructee, we will create
dependent equalities between them based on nested sigTs, one level of nesting
for each type index involved.

Once we destruct b with the sigT equality in place, the non-generalized side
of the sigT equalities will be allowed to type-change along with b without
illegally impacting the type of the sigT equality itself.

Before going further, we process any equalities that may have come from fields
of a or b, doing injections on them as needed, subject to the requirement that
these early injections don't require us to prove other eqdecs (or eqems).
Then, we "block" any remaining equalities in the goal, so they don't lead us
astray later (into working to prove other eqdecs or eqems that we really don't
need).  We will unblock these just before finishing.

In the dependent destruction case, we then turn our attention to the sigT
equalities - we need to process them in each subgoal so that the eqdec (eqem)
goal becomes about constructors on both sides of the (in)equalities.  There
are three tools we use to do injections (which are also used above on the
field equalities, if necessary).  One is obviously the injection tactic,
although we wrap it in a way so that it will fail if the injection it does
isn't productive.  The second is the inj_pair2_alias theorem, which allows us
to break down the sigT equality one nesting level at a time.  The third is a
"deslimer" (Conor McBride's paper "A polynomial testing principle" mentions
"green slime" in reference to non-injective functions that appear in inductive
type indexes) - which cuts through the slime also by using a sub-eqdec (or
sub-eqem) on differences between the "green slime" for a's and b's ctors,
using the fact that the right constructor of a sub-eqdec (or sub-eqem) would
imply that any such difference spotted in the slime at the field level is
truly a difference - and that in turn will allow us to prove the right
constructor of the current eqdec (or eqem) by contradiction, possibly after
doing some more of these injections.

Once we force the current eqdec (eqem) to be about constructors (which we can
determine easily by examining the "b" side to see if "is_var b" succeeds or
not - if it succeeds, then b is not a constructor-based term), we can turn our
attention to the fields of the constructors involved in the conclusion.
Actually, when doing injections, we always try to see if each subgoal can be
solved, as those that obviously discriminate will get done quickly here.  But,
on those that are left, we turn our attention to the fields of the now like
constructors.  Interestingly, we can re-use the deslimer code to handle the
fields quite nicely - whether or not the fields actually contain any green
slime.

 *)

(*

TODO:

- I believe that dependent decide equality will not loop if the
  inj_pair2_alias is set properly - this is due to the fact that start_eqdec
  does induction and destruction on the elements, else it fails.  But, might
  generalize_eqdep undo this?

- It might be nice to have a way for users to declare that some green-slime
  functions are injective on some args - and by doing so possibly avoid extra
  eqdep/eqem obligations.  I'm not sure how to do this (somehow with
  typeclasses?) or whether it would actually work (maybe all those obligations
  would still occur).

- What about functional extensionality and function fields?  Currently, we
  just leave functional fields alone to generate eqdep/eqem obligations, like:

  {f = g} + {f <> g}

  but if the functions are known to have extensionality on them, or if
  extensionality is globally true (by axiom), then we can do this instead:

  {forall x, f x = g x} + {~ forall x, f x = g x}

  which, although not an eqdec/eqem, may be more tractable.

 *)

(*for hyps we process, either clear them or double-block them so that they get
cleared at the end of this eqdep goal*)
Ltac clear_or_double_block_hyp H :=
  clear H || (block_hyp H; block_hyp H) || fail 999 "can't clear or block" H.
  
Ltac clear_useless_eqs :=
  repeat
    match goal with
    | H : ?A = ?A |- _ =>
      clear_or_double_block_hyp H
    | H : existT ?P ?p ?x = existT ?P ?p ?y, H' : ?x = ?y |- _ =>
      clear_or_double_block_hyp H
    | H : existT ?P ?p ?x = existT ?P ?p ?y, H' : ?y = ?x |- _ =>
      clear_or_double_block_hyp H
    end.

Ltac generalize_indexes term :=
  let T := type of term in
  let pT := get_paramed_type_head T in
  let rec f T :=
      lazymatch T with
      | pT => idtac
      | ?F ?A => generalize A; f F
      end in
  f T.

(* In order to make sure that existing hyps don't interfere with the
algorithm, we generalize the eqdep goal over the type indexes to remove the
possibility of dependencies between it and any existing hyps.  This, however,
means that if the initial eqdep target was specific to a particular
parameterization of the indexes, we will attempt to solve instead one that
might be too general.  Consider a type like "Inductive Foo : Set -> Set ..."
where the Set index doesn't change among the ctors - in this case, we will
generalize it and lose the ability to solve it.  We allow the user to specify
(by setting genindexes to false) that they don't want indexes generalized -
then they are responsible for doing any necessary generalization themselves in
order to prevent interference *)
Ltac generalize_eqdep genindexes :=
  repeat intro;
  lazymatch goal with
  | |- _ (?a = ?b) (?a <> ?b) =>
    generalize a, b;
    tryif constr_eq genindexes true
    then generalize_indexes a
    else idtac
  end.

Ltac eqdec_needs_injs :=
  lazymatch goal with
  | |- _ (_ = ?b) _ => is_var b
  end.

Ltac clear_unblocked_eqs :=
  repeat
    match goal with
    | H : _ = _ |- _ => clear H
    | H : block.block (block.block (_ = _)) |- _ => clear H (*clear double-blocked ones as well*)
    end.

Ltac default_handle_sub_eqdec := try typeclasses eauto.

Ltac handle_sub_eqdec := default_handle_sub_eqdec.

Ltac solve_congruences_directly := discriminate || congruence.

Ltac try_hyp :=
  try match goal with
         H : _ |- ?G => apply H; assumption
      end;
  try (apply eqdec_implies_eqem;
       match goal with
         H : _ |- ?G => apply H; assumption
       end).

Ltac solve_equality immediate :=
  try solve_congruences_directly;
  try (let A := proof_irrelevance_alias in apply A);
  (let A := UIP_alias in apply A);
  solve_or_defer_sub_eqdec immediate
with solve_or_defer_sub_eqdec immediate :=
  repeat intro; subst;
  clear_unblocked_eqs; clear_all_blocks; try_hyp;
  try (left;
       (*left changes the goal, so calling solve_equality is safe:*)
       solve_equality immediate);
  constr_eq immediate false; handle_sub_eqdec; shelve.

Ltac do_injections immediate := fail 999. (*forward def, redefined below, calls solve_it*)

Ltac solve_it immediate :=
  let G := goaltype in
  Debug 5 idtac "Debug: solve_it" immediate "on" G;
  tryif 
    lazymatch G with
    | False => solve_congruences_directly
    | _ <> _ => intro; subst; solve_congruences_directly
    | _ = _ => solve_equality immediate
    | _ (_ = _) _ =>
      try_hyp; constructor; try intro; subst;
      (*this call to do_injections, which calls solve_it, is safe due to the
      use of constructor above - hence the goal must have changed to a = or
      <>:*)
      do_injections immediate; fail
    end
  then idtac
  else (Debug 5 idtac "Debug: solve_it" immediate "failed on" G; fail).

(* Why do we call solve_or_defer_sub_eqdec below instead of solve_it?  And why
doesn't solve_it call solve_or_defer_sub_eqdec?  Note that solve_it will call
do_injections on the left/right parts of an eqdec and won't ever call
handle_sub_eqdec, while solve_or_defer_sub_eqdec won't do injections, but will
call handle_sub_eqdec.  The difference is that while on the eqdec we're
currently trying to solve, we call solve_it after possibly simplifying that
goal, but on sub eqdecs created in order to help solve that goal, we
call solve_or_defer_sub_eqdec instead, which may defer it.  *)

Ltac deslime pair :=
  Debug 4 idtac "Debug: deslime" pair;
  lazymatch pair with
  | (?A, ?A) => fail
  | (?A ?X, ?A ?Y) => deslime (X, Y)
  | (?X _, ?Y _) => deslime (X, Y)
  | (?X, ?Y) =>
    let H := fresh in
    first
      [assert (X<>Y) as H by solve_it false;
       right; contradict H; do_injections false; fail
      |assert (X=Y) as H by solve_it false;
       force_subst H
      |let H' := fresh in
       let tX := type of X in
       Debug 1 idtac "Debug: deslime obligated sub-eqdec on type" tX "to deslime" pair;
       (tryif is_prop
         then assert ((X=Y)\/(X<>Y)) as H
         else assert ({X=Y}+{X<>Y}) as H);
       [|case H; intros H'];
       revgoals;
       [right; contradict H'; do_injections false; fail
       |force_subst H'
       |solve_or_defer_sub_eqdec false]
      ]
  end.

Ltac do_subless_sigT_inj H :=
  let H' := fresh in
  (let A :=inj_pair2_alias in apply A in H as H');
  [|assumption..];
  Debug 1 let tH := type of H in idtac "Debug: do_subless_sigT_inj applied on" tH.

Ltac do_sigT_inj H immediate :=
  first
    [do_subless_sigT_inj H
    |let subT := fresh in
     (*use evar sub:subT to capture sub-eqdec needed by inj_pair2_alias for
     re-use.  Note that using refine to establish the evar will provoke typeclass
     search, which we don't want to do yet.*)
     evar (subT : Type);
     let sub := fresh in
     unshelve evar (sub:subT);subst subT;revgoals;
     [(*TBD: note that by using inj_pair2_eqem as inj_pair2_alias, the sub
      will be an eqem - which means we will be saving eqems as hyps, which are
      not useful for future eqdecs.  Hence we may have more work to do.*)
      let H' := fresh H in
      (let A :=inj_pair2_alias in apply A with (1:=sub) in H as H');
      (*make sure this apply did something useful:*)
      let tH' := type of H' in
      lazymatch tH' with ?A = ?A => fail | _ => idtac end;
      revert H';
      lazymatch goal with H : tH' |- _ => fail | _ => idtac end;
      intro H';
      clearbody sub (*else not reusable*)
     |solve_or_defer_sub_eqdec immediate]
    ];
  clear_or_double_block_hyp H;
  subst.

Ltac block_equalities :=
  repeat
    lazymatch goal with | H : _ = _ |- _ => block_hyp H end.

Ltac do_one_injection immediate :=
  Debug 6 idtac "Debug: do_one_injection" immediate;
  match goal with
  | H : @eq ?T ?X ?Y |- _ =>
    first
      [ helpful_injection H
      | lazymatch T with
        | sigT _ => do_sigT_inj H immediate
        | _ => constr_eq immediate false; deslime (X, Y)
        end
      ]
  end.

Ltac do_injections immediate ::=
  repeat
    (subst; (*refine _ here for early typeclass search*)
     clear_useless_eqs;
     try (try solve_it immediate; do_one_injection immediate)).

Ltac do_eqdec_needed_injs :=
  repeat
    (eqdec_needs_injs;
     clear_useless_eqs;
     do_one_injection false;
     subst);
  try (constructor; solve_it false).

Ltac non_dep_destruct_cleanup :=
  intros; subst;
  Debug 3 idtac "Debug: non_dep_destruct_cleanup doing immediate injections";
  do_injections true;
  block_equalities.

Ltac dep_destruct_cleanup :=
  intros;
  subst;
  do_injections true;
  block_equalities;
  unblock_conc;
  intros;
  do_eqdec_needed_injs;
  do_injections false.

Ltac depdestruct H := sigT_generalize_eqs H; block_conc; destruct H.

Ltac start_eqdec genindexes ind :=
  generalize_eqdep genindexes;
  intros;
  let b := last_hyp in
  revert b;
  let a := last_hyp in
  helpful_induction a ind;
  intros;
  let b := last_hyp in
  subst;
  tryif destruct b
  then non_dep_destruct_cleanup
  else (once depdestruct b; dep_destruct_cleanup).

Ltac do_next_field pair :=
  Debug 4 idtac "Debug: do_next_field" pair;
  lazymatch pair with
  | (?A, ?A) => left; reflexivity
  | (?A ?X, ?A ?Y) =>
    (*may not be slime, if X&Y are constants, but deslime handles that:*)
    deslime (X, Y)
  | (?X _, ?Y _) => do_next_field (X, Y)
  | _ => right; discriminate
  end.

Ltac do_fields :=
  repeat
    (repeat lazymatch goal with
            | |- _ (?X = ?Y) _ => do_next_field (X, Y)
            end;
     do_injections false).

Ltac decide_one_equality genindexes ind :=
  unshelve (start_eqdec genindexes ind; do_fields; handle_sub_eqdec).

Ltac check_inj_pair2_alias :=
  tryif constr_eq inj_pair2_alias False
  then fail "Please re-define Ltac inj_pair2_alias to an acceptable value"
  else idtac.

(*the "simple" version doesn't do its own index generalizing:*)
Tactic Notation "simple" "dependent" "decide" "equality" "using" constr(ind) :=
  check_inj_pair2_alias;
  repeat decide_one_equality false ind.
Tactic Notation "simple" "dependent" "decide" "equality" :=
  check_inj_pair2_alias;
  repeat decide_one_equality false False.
Tactic Notation "dependent" "decide" "equality" "using" constr(ind) :=
  check_inj_pair2_alias;
  repeat decide_one_equality true ind.
Tactic Notation "dependent" "decide" "equality" :=
  check_inj_pair2_alias;
  repeat decide_one_equality true False.

Ltac dependent_compare x y genindexes ind :=
  check_inj_pair2_alias;
  try typeclasses eauto;
  let H := fresh in
  first
    [assert (x=y \/ x<>y) as [H|H] by (repeat decide_one_equality genindexes ind)
    |assert ({x=y}+{x<>y}) as [H|H] by (repeat decide_one_equality genindexes ind)
    ];
  revert H.

Tactic Notation "simple" "dependent" "compare" constr(x) constr(y) "using" constr(ind) :=
  dependent_compare x y false ind.
Tactic Notation "simple" "dependent" "compare" constr(x) constr(y) :=
  dependent_compare x y false False.
Tactic Notation "dependent" "compare" constr(x) constr(y) "using" constr(ind) :=
  dependent_compare x y true ind.
Tactic Notation "dependent" "compare" constr(x) constr(y) :=
  dependent_compare x y true False.

Existing Class sumbool.
Hint Mode sumbool + + : typeclass_instances.
Existing Class or.
Hint Mode or + + : typeclass_instances.

(*The eqdec and eqem notations are convenient ways to create an eqdec or eqem
types from another type - see examples:*)

Definition eqthing orfun := fun (x : Type) => forall (a b : x), orfun (a = b) (a <> b).

Ltac make_eq_type type orfun :=
  let x := under_binders type ltac:(fun x => constr:(eqthing orfun x)) in
  let x' := (eval cbv beta delta [eqthing] in x) in
  exact x'.

Notation eq_type type orfun := (ltac:(make_eq_type type orfun)) (only parsing).

Notation eqdec type := (eq_type type sumbool) (only parsing).
Notation eqem type := (eq_type type or) (only parsing).
