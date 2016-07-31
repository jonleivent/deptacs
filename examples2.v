Require Import decideq.

(**********************************************************************)

(*Definining a dependent destruct from decideq:*)

Ltac dep_destruct H := depdestruct H; dep_destruct_cleanup; try discriminate.

Ltac dde := dependent decide equality.
Notation defeq := (ltac:(dde)) (only parsing).

Require PeanoNat.
Existing Instance PeanoNat.Nat.eq_dec.

(* Require Eqdep. *)
(* Ltac UIP_alias ::= Eqdep.EqdepTheory.UIP. *)
(* Ltac inj_pair2_alias ::= Eqdep.EqdepTheory.inj_pair2. *)

Require Eqdep_dec.
Ltac UIP_alias ::= Eqdep_dec.UIP_dec.
Ltac inj_pair2_alias ::= Eqdep_dec.inj_pair2_eq_dec.

(* Require Eqdep_em. *)
(* Ltac UIP_alias ::= Eqdep_em.UIP_em. *)
(* Ltac inj_pair2_alias ::= Eqdep_em.inj_pair2_eqem. *)

(**********************************************************************)

(* example from James Wilcox - see:
http://homes.cs.washington.edu/~jrw12/dep-destruct.html*)

Inductive Fin : nat -> Set :=
| F1 : forall n : nat, Fin (S n)
| FS : forall n : nat, Fin n -> Fin (S n).

Instance Fin_eqdec : eqdec Fin := defeq.
Print Assumptions Fin_eqdec.

Definition cardinality (n : nat) (A : Type) : Prop :=
  exists (f : A -> Fin n) (g : Fin n -> A),
    (forall x, g (f x) = x) /\
    (forall y, f (g y) = y).

Definition bool_to_Fin_2 (x : bool) : Fin 2 :=
  if x then FS _ (F1 _) else F1 _.

Definition Fin_2_to_bool (y : Fin 2) : bool :=
  match y with
  | F1 _ => false
  | FS _ (F1 _) => true
  | _ => false (* bogus! *)
  end.

Theorem bool_cardinality_2 : cardinality 2 bool.
Proof.
  unfold cardinality.
  exists bool_to_Fin_2.
  exists Fin_2_to_bool.
  split; intros.
  - destruct x; reflexivity.
  - dep_destruct y; try reflexivity.
    dep_destruct y; try reflexivity.
    dep_destruct y.
Qed.
Print Assumptions bool_cardinality_2.

Lemma fin_case :
  forall n (P : Fin (S n) -> Type),
    (P (F1 _)) ->
    (forall x, P (FS _ x)) ->
    (forall x, P x).
Proof.
  intros n P X X0 x. 
  dep_destruct x.
  all:auto with nocore.
Qed.
Print Assumptions fin_case.

(**********************************************************************)

Lemma le_minus : forall n:nat, n < 1 -> n = 0.
Proof.
  intros n H.
  dep_destruct H. (*not enough generalizing*)
  Undo.
  solve [dep_destruct H; inversion H]. (*but backtracking forces it*)
  Undo.
  Ltac sigTgen.sigT_generalize_as_needed ::= false.
  dep_destruct H. (*now have enough without backtracking*)
  inversion H.
Qed.
Print Assumptions le_minus.

Ltac sigTgen.sigT_generalize_as_needed ::= true.

Inductive vect A : nat -> Type :=
| vnil : vect A 0
| vcons : forall (h:A) (n:nat), vect A n -> vect A (S n).

Lemma vect_break: forall A n, forall v : vect A (S n), exists v' : vect A n, exists a : A, v = vcons A a _ v'.
Proof.
  intros A n v.
  dep_destruct v.
  do 2 eexists.
  reflexivity.
Qed.
Print Assumptions vect_break.


(*from /test-suite/success/dependentind.v:*)
(** Example by Andrew Kenedy, uses simplification of the first component of dependent pairs. *)

Set Implicit Arguments.

Inductive Ty :=
 | Nat : Ty
 | Prod : Ty -> Ty -> Ty.

Instance Ty_eqdec : eqdec Ty := defeq.
Print Assumptions Ty_eqdec.

Inductive Exp : Ty -> Type :=
| Const : nat -> Exp Nat
| Pair : forall t1 t2, Exp t1 -> Exp t2 -> Exp (Prod t1 t2)
| Fst : forall t1 t2, Exp (Prod t1 t2) -> Exp t1.

Instance Exp_eqdec : eqdec Exp := defeq.
Print Assumptions Exp_eqdec.

Inductive Ev : forall t, Exp t -> Exp t -> Prop :=
| EvConst   : forall n, Ev (Const n) (Const n)
| EvPair    : forall t1 t2 (e1:Exp t1) (e2:Exp t2) e1' e2',
               Ev e1 e1' -> Ev e2 e2' -> Ev (Pair e1 e2) (Pair e1' e2')
| EvFst     : forall t1 t2 (e:Exp (Prod t1 t2)) e1 e2,
               Ev e (Pair e1 e2) ->
               Ev (Fst e) e1.

Lemma EvFst_inversion : forall t1 t2 (e:Exp (Prod t1 t2)) e1, Ev (Fst e) e1 -> exists e2, Ev e (Pair e1 e2).
  intros t1 t2 e e1 ev.
  dep_destruct ev.
  Fail eexists; eassumption.
  Undo 2.
  (*backtrack to generalize enough works:*)
  dep_destruct ev; eexists; eassumption.
  Undo.
  (*or, turn off as_needed mode:*)
  Ltac sigTgen.sigT_generalize_as_needed ::= false.
  dep_destruct ev.
  eexists; eassumption.
Qed.
Print Assumptions EvFst_inversion. (*closed now, was using eq_rect_eq*)

