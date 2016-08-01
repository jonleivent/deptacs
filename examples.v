Require Import decideq.

(**********************************************************************)

Ltac dde := dependent decide equality.
Notation defeq := (ltac:(dde)) (only parsing).

(*Notation "[ x  &  ..  &  y  &  z ]" := (existT _ x .. (existT _ y z ) ..).*)

(* Typeclasses eauto := debug. *)
(* Ltac debug.Debug_Level ::= 99. *)

Require PeanoNat.
Existing Instance PeanoNat.Nat.eq_dec.

Require Bool.
Existing Instance Bool.bool_dec.

Require BinNums.

(*Ltac handle_sub_eqdec ::= idtac. *)
(* Hint Cut [*] : typeclass_instances. (*turns off typeclass search*) *)

(* Require Eqdep. *)
(* Ltac UIP_alias ::= Eqdep.EqdepTheory.UIP. *)
(* Ltac inj_pair2_alias ::= Eqdep.EqdepTheory.inj_pair2. *)

Require Eqdep_dec.
Ltac UIP_alias ::= Eqdep_dec.UIP_dec.
Ltac inj_pair2_alias ::= Eqdep_dec.inj_pair2_eq_dec.

(* Require Eqdep_em. *)
(* Ltac UIP_alias ::= Eqdep_em.UIP_em. *)
(* Ltac inj_pair2_alias ::= Eqdep_em.inj_pair2_eqem. *)

Inductive Bad (A : Type) : Type -> Type -> Type :=
  bad1 : Bad A nat bool.

Instance BadNat_eqdec : eqdec (Bad unit nat bool).
Proof.
  Fail decide equality.
  dde.
Abort.

Inductive Fin : nat -> Set :=
| F1 : forall n : nat, Fin (S n)
| FS : forall n : nat, Fin n -> Fin (S n).

Instance Fin_eqdec : eqdec Fin.
Proof.
  Fail decide equality.
  dde.
Qed.
Print Assumptions Fin_eqdec.

Inductive Fin3 : forall n (f1 f2 : Fin n), Set :=
| F31 : forall m (f1 f2 : Fin m), (f1 = f2) -> Fin3 (S m) (FS _ f1) (FS _ f2)
| F3S : forall m (f1 f2 : Fin m), Fin3 m f1 f2 -> Fin3 (S m) (FS _ f1) (FS _ f2).

Instance Fin3_eqdec : forall n f1 f2 (a b : Fin3 n f1 f2), {a=b}+{a<>b}.
Proof.
  Fail decide equality.
  dde.
Qed.
Print Assumptions Fin3_eqdec.

Inductive Finx(n : nat) : Set :=
| Fx1(i : nat)(e : n = S i)
| FxS(i : nat)(f : Finx i)(e : n = S i).

Instance Finx_eqdec : forall n (a b : Finx n), {a=b}+{a<>b}.
Proof.
  Fail decide equality.
  dde.
Qed.
Print Assumptions Finx_eqdec.

Inductive vect A : nat -> Type :=
| vnil : vect A 0
| vcons : forall (h:A) (n:nat), vect A n -> vect A (S n).

Instance vect_eqdec A `{A_eqdec : eqdec A} : eqdec (vect A).
Proof.
  Fail decide equality.
  dde.
Qed.
Print Assumptions vect_eqdec.

Section Green_Slime.
  Variable Goo : Set.
  Context {Goo_eqdec : forall g1 g2 : Goo, {g1=g2}+{g1<>g2}}.
  Variable green_slime : bool -> Goo.
  Variable blue_slime : bool -> bool.

  Inductive Foo : bool -> Goo -> Set :=
  | foo(b : bool) : Foo (blue_slime b) (green_slime b).
  
  Instance Foo_dec : eqdec Foo.
  Proof.
    Fail decide equality.
    dde.
  Qed.
  Print Assumptions Foo_dec.

  Variable A : Set.
  Variable slimier : A -> bool -> A -> bool -> A -> bool.

  Inductive Bar(a : A) : bool -> Goo -> Set :=
  | bar(b : bool)(b' : bool) : Bar a (slimier a b a b a) (green_slime (negb b')).

  (*because the a arg for Bar is not an index, but we gen over it, we are left
  with needing eqem on A when otherwis e we wouldn't need it.*)

  Instance Bar_dec : forall a b1 b2 (x y : Bar a b1 b2), {x=y}+{x<>y}.
  Proof.
    Fail decide equality.
    dde.
  Qed.
  Print Assumptions Bar_dec.
    
End Green_Slime.

Import BinNums.
Instance positive_dec : forall (a b : positive), {a=b}+{a<>b}.
Proof.
  decide equality.
  Restart.
  dde.
Qed.
Print Assumptions positive_dec.

Section Tconstr.
  (*test case from Frédéric Besson:*)
  Variable arity : positive -> nat.

  Variable styp : Type.

  Inductive tconstr  : nat -> Type := 
    | BT   : forall (p:positive), tconstr (arity p)
    | AppT : forall (n:nat) (ty : tconstr  (S n)) (to : styp), tconstr n.

  Context `{StypDec : forall (a b:styp), {a=b}+{a<>b} }.

  Instance tconstr_dec : forall n (a b : tconstr n), {a=b}+{a<>b}.
  Proof.
    Fail decide equality.
    dde.
  Qed.
  Print Assumptions tconstr_dec.
  
  (*index-free version of tconstr:*)
  Inductive tconstrx(i : nat) : Type :=
  | BTx (p : positive) (e : i=arity p)
  | AppTx (n : nat) (ty : tconstrx (S n)) (to : styp) (e : i=n).

  Instance tconstrx_dec : forall n (a b : tconstrx n), {a=b}+{a<>b}.
  Proof.
    Fail decide equality.
    dde.
  Qed.
  Print Assumptions tconstrx_dec.

End Tconstr.

Section Hlist.
  (** Heterogeneous lists indexed by A with types given by the family B *)

  Variable A : Type.
  Variable B : A -> Type.

  Inductive hlist : list A -> Type :=
  | HNil : hlist nil
  | HCons : forall (a:A) (types:list A), B a -> hlist types -> hlist (a::types).

  Instance hlist_dec
           (types : list A)
           {eqdec_A : eqdec A}
           {eqdec_B : forall a, eqdec (B a)} : forall (a b : hlist types), {a=b}+{a<>b}.
  Proof.
    Fail decide equality.
    dde.
  Qed.
  Print Assumptions hlist_dec.

End Hlist.

(**********************************************************************)

(*from http://adam.chlipala.net/cpdt/html/ProgLang.html:*)

Set Implicit Arguments.
Inductive type : Type :=  Nat : type | Func : type -> type -> type.

Instance type_eqdec : eqdec type.
Proof.
  decide equality.
Qed.
Print Assumptions type_eqdec.

Require Import List.
Import ListNotations.

Inductive member (A : Type) (elm : A) : list A -> Type :=
  HFirst : forall ls : list A, member elm (elm :: ls)
| HNext : forall (x : A) (ls : list A),
    member elm ls -> member elm (x :: ls).

(*Note that we skip eqdec on member due to no A_eqdec, but this is OK wrt term
below, where A is type:*)

Inductive term : list type -> type -> Type :=
  Var : forall (G : list type) (t : type), member t G -> term G t
| Const : forall G : list type, nat -> term G Nat
| Plus : forall G : list type, term G Nat -> term G Nat -> term G Nat
| Abs : forall (G : list type) (dom ran : type),
    term (dom :: G) ran -> term G (Func dom ran)
| App : forall (G : list type) (dom ran : type),
    term G (Func dom ran) -> term G dom -> term G ran
| Let : forall (G : list type) (t1 t2 : type),
    term G t1 -> term (t1 :: G) t2 -> term G t2.

Instance list_eqdec A {A_eqdec : eqdec A} : eqdec (list A).
Proof.
  decide equality.
Qed.
Print Assumptions list_eqdec.

Instance term_eqdec : eqdec term.
Proof.
  Fail decide equality.
  dde.
Qed.
Print Assumptions term_eqdec.
