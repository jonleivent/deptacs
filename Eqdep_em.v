(*A slight rewriting of Eqdep_dec that uses weakly decidable equality (x=y \/
x<>y) instead of strongly decidable equality ({x=y}+{x<>y})*)

Set Implicit Arguments.
(* Set Universe Polymorphism. *)

Section EqdepEm.

  Variable A : Type.

  Let comp (x y y':A) (eq1:x = y) (eq2:x = y') : y = y' :=
    match eq1 with eq_refl => eq2 end.

  Let trans_sym_eq : forall (x y:A) (u:x = y), comp u u = eq_refl y.
  Proof.
    unfold comp. simple destruct u. reflexivity.
  Qed.

  Variable x : A.

  Variable eqem : forall y:A, x = y \/ x <> y.

  (*Understanding nu: it looks like an identity function - but its purpose is
  to redirect callers that provide an arbitrary instance for u to the specific
  instance captured within eqem.  That way, all nus are the same specific
  instance.*)
  Let nu (y:A) (u:x = y) : x = y :=
    match eqem y with
      | or_introl eqxy => eqxy
      | or_intror neqxy => False_ind _ (neqxy u)
    end.

  Let nu_constant : forall (y:A) (u v:x = y), nu u = nu v.
  Proof.
    intros.
    unfold nu.
    (*Only the proof of false needs help*)
    destruct (eqem y) as [|Hneq].
    - reflexivity.
    - (*All proofs of False are the trivially the same*) case Hneq.
  Qed.

  (*nu_inv isn't an inverse in the sense of actually finding the original u
  for each nu u - it can't be, as that original u is not anywhere to be found.
  Instead, it merely allows u to be cased to eq_refl in both lhs and rhs.*)
  Let nu_inv (y:A) (v:x = y) : x = y := comp (nu (eq_refl x)) v.
  
  Let nu_left_inv_on : forall (y:A) (u:x = y), nu_inv (nu u) = u.
  Proof.
    unfold nu_inv.
    (*This next case is what nu_inv is allowing:*) simple destruct u.
    apply trans_sym_eq.
  Qed.

  Theorem eq_proofs_unicity_on : forall (y:A) (p1 p2:x = y), p1 = p2.
  Proof.
    intros.
    elim nu_left_inv_on with (u := p1).
    elim nu_left_inv_on with (u := p2).
    elim nu_constant with y p1 p2.
    reflexivity.
  Qed.

  Theorem K_em_on :
    forall P:x = x -> Prop, P (eq_refl x) -> forall p:x = x, P p.
  Proof.
    intros.
    elim eq_proofs_unicity_on with x (eq_refl x) p.
    assumption.
  Qed.

  (** The corollary *)

  Let proj (P:A -> Prop) (exP:ex P) (def:P x) : P x :=
    match exP with
      | ex_intro _ x' prf =>
        match eqem x' with
          | or_introl eqprf => eq_ind x' P prf x (eq_sym eqprf)
          | _ => def
        end
    end.

  Theorem inj_right_pair_on :
    forall (P:A -> Prop) (y y':P x),
      ex_intro P x y = ex_intro P x y' -> y = y'.
  Proof.
    intros.
    cut (proj (ex_intro P x y) y = proj (ex_intro P x y') y).
    - cbn. destruct (eqem x) as [Heq|Hneq].
      + elim Heq using K_em_on. cbv. tauto.
      + case Hneq. reflexivity.
    - case H. reflexivity.
  Qed.

End EqdepEm.

Theorem eq_proofs_unicity A (eqem : forall x y : A, x = y \/ x <> y) (x : A)
: forall (y:A) (p1 p2:x = y), p1 = p2.
Proof (@eq_proofs_unicity_on A x (eqem x)).

Theorem K_em A (eqem : forall x y : A, x = y \/ x <> y) (x : A)
: forall P:x = x -> Prop, P (eq_refl x) -> forall p:x = x, P p.
Proof (@K_em_on A x (eqem x)).

Theorem inj_right_pair A (eqem : forall x y : A, x = y \/ x <> y) (x : A)
: forall (P:A -> Prop) (y y':P x),
    ex_intro P x y = ex_intro P x y' -> y = y'.
Proof (@inj_right_pair_on A x (eqem x)).

Require Coq.Logic.EqdepFacts.

Theorem K_em_type :
  forall A:Type,
    (forall x y:A, x = y \/ x <> y) ->
    forall (x:A) (P:x = x -> Prop), P (eq_refl x) -> forall p:x = x, P p.
Proof. apply K_em. Qed.

Theorem K_em_set :
  forall A:Set,
    (forall x y:A, x = y \/ x <> y) ->
    forall (x:A) (P:x = x -> Prop), P (eq_refl x) -> forall p:x = x, P p.
Proof fun A => K_em_type (A:=A).

Theorem eq_rect_eqem :
  forall A:Type,
    (forall x y:A, x = y \/ x <> y) ->
    forall (p:A) (Q:A -> Type) (x:Q p) (h:p = p), x = eq_rect p Q x p h.
Proof.
  intros A eqem.
  apply (EqdepFacts.Streicher_K__eq_rect_eq A (K_em_type eqem)).
Qed.

Theorem eq_dep_eqem :
  forall A:Type,
    (forall x y:A, x = y \/ x <> y) ->
     forall (P:A->Type) (p:A) (x y:P p), EqdepFacts.eq_dep A P p x p y -> x = y.
Proof (fun A eqem => EqdepFacts.eq_rect_eq__eq_dep_eq A (eq_rect_eqem eqem)).

Theorem UIP_em :
  forall (A:Type),
    (forall x y:A, x = y \/ x <> y) ->
    forall (x y:A) (p1 p2:x = y), p1 = p2.
Proof. apply eq_proofs_unicity. Qed.

Lemma inj_pair2_eqem : forall A:Type, (forall x y:A, x=y \/ x<>y) ->
   ( forall (P:A -> Type) (p:A) (x y:P p), existT P p x = existT P p y -> x = y ).
Proof.
  intros A eqem.
  apply EqdepFacts.eq_dep_eq__inj_pair2.
  apply EqdepFacts.eq_rect_eq__eq_dep_eq.
  unfold EqdepFacts.Eq_rect_eq, EqdepFacts.Eq_rect_eq_on.
  intros; apply eq_rect_eqem.
  apply eqem.
Qed.

Unset Implicit Arguments.
