(** * Limits of chains and cochains in the precategory of types *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.NaturalNumbers.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.MoreFoundations.Univalence.
Require Import UniMath.MoreFoundations.WeakEquivalences.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.categories.Types.

Require Import UniMath.CategoryTheory.Chains.Chains.
Require Import UniMath.CategoryTheory.Chains.Cochains.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.FunctorCoalgebras.

Require Import UniMath.Induction.PolynomialFunctors.
Require Import UniMath.Induction.M.Limits.
Require Import UniMath.Induction.M.Core.

(** The shifted chain (X', π') from (X, π) is one where Xₙ' = Xₙ₊₁ and πₙ' = πₙ₊₁. *)
Definition shift_chain (cha : chain type_precat) : chain type_precat.
Proof.
  use tpair.
  - exact (dob cha ∘ S).
  - exact (λ _ _ path, dmor cha (maponpaths S path)).
Defined.

(** The shifted cochain (X', π') from (X, π) is one where Xₙ' = Xₙ₊₁ and πₙ' = πₙ₊₁. *)
Definition shift_cochain {C : precategory} (cochn : cochain C) : cochain C.
Proof.
  use cochain_weq; use tpair.
  - exact (dob cochn ∘ S).
  - intros n; cbn.
    apply (dmor cochn).
    exact (idpath _).
Defined.

(** Interaction between transporting over (maponpaths S ed) and shifting the cochain *)
Definition transport_shift_cochain :
  ∏ cochn ver1 ver2 (ed : ver1 = ver2)
    (stdlim_shift : standard_limit (shift_cochain cochn)),
  transportf (dob cochn) (maponpaths S ed) (pr1 stdlim_shift ver1) =
  transportf (dob (shift_cochain cochn)) ed (pr1 stdlim_shift ver1).
Proof.
  intros cochn ver1 ver2 ed stdlim_shift.
  induction ed.
  reflexivity.
Defined.

(** Ways to prove that [dmor]s are equal on cochains *)
Lemma cochain_dmor_paths {C : precategory} {ver1 ver2 : vertex conat_graph}
      (cochn : cochain C) (p1 p2 : edge ver1 ver2) : dmor cochn p1 = dmor cochn p2.
Proof.
  apply maponpaths, proofirrelevance, isasetnat.
Defined.

(** More ways to prove that [dmor]s are equal on cochains *)
Lemma cochain_dmor_paths_type {ver1 ver2 ver3 : vertex conat_graph}
  (cochn : cochain type_precat) (p1 : edge ver1 ver3) (p2 : edge ver2 ver3)
  (q1 : ver1 = ver2) :
  ∏ v1 : dob cochn ver1, dmor cochn p1 v1 = dmor cochn p2 (transportf _ q1 v1).
Proof.
  intro v1; cbn in *.
  induction q1.
  cbn; unfold idfun.
  exact (toforallpaths _ _ _ (cochain_dmor_paths cochn p1 p2) v1).
Defined.


(** We use the following tactic notations to mirror the "equational style" of
    reasoning used in Ahrens, Capriotti, and Spadotti. *)
Local Tactic Notation "≃" constr(H) "by" tactic(t) := intermediate_weq H; [t|].
Local Tactic Notation "≃'" constr(H) "by" tactic(t) := intermediate_weq H; [|t].
Local Tactic Notation "≃" constr(H) := intermediate_weq H.
Local Tactic Notation "≃'" constr(H) := apply invweq; intermediate_weq H.

Local Lemma combine_over_nat_basic {X Y Z : nat → UU} :
  X 0 ≃ Z 0 → (∏ n : nat, Y (S n) ≃ Z (S n)) →
  (X 0 × ∏ n : nat, Y (S n)) ≃ ∏ n : nat, Z n.
Proof.
  intros x0z0 yszs.
  ≃ (Z 0 × (∏ n : nat, Z (S n))).
  - apply weqdirprodf; [apply x0z0|].
    apply weqonsecfibers, yszs.
  - use weq_iso.
    + intros z0zs.
      intros n; induction n.
      * exact (dirprod_pr1 z0zs).
      * apply (dirprod_pr2 z0zs).
    + intros xs; use dirprodpair.
      * apply xs.
      * exact (xs ∘ S).
    + reflexivity.
    + intros xs.
      apply funextsec; intros n.
      induction n; reflexivity.
Defined.

Local Lemma combine_over_nat {X : nat → UU} {P : (X 0 × (∏ n : nat, X (S n))) → UU} :
  (∑ x0 : X 0, ∑ xs : ∏ n : nat, X (S n), P (dirprodpair x0 xs)) ≃
  (∑ xs : ∏ n : nat, X n, P (dirprodpair (xs 0) (xs ∘ S))).
Proof.
  ≃ (∑ pair : (X 0 × ∏ n : nat, X (S n)), P pair) by apply weqtotal2asstol.
  use weqbandf.
  - apply (@combine_over_nat_basic X X X); intros; apply idweq.
  - intros x0xs; cbn.
    apply idweq.
Defined.

Local Lemma combine_over_nat' {X : nat → UU} {P : X 0 → (∏ n : nat, X (S n)) → UU} :
  (∑ x0 : X 0, ∑ xs : ∏ n : nat, X (S n), P x0 xs) ≃
  (∑ xs : ∏ n : nat, X n, P (xs 0) (xs ∘ S)).
Proof.
  ≃ (∑ (x0 : X 0) (xs : ∏ n : nat, X (S n)), (uncurry (Z := λ _, UU) P)
                                             (dirprodpair x0 xs)) by apply idweq.
  ≃' (∑ xs : ∏ n : nat, X n, uncurry P (Z := λ _, UU)
                                     (dirprodpair (xs 0) (xs ∘ S))) by apply idweq.
  apply combine_over_nat.
Defined.

(** If the base type is contractible, so is the type of sections over it. *)
Definition weqsecovercontr_uncurried {X : UU} {Y : X -> UU}
           (P : ∏ x : X, Y x -> UU) (isc : iscontr (∑ x : X, Y x)) :
  (∏ (x : X) (y : Y x), P x y) ≃ (P (pr1 (iscontrpr1 isc)) (pr2 (iscontrpr1 isc))).
Proof.
  ≃ (∏ pair : (∑ x : X, Y x), uncurry (Z := λ _, UU) P pair) by
    apply invweq, weqsecovertotal2.
  ≃' (uncurry (Z := λ _, UU) P (iscontrpr1 isc)) by (apply idweq).
  apply weqsecovercontr.
Defined.

(** Shifted cochains have equivalent limits.
    (Lemma 12 in Ahrens, Capriotti, and Spadotti) *)

Definition shifted_limit (cocha : cochain type_precat) :
  standard_limit (shift_cochain cocha) ≃ standard_limit cocha.
Proof.
  pose (X := dob cocha); cbn in X.
  pose (π n := (@dmor _ _ cocha (S n) n (idpath _))).
  unfold standard_limit, shift_cochain, funcomp, idfun; cbn.

  assert (isc : ∏ x : ∏ v : nat, dob cocha (S v),
                iscontr (∑ x0 : X 0, (π 0 (x 0)) = x0)).
  {
    intros x.
    apply iscontr_paths_from.
  }

  (** Step (2) *)
  (** This is the direct product with the type proven contractible above *)
  ≃ (∑ xs : ∏ v : nat, X (S v),
    (∏ (u v : nat) (e : S v = u),
    (dmor cocha (idpath (S (S v)))
      ∘ transportf (λ o : nat, X (S o) → X (S (S v))) e
      (idfun (X (S (S v))))) (xs u) = xs v)
    × (∑ x0 : X 0, (π 0 (xs 0)) = x0)) by
    (apply weqfibtototal; intro; apply dirprod_with_contr_r; apply isc).

  (** Now, we swap the components in the direct product. *)
  ≃ (∑ xs : ∏ v : nat, X (S v),
    (∑ x0 : X 0, π 0 (xs 0) = x0) ×
    (∏ (u v : nat) (e : S v = u),
      (dmor cocha (idpath (S (S v)))
      ∘ transportf (λ o : nat, X (S o) → X (S (S v))) e
      (idfun (X (S (S v))))) (xs u) = xs v)) by
    (apply weqfibtototal; intro; apply weqdirprodcomm).

  (** Using associativity of Σ-types, *)
  ≃ (∑ xs : ∏ v : nat, X (S v),
     ∑ x0 : X 0,
     (π 0 (xs 0) = x0) ×
     (∏ (u v : nat) (e : S v = u),
       (dmor cocha (idpath (S (S v)))
       ∘ transportf (λ o : nat, X (S o) → X (S (S v))) e
       (idfun (X (S (S v))))) (xs u) = xs v)) by
    (apply weqfibtototal; intro; apply weqtotal2asstor).

  (** And again by commutativity of ×, we swap the first components *)
  ≃ (∑ x0 : X 0,
     ∑ xs : ∏ n : nat, X (S n),
     (π 0 (xs 0) = x0) ×
     (∏ (u v : nat) (e : S v = u),
       (dmor cocha (idpath (S (S v)))
       ∘ transportf (λ o : nat, X (S o) → X (S (S v))) e
       (idfun (X (S (S v))))) (xs u) = xs v)) by (apply weqtotal2comm).

  (** Step 3: combine the first bits *)
  ≃ (∑ xs : ∏ n : nat, X n,
      (π 0 (xs 1) = xs 0) ×
      (∏ (u v : nat) (e : S v = u),
        (dmor cocha (idpath (S (S v)))
        ∘ transportf (λ o : nat, dob cocha (S o) → dob cocha (S (S v))) e
        (idfun (dob cocha (S (S v))))) (xs (S u)) = xs (S v))).
  apply (@combine_over_nat' X
        (λ x0 xs,
        π 0 (xs 0) = x0
        × (∏ (u v : nat) (e : S v = u),
            (dmor cocha (idpath (S (S v)))
            ∘ transportf (λ o : nat, X (S o) → X (S (S v))) e (idfun (X (S (S v)))))
              (xs u) = xs v))).

  (** Now the first component is the same. *)
  apply weqfibtototal; intros xs.

  ≃ (π 0 (xs 1) = xs 0
    × (∏ (v u : nat) (e : S v = u),
      (dmor cocha (idpath (S (S v)))
        ∘ transportf (λ o : nat, dob cocha (S o) → dob cocha (S (S v))) e
            (idfun (dob cocha (S (S v))))) (xs (S u)) = xs (S v))) by
    apply weqdirprodf; [apply idweq|apply flipsec_weq].

  ≃' (∏ (v u : nat) (e : S v = u), dmor cocha e (xs u) = xs v) by
    apply flipsec_weq.

  (** Split into cases on n = 0 or n > 0. *)
  (** Coq is bad about coming up with these implicit arguments, so we have to be
      very excplicit. *)
  apply (@combine_over_nat_basic
           (λ n, π n (xs (S n)) = xs n)
           (λ v, ∏ (u : nat) (e : v = u),
             (dmor cocha (idpath (S v))
               ∘ _ (idfun (dob cocha (S v)))) (xs (S u)) = xs v)
           (λ v, ∏ (u : nat) (e : S v = u), dmor cocha e (xs u) = xs v)).

  (** We use the following fact over and over to simplify the remaining types:
      for any x : X, the type ∑ y : X, x = y is contractible. *)
  - apply invweq.
    apply (@weqsecovercontr_uncurried
             nat (λ n, 1 = n) (λ _ _, _ = xs 0) (iscontr_paths_from 1)).
  - intros u.
    ≃ ((dmor cocha (idpath (S (S u)))
            ∘ transportf (λ o : nat, dob cocha (S o) → dob cocha (S (S u)))
                (idpath (S u)) (idfun (dob cocha (S (S u))))) (xs (S (S u))) =
          xs (S u)).
    + apply (@weqsecovercontr_uncurried
               nat (λ n, (S u) = n) (λ _ _, _ _ = xs (S u)) (iscontr_paths_from _)).
    + cbn; unfold funcomp, idfun.
      apply invweq.
      apply (@weqsecovercontr_uncurried
               nat (λ n, (S (S u)) = n) (λ _ _, _ = xs (S u)) (iscontr_paths_from _)).
Defined.


Local Lemma transportf_paths_FlFr {A B : UU} {f g : A -> B} {x1 x2 : A}
 (p : x1 = x2) (q : f x1 = g x1)
 : transportf (λ x, f x = g x) p q = !maponpaths f p @ q @ maponpaths g p.
Proof.
 induction p; cbn.
 cbn.
 symmetry.
 apply pathscomp0rid.
Defined.

Definition maponpaths_funextsec {A : UU} {B : A -> UU}
          (f g : ∏ x, B x) (x : A) (p : f ~ g) :
 maponpaths (λ h, h x) (funextsec _ f g p) = p x.
Proof.
 intermediate_path (toforallpaths _ _ _ (funextsec _ f g p) x).
 - generalize (funextsec _ f g p); intros q.
   induction q.
   reflexivity.
 - apply (eqtohomot (eqtohomot (toforallpaths_funextsec_comp f g x) p) x).
Qed.

Local Lemma transportf_sec_constant
 {A B : UU} {C : A -> B -> UU}
 {x1 x2 : A} (p : x1 = x2) (f : ∏ y : B, C x1 y)
 : (transportf (λ x, ∏ y : B, C x y) p f)
   = (λ y, transportf (λ x, C x y) p (f y)).
Proof.
 induction p; cbn; unfold idfun.
 reflexivity.
Defined.

(** Lemma 11 in Ahrens, Capriotti, and Spadotti *)
Local Definition Z X l :=
 ∑ (x : ∏ n, X n), ∏ n, x (S n) = l n (x n).
Lemma lemma_11 (X : nat -> UU) (l : ∏ n, X n -> X (S n)) : Z X l ≃ X 0.
Proof.
 set (f (xp : Z X l) := pr1 xp 0).
 transparent assert (g : (X 0 -> Z X l)). {
   intros x.
   exists (nat_rect _ x l).
   exact (λ n, idpath _).
 }
 apply (weqpair f).
 apply (isweq_iso f g).
 - cbn.
   intros xp; induction xp as [x p].
   transparent assert ( q : (nat_rect X (x 0) l ~ x )). {
     intros n; induction n; cbn.
     * reflexivity.
     * exact (maponpaths (l n) IHn @ !p n).
   }
   set (q' := funextsec _ _ _ q).
   use total2_paths_f; cbn.
   + exact q'.
   + rewrite transportf_sec_constant. apply funextsec; intros n.
     intermediate_path (!maponpaths (λ x, x (S n)) q' @
                         maponpaths (λ x, l n (x n)) q'). {
       use transportf_paths_FlFr.
     }
     intermediate_path (!maponpaths (λ x, x (S n)) q' @
                         maponpaths (l n) (maponpaths (λ x, x n) q')). {
       apply maponpaths. symmetry. use maponpathscomp.
     }
     intermediate_path (! q (S n) @ maponpaths (l n) (q n)). {
       unfold q'.
       repeat rewrite maponpaths_funextsec.
       reflexivity.
     }
     intermediate_path (! (maponpaths (l n) (q n) @ ! p n) @
                          maponpaths (l n) (q n)). {
       reflexivity.
     }
     rewrite pathscomp_inv.
     rewrite <- path_assoc.
     rewrite pathsinv0l.
     rewrite pathsinv0inv0.
     rewrite pathscomp0rid.
     reflexivity.
 - cbn.
   reflexivity.
Defined.

(* Maybe easier to apply in Lemma *)
Definition lemma_11_unfolded (X : nat -> UU) (l : ∏ n, X n -> X (S n)) :
  (∑ (x : ∏ n, X n), ∏ n, x (S n) = l n (x n)) ≃ X 0 := lemma_11 X l.

Lemma total2_assoc_fun_left {A B : UU} (C : A -> B -> UU) (D : (∏ a : A, ∑ b : B, C a b) -> UU) :
 (∑ (x : ∏ a : A, ∑ b : B, C a b), D x) ≃
 ∑ (x : ∏ _ : A, B),
   ∑ (y : ∏ a : A, C a (x a)),
     D (fun a : A => (x a,, y a)).
Proof.
 use weq_iso.
 - intros p.
   exists (fun a => (pr1 (pr1 p a))).
   exists (fun a => (pr2 (pr1 p a))).
   exact (pr2 p).
 - intros p.
   use tpair.
   + intros a.
     use tpair.
     * exact (pr1 p a).
     * exact (pr1 (pr2 p) a).
   + exact (pr2 (pr2 p)).
 - reflexivity.
 - reflexivity.
Qed.

Lemma sec_total2_distributivity {A : UU} {B : A -> UU} (C : ∏ a, B a -> UU) :
  (∏ a : A, ∑ b : B a, C a b)
    ≃ (∑ b : ∏ a : A, B a, ∏ a, C a (b a)).
Proof.
  use weq_iso.
  - intro f.
    use tpair.
    + exact (fun a => pr1 (f a)).
    + exact (fun a => pr2 (f a)).
  - intro f.
    intro a.
    exists ((pr1 f) a).
    apply (pr2 f).
  - apply idpath.
  - apply idpath.
Defined.


Lemma weq_functor_total2 {A B : UU} (C : A -> UU) (D : B -> UU) :
  ∏ e : A ≃ B,
        (∏ x, C x ≃ D (e x)) ->
        (∑ x, C x) ≃ (∑ x, D x).
Proof.
  intros e f.
  exact (weqbandf e C D f).
Defined.

Lemma weq_functor_total2_id {A : UU} (B C : A -> UU) :
  (∏ x, B x ≃ C x) ->
  (∑ x, B x) ≃ (∑ x, C x).
Proof.
  intros e.
  apply (weqfibtototal B C e).
Defined.

Lemma cochain_limit_standard_limit_weq (cha cha' : cochain type_precat) :
  cochain_limit cha ≃ cochain_limit cha' → standard_limit cha ≃ standard_limit cha'.
Proof.
  intro f.
  apply (weqcomp (invweq (lim_equiv _))).
  apply (weqcomp f).
  apply (lim_equiv _).
Defined.

Section theorem_7.
  Context (A : UU) (B : A → UU).

Definition cochain_weq_eq (cha cha' : cochain type_precat)
           (p : (invweq cochain_weq) cha = (invweq cochain_weq) cha') :
  cha = cha'.
Proof.
  apply (isweqmaponpaths (invweq cochain_weq)).
  assumption.
Defined.

Definition apply_on_chain (cha : cochain type_precat) : cochain type_precat :=
  mapcochain (polynomial_functor A B) cha.

Definition weq_polynomial_functor_on_limit (cha : cochain type_precat) :
  polynomial_functor A B (standard_limit cha) ≃ standard_limit (apply_on_chain cha).
Proof.
  apply invweq.
  eapply weqcomp.
  apply (invweq (lim_equiv _)).
  apply invweq.
  intermediate_weq (polynomial_functor A B (cochain_limit cha)). {
    apply eqweqmap.
    induction (weqtopaths (lim_equiv ltac:(assumption))).
    reflexivity.
  }
  induction cha as [X π]; unfold apply_on_chain. simpl.
  unfold mapcochain, mapdiagram, standard_limit; cbn.
  unfold polynomial_functor_obj.
  unfold cochain_limit; cbn.
  apply invweq.

  intermediate_weq (
      (∑ (x : nat → A) (y : ∏ a : nat, B (x a) → X a),
       ∏ n, polynomial_functor_arr A B (π _ n (idpath _)) (x (S n),, y (S n)) =
            x n,, y n)). {
    apply (@total2_assoc_fun_left
            nat A
            (fun v a =>  B a -> X v)
            (fun x =>  ∏ n,
                polynomial_functor_arr A B (π _ n (idpath _)) (x (S n)) = x n)).
  }
  unfold polynomial_functor_arr, pr1, pr2.
  intermediate_weq (
    (∑ (x : nat → A),
     ∑ (y : ∏ a : nat, B (x a) → X a),
     ∏ (n : nat),
     ∑ (p : x (S n) = x n),
     transportf (fun z => B z -> X n) p (π _ n (idpath _) ∘ y (S n)) = y n)). {
    do 2 (apply weqfibtototal; intro).
    apply weqonsecfibers; intro.
    apply total2_paths_equiv.
  }
  (* Now, we just move the ∑ over a few quantifiers*)
  intermediate_weq (
    (∑ (x : nat → A),
     ∑ (y : ∏ a : nat, B (x a) → X a),
     ∑ (p : ∏ n, x (S n) = x n),
     ∏ (n : nat),
     transportf (fun a => B a -> X n) (p n) (π _ n (idpath _) ∘ y (S n)) = y n)). {
    do 2 (apply weqfibtototal; intro).
    apply sec_total2_distributivity.
  }
  intermediate_weq (
    (∑ (a : nat → A),
     ∑ (p : ∏ n, a (S n) = a n),
     ∑ (u : ∏ m : nat, B (a m) → X m),
     ∏ (n : nat),
     transportf (fun z => B z -> X n) (p n) (π _ n (idpath _) ∘ u (S n)) = u n)). {
    apply weqfibtototal; intro.
    apply weqtotal2comm.
  }
  intermediate_weq (
    (∑ (a : A),
     ∑ (u : ∏ n, B a → X n),
     ∏ (n : nat), π _ n (idpath _) ∘ u (S n) = u n)). {
    (* Should follow from correct application of  lemma_11 *)
    admit.
  }
  intermediate_weq (
    ∑(a : A),
    B a →  cochain_limit (X ,, π)). {
    apply weqfibtototal; intro a.
    unfold cochain_limit.
    simpl.
    (* Should follow directly by some Lemma in unimath *)
    admit.
  }
  unfold cochain_limit.
  cbn.
  apply idweq.
Admitted.

Definition terminal_cochain  : cochain type_precat :=
  termCochain (TerminalType) (polynomial_functor A B).

Definition m_type  := standard_limit terminal_cochain.

(* Shifting the terminal cochain is equivalent to applying
   the polynomial functor once *)
Definition terminal_cochain_shifted_lim :
  standard_limit (shift_cochain terminal_cochain) ≃
                 standard_limit (apply_on_chain terminal_cochain).
Proof.
  apply cochain_limit_standard_limit_weq.
  unfold shift_cochain, apply_on_chain, cochain_limit.
  apply weqfibtototal;intros.
  apply weqonsecfibers; intro n.
  apply idweq.
Defined.

Definition m_in : (polynomial_functor A B) m_type ≃ m_type.
  eapply weqcomp.
  exact (weq_polynomial_functor_on_limit terminal_cochain).
  eapply weqcomp.
  exact (invweq terminal_cochain_shifted_lim).
  exact (shifted_limit terminal_cochain).
Defined.

Definition m_out : (type_precat ⟦ m_type, (polynomial_functor A B) m_type ⟧)%Cat :=
  invweq m_in.

Definition m_coalgebra : coalgebra (polynomial_functor A B) := m_type,, m_out.

Local Open Scope cat.
Lemma m_coalgebra_is_final : is_final m_coalgebra.
Proof.
  unfold is_final.
  intro coalg; induction coalg as [C γ].
  apply iscontrifweqtounit.
  Check (pr2 (pr1 (polynomial_functor A B))) C m_type.
  intermediate_weq (
      ∑ (f : C  → m_type), (invweq m_in) ∘ f =
           (pr2 (pr1 (polynomial_functor A B)) C m_type f) ∘ γ)%functions. {
    unfold polynomial_functor, coalgebra_homo.
    cbn.
    apply weqfibtototal;intros.
    unfold is_coalgebra_homo.
    cbn.
    apply (pathsinv0,, isweqpathsinv0 _ _).
  }
  intermediate_weq (
    ∑ (f : C  → m_type),
    m_in ∘ (invweq m_in) ∘ f =
    m_in ∘ (pr2 (pr1 (polynomial_functor A B)) C m_type f) ∘ γ)%functions. {
    apply weqfibtototal;intros f.
    (* ----- Below term is veeeery slow ------- *)
    (*
    apply (@weqonpaths
             (C → (polynomial_functor A B) m_type)
             (C → m_type)
             (@weqffun C (polynomial_functor A B m_type) m_type m_in)
             (invweq m_in ∘ f)
             ((pr21 (polynomial_functor A B)) C m_type f ∘ γ)
          ).
     *)
    admit.
  }
  set (ψ f := m_in ∘ (pr2 (pr1 (polynomial_functor A B)) C m_type f) ∘ γ).
  intermediate_weq (
    ∑ (f : C  → m_type),
    f = (ψ f)). {
    apply weqfibtototal;intro f.
    apply (@transitive_paths_weq _ (m_in ∘ invweq m_in ∘ f)%functions f (ψ f)).
    apply funextfun; intros c.
    exact (homotweqinvweq m_in (f c)).
  }
  set (Cone := cone terminal_cochain C).
  set (e := (invweq (@limit_up_weq conat_graph terminal_cochain C m_type (type_cone terminal_cochain) limit_universal )) :
              Cone ≃ (C -> m_type)).
  intermediate_weq (∑ c : Cone, e c = ψ (e c)). {
    apply invweq.
    use weq_functor_total2.
    - exact e.
    - intros c.
      apply idweq.
  }
  set (Φ := (invmap e ∘ (ψ : (C -> m_type) -> C -> m_type) ∘ e)%functions :
              Cone -> Cone).
  intermediate_weq (∑ c : Cone, e c = e (Φ c)). {
    apply weq_functor_total2_id; intros c.
    assert (H : ∏ {A : UU} (a b c : A),
              b = c ->
              (a = b) ≃ (a = c)).
    {
       intros ? ? ? ? e'; induction e'; apply idweq.
    }
    apply H.
    unfold Φ.
    change (ψ (e c) = e (invmap e (ψ (e c)))).
    rewrite homotweqinvweq.
    reflexivity.
  }
  intermediate_weq (∑ c : Cone, c = Φ c). {
    apply weqfibtototal; intro.
    apply (invweq (weqonpaths _ _ _)).
  }
  Check iter_functor (polynomial_functor A B).
  set (W n := iter_functor (polynomial_functor A B) n unit).
  set (Cone0' n := C -> W n).
  set (Cone0 := ∏ n, Cone0' n).
  set (π n := dmor terminal_cochain (idpath (S n))).
  set (Cone1' (u : Cone0) n := (π n ∘ u (S n) = u n)%functions).
  set (Cone1 (u : Cone0) := ∏ n, Cone1' u n).
  assert (Cone = (∑ u : Cone0, Cone1 u)). {
    unfold Cone, cone, Cone0, Cone1, Cone0', Cone1'.
    apply weqtopaths.
    apply weqfibtototal; intro.
    use weq_iso.
    - intros eq ?.
      apply (eq (S n) n (idpath _)).
    - intros n u v e'.
      unfold edge in *.
      cbn in e'.
      Check (dmor terminal_cochain e')%functions.
      apply funextsec; intro.
      induction e'.
      cbn.
      rewrite (simplify_cochain_step terminal_cochain).
      rewrite ((simplify_cochain_step terminal_cochain _ _)).
      Check simplify_cochain_step terminal_cochain _ e'.
      cbn.

    -
    -
    Check simplify_cochain_step terminal_cochain.

    use weqbandf.
    - apply idweq.
      reflexivity.
      cbn.
      refl.
    unfold W, dob, vertex.
    unfold terminal_cochain, termCochain, pr1.

    cbn.
    apply weqfibtototal.
      }by reflexivity.
  intermediate_weq (∑ u : Cone0, ∑ q : Cone1 u, u,, q = Φ (u,, q)). {
    apply total2_associativity.
}
  intermediate_weq (∑ (u : Cone) (q : Cone),
                    ∑ (p : u =
                    c = Φ c). {
  }

  admit.
Admitted.
End theorem_7.