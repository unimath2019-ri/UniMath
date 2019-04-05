Require Export UniMath.Foundations.PartA.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.ProductCategory.
Require Import UniMath.CategoryTheory.categories.Types.
Require Import UniMath.CategoryTheory.Core.Functors.


Notation "x .1" := (pr1 x) (at level 3, format "x '.1'").
Notation "x .2" := (pr2 x) (at level 3, format "x '.2'").

(* suggested replacement that should get the name [Fam]: *)
Definition Fam (I: UU): precategory_data := power_precategory I type_precat.

Local Open Scope cat.

Section Test.
  Variable I: UU.
  Variable A: ob(Fam I).
  Eval compute in (identity A).
End Test.

Section Test.
  Variable I: UU.
  Variable A B C: ob(Fam I).
  Variable f : Fam I ⟦ B , C ⟧.
  Variable g : Fam I ⟦ A , B ⟧.
  Eval compute in (f ∘ g).
End Test.

Section Test.
  Variable I J: UU.
  Eval compute in (functor (Fam I) (Fam J)).
End Test.

Local Close Scope cat.
