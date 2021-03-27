import category_theory.category
import category_theory.adjunction.basic
import category_theory.arrow
import category_theory.model_categories.arrow_classes

universes v v' u u'

namespace category_theory

open category_theory

variables {C : Type u} [category.{v} C]
variables {D : Type u} [category.{v} D]

structure weak_factorization_system {C : Type u} [category.{v} C] :=
  (A B : arrow_cond C)
  (retracts : closed_under_retracts A ∧ closed_under_retracts B)
  (lifting : ∀ i : arrow C, A i → left_lifting_property B i)
  (factorization : ∀ i : arrow C, ∃ Z : C, ∃ a : i.left ⟶ Z, ∃ b : Z ⟶ i.right,
    i.hom = a ≫ b ∧ A (arrow.mk a) ∧ B (arrow.mk b) )



/-
Cisinski Proposition 2.1.12. LetF : C ? C 0 : Gbeanadjunction.AssumethatCandC 0
are endowed with weak factorisation systems (A, B) and (A 0 , B 0 ), respectively.
Then we have F(A) ⊂ A 0 if and only if G(B 0 ) ⊂ B-/

lemma weak_factorization_system_adjunction
  (V : weak_factorization_system C) (W : weak_factorization_system C)
  {F : C ⥤ D} {G : D ⥤ C} [F ⊣ G : adjunction] :
  arrow_cond.image F V.A ⊂ W.A ↔ arrow_cond.image G W.A ⊂ V.A :=
begin
  sorry -- use lifting_properties_adjunction
end

end category_theory
