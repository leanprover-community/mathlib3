import category_theory.sites.grothendieck
import category_theory.sites.cover_preserving
import category_theory.sites.cover_lifting

universes v₁ v₂ u₁ u₂

namespace category_theory
variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D] (F : C ⥤ D)
variables (J : grothendieck_topology D)


def induced_topology : grothendieck_topology C :=
{ sieves := λ X S,
    ∀ (K : grothendieck_topology C)
      (H : ∀ ⦃Y⦄ (T : J (F.obj Y)), T.val.functor_pullback F ∈ K Y), S ∈ K X,
  top_mem' := λ X K _, K.top_mem _,
  pullback_stable' := λ X Y S f hf K H, K.pullback_stable f (hf K H),
  transitive' := λ X S hS S' f K H, K.transitive (hS K H) _ (λ _ _ hg, f hg K H) }

lemma is_cover_of_functor_pullback {X : C} (S: J (F.obj X)) :
  S.val.functor_pullback F ∈ (induced_topology F J) X := λ K H, H S

def induced_cover_lifting : cover_lifting (induced_topology F J) J F :=
{ cover_lift := λ U S hS, is_cover_of_functor_pullback F J ⟨S, hS⟩ }



end category_theory
