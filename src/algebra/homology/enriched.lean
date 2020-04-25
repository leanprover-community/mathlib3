import algebra.homology.chain_complex
import category_theory.enriched.enriched_over
import algebra.category.Group.basic

universes v u

open category_theory
open category_theory.limits

variables (V : Type u) [𝒱 : category.{v} V]
variables [has_zero_morphisms.{v} V]
include 𝒱

instance [enriched_over.{v} AddCommGroup V] (C D : cochain_complex V) : add_monoid (C ⟶ D) :=
{ zero := ⟨λ i, 0, begin dsimp, ext, simp, end⟩,
  add := λ f g, ⟨λ i, f.f i + g.f i, sorry⟩,
  zero_add := sorry,
  add_zero := sorry,
  add_assoc := sorry, }

instance [enriched_over.{v} AddCommGroup V] : enriched_over.{v} AddCommGroup (cochain_complex V) :=
{
  enriched_hom := λ C D, AddCommGroup.of (C ⟶ D),
  comp_left := sorry,
  comp_right := sorry,
}
