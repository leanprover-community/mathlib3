import algebra.homology.chain_complex
import category_theory.monoidal.category

universes v u

open category_theory
open category_theory.limits

namespace chain_complex
variables {V : Type u} [category.{v} V] [𝒱 : monoidal_category.{v} V] [has_zero_morphisms.{v} V]
include 𝒱

def product (C D : chain_complex.{v} V) : double_complex.{v} V :=
{ C := λ i j, C.C i ⊗ D.C j,
  d₁ := λ i j, C.d i ⊗ (𝟙 (D.C j)),
  d₂ := λ i j, (𝟙 (C.C i)) ⊗ D.d j,
  d₁_squared := sorry,
  d₂_squared := sorry,
  d_comm := sorry, }

-- TODO use this to define a monoidal structure on `chain_complex V`,
-- (or at least bounded ones)
-- as long as V is enriched in AddCommGroup, so we can collapse double complexes.

end chain_complex
