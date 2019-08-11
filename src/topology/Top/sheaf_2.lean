import topology.Top.presheaf
import category_theory.limits.opposites
import category_theory.full_subcategory

universes v u

open category_theory
open category_theory.limits
open topological_space
open opposite

namespace Top

variables {X : Top.{v}}

variables {C : Type u} [𝒞 : category.{v+1} C]
include 𝒞

namespace presheaf
variables (F : X.presheaf C)

/--
By Proposition 2.10 of https://ncatlab.org/nlab/show/sheaf,
a sheaf is a presheaf which preserves limits along complete full subcategories of `(opens X)ᵒᵖ`.
A complete full subcategory of `(opens X)ᵒᵖ` is just a collection of open sets closed under intersections.
-/
def sheaf_condition :=
Π (𝒰 : set (opens X)) (h : Π 𝒳, 𝒳 ⊂ 𝒰 → lattice.Inf 𝒳 ∈ 𝒰),
  preserves_limit (full_subcategory_inclusion (λ U, (unop U) ∈ 𝒰)) F.

variables [has_limits.{v} C]

def sheaf_condition_2 :=
Π (𝒰 : set (opens X)) (h : Π 𝒳, 𝒳 ⊂ 𝒰 → lattice.Inf 𝒳 ∈ 𝒰),
  is_iso (limit.post (full_subcategory_inclusion (λ U, (unop U) ∈ 𝒰)) F)

-- Proving the equivalence of those two should just be something general about `preserves_limit`

-- def separation_condition :=
-- Π (𝒰 : set (opens X)) (h : Π 𝒳, 𝒳 ⊂ 𝒰 → lattice.Inf 𝒳 ∈ 𝒰),
--   is_mono (limit.post (full_subcategory_inclusion (λ U, (unop U) ∈ 𝒰)) F)

end presheaf

structure sheaf :=
(F : X.presheaf C)
(condition : F.sheaf_condition)

end Top
