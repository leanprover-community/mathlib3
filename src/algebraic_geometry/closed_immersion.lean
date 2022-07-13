import topology.sheaves.functors
import topology.sheaves.presheaf
import algebraic_geometry.Scheme

universes w v u

/- Formalizing the equivalence of (2) and (4) in
   https://stacks.math.columbia.edu/tag/01QN -/

noncomputable theory

section locally_surjective

open category_theory
open topological_space
open opposite

variables {C : Type u} [category.{v} C] [concrete_category C]
   {X : Top.{w}}

def sections (ℱ : X.presheaf C) (U : opens X) :=
   (forget C).obj (ℱ.obj (op U))

infix ` on ` : 80 := sections

variables {ℱ : X.presheaf C} {𝒢 : X.presheaf C}

def is_cover_of {U : opens X} {ι : Type} {V : ι → opens X}
   (sub : Π i, V i ⟶ U) := U ≤ supr V

structure Cover (U : opens X) :=
   (ι : Type)
   (V : ι → opens X)
   (sub : Π i, V i ⟶ U)
   (covers : U ≤ supr V)

def is_locally_surjective (T : ℱ ⟶ 𝒢) :=
   ∀ (U : opens X) (t : 𝒢 on U),
   ∃ (𝒱 : Cover U)
     (s : Π (i : 𝒱.ι), ℱ on (𝒱.V i)),
     ∀ (i : 𝒱.ι),
   (forget C).map (T.app (op (𝒱.V i))) (s i) =
   (forget C).map (𝒢.map (𝒱.sub i).op) t
-- tᵢ := (forget C).map (𝒢.map (𝒱.sub i).op) t,
-- Tsᵢ := (forget C).map (T.app (op (𝒱.V i))) (s i),
-- then Tsᵢ = tᵢ



end locally_surjective

namespace algebraic_geometry

variables {X Y : Scheme.{u}} (f : X ⟶ Y)




/- Our definition here is item (4) in
   https://stacks.math.columbia.edu/tag/01QO -/

structure is_closed_immersion (f : X ⟶ Y) : Prop :=
    (is_closed_embedding_base : closed_embedding f.val.base)
    (is_surjective_on_sections : is_locally_surjective (f.val.c))



end algebraic_geometry
