import topology.sheaves.presheaf
import category_theory.limits.shapes.products
import category_theory.limits.shapes.equalizers
import category_theory.full_subcategory

universes v u

open category_theory
open category_theory.limits
open topological_space
open opposite
open Top

namespace topological_space.opens
variables {X : Top.{v}}

-- This is tedious, but necessary because we decided not to allow Prop as morphisms in a category...

def inf_le_left (U V : opens X) : U ⊓ V ⟶ U :=
ulift.up (plift.up inf_le_left)

def inf_le_right (U V : opens X) : U ⊓ V ⟶ V :=
ulift.up (plift.up inf_le_right)

def le_supr {ι : Type*} (U : ι → opens X) (i : ι) : U i ⟶ supr U :=
ulift.up (plift.up (le_supr U i))

end topological_space.opens

open topological_space.opens

namespace Top

variables {C : Type u} [category.{v} C] [has_products C]
variables {X : Top.{v}} (F : presheaf C X) {ι : Type v} (U : ι → opens X)

namespace sheaf_condition

/-- The product of the sections of a presheaf over a family of open sets. -/
def pi_opens : C := ∏ (λ i : ι, F.obj (op (U i)))
/--
The product of the sections of a presheaf over the pairwise intersections of
a family of open sets.
-/
def pi_inters : C := ∏ (λ p : ι × ι, F.obj (op (U p.1 ⊓ U p.2)))

/--
The morphism `Π F.obj (U i) ⟶ Π F.obj (U i) ⊓ (U j)` whose components
are given by the restriction maps from `U i` to `U i ⊓ U j`.
-/
def left_res : pi_opens F U ⟶ pi_inters F U :=
pi.lift (λ p : ι × ι, pi.π _ p.1 ≫ F.map (inf_le_left (U p.1) (U p.2)).op)

/--
The morphism `Π F.obj (U i) ⟶ Π F.obj (U i) ⊓ (U j)` whose components
are given by the restriction maps from `U j` to `U i ⊓ U j`.
-/
def right_res : pi_opens F U ⟶ pi_inters F U :=
pi.lift (λ p : ι × ι, pi.π _ p.2 ≫ F.map (inf_le_right (U p.1) (U p.2)).op)

/--
The morphism `F.obj U ⟶ Π F.obj (U i)` whose components
are given by the restriction maps from `U j` to `U i ⊓ U j`.
-/
def res : F.obj (op (supr U)) ⟶ pi_opens F U :=
pi.lift (λ i : ι, F.map (topological_space.opens.le_supr U i).op)

lemma w : res F U ≫ left_res F U = res F U ≫ right_res F U :=
begin
  dsimp [res, left_res, right_res],
  ext,
  simp,
  rw [←F.map_comp],
  rw [←F.map_comp],
  congr,
end

/--
The equalizer diagram for the sheaf condition.
-/
def diagram : walking_parallel_pair ⥤ C :=
parallel_pair (left_res F U) (right_res F U)

/--
The restriction map `F.obj U ⟶ Π F.obj (U i)` gives a cone over the equalizer diagram
for the sheaf condition. The sheaf condition asserts this cone is a limit cone.
-/
def fork : fork (left_res F U) (right_res F U) := fork.of_ι _ (w F U)

@[simp]
lemma fork_ι : (fork F U).ι = res F U := rfl
@[simp]
lemma fork_π_app_walking_parallel_pair_zero :
  (fork F U).π.app walking_parallel_pair.zero = res F U := rfl
@[simp]
lemma fork_π_app_walking_parallel_pair_one :
  (fork F U).π.app walking_parallel_pair.one = res F U ≫ left_res F U := rfl

end sheaf_condition

/--
The sheaf condition of a `F : presheaf C X` requires that the morphism
`F.obj U ⟶ ∏ F.obj (U i)` (where `U` is some open set which is the union of the `U i`)
is the equalizer of the two morphisms
`∏ F.obj (U i) ⟶ ∏ F.obj (U i) ⊓ (U j)`.
-/
-- Perhaps we want to work with sets of opens, rather than indexed families,
-- to avoid the `v+1` here in the universe levels?
@[derive subsingleton]
def sheaf_condition (F : presheaf C X) : Type (max u (v+1)) :=
Π ⦃ι : Type v⦄ (U : ι → opens X), is_limit (sheaf_condition.fork F U)

variables (C X)

/--
A `sheaf C X` is a presheaf of objects from `C` over a (bundled) topological space `X`,
satisfying the sheaf condition.
-/
structure sheaf :=
(presheaf : presheaf C X)
(sheaf_condition : sheaf_condition presheaf)

instance : category (sheaf C X) :=
begin
  change category (induced_category (presheaf C X) sheaf.presheaf),
  apply_instance,
end

end Top
