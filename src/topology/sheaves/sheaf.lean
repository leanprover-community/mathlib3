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

variables {C : Type u} [category.{v} C] [has_products C]
variables {X : Top.{v}} (F : presheaf C X) {ι : Type v} (U : ι → opens X)

namespace sheaf_condition

def product_over_opens : C := pi_obj (λ i : ι, F.obj (op (U i)))
def product_over_intersections : C := limits.pi_obj (λ p : ι × ι, F.obj (op (U p.1 ⊓ U p.2)))

def left_restriction : product_over_opens F U ⟶ product_over_intersections F U :=
pi.lift (λ p : ι × ι, pi.π _ p.1 ≫ F.map (inf_le_left (U p.1) (U p.2)).op)

def right_restriction : product_over_opens F U ⟶ product_over_intersections F U :=
pi.lift (λ p : ι × ι, pi.π _ p.2 ≫ F.map (inf_le_right (U p.1) (U p.2)).op)

def restriction : F.obj (op (supr U)) ⟶ product_over_opens F U :=
pi.lift (λ i : ι, F.map (topological_space.opens.le_supr U i).op)

lemma fork_condition : restriction F U ≫ left_restriction F U = restriction F U ≫ right_restriction F U :=
begin
  dsimp [restriction, left_restriction, right_restriction],
  ext,
  simp,
  rw [←F.map_comp],
  rw [←F.map_comp],
  congr,
end

def fork : fork (left_restriction F U) (right_restriction F U) := fork.of_ι _ (fork_condition F U)

end sheaf_condition

-- Perhaps we want to work with sets of opens, rather than indexed families,
-- to avoid the `v+1` here in the universe levels?
@[derive subsingleton]
def sheaf_condition (F : presheaf C X) : Type (max u (v+1)) :=
Π {ι : Type v} (U : ι → opens X), is_limit (sheaf_condition.fork F U)

variables (C X)

structure sheaf :=
(presheaf : presheaf C X)
(sheaf_condition : sheaf_condition presheaf)

instance : category (sheaf C X) :=
begin
  change category (induced_category (presheaf C X) sheaf.presheaf),
  apply_instance,
end
