import algebra.category.Group.limits
import algebra.category.Group.images
import category_theory.limits.shapes.kernels
import group_theory.quotient_group
import category_theory.over

open category_theory
open category_theory.limits

universes u

namespace AddCommGroup

@[simp]
lemma coe_of {G : Type*} [add_comm_group G] : (AddCommGroup.of G : Type*) = G := rfl

-- What is the right generality to prove this?
@[simp]
lemma zero_morphism_apply {G H : AddCommGroup} (g : G) : (0 : G ⟶ H) g = 0 := rfl

@[simps]
def of_add_subgroup_bot {G : Type*} [add_comm_group G] : AddCommGroup.of (⊥ : add_subgroup G) ≅ 0 :=
{ hom := 0, inv := 0, }

def of_add_subgroup_top {G : Type*} [add_comm_group G] :
  AddCommGroup.of (⊤ : add_subgroup G) ≅ AddCommGroup.of G :=
{ hom := add_subgroup.subtype ⊤,
  inv := { to_fun := λ g, ⟨g, by trivial⟩, map_zero' := by tidy, map_add' := by tidy, }, }

def of_add_subgroup_le {G : Type*} [add_comm_group G] {H K : add_subgroup G} (w : H ≤ K) :
  AddCommGroup.of H ⟶ AddCommGroup.of K :=
{ to_fun := λ h, ⟨h.1, add_subgroup.le_def.mp w h.2⟩,
  map_zero' := by tidy,
  map_add' := by tidy, }

@[simp] lemma of_add_subgroup_le_apply_val
  {G : Type*} [add_comm_group G] {H K : add_subgroup G} (w : H ≤ K) (h : H) :
  (of_add_subgroup_le w h : K).1 = h.1 := rfl

@[simps]
def of_add_subgroup_eq {G : Type*} [add_comm_group G] {H K : add_subgroup G} (w : H = K) :
  AddCommGroup.of H ≅ AddCommGroup.of K :=
{ hom := of_add_subgroup_le (le_of_eq w),
  inv := of_add_subgroup_le (le_of_eq w.symm), }

end AddCommGroup
