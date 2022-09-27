import category_theory.groupoid
import algebra.group.defs
import algebra.hom.group
import algebra.hom.equiv
import logic.equiv.transfer_instance
import category_theory.endomorphism -- has the group instance for c ≃ c in a category C
import combinatorics.quiver.path
import combinatorics.quiver.connected_component

namespace category_theory

universes u v

variables {C : Type u} [groupoid C]

instance groupoid.vertex_group  {C : Type u} [G : groupoid C] (c : C) : group (c ⟶ c) :=
  @equiv.group _ _ (groupoid.iso_equiv_hom c c).symm (Aut.group c)

/-
@[simp] lemma groupoid.vertex_group.mul_eq_comp (c : C) (γ δ : c ⟶ c) : γ * δ = δ ≫ γ := by
{ simp only [End.mul_def]}
@[simp] lemma groupoid.vertex_group.inv_eq_inv (c : C) (γ : c ⟶ c) : γ ⁻¹ = inv γ := by
{  }
-/
def groupoid.vertex_group_isom_of_map [groupoid C] {c d : C} (f : c ⟶ d) :
  (c ⟶ c) ≃* (d ⟶ d) :=
begin
  apply Aut.Aut_mul_equiv_of_iso,
end

def groupoid.vertex_group_isom_of_path [groupoid C] (c d : C)  (p : quiver.path c d) : (c ⟶ c) ≃* (d ⟶ d) :=
begin
  induction p,
  { reflexivity },
  { apply p_ih.trans,  apply groupoid.vertex_group_isom_of_map, assumption, }
end

end category_theory
