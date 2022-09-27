import category_theory.groupoid
import algebra.group.defs
import algebra.hom.group
import algebra.hom.equiv
import combinatorics.quiver.path


namespace category_theory

universes u v

variables {C : Type u} [groupoid C]

instance groupoid.vertex_group (c : C): group (c ⟶ c) :=
{ mul := λ (x y : c ⟶ c), x ≫ y
, mul_assoc := category.assoc
, one := 𝟙 c
, one_mul := category.id_comp
, mul_one := category.comp_id
, inv := groupoid.inv
, mul_left_inv := groupoid.inv_comp }

@[simp] lemma groupoid.vertex_group.mul_eq_comp (c : C) (γ δ : c ⟶ c) : γ * δ = γ ≫ δ := rfl
@[simp] lemma groupoid.vertex_group.inv_eq_inv (c : C) (γ : c ⟶ c) : γ ⁻¹ = inv γ := by
{ apply groupoid.inv_eq_inv, }

def groupoid.vertex_group_isom_of_map [groupoid C] {c d : C} (f : c ⟶ d) :
  (c ⟶ c) ≃* (d ⟶ d) :=
begin
  refine_struct ⟨λ γ, (groupoid.inv f) ≫ γ ≫ f, λ δ, f ≫ δ ≫ (groupoid.inv f), _, _, _⟩,
  { rintro x,
    simp_rw [category.assoc, groupoid.comp_inv, category.comp_id,←category.assoc, groupoid.comp_inv, category.id_comp], },
  { rintro x,
    simp_rw [category.assoc, groupoid.inv_comp, ←category.assoc, groupoid.inv_comp,category.id_comp, category.comp_id], },
  { rintro x y,
    have : x ≫ y = x ≫ f ≫ (groupoid.inv f) ≫ y, by
    { congr, rw [←category.assoc,groupoid.comp_inv,category.id_comp], },
    simp [this,groupoid.vertex_group.mul_eq_comp,category.assoc], },
end


def groupoid.vertex_group_isom_of_path [groupoid C] (c d : C)  (p : quiver.path c d) : (c ⟶ c) ≃* (d ⟶ d) :=
begin
  induction p,
  { reflexivity },
  { apply p_ih.trans,  apply groupoid.vertex_group_isom_of_map, assumption, }
end

end category_theory
