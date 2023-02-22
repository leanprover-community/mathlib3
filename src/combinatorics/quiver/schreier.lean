import combinatorics.quiver.basic
import combinatorics.quiver.single_obj
import group_theory.group_action.basic
import group_theory.group_action.group
import combinatorics.quiver.covering
import group_theory.subgroup.basic
import group_theory.coset
import group_theory.quotient_group
import group_theory.group_action.quotient

universes u v w

namespace quiver

section basic

def schreier_graph (V : Type*) {M : Type*} [has_smul M V] {S : Type*} (ι : S → M) := V

@[simps] def equiv_schreier_graph {V : Type*} {M : Type*} [has_smul M V] {S : Type*} {ι : S → M} :
  V ≃ schreier_graph V ι := equiv.refl V

variables (V : Type*) {M : Type*} [has_smul M V] {S : Type*} (ι : S → M)

instance : has_smul M (schreier_graph V ι) :=
{ smul := λ x y, equiv_schreier_graph $ x • (equiv_schreier_graph.symm y)}

instance schreier_graph.quiver : quiver (schreier_graph V ι) :=
{ hom := λ x y, {s : S // (ι s) • x = y} }

@[simps] def schreier_graph_covering : (schreier_graph V ι) ⥤q single_obj S :=
{ obj := λ (x : schreier_graph V ι), single_obj.star S,
  map := λ x y e, subtype.rec_on e (λ s h, s), }

end basic

section group_action

variables (V : Type*) {M : Type*} [group M] [mul_action M V] {S : Type*} (ι : S → M)

instance : mul_action M (schreier_graph V ι) :=
{ smul := has_smul.smul,
  one_smul := mul_action.one_smul,
  mul_smul := mul_action.mul_smul }

lemma schreier_graph_covering_is_covering : (schreier_graph_covering V ι).is_covering :=
begin
  refine ⟨λ u, ⟨_, _⟩, λ u, ⟨_, _⟩⟩,
  { rintro ⟨v,⟨x,hx⟩⟩ ⟨w,⟨y,hy⟩⟩ h,
    simp only [prefunctor.star_apply, schreier_graph_covering_map, single_obj.to_hom_apply,
               eq_iff_true_of_subsingleton, heq_iff_eq, true_and] at h,
    subst_vars, },
  { rintro ⟨⟨⟩,x⟩, exact ⟨⟨(ι x) • u, ⟨x, rfl⟩⟩, rfl⟩, },
  { rintro ⟨v,⟨x,hx⟩⟩ ⟨w,⟨y,hy⟩⟩ h,
    simp only [prefunctor.costar_apply, schreier_graph_covering_map, single_obj.to_hom_apply,
               eq_iff_true_of_subsingleton, heq_iff_eq, true_and] at h,
    subst_vars,
    simp only [smul_left_cancel_iff] at hy,
    subst hy, },
  { rintro ⟨⟨⟩,x⟩,
    exact ⟨⟨(ι x) ⁻¹ • u, ⟨x, by simp⟩⟩, by simp⟩, },
end

abbreviation schreier_coset_graph (H : subgroup M) := schreier_graph (M ⧸ H) ι

abbreviation cayley_graph := schreier_coset_graph ι (⊥ : subgroup M)

end group_action

end quiver
