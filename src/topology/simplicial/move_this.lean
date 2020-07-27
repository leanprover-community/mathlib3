--move this

import category_theory.functor_category
import category_theory.whiskering
import algebra.category.Module.basic
import linear_algebra.tensor_product
import category_theory.graded_object

namespace category_theory

variables {C D E : Type*} [category C] [category D] [category E]

def functor.comp_left (F : C ⥤ D) :
  (D ⥤ E) ⥤ (C ⥤ E) :=
{ obj := λ G, F ⋙ G,
  map := λ G₁ G₂ f, whisker_left F f }

def functor.comp_right (G : D ⥤ E) :
  (C ⥤ D) ⥤ (C ⥤ E) :=
{ obj := λ F, F ⋙ G,
  map := λ F₁ F₂ f, whisker_right f G }

end category_theory

noncomputable def finsupp.lmap_domain (R : Type*) [ring R] {X Y : Type*} (f : X ⟶ Y) :
  linear_map R (X →₀ R) (Y →₀ R) :=
{ to_fun := finsupp.map_domain f,
  map_add' := λ _ _, finsupp.map_domain_add,
  map_smul' := λ _ _, finsupp.map_domain_smul _ _ }

@[simp] lemma finsupp.coe_lmap_domain (R : Type*) [ring R] {X Y : Type*} (f : X ⟶ Y) :
  (finsupp.lmap_domain R f : (X →₀ R) → (Y →₀ R)) = finsupp.map_domain f := rfl

namespace Module

universe variables u

variables (R : Type u) [ring R]

@[simps]
noncomputable def Free : Type u ⥤ Module R :=
{ obj := λ X, Module.of R (X →₀ R),
  map := λ X Y f, finsupp.lmap_domain R f,
  map_id' := by { intros, ext1 v, exact finsupp.map_domain_id },
  map_comp' := by { intros, ext1 v,
    simp only [finsupp.coe_lmap_domain, function.comp_app, coe_comp],
    exact finsupp.map_domain_comp } }

end Module

namespace linear_map
variables (R M N P : Type*) [comm_ring R]
variables [add_comm_group M] [module R M]
variables [add_comm_group N] [module R N]
variables [add_comm_group P] [module R P]
variables (f : M →ₗ[R] N) (g : N →ₗ[R] P)

lemma lcomp_comp : lcomp R P f g = g.comp f := rfl

lemma llcomp_lcomp : llcomp R M N P g f = lcomp R P f g := rfl

end linear_map

namespace finset
open_locale big_operators
variables (α β : Type*) [fintype α] [fintype β]

@[simp]
lemma univ_product_univ : finset.univ.product finset.univ = (finset.univ : finset (α × β)) :=
by simp only [finset.eq_univ_iff_forall, prod.forall, mem_univ, forall_2_true_iff, and_self, mem_product]

open_locale classical

noncomputable instance : has_compl (finset α) :=
{ compl := λ s, univ \ s }

variables {α β} {M : Type*} [comm_monoid M]

@[simp] lemma mem_compl_iff (s : finset α) (a : α) : a ∈ sᶜ ↔ a ∉ s :=
show a ∈ (univ \ s) ↔ ¬ a ∈ s, by simp only [true_and, mem_sdiff, mem_univ]

@[to_additive]
lemma prod_mul_prod_compl (s : finset α) (f : α → M) :
  (∏ i in s, f i) * ∏ i in sᶜ, f i = ∏ i, f i :=
by { rw [← prod_sdiff (subset_univ s), mul_comm], refl, }

end finset

namespace category_theory
namespace graded_object
universe variables u v w
variables {C : Type u} [category.{v} C] {β : Type w}
variables {X Y : graded_object β C}

lemma hom_congr (f : X ⟶ Y) {i j : β} (h : i = j) :
  f i = eq_to_hom (by simp [h]) ≫ f j ≫ eq_to_hom (by simp [h.symm]) :=
by { cases h, simp, }

end graded_object
end category_theory
