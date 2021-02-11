--move this

import category_theory.functor_category
import category_theory.whiskering
import algebra.category.Module.basic
import linear_algebra.tensor_product
import category_theory.graded_object

namespace category_theory

section
variables {C D E : Type*} [category C] [category D] [category E]

-- These already exist in `whiskering.lean`:

@[simps]
def functor.comp_left (F : C ⥤ D) :
  (D ⥤ E) ⥤ (C ⥤ E) :=
{ obj := λ G, F ⋙ G,
  map := λ G₁ G₂ f, whisker_left F f }

@[simps]
def functor.comp_right (G : D ⥤ E) :
  (C ⥤ D) ⥤ (C ⥤ E) :=
{ obj := λ F, F ⋙ G,
  map := λ F₁ F₂ f, whisker_right f G }

end

section
universe variables u
open opposite
variables {C D : Type (u+1)} [large_category C] [large_category D]

@[simps]
def yoneda_hom_comp_yoneda (F : C ⥤ D) :
  yoneda ⟶ ((F.op.comp_left.comp_right).obj (F ⋙ yoneda)) :=
{ app := λ X,
  { app := λ Y f, F.map f,
    naturality' := by { intros Y Z f, ext1 g, exact F.map_comp _ _, } },
  naturality' := by { intros X Y f, ext _ Z g, exact F.map_comp _ _, } }

end

end category_theory

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

open_locale classical

noncomputable instance : has_compl (finset α) :=
{ compl := λ s, univ \ s }

variables {α β} {M : Type*} [comm_monoid M]

@[simp] lemma mem_compl_iff (s : finset α) (a : α) : a ∈ sᶜ ↔ a ∉ s :=
show a ∈ (univ \ s) ↔ ¬ a ∈ s, by simp only [true_and, mem_sdiff, mem_univ]

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
