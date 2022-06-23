/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.abelian.fully_abelian
import category_theory.abelian.projective
import category_theory.preadditive.generator

/-!
# A special case of the Freyd-Mitchell embedding theorem

We show that cocomplete abelian categories with a projective generator are fully abelian.
-/

noncomputable theory
open_locale classical

open category_theory
open category_theory.limits

universes v u

section
variables {α : Type*} (β : α → Type*) [Π (a : α), has_zero (β a)] [decidable_eq α]

def sigma.proj (a : α) : (Σ (a : α), β a) → β a :=
λ x, if h : x.1 = a then by { subst h, exact x.2 } else 0

lemma sigma.proj_same (a : α) (b : β a) : sigma.proj β a ⟨a, b⟩ = b :=
by simp [sigma.proj]

lemma sigma.proj_diff (a a' : α) (h : a ≠ a') (b : β a') : sigma.proj β a ⟨a', b⟩ = 0 :=
begin
  simp only [sigma.proj, dite_eq_right_iff],
  exact λ h', false.elim (h h'.symm)
end

end

namespace category_theory.abelian
variables {C : Type u} [category.{v} C] [abelian C] [has_coproducts C]
variables (P : C) (hs : is_separator P) [projective P]
variables {D : Type v} [small_category D] [abelian D] (F : D ⥤ C) [full F] [faithful F]
include hs
open_locale zero_object

abbreviation refined_generator : C :=
sigma_obj (λ (f : Σ (A : D), P ⟶ F.obj A), P)

example : projective (refined_generator P hs F) :=
infer_instance

lemma is_separator_refined_generator : is_separator (refined_generator P hs F) :=
is_separator_sigma_of_is_separator _ ⟨0, 0⟩ hs

def from_refined (A : D) : refined_generator P hs F ⟶ F.obj A :=
sigma.desc $ sigma.proj _ A

instance (A : D) : epi (from_refined P hs F A) :=
begin
  let t : refined_generator P hs F ⟶ ∐ (λ (f : P ⟶ F.obj A), P) := sigma.desc
    (λ f, if h : f.1 = A then by { subst h, exact sigma.ι (λ (f : P ⟶ F.obj f.1), P) f.2 } else 0),
  haveI : split_epi t,
  { refine ⟨sigma.desc (λ f, sigma.ι (λ (f : Σ (A : D), P ⟶ F.obj A), P) ⟨_, f⟩), _⟩,
    simp only [t, auto_param_eq],
    ext,
    cases j,
    simp only [colimit.ι_desc_assoc, cofan.mk_ι_app, colimit.ι_desc, eq_self_iff_true, dite_eq_ite,
      if_true, category.comp_id] },
  -- Now just compose with the epimorphism coming from the fact that P is a separator...
end

end category_theory.abelian
