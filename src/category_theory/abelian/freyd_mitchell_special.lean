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
open opposite

universes w v u

namespace category_theory.abelian
variables {C : Type u} [category.{v} C] [abelian C] [has_coproducts C]
variables (P : C) (hs : is_separator P) [projective P]
variables {D : Type v} [small_category D] [abelian D] (F : D ⥤ C) [full F] [faithful F]
include hs
open_locale zero_object

abbreviation refined_generator_component (A : D) : C :=
sigma_obj (λ (f : P ⟶ F.obj A), P)

abbreviation refined_generator : C :=
sigma_obj (refined_generator_component P hs F)

example : projective (refined_generator P hs F) :=
infer_instance

lemma is_separator_refined_generator_component (A : D) :
  is_separator (refined_generator_component P hs F A) :=
is_separator_sigma_of_is_separator _ 0 hs

lemma is_separator_refined_generator : is_separator (refined_generator P hs F) :=
is_separator_sigma_of_is_separator _ 0 $ is_separator_refined_generator_component P hs F _

def from_refined (A : D) : refined_generator P hs F ⟶ F.obj A :=
sigma.desc (pi.single _ (𝟙 (refined_generator_component P hs F A))) ≫
  sigma.desc (λ (f : P ⟶ F.obj A), f)

lemma epi_blub {β : Type w} (f : β → C) [has_coproduct f]
  (a : β) : split_epi (sigma.desc (pi.single a (𝟙 (f a)))) :=
⟨sigma.ι f a⟩

instance (A : D) : epi (from_refined P hs F A) :=
begin
  haveI := (is_separator_iff_epi _).1 hs (F.obj A),
  haveI : split_epi (sigma.desc (pi.single _ (𝟙 (refined_generator_component P hs F A)))),
  { apply epi_blub P hs (refined_generator_component P hs F), },
  apply epi_comp
end

instance : faithful (coyoneda.obj (op (refined_generator P hs F))) :=
sorry

instance : preserves_finite_limits (coyoneda.obj (op (refined_generator P hs F))) :=
sorry

instance : preserves_finite_colimits (coyoneda.obj (op (refined_generator P hs F))) :=
sorry

instance : full (F ⋙ coyoneda.obj (op (refined_generator P hs F))) :=
begin
  suffices : ∀ (A B : D), function.surjective ((F ⋙ coyoneda.obj (op (refined_generator P hs F))).map : (A ⟶ B) → _)
end

end category_theory.abelian
