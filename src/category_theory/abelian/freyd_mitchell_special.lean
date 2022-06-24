/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.abelian.fully_abelian
import category_theory.abelian.projective
import category_theory.preadditive.generator
import category_theory.preadditive.yoneda
import category_theory.limits.constructions.epi_mono
import algebra.category.Module.projective

/-!
# A special case of the Freyd-Mitchell embedding theorem

We show that cocomplete abelian categories with a projective generator are fully abelian.
-/

noncomputable theory
open_locale classical

open category_theory
open category_theory.limits
open opposite

universes w v u v₁ v₂ u₁ u₂

namespace category_theory.functor
variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D] (F : C ⥤ D)

def full_of_surjective (h : ∀ (X Y : C) (f : F.obj X ⟶ F.obj Y), ∃ f', F.map f' = f) : full F :=
begin
  choose f h using h,
  exact ⟨f, h⟩
end

end category_theory.functor

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

instance : faithful (preadditive_coyoneda_obj (op (refined_generator P hs F))) :=
sorry

instance : preserves_finite_limits (preadditive_coyoneda_obj (op (refined_generator P hs F))) :=
sorry

instance : preserves_finite_colimits (preadditive_coyoneda_obj (op (refined_generator P hs F))) :=
sorry

instance : full (F ⋙ preadditive_coyoneda_obj (op (refined_generator P hs F))) :=
begin
  let G := preadditive_coyoneda_obj (op (refined_generator P hs F)),
  haveI : faithful G,
  { dsimp [G], apply_instance },
  let F' := F ⋙ G,
  apply category_theory.functor.full_of_surjective,
  rintros X Y (f : F'.obj X ⟶ F'.obj Y),
  let l := from_refined P hs F X,
  let R := End (op (refined_generator P hs F)),
  haveI : projective (G.obj (refined_generator P hs F)),
  { sorry, },
  let t : End _ := projective.factor_thru
    (G.map (from_refined P hs F X) ≫ f) (G.map (from_refined P hs F Y)),
  dsimp [G] at t,
  let t' : End (Module.of _ (End _)) := t,
  let r : refined_generator P hs F ⟶ refined_generator P hs F := t'.to_fun (𝟙 _),
  have h : G.map r = t',
  { ext1,
    dsimp,
    have hx : x = ((x.op : End (op (refined_generator P hs F))) • (𝟙 _)) :=
       (category.comp_id _).symm,
    conv_rhs { rw [hx] },
    simp only [linear_map.map_smulₛₗ, ring_hom.id_apply],
    refl },
  have hr : kernel.ι (from_refined P hs F X) ≫ r ≫ from_refined P hs F Y = 0,
  { apply G.map_injective,
    simp only [h, functor.map_comp, projective.factor_thru_comp, functor.map_zero],
    rw [← category.assoc, ← G.map_comp, kernel.condition, G.map_zero, zero_comp] },
  let hcoker : is_colimit (cokernel_cofork.of_π (from_refined P hs F X) (kernel.condition _) :
    cokernel_cofork (kernel.ι (from_refined P hs F X))) :=
    sorry,
  let w := hcoker.desc (cokernel_cofork.of_π _ hr),
  refine ⟨F.preimage w, _⟩,
  rw ← cancel_epi (G.map (from_refined P hs F X)),
  simp only [functor.comp_map, functor.image_preimage],
  erw [←G.map_comp],
  have hc := hcoker.fac (cokernel_cofork.of_π _ hr) walking_parallel_pair.one,
  simp only [cofork.of_π_ι_app] at hc,
  erw [hc, functor.map_comp, h],
  exact projective.factor_thru_comp _ _
end

end category_theory.abelian
