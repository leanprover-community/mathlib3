/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.limits.shapes.normal_mono.basic
import category_theory.limits.shapes.finite_products

/-!
# Normal mono categories with finite products and kernels have all equalizers.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This, and the dual result, are used in the development of abelian categories.
-/

noncomputable theory

open category_theory
open category_theory.limits

variables {C : Type*} [category C] [has_zero_morphisms C]

namespace category_theory.normal_mono_category

variables [has_finite_products C] [has_kernels C] [normal_mono_category C]

/-- The pullback of two monomorphisms exists. -/
@[irreducible]
lemma pullback_of_mono {X Y Z : C} (a : X ⟶ Z) (b : Y ⟶ Z) [mono a] [mono b] :
  has_limit (cospan a b) :=
let ⟨P, f, haf, i⟩ := normal_mono_of_mono a in
let ⟨Q, g, hbg, i'⟩ := normal_mono_of_mono b in
let ⟨a', ha'⟩ := kernel_fork.is_limit.lift' i (kernel.ι (prod.lift f g)) $
    calc kernel.ι (prod.lift f g) ≫ f
        = kernel.ι (prod.lift f g) ≫ prod.lift f g ≫ limits.prod.fst : by rw prod.lift_fst
    ... = (0 : kernel (prod.lift f g) ⟶ P ⨯ Q) ≫ limits.prod.fst : by rw kernel.condition_assoc
    ... = 0 : zero_comp in
let ⟨b', hb'⟩ := kernel_fork.is_limit.lift' i' (kernel.ι (prod.lift f g)) $
    calc kernel.ι (prod.lift f g) ≫ g
        = kernel.ι (prod.lift f g) ≫ (prod.lift f g) ≫ limits.prod.snd : by rw prod.lift_snd
    ... = (0 : kernel (prod.lift f g) ⟶ P ⨯ Q) ≫ limits.prod.snd : by rw kernel.condition_assoc
    ... = 0 : zero_comp in
has_limit.mk { cone := pullback_cone.mk a' b' $ by { simp at ha' hb', rw [ha', hb'] },
  is_limit := pullback_cone.is_limit.mk _
    (λ s, kernel.lift (prod.lift f g) (pullback_cone.snd s ≫ b) $ prod.hom_ext
      (calc ((pullback_cone.snd s ≫ b) ≫ prod.lift f g) ≫ limits.prod.fst
            = pullback_cone.snd s ≫ b ≫ f : by simp only [prod.lift_fst, category.assoc]
        ... = pullback_cone.fst s ≫ a ≫ f : by rw pullback_cone.condition_assoc
        ... = pullback_cone.fst s ≫ 0 : by rw haf
        ... = 0 ≫ limits.prod.fst :
          by rw [comp_zero, zero_comp])
      (calc ((pullback_cone.snd s ≫ b) ≫ prod.lift f g) ≫ limits.prod.snd
            = pullback_cone.snd s ≫ b ≫ g : by simp only [prod.lift_snd, category.assoc]
        ... = pullback_cone.snd s ≫ 0 : by rw hbg
        ... = 0 ≫ limits.prod.snd :
          by rw [comp_zero, zero_comp]))
    (λ s, (cancel_mono a).1 $
      by { rw kernel_fork.ι_of_ι at ha', simp [ha', pullback_cone.condition s] })
    (λ s, (cancel_mono b).1 $
      by { rw kernel_fork.ι_of_ι at hb', simp [hb'] })
    (λ s m h₁ h₂, (cancel_mono (kernel.ι (prod.lift f g))).1 $ calc m ≫ kernel.ι (prod.lift f g)
          = m ≫ a' ≫ a : by { congr, exact ha'.symm }
      ... = pullback_cone.fst s ≫ a : by rw [←category.assoc, h₁]
      ... = pullback_cone.snd s ≫ b : pullback_cone.condition s
      ... = kernel.lift (prod.lift f g) (pullback_cone.snd s ≫ b) _ ≫ kernel.ι (prod.lift f g) :
        by rw kernel.lift_ι) }

section

local attribute [instance] pullback_of_mono

/-- The pullback of `(𝟙 X, f)` and `(𝟙 X, g)` -/
private abbreviation P {X Y : C} (f g : X ⟶ Y)
  [mono (prod.lift (𝟙 X) f)] [mono (prod.lift (𝟙 X) g)] : C :=
pullback (prod.lift (𝟙 X) f) (prod.lift (𝟙 X) g)

/-- The equalizer of `f` and `g` exists. -/
@[irreducible]
lemma has_limit_parallel_pair {X Y : C} (f g : X ⟶ Y) : has_limit (parallel_pair f g) :=
have huv : (pullback.fst : P f g ⟶ X) = pullback.snd, from
  calc (pullback.fst : P f g ⟶ X) = pullback.fst ≫ 𝟙 _ : eq.symm $ category.comp_id _
    ... = pullback.fst ≫ prod.lift (𝟙 X) f ≫ limits.prod.fst : by rw prod.lift_fst
    ... = pullback.snd ≫ prod.lift (𝟙 X) g ≫ limits.prod.fst : by rw pullback.condition_assoc
    ... = pullback.snd : by rw [prod.lift_fst, category.comp_id],
have hvu : (pullback.fst : P f g ⟶ X) ≫ f = pullback.snd ≫ g, from
  calc (pullback.fst : P f g ⟶ X) ≫ f
        = pullback.fst ≫ prod.lift (𝟙 X) f ≫ limits.prod.snd : by rw prod.lift_snd
    ... = pullback.snd ≫ prod.lift (𝟙 X) g ≫ limits.prod.snd : by rw pullback.condition_assoc
    ... = pullback.snd ≫ g : by rw prod.lift_snd,
have huu : (pullback.fst : P f g ⟶ X) ≫ f = pullback.fst ≫ g, by rw [hvu, ←huv],
has_limit.mk { cone := fork.of_ι pullback.fst huu,
  is_limit := fork.is_limit.mk _
  (λ s, pullback.lift (fork.ι s) (fork.ι s) $ prod.hom_ext
    (by simp only [prod.lift_fst, category.assoc])
    (by simp only [prod.comp_lift, fork.condition]))
  (λ s, by simp only [fork.ι_of_ι, pullback.lift_fst])
  (λ s m h, pullback.hom_ext
    (by simpa only [pullback.lift_fst] using h)
    (by simpa only [huv.symm, pullback.lift_fst] using h)) }

end

section
local attribute [instance] has_limit_parallel_pair

/-- A `normal_mono_category` category with finite products and kernels has all equalizers. -/
@[priority 100] instance has_equalizers : has_equalizers C :=
has_equalizers_of_has_limit_parallel_pair _

end

/-- If a zero morphism is a cokernel of `f`, then `f` is an epimorphism. -/
lemma epi_of_zero_cokernel {X Y : C} (f : X ⟶ Y) (Z : C)
  (l : is_colimit (cokernel_cofork.of_π (0 : Y ⟶ Z) (show f ≫ 0 = 0, by simp))) : epi f :=
⟨λ P u v huv,
 begin
  obtain ⟨W, w, hw, hl⟩ := normal_mono_of_mono (equalizer.ι u v),
  obtain ⟨m, hm⟩ := equalizer.lift' f huv,
  have hwf : f ≫ w = 0,
  { rw [←hm, category.assoc, hw, comp_zero] },
  obtain ⟨n, hn⟩ := cokernel_cofork.is_colimit.desc' l _ hwf,
  rw [cofork.π_of_π, zero_comp] at hn,
  haveI : is_iso (equalizer.ι u v),
  { apply is_iso_limit_cone_parallel_pair_of_eq hn.symm hl },
  apply (cancel_epi (equalizer.ι u v)).1,
  exact equalizer.condition _ _
 end⟩

section
variables [has_zero_object C]
open_locale zero_object

/-- If `f ≫ g = 0` implies `g = 0` for all `g`, then `g` is a monomorphism. -/
lemma epi_of_zero_cancel {X Y : C} (f : X ⟶ Y)
  (hf : ∀ (Z : C) (g : Y ⟶ Z) (hgf : f ≫ g = 0), g = 0) : epi f :=
epi_of_zero_cokernel f 0 $ zero_cokernel_of_zero_cancel f hf

end

end category_theory.normal_mono_category

namespace category_theory.normal_epi_category

variables [has_finite_coproducts C] [has_cokernels C] [normal_epi_category C]

/-- The pushout of two epimorphisms exists. -/
@[irreducible]
lemma pushout_of_epi {X Y Z : C} (a : X ⟶ Y) (b : X ⟶ Z) [epi a] [epi b] :
  has_colimit (span a b) :=
let ⟨P, f, hfa, i⟩ := normal_epi_of_epi a in
let ⟨Q, g, hgb, i'⟩ := normal_epi_of_epi b in
let ⟨a', ha'⟩ := cokernel_cofork.is_colimit.desc' i (cokernel.π (coprod.desc f g)) $
  calc f ≫ cokernel.π (coprod.desc f g)
      = coprod.inl ≫ coprod.desc f g ≫ cokernel.π (coprod.desc f g) : by rw coprod.inl_desc_assoc
  ... = coprod.inl ≫ (0 : P ⨿ Q ⟶ cokernel (coprod.desc f g)) : by rw cokernel.condition
  ... = 0 : has_zero_morphisms.comp_zero _ _ in
let ⟨b', hb'⟩ := cokernel_cofork.is_colimit.desc' i' (cokernel.π (coprod.desc f g)) $
  calc g ≫ cokernel.π (coprod.desc f g)
      = coprod.inr ≫ coprod.desc f g ≫ cokernel.π (coprod.desc f g) : by rw coprod.inr_desc_assoc
  ... = coprod.inr ≫ (0 : P ⨿ Q ⟶ cokernel (coprod.desc f g)) :  by rw cokernel.condition
  ... = 0 : has_zero_morphisms.comp_zero _ _ in
has_colimit.mk
{ cocone := pushout_cocone.mk a' b' $ by { simp only [cofork.π_of_π] at ha' hb', rw [ha', hb'] },
  is_colimit := pushout_cocone.is_colimit.mk _
  (λ s, cokernel.desc (coprod.desc f g) (b ≫ pushout_cocone.inr s) $ coprod.hom_ext
    (calc coprod.inl ≫ coprod.desc f g ≫ b ≫ pushout_cocone.inr s
          = f ≫ b ≫ pushout_cocone.inr s : by rw coprod.inl_desc_assoc
      ... = f ≫ a ≫ pushout_cocone.inl s : by rw pushout_cocone.condition
      ... = 0 ≫ pushout_cocone.inl s : by rw reassoc_of hfa
      ... = coprod.inl ≫ 0 : by rw [comp_zero, zero_comp])
    (calc coprod.inr ≫ coprod.desc f g ≫ b ≫ pushout_cocone.inr s
          = g ≫ b ≫ pushout_cocone.inr s : by rw coprod.inr_desc_assoc
      ... = 0 ≫ pushout_cocone.inr s : by rw reassoc_of hgb
      ... = coprod.inr ≫ 0 : by rw [comp_zero, zero_comp]))
  (λ s, (cancel_epi a).1 $
    by { rw cokernel_cofork.π_of_π at ha', simp [reassoc_of ha', pushout_cocone.condition s] })
  (λ s, (cancel_epi b).1 $ by { rw cokernel_cofork.π_of_π at hb', simp [reassoc_of hb'] })
  (λ s m h₁ h₂, (cancel_epi (cokernel.π (coprod.desc f g))).1 $
  calc cokernel.π (coprod.desc f g) ≫ m
        = (a ≫ a') ≫ m : by { congr, exact ha'.symm }
    ... = a ≫ pushout_cocone.inl s : by rw [category.assoc, h₁]
    ... = b ≫ pushout_cocone.inr s : pushout_cocone.condition s
    ... = cokernel.π (coprod.desc f g) ≫
            cokernel.desc (coprod.desc f g) (b ≫ pushout_cocone.inr s) _ :
      by rw cokernel.π_desc) }



section
local attribute [instance] pushout_of_epi

/-- The pushout of `(𝟙 Y, f)` and `(𝟙 Y, g)`. -/
private abbreviation Q {X Y : C} (f g : X ⟶ Y)
  [epi (coprod.desc (𝟙 Y) f)] [epi (coprod.desc (𝟙 Y) g)] : C :=
pushout (coprod.desc (𝟙 Y) f) (coprod.desc (𝟙 Y) g)

/-- The coequalizer of `f` and `g` exists. -/
@[irreducible]
lemma has_colimit_parallel_pair {X Y : C} (f g : X ⟶ Y) : has_colimit (parallel_pair f g) :=
have huv : (pushout.inl : Y ⟶ Q f g) = pushout.inr, from
  calc (pushout.inl : Y ⟶ Q f g) = 𝟙 _ ≫ pushout.inl : eq.symm $ category.id_comp _
    ... = (coprod.inl ≫ coprod.desc (𝟙 Y) f) ≫ pushout.inl : by rw coprod.inl_desc
    ... = (coprod.inl ≫ coprod.desc (𝟙 Y) g) ≫ pushout.inr :
      by simp only [category.assoc, pushout.condition]
    ... = pushout.inr : by rw [coprod.inl_desc, category.id_comp],
have hvu : f ≫ (pushout.inl : Y ⟶ Q f g) = g ≫ pushout.inr, from
  calc f ≫ (pushout.inl : Y ⟶ Q f g)
        = (coprod.inr ≫ coprod.desc (𝟙 Y) f) ≫ pushout.inl : by rw coprod.inr_desc
    ... = (coprod.inr ≫ coprod.desc (𝟙 Y) g) ≫ pushout.inr :
      by simp only [category.assoc, pushout.condition]
    ... = g ≫ pushout.inr : by rw coprod.inr_desc,
have huu : f ≫ (pushout.inl : Y ⟶ Q f g) = g ≫ pushout.inl, by rw [hvu, huv],
has_colimit.mk { cocone := cofork.of_π pushout.inl huu,
  is_colimit := cofork.is_colimit.mk _
  (λ s, pushout.desc (cofork.π s) (cofork.π s) $ coprod.hom_ext
    (by simp only [coprod.inl_desc_assoc])
    (by simp only [coprod.desc_comp, cofork.condition]))
  (λ s, by simp only [pushout.inl_desc, cofork.π_of_π])
  (λ s m h, pushout.hom_ext
    (by simpa only [pushout.inl_desc] using h)
    (by simpa only [huv.symm, pushout.inl_desc] using h)) }

end

section
local attribute [instance] has_colimit_parallel_pair

/-- A `normal_epi_category` category with finite coproducts and cokernels has all coequalizers. -/
@[priority 100] instance has_coequalizers : has_coequalizers C :=
has_coequalizers_of_has_colimit_parallel_pair _

end

/-- If a zero morphism is a kernel of `f`, then `f` is a monomorphism. -/
lemma mono_of_zero_kernel {X Y : C} (f : X ⟶ Y) (Z : C)
  (l : is_limit (kernel_fork.of_ι (0 : Z ⟶ X) (show 0 ≫ f = 0, by simp))) : mono f :=
⟨λ P u v huv,
 begin
  obtain ⟨W, w, hw, hl⟩ := normal_epi_of_epi (coequalizer.π u v),
  obtain ⟨m, hm⟩ := coequalizer.desc' f huv,
  have hwf : w ≫ f = 0,
  { rw [←hm, reassoc_of hw, zero_comp] },
  obtain ⟨n, hn⟩ := kernel_fork.is_limit.lift' l _ hwf,
  rw [fork.ι_of_ι, has_zero_morphisms.comp_zero] at hn,
  haveI : is_iso (coequalizer.π u v),
  { apply is_iso_colimit_cocone_parallel_pair_of_eq hn.symm hl },
  apply (cancel_mono (coequalizer.π u v)).1,
  exact coequalizer.condition _ _
 end⟩

section
variables [has_zero_object C]
open_locale zero_object

/-- If `g ≫ f = 0` implies `g = 0` for all `g`, then `f` is a monomorphism. -/
lemma mono_of_cancel_zero {X Y : C} (f : X ⟶ Y)
  (hf : ∀ (Z : C) (g : Z ⟶ X) (hgf : g ≫ f = 0), g = 0) : mono f :=
mono_of_zero_kernel f 0 $ zero_kernel_of_cancel_zero f hf

end

end category_theory.normal_epi_category
