/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.abelian.pseudoelements

/-!
# The four lemma

Consider the following commutative diagram with exact rows in an abelian category:

A ---f--> B ---g--> C ---h--> D
|         |         |         |
α         β         γ         δ
|         |         |         |
v         v         v         v
A' --f'-> B' --g'-> C' --h'-> D'

We prove the "mono" version of the four lemma: if α is an epimorphism and β and δ are monomorphisms,
then γ is a monomorphism.

## Future work

The "epi" four lemma and the five lemma, which is then an easy corollary.

## Tags

four lemma, diagram lemma, diagram chase
-/
open category_theory (hiding comp_apply)
open category_theory.abelian.pseudoelement
open category_theory.limits

universes v u

variables {V : Type u} [category.{v} V] [abelian V]

local attribute [instance] preadditive.has_equalizers_of_has_kernels
local attribute [instance] object_to_sort hom_to_fun

namespace category_theory.abelian

def pullback.is_limit_inner {A B C D : V} (f : A ⟶ C) (g : B ⟶ C) (h : D ⟶ C) [mono h]
  (x : A ⟶ D) (y : B ⟶ D) (hxh : x ≫ h = f) (hyh : y ≫ h = g) (s : pullback_cone f g)
  (hs : is_limit s) : is_limit (pullback_cone.mk _ _ (show s.fst ≫ x = s.snd ≫ y,
    from (cancel_mono h).1 $ by simp only [category.assoc, hxh, hyh, s.condition])) :=
pullback_cone.is_limit_aux' _ $ λ t,
  ⟨hs.lift (pullback_cone.mk t.fst t.snd $ by rw [←hxh, ←hyh, reassoc_of t.condition]),
  ⟨hs.fac _ walking_cospan.left, hs.fac _ walking_cospan.right, λ r hr hr',
  begin
    apply pullback_cone.is_limit.hom_ext hs;
    simp only [pullback_cone.mk_fst, pullback_cone.mk_snd] at ⊢ hr hr';
    simp only [hr, hr'];
    symmetry,
    exacts [hs.fac _ walking_cospan.left, hs.fac _ walking_cospan.right]
  end⟩⟩

def pushout.is_colimit_inner {A B C D : V} (f : A ⟶ B) (g : A ⟶ C) (h : A ⟶ D) [epi h] (x : D ⟶ B)
  (y : D ⟶ C) (hhx : h ≫ x = f) (hhy : h ≫ y = g) (s : pushout_cocone f g) (hs : is_colimit s) :
  is_colimit (pushout_cocone.mk _ _ (show x ≫ s.inl = y ≫ s.inr,
    from (cancel_epi h).1 $ by rw [reassoc_of hhx, reassoc_of hhy, s.condition])) :=
pushout_cocone.is_colimit_aux' _ $ λ t,
  ⟨hs.desc (pushout_cocone.mk t.inl t.inr $
    by rw [←hhx, ←hhy, category.assoc, category.assoc, t.condition]),
  ⟨hs.fac _ walking_span.left, hs.fac _ walking_span.right, λ r hr hr',
  begin
    apply pushout_cocone.is_colimit.hom_ext hs;
    simp only [pushout_cocone.mk_inl, pushout_cocone.mk_inr] at ⊢ hr hr';
    simp only [hr, hr'];
    symmetry,
    exacts [hs.fac _ walking_span.left, hs.fac _ walking_span.right]
  end⟩⟩

lemma epi_fst_of_factor_thru_epi_mono_factorization {A B C D : V} (f : A ⟶ C) (g : B ⟶ C) (g₁ : B ⟶ D)
  [epi g₁] (g₂ : D ⟶ C) [mono g₂] (hg : g₁ ≫ g₂ = g) (f' : A ⟶ D) (hf : f' ≫ g₂ = f)
  (t : pullback_cone f g) (ht : is_limit t) : epi t.fst :=
begin
  let := pullback.is_limit_inner f g g₂ f' g₁ hf hg t ht,
  apply abelian.epi_fst_of_is_limit _ _ this
end

lemma mono_inl_of_factor_thru_epi_mono_factorization {A B C D : V} (f : A ⟶ B) (g : A ⟶ C) (g₁ : A ⟶ D)
  [epi g₁] (g₂ : D ⟶ C) [mono g₂] (hg : g₁ ≫ g₂ = g) (f' : D ⟶ B) (hf : g₁ ≫ f' = f)
  (t : pushout_cocone f g) (ht : is_colimit t) : mono t.inl :=
begin
  let := pushout.is_colimit_inner _ _ _ _ _ hf hg t ht,
  apply abelian.mono_inl_of_is_colimit _ _ this
end

variables {A B C D A' B' C' D' : V}
variables {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D}
variables {f' : A' ⟶ B'} {g' : B' ⟶ C'} {h' : C' ⟶ D'}
variables {α : A ⟶ A'} {β : B ⟶ B'} {γ : C ⟶ C'} {δ : D ⟶ D'}
variables [exact f g] [exact g h] [exact f' g']
variables (comm₁ : α ≫ f' = f ≫ β) (comm₂ : β ≫ g' = g ≫ γ) (comm₃ : γ ≫ h' = h ≫ δ)
include comm₁ comm₂ comm₃

/-- The four lemma, mono version. For names of objects and morphisms, consider the following
    diagram:

```
A ---f--> B ---g--> C ---h--> D
|         |         |         |
α         β         γ         δ
|         |         |         |
v         v         v         v
A' --f'-> B' --g'-> C' --h'-> D'
```
-/
lemma mono_of_epi_of_mono_of_mono (hα : epi α) (hβ : mono β) (hδ : mono δ) : mono γ :=
mono_of_zero_of_map_zero _ $ λ c hc,
  have h c = 0, from
    suffices δ (h c) = 0, from zero_of_map_zero _ (pseudo_injective_of_mono _) _ this,
    calc δ (h c) = h' (γ c) : by rw [←comp_apply, ←comm₃, comp_apply]
             ... = h' 0     : by rw hc
             ... = 0        : apply_zero _,
  exists.elim (pseudo_exact_of_exact.2 _ this) $ λ b hb,
    have g' (β b) = 0, from
      calc g' (β b) = γ (g b) : by rw [←comp_apply, comm₂, comp_apply]
                ... = γ c     : by rw hb
                ... = 0       : hc,
    exists.elim (pseudo_exact_of_exact.2 _ this) $ λ a' ha',
      exists.elim (pseudo_surjective_of_epi α a') $ λ a ha,
      have f a = b, from
        suffices β (f a) = β b, from pseudo_injective_of_mono _ this,
        calc β (f a) = f' (α a) : by rw [←comp_apply, ←comm₁, comp_apply]
                 ... = f' a'    : by rw ha
                 ... = β b      : ha',
      calc c = g b     : hb.symm
         ... = g (f a) : by rw this
         ... = 0       : pseudo_exact_of_exact.1 _

variables [exact g' h']

lemma epi_of_epi_of_epi_of_mono (hα : epi α) (hγ : epi γ) (hδ : mono δ) : epi β :=
begin
  apply preadditive.epi_of_cancel_zero,
  intros R r hβr,
  have hf'r : f' ≫ r = 0,
  { apply limits.zero_of_epi_comp α,
    rw [reassoc_of comm₁, hβr, limits.comp_zero] },
  haveI key : mono (pushout.inl : R ⟶ pushout r g') :=
    mono_inl_of_factor_thru_epi_mono_factorization r g' (cokernel.π f')
    (cokernel.desc f' g' (by simp)) (by simp) (cokernel.desc f' r hf'r) (by simp) _ (colimit.is_colimit _),
  have hz : g ≫ γ ≫ (pushout.inr : C' ⟶ pushout r g') = 0,
  { rw [←reassoc_of comm₂, ←pushout.condition, reassoc_of hβr, limits.zero_comp] },
  haveI key2 : mono (pushout.inl : pushout r g' ⟶ pushout (γ ≫ (pushout.inr : C' ⟶ pushout r g')) (h ≫ δ)) :=
    mono_inl_of_factor_thru_epi_mono_factorization (γ ≫ pushout.inr) (h ≫ δ) (cokernel.π g)
      (cokernel.desc g h (by simp) ≫ δ) (by simp) (cokernel.desc _ _ hz) (by simp) _ (colimit.is_colimit _),
  have : (pushout.inr : C' ⟶ pushout r g') ≫ (pushout.inl : pushout r g' ⟶ pushout (γ ≫ (pushout.inr : C' ⟶ pushout r g')) (h ≫ δ)) = h' ≫ (pushout.inr : D' ⟶ pushout (γ ≫ (pushout.inr : C' ⟶ pushout r g')) (h ≫ δ)),
  { apply (cancel_epi γ).1,
    rw [←category.assoc, pushout.condition, ←comm₃, category.assoc] },
  apply zero_of_comp_mono (pushout.inl : R ⟶ pushout r g'),
  apply zero_of_comp_mono (pushout.inl : pushout r g' ⟶ pushout (γ ≫ (pushout.inr : C' ⟶ pushout r g')) (h ≫ δ)),
  rw [pushout.condition, category.assoc, this, ←category.assoc],
  simp only [zero_comp, exact.w],
end

end category_theory.abelian
