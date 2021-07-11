/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.abelian.pseudoelements

/-!
# The four and five lemmas

Consider the following commutative diagram with exact rows in an abelian category:

A ---f--> B ---g--> C ---h--> D ---i--> E
|         |         |         |         |
α         β         γ         δ         ε
|         |         |         |         |
v         v         v         v         v
A' --f'-> B' --g'-> C' --h'-> D' --i'-> E'

We show:
- the "mono" version of the four lemma: if `α` is an epimorphism and `β` and `δ` are monomorphisms,
  then `γ` is a monomorphism,
- the "epi" version of the four lemma: if `β` and `δ` are epimorphisms and `ε` is a monomorphism,
  then `γ` is an epimorphism,
- the five lemma: if `α`, `β`, `δ` and `ε` are isomorphisms, then `γ` is an isomorphism.

## Implementation details

To show the mono version, we use pseudoelements. For the epi version, we use a completely different
arrow-theoretic proof. In theory, it should be sufficient to have one version and the other should
follow automatically by duality. In practice, mathlib's knowledge about duality isn't quite at the
point where this is doable easily.

However, one key duality statement about exactness is needed in the proof of the epi version of the
four lemma: we need to know that exactness of a pair `(f, g)`, which we defined via the map from
the image of `f` to the kernel of `g`, is the same as "co-exactness", defined via the map from the
cokernel of `f` to the coimage of `g` (more precisely, we only need the consequence that if `(f, g)`
is exact, then the factorization of `g` through the cokernel of `f` is monomorphic). Luckily, in the
case of abelian categories, we have the characterization that `(f, g)` is exact if and only if
`f ≫ g = 0` and `kernel.ι g ≫ cokernel.π f = 0`, and the latter condition is self dual, so the
equivalence of exactness and co-exactness follows easily.

## Tags

four lemma, five lemma, diagram lemma, diagram chase
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
by apply abelian.epi_fst_of_is_limit _ _ (pullback.is_limit_inner f g g₂ f' g₁ hf hg t ht)

lemma mono_inl_of_factor_thru_epi_mono_factorization {A B C D : V} (f : A ⟶ B) (g : A ⟶ C) (g₁ : A ⟶ D)
  [epi g₁] (g₂ : D ⟶ C) [mono g₂] (hg : g₁ ≫ g₂ = g) (f' : D ⟶ B) (hf : g₁ ≫ f' = f)
  (t : pushout_cocone f g) (ht : is_colimit t) : mono t.inl :=
by apply abelian.mono_inl_of_is_colimit _ _ (pushout.is_colimit_inner _ _ _ _ _ hf hg t ht)

variables {A B C D A' B' C' D' : V}
variables {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D}
variables {f' : A' ⟶ B'} {g' : B' ⟶ C'} {h' : C' ⟶ D'}
variables {α : A ⟶ A'} {β : B ⟶ B'} {γ : C ⟶ C'} {δ : D ⟶ D'}
variables (comm₁ : α ≫ f' = f ≫ β) (comm₂ : β ≫ g' = g ≫ γ) (comm₃ : γ ≫ h' = h ≫ δ)
include comm₁ comm₂ comm₃

section
variables [exact f g] [exact g h] [exact f' g']


/-- The four lemma, mono version. For names of objects and morphisms, refer to the following
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

end

section
variables [exact g h] [exact f' g'] [exact g' h']

/-- The four lemma, epi version. For names of objects and morphisms, refer to the following
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
lemma epi_of_epi_of_epi_of_mono (hα : epi α) (hγ : epi γ) (hδ : mono δ) : epi β :=
preadditive.epi_of_cancel_zero _ $ λ R r hβr,
  have hf'r : f' ≫ r = 0, from limits.zero_of_epi_comp α $
    calc α ≫ f' ≫ r = f ≫ β ≫ r : by rw reassoc_of comm₁
                 ... = f ≫ 0      : by rw hβr
                 ... = 0           : has_zero_morphisms.comp_zero _ _,
  let y : R ⟶ pushout r g' := pushout.inl, z : C' ⟶ pushout r g' := pushout.inr in
  have mono y, from mono_inl_of_factor_thru_epi_mono_factorization r g' (cokernel.π f')
    (cokernel.desc f' g' (by simp)) (by simp) (cokernel.desc f' r hf'r) (by simp) _
    (colimit.is_colimit _),
  have hz : g ≫ γ ≫ z = 0, from
    calc g ≫ γ ≫ z = β ≫ g' ≫ z : by rw ←reassoc_of comm₂
                ... = β ≫ r ≫ y  : by rw ←pushout.condition
                ... = 0 ≫ y       : by rw reassoc_of hβr
                ... = 0           : has_zero_morphisms.zero_comp _ _,
  let v : pushout r g' ⟶ pushout (γ ≫ z) (h ≫ δ) := pushout.inl,
      w : D' ⟶ pushout (γ ≫ z) (h ≫ δ) := pushout.inr in
  have mono v, from mono_inl_of_factor_thru_epi_mono_factorization _ _ (cokernel.π g)
    (cokernel.desc g h (by simp) ≫ δ) (by simp) (cokernel.desc _ _ hz) (by simp) _
    (colimit.is_colimit _),
  have hzv : z ≫ v = h' ≫ w, from (cancel_epi γ).1 $
    calc γ ≫ z ≫ v = h ≫ δ ≫ w  : by rw [←category.assoc, pushout.condition, category.assoc]
                ... = γ ≫ h' ≫ w : by rw reassoc_of comm₃,
  suffices (r ≫ y) ≫ v = 0, by exactI zero_of_comp_mono _ (zero_of_comp_mono _ this),
  calc (r ≫ y) ≫ v = g' ≫ z ≫ v : by rw [pushout.condition, category.assoc]
                ... = g' ≫ h' ≫ w : by rw hzv
                ... = 0 ≫ w        : exact.w_assoc _
                ... = 0            : has_zero_morphisms.zero_comp _ _

end

section five
variables {E E' : V} {i : D ⟶ E} {i' : D' ⟶ E'} {ε : E ⟶ E'} (comm₄ : δ ≫ i' = i ≫ ε)
variables [exact f g] [exact g h] [exact h i] [exact f' g'] [exact g' h'] [exact h' i']
variables [is_iso α] [is_iso β] [is_iso δ] [is_iso ε]
include comm₄


/-- The five lemma. For names of objects and morphisms, refer to the following diagram:

```
A ---f--> B ---g--> C ---h--> D ---i--> E
|         |         |         |         |
α         β         γ         δ         ε
|         |         |         |         |
v         v         v         v         v
A' --f'-> B' --g'-> C' --h'-> D' --i'-> E'
```
-/
lemma is_iso_of_is_iso_of_is_iso_of_is_iso_of_is_iso : is_iso γ :=
have mono γ, by apply mono_of_epi_of_mono_of_mono comm₁ comm₂ comm₃; apply_instance,
have epi γ, by apply epi_of_epi_of_epi_of_mono comm₂ comm₃ comm₄; apply_instance,
by exactI is_iso_of_mono_of_epi _

end five
end category_theory.abelian
