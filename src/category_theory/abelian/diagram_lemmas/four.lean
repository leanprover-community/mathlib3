/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.abelian.pseudoelements

/-!
# The four and five lemmas

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Consider the following commutative diagram with exact rows in an abelian category:

```
A ---f--> B ---g--> C ---h--> D ---i--> E
|         |         |         |         |
α         β         γ         δ         ε
|         |         |         |         |
v         v         v         v         v
A' --f'-> B' --g'-> C' --h'-> D' --i'-> E'
```

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

open_locale pseudoelement

namespace category_theory.abelian

variables {A B C D A' B' C' D' : V}
variables {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D}
variables {f' : A' ⟶ B'} {g' : B' ⟶ C'} {h' : C' ⟶ D'}
variables {α : A ⟶ A'} {β : B ⟶ B'} {γ : C ⟶ C'} {δ : D ⟶ D'}
variables (comm₁ : α ≫ f' = f ≫ β) (comm₂ : β ≫ g' = g ≫ γ) (comm₃ : γ ≫ h' = h ≫ δ)
include comm₁ comm₂ comm₃

section
variables (hfg : exact f g) (hgh : exact g h) (hf'g' : exact f' g')


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
  exists.elim ((pseudo_exact_of_exact hgh).2 _ this) $ λ b hb,
    have g' (β b) = 0, from
      calc g' (β b) = γ (g b) : by rw [←comp_apply, comm₂, comp_apply]
                ... = γ c     : by rw hb
                ... = 0       : hc,
    exists.elim ((pseudo_exact_of_exact hf'g').2 _ this) $ λ a' ha',
      exists.elim (pseudo_surjective_of_epi α a') $ λ a ha,
      have f a = b, from
        suffices β (f a) = β b, from pseudo_injective_of_mono _ this,
        calc β (f a) = f' (α a) : by rw [←comp_apply, ←comm₁, comp_apply]
                 ... = f' a'    : by rw ha
                 ... = β b      : ha',
      calc c = g b     : hb.symm
         ... = g (f a) : by rw this
         ... = 0       : (pseudo_exact_of_exact hfg).1 _

end

section
variables (hgh : exact g h) (hf'g' : exact f' g') (hg'h' : exact g' h')

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
    (cokernel.desc f' g' hf'g'.w) (by simp) (cokernel.desc f' r hf'r) (by simp) _
    (colimit.is_colimit _),
  have hz : g ≫ γ ≫ z = 0, from
    calc g ≫ γ ≫ z = β ≫ g' ≫ z : by rw ←reassoc_of comm₂
                ... = β ≫ r ≫ y  : by rw ←pushout.condition
                ... = 0 ≫ y       : by rw reassoc_of hβr
                ... = 0           : has_zero_morphisms.zero_comp _ _,
  let v : pushout r g' ⟶ pushout (γ ≫ z) (h ≫ δ) := pushout.inl,
      w : D' ⟶ pushout (γ ≫ z) (h ≫ δ) := pushout.inr in
  have mono v, from mono_inl_of_factor_thru_epi_mono_factorization _ _ (cokernel.π g)
    (cokernel.desc g h hgh.w ≫ δ) (by simp) (cokernel.desc _ _ hz) (by simp) _
    (colimit.is_colimit _),
  have hzv : z ≫ v = h' ≫ w, from (cancel_epi γ).1 $
    calc γ ≫ z ≫ v = h ≫ δ ≫ w  : by rw [←category.assoc, pushout.condition, category.assoc]
                ... = γ ≫ h' ≫ w : by rw reassoc_of comm₃,
  suffices (r ≫ y) ≫ v = 0, by exactI zero_of_comp_mono _ (zero_of_comp_mono _ this),
  calc (r ≫ y) ≫ v = g' ≫ z ≫ v : by rw [pushout.condition, category.assoc]
                ... = g' ≫ h' ≫ w : by rw hzv
                ... = 0 ≫ w        : hg'h'.w_assoc _
                ... = 0            : has_zero_morphisms.zero_comp _ _

end

section five
variables {E E' : V} {i : D ⟶ E} {i' : D' ⟶ E'} {ε : E ⟶ E'} (comm₄ : δ ≫ i' = i ≫ ε)
variables (hfg : exact f g) (hgh : exact g h) (hhi : exact h i)
variables (hf'g' : exact f' g') (hg'h' : exact g' h') (hh'i' : exact h' i')
variables [is_iso α] [is_iso β] [is_iso δ] [is_iso ε]
include comm₄ hfg hgh hhi hf'g' hg'h' hh'i'


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
have mono γ, by apply mono_of_epi_of_mono_of_mono comm₁ comm₂ comm₃ hfg hgh hf'g'; apply_instance,
have epi γ, by apply epi_of_epi_of_epi_of_mono comm₂ comm₃ comm₄ hhi hg'h' hh'i'; apply_instance,
by exactI is_iso_of_mono_of_epi _

end five
end category_theory.abelian
