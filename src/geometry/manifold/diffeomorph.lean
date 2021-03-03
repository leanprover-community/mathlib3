/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Nicolò Cavalleri.
-/

import geometry.manifold.times_cont_mdiff_map

/-!
# Diffeomorphisms
This file implements diffeomorphisms.

## Definitions

* `times_diffeomorph I I' M M' n`:  `n`-times continuously differentiable diffeomorphism between
                                    `M` and `M'` with respect to I and I'
* `diffeomorph  I I' M M'` : smooth diffeomorphism between `M` and `M'` with respect to I and I'

## Notations

* `M ≃ₘ^n⟮I, I'⟯ M'`  := `times_diffeomorph I J M N n`
* `M ≃ₘ⟮I, I'⟯ M'`    := `times_diffeomorph I J M N ⊤`

## Implementation notes

This notion of diffeomorphism is needed although there is already a notion of structomorphism
because structomorphisms do not allow the model spaces `H` and `H'` of the two manifolds to be
different, i.e. for a structomorphism one has to impose `H = H'` which is often not the case in
practice.

-/

open_locale manifold
open function set

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{E' : Type*} [normed_group E'] [normed_space 𝕜 E']
{F : Type*} [normed_group F] [normed_space 𝕜 F]
{H : Type*} [topological_space H]
{H' : Type*} [topological_space H']
{G : Type*} [topological_space G]
{I : model_with_corners 𝕜 E H} {I' : model_with_corners 𝕜 E' H'}
{J : model_with_corners 𝕜 F G}

variables {M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
{M' : Type*} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']
{N : Type*} [topological_space N] [charted_space G N] [smooth_manifold_with_corners J N]
{n : with_top ℕ}

section defs

variables (I I' M M' n)

/--
`n`-times continuously differentiable diffeomorphism between `M` and `M'` with respect to I and I'
-/
@[protect_proj, nolint has_inhabited_instance]
structure times_diffeomorph extends M ≃ M' :=
(times_cont_mdiff_to_fun  : times_cont_mdiff I I' n to_fun)
(times_cont_mdiff_inv_fun : times_cont_mdiff I' I n inv_fun)

end defs

localized "notation M ` ≃ₘ^`:50 n `⟮` I `,` J `⟯ ` N := times_diffeomorph I J M N n" in manifold
localized "notation M ` ≃ₘ⟮` I `,` J `⟯ ` N := times_diffeomorph I J M N ⊤" in manifold
notation E ` ≃ₘ^` n `[` 𝕜 `] ` E' := times_diffeomorph (𝓘(𝕜, E)) (𝓘(𝕜, E')) E E' n
localized "notation E ` ≃ₘ[` 𝕜 `] ` E' := times_diffeomorph (𝓘(𝕜, E)) (𝓘(𝕜, E')) E E' ⊤" in manifold

namespace times_diffeomorph
instance : has_coe_to_fun (M ≃ₘ^n⟮I, I'⟯ M') := ⟨λ _, M → M', λe, e.to_equiv⟩

instance : has_coe (M ≃ₘ^n⟮I, I'⟯ M') C^n⟮I, M; I', M'⟯ := ⟨λ Φ, ⟨Φ, Φ.times_cont_mdiff_to_fun⟩⟩

protected lemma continuous (h : M ≃ₘ^n⟮I, I'⟯ M') : continuous h :=
h.times_cont_mdiff_to_fun.continuous
protected lemma times_cont_mdiff (h : M ≃ₘ^n⟮I, I'⟯ M') : times_cont_mdiff I I' n h :=
h.times_cont_mdiff_to_fun
protected lemma times_cont_diff (h : E ≃ₘ^n[𝕜] E') : times_cont_diff 𝕜 n h := h.times_cont_mdiff.times_cont_diff
protected lemma smooth (h : M ≃ₘ⟮I, I'⟯ M') : smooth I I' h := h.times_cont_mdiff_to_fun
protected lemma mdifferentiable (h : M ≃ₘ^n⟮I, I'⟯ M') (hn : 1 ≤ n) : mdifferentiable I I' h :=
h.times_cont_mdiff.mdifferentiable hn
protected lemma mdifferentiable_on (h : M ≃ₘ^n⟮I, I'⟯ M') (s : set M) (hn : 1 ≤ n) :
  mdifferentiable_on I I' h s :=
(h.mdifferentiable hn).mdifferentiable_on

@[simp] lemma coe_to_equiv (h : M ≃ₘ^n⟮I, I'⟯ M') : ⇑h.to_equiv = h := rfl
@[simp, norm_cast] lemma coe_coe (h : M ≃ₘ^n⟮I, I'⟯ M') : ⇑(h : C^n⟮I, M; I', M'⟯) = h := rfl

lemma to_equiv_injective : injective (times_diffeomorph.to_equiv : (M ≃ₘ^n⟮I, I'⟯ M') → (M ≃ M'))
| ⟨e, _, _⟩ ⟨e', _, _⟩ rfl := rfl

@[simp] lemma to_equiv_inj {h h' : M ≃ₘ^n⟮I, I'⟯ M'} : h.to_equiv = h'.to_equiv ↔ h = h' :=
to_equiv_injective.eq_iff

lemma coe_fn_injective : injective (λ (h : M ≃ₘ^n⟮I, I'⟯ M') (x : M), h x) :=
equiv.injective_coe_fn.comp to_equiv_injective

@[ext] lemma ext {h h' : M ≃ₘ^n⟮I, I'⟯ M'} (Heq : ∀ x, h x = h' x) : h = h' :=
coe_fn_injective $ funext Heq

section

variables (M I n)

/-- Identity map as a diffeomorphism. -/
protected def refl : M ≃ₘ^n⟮I, I⟯ M :=
{ times_cont_mdiff_to_fun := times_cont_mdiff_id,
  times_cont_mdiff_inv_fun := times_cont_mdiff_id,
  to_equiv := equiv.refl M }

@[simp] lemma refl_to_equiv : (times_diffeomorph.refl I M n).to_equiv = equiv.refl _ := rfl
@[simp] lemma coe_refl : ⇑(times_diffeomorph.refl I M n) = id := rfl

end

/-- Composition of two diffeomorphisms. -/
protected def trans (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : M' ≃ₘ^n⟮I', J⟯ N) :
  M ≃ₘ^n⟮I, J⟯ N :=
{ times_cont_mdiff_to_fun  := h₂.times_cont_mdiff_to_fun.comp h₁.times_cont_mdiff_to_fun,
  times_cont_mdiff_inv_fun := h₁.times_cont_mdiff_inv_fun.comp h₂.times_cont_mdiff_inv_fun,
  to_equiv := h₁.to_equiv.trans h₂.to_equiv }

@[simp] lemma trans_refl (h : M ≃ₘ^n⟮I, I'⟯ M') : h.trans (times_diffeomorph.refl I' M' n) = h :=
ext $ λ _, rfl
@[simp] lemma refl_trans (h : M ≃ₘ^n⟮I, I'⟯ M') : (times_diffeomorph.refl I M n).trans h = h :=
ext $ λ _, rfl
@[simp] lemma coe_trans (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : M' ≃ₘ^n⟮I', J⟯ N) :
  ⇑(h₁.trans h₂) = h₂ ∘ h₁ := rfl

/-- Inverse of a diffeomorphism. -/
protected def symm (h : M ≃ₘ^n⟮I, J⟯ N) : N ≃ₘ^n⟮J, I⟯ M :=
{ times_cont_mdiff_to_fun  := h.times_cont_mdiff_inv_fun,
  times_cont_mdiff_inv_fun := h.times_cont_mdiff_to_fun,
  to_equiv := h.to_equiv.symm }

@[simp] lemma apply_symm_apply (h : M ≃ₘ^n⟮I, J⟯ N) (x : N) : h (h.symm x) = x :=
h.to_equiv.apply_symm_apply x
@[simp] lemma symm_apply_apply (h : M ≃ₘ^n⟮I, J⟯ N) (x : M) : h.symm (h x) = x :=
h.to_equiv.symm_apply_apply x

@[simp] lemma symm_refl : (times_diffeomorph.refl I M n).symm = times_diffeomorph.refl I M n :=
ext $ λ _, rfl
@[simp] lemma trans_symm (h : M ≃ₘ^n⟮I, J⟯ N) : h.trans h.symm = times_diffeomorph.refl I M n :=
ext h.symm_apply_apply
@[simp] lemma symm_trans (h : M ≃ₘ^n⟮I, J⟯ N) : h.symm.trans h = times_diffeomorph.refl J N n :=
ext h.apply_symm_apply
@[simp] lemma symm_trans' (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : M' ≃ₘ^n⟮I', J⟯ N) :
  (h₁.trans h₂).symm = h₂.symm.trans h₁.symm := rfl

lemma image_eq_preimage (h : M ≃ₘ^n⟮I, J⟯ N) (s : set M) : h '' s = h.symm ⁻¹' s :=
h.to_equiv.image_eq_preimage s
lemma symm_image_eq_preimage (h : M ≃ₘ^n⟮I, J⟯ N) (s : set N) : h.symm '' s = h ⁻¹' s :=
h.symm.image_eq_preimage s

@[simp] lemma image_symm_image (h : M ≃ₘ^n⟮I, J⟯ N) (s : set N) : h '' (h.symm '' s) = s :=
h.to_equiv.image_symm_image s
@[simp] lemma symm_image_image (h : M ≃ₘ^n⟮I, J⟯ N) (s : set M) : h.symm '' (h '' s) = s :=
h.to_equiv.symm_image_image s

/-- A diffeomorphism is a homeomorphism. -/
def to_homeomorph (h : M ≃ₘ^n⟮I, J⟯ N) : M ≃ₜ N :=
⟨h.to_equiv, h.continuous, h.symm.continuous⟩

@[simp] lemma to_homeomorph_to_equiv (h : M ≃ₘ^n⟮I, J⟯ N) :
  h.to_homeomorph.to_equiv = h.to_equiv :=
rfl
@[simp] lemma symm_to_homeomorph (h : M ≃ₘ^n⟮I, J⟯ N) :
  h.symm.to_homeomorph = h.to_homeomorph.symm :=
rfl

@[simp] lemma coe_to_homeomorph (h : M ≃ₘ^n⟮I, J⟯ N) : ⇑h.to_homeomorph = h := rfl
@[simp] lemma coe_to_homeomorph_symm (h : M ≃ₘ^n⟮I, J⟯ N) :
  ⇑h.to_homeomorph.symm = h.symm := rfl

lemma to_local_homeomorph_mdifferentiable (h : M ≃ₘ^n⟮I, J⟯ N) (hn : 1 ≤ n) :
  h.to_homeomorph.to_local_homeomorph.mdifferentiable I J :=
⟨h.mdifferentiable_on _ hn, h.symm.mdifferentiable_on _ hn⟩

lemma unique_mdiff_on_image_aux (h : M ≃ₘ^n⟮I, J⟯ N) (hn : 1 ≤ n)
  {s : set M} (hs : unique_mdiff_on I s) :
  unique_mdiff_on J (h '' s) :=
begin
  convert hs.unique_mdiff_on_preimage (h.to_local_homeomorph_mdifferentiable hn),
  simp [h.image_eq_preimage]
end

@[simp] lemma unique_mdiff_on_image (h : M ≃ₘ^n⟮I, J⟯ N) (hn : 1 ≤ n) {s : set M} :
  unique_mdiff_on J (h '' s) ↔ unique_mdiff_on I s :=
⟨λ hs, h.symm_image_image s ▸ h.symm.unique_mdiff_on_image_aux hn hs,
  h.unique_mdiff_on_image_aux hn⟩

@[simp] lemma unique_mdiff_on_preimage (h : M ≃ₘ^n⟮I, J⟯ N) (hn : 1 ≤ n) {s : set N} :
  unique_mdiff_on I (h ⁻¹' s) ↔ unique_mdiff_on J s :=
h.symm_image_eq_preimage s ▸ h.symm.unique_mdiff_on_image hn

@[simp] lemma unique_diff_on_image (h : E ≃ₘ^5[𝕜] F) (hn : 1 ≤ n) {s : set E} :
  unique_diff_on 𝕜 (h '' s) ↔ unique_diff_on 𝕜 s :=
by rw [← unique_mdiff_on_iff_unique_diff_on, unique_mdiff_on_image]

@[simp] lemma unique_mdiff_on_preimage (h : M ≃ₘ^n⟮I, J⟯ N) (hn : 1 ≤ n) {s : set N} :
  unique_mdiff_on I (h ⁻¹' s) ↔ unique_mdiff_on J s :=
h.symm_image_eq_preimage s ▸ h.symm.unique_mdiff_on_image hn

end times_diffeomorph

namespace continuous_linear_equiv

variable (e : E ≃L[𝕜] E')

/-- A continuous linear equivalence between normed spaces is a diffeomorphism. -/
def to_diffeomorph : E ≃ₘ[𝕜] E' :=
{ times_cont_mdiff_to_fun := e.times_cont_diff.times_cont_mdiff,
  times_cont_mdiff_inv_fun := e.symm.times_cont_diff.times_cont_mdiff,
  to_equiv := e.to_linear_equiv.to_equiv }

@[simp] lemma coe_to_diffeomorph : ⇑e.to_diffeomorph = e := rfl
@[simp] lemma symm_to_diffeomorph : e.to_diffeomorph.symm = e.symm.to_diffeomorph := rfl

end continuous_linear_equiv

namespace model_with_corners

variables (e : E ≃ₘ[𝕜] E')

def trans_diffeomorph (I : model_with_corners 𝕜 E H) (e : E ≃ₘ[𝕜] E') :
  model_with_corners 𝕜 E' H :=
{ to_local_equiv := I.to_local_equiv.trans e.to_equiv.to_local_equiv,
  source_eq := by simp,
  unique_diff' := by simp [range_comp e],
}

end model_with_corners
