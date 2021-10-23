/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Yury Kudryashov
-/

import geometry.manifold.times_cont_mdiff_map

/-!
# Diffeomorphisms
This file implements diffeomorphisms.

## Definitions

* `diffeomorph I I' M M' n`:  `n`-times continuously differentiable diffeomorphism between
  `M` and `M'` with respect to I and I'; we do not introduce a separate definition for the case
  `n = ∞`; we use notation instead.
* `diffeomorph.to_homeomorph`: reinterpret a diffeomorphism as a homeomorphism.
* `continuous_linear_equiv.to_diffeomorph`: reinterpret a continuous equivalence as
  a diffeomorphism.
* `model_with_corners.trans_diffeomorph`: compose a given `model_with_corners` with a diffeomorphism
  between the old and the new target spaces. Useful, e.g, to turn any finite dimensional manifold
  into a manifold modelled on a Euclidean space.
* `diffeomorph.to_trans_diffeomorph`: the identity diffeomorphism between `M` with model `I` and `M`
  with model `I.trans_diffeomorph e`.

## Notations

* `M ≃ₘ^n⟮I, I'⟯ M'`  := `diffeomorph I J M N n`
* `M ≃ₘ⟮I, I'⟯ M'`    := `diffeomorph I J M N ⊤`
* `E ≃ₘ^n[𝕜] E'`      := `E ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, E')⟯ E'`
* `E ≃ₘ[𝕜] E'`        := `E ≃ₘ⟮𝓘(𝕜, E), 𝓘(𝕜, E')⟯ E'`

## Implementation notes

This notion of diffeomorphism is needed although there is already a notion of structomorphism
because structomorphisms do not allow the model spaces `H` and `H'` of the two manifolds to be
different, i.e. for a structomorphism one has to impose `H = H'` which is often not the case in
practice.

## Keywords

diffeomorphism, manifold
-/

open_locale manifold topological_space
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

variables {M : Type*} [topological_space M] [charted_space H M]
{M' : Type*} [topological_space M'] [charted_space H' M']
{N : Type*} [topological_space N] [charted_space G N]
{n : with_top ℕ}

section defs

variables (I I' M M' n)

/--
`n`-times continuously differentiable diffeomorphism between `M` and `M'` with respect to I and I'
-/
@[protect_proj, nolint has_inhabited_instance]
structure diffeomorph extends M ≃ M' :=
(times_cont_mdiff_to_fun  : times_cont_mdiff I I' n to_equiv)
(times_cont_mdiff_inv_fun : times_cont_mdiff I' I n to_equiv.symm)

end defs

localized "notation M ` ≃ₘ^` n:1000 `⟮`:50 I `,` J `⟯ ` N := diffeomorph I J M N n" in manifold
localized "notation M ` ≃ₘ⟮` I `,` J `⟯ ` N := diffeomorph I J M N ⊤" in manifold
localized "notation E ` ≃ₘ^` n:1000 `[`:50 𝕜 `] ` E' :=
  diffeomorph (model_with_corners_self 𝕜 E) (model_with_corners_self 𝕜 E') E E' n" in manifold
localized "notation E ` ≃ₘ[` 𝕜 `] ` E' :=
  diffeomorph (model_with_corners_self 𝕜 E) (model_with_corners_self 𝕜 E') E E' ⊤" in manifold

namespace diffeomorph
instance : has_coe_to_fun (M ≃ₘ^n⟮I, I'⟯ M') (λ _, M → M') := ⟨λe, e.to_equiv⟩

instance : has_coe (M ≃ₘ^n⟮I, I'⟯ M') C^n⟮I, M; I', M'⟯ := ⟨λ Φ, ⟨Φ, Φ.times_cont_mdiff_to_fun⟩⟩

@[continuity] protected lemma continuous (h : M ≃ₘ^n⟮I, I'⟯ M') : continuous h :=
h.times_cont_mdiff_to_fun.continuous
protected lemma times_cont_mdiff (h : M ≃ₘ^n⟮I, I'⟯ M') : times_cont_mdiff I I' n h :=
h.times_cont_mdiff_to_fun
protected lemma times_cont_mdiff_at (h : M ≃ₘ^n⟮I, I'⟯ M') {x} : times_cont_mdiff_at I I' n h x :=
h.times_cont_mdiff.times_cont_mdiff_at
protected lemma times_cont_mdiff_within_at (h : M ≃ₘ^n⟮I, I'⟯ M') {s x} :
  times_cont_mdiff_within_at I I' n h s x :=
h.times_cont_mdiff_at.times_cont_mdiff_within_at
protected lemma times_cont_diff (h : E ≃ₘ^n[𝕜] E') : times_cont_diff 𝕜 n h :=
h.times_cont_mdiff.times_cont_diff
protected lemma smooth (h : M ≃ₘ⟮I, I'⟯ M') : smooth I I' h := h.times_cont_mdiff_to_fun
protected lemma mdifferentiable (h : M ≃ₘ^n⟮I, I'⟯ M') (hn : 1 ≤ n) : mdifferentiable I I' h :=
h.times_cont_mdiff.mdifferentiable hn
protected lemma mdifferentiable_on (h : M ≃ₘ^n⟮I, I'⟯ M') (s : set M) (hn : 1 ≤ n) :
  mdifferentiable_on I I' h s :=
(h.mdifferentiable hn).mdifferentiable_on

@[simp] lemma coe_to_equiv (h : M ≃ₘ^n⟮I, I'⟯ M') : ⇑h.to_equiv = h := rfl
@[simp, norm_cast] lemma coe_coe (h : M ≃ₘ^n⟮I, I'⟯ M') : ⇑(h : C^n⟮I, M; I', M'⟯) = h := rfl

lemma to_equiv_injective : injective (diffeomorph.to_equiv : (M ≃ₘ^n⟮I, I'⟯ M') → (M ≃ M'))
| ⟨e, _, _⟩ ⟨e', _, _⟩ rfl := rfl

@[simp] lemma to_equiv_inj {h h' : M ≃ₘ^n⟮I, I'⟯ M'} : h.to_equiv = h'.to_equiv ↔ h = h' :=
to_equiv_injective.eq_iff

/-- Coercion to function `λ h : M ≃ₘ^n⟮I, I'⟯ M', (h : M → M')` is injective. -/
lemma coe_fn_injective : injective (λ (h : M ≃ₘ^n⟮I, I'⟯ M') (x : M), h x) :=
equiv.coe_fn_injective.comp to_equiv_injective

@[ext] lemma ext {h h' : M ≃ₘ^n⟮I, I'⟯ M'} (Heq : ∀ x, h x = h' x) : h = h' :=
coe_fn_injective $ funext Heq

section

variables (M I n)

/-- Identity map as a diffeomorphism. -/
protected def refl : M ≃ₘ^n⟮I, I⟯ M :=
{ times_cont_mdiff_to_fun := times_cont_mdiff_id,
  times_cont_mdiff_inv_fun := times_cont_mdiff_id,
  to_equiv := equiv.refl M }

@[simp] lemma refl_to_equiv : (diffeomorph.refl I M n).to_equiv = equiv.refl _ := rfl
@[simp] lemma coe_refl : ⇑(diffeomorph.refl I M n) = id := rfl

end

/-- Composition of two diffeomorphisms. -/
protected def trans (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : M' ≃ₘ^n⟮I', J⟯ N) :
  M ≃ₘ^n⟮I, J⟯ N :=
{ times_cont_mdiff_to_fun  := h₂.times_cont_mdiff_to_fun.comp h₁.times_cont_mdiff_to_fun,
  times_cont_mdiff_inv_fun := h₁.times_cont_mdiff_inv_fun.comp h₂.times_cont_mdiff_inv_fun,
  to_equiv := h₁.to_equiv.trans h₂.to_equiv }

@[simp] lemma trans_refl (h : M ≃ₘ^n⟮I, I'⟯ M') : h.trans (diffeomorph.refl I' M' n) = h :=
ext $ λ _, rfl
@[simp] lemma refl_trans (h : M ≃ₘ^n⟮I, I'⟯ M') : (diffeomorph.refl I M n).trans h = h :=
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

@[simp] lemma symm_refl : (diffeomorph.refl I M n).symm = diffeomorph.refl I M n :=
ext $ λ _, rfl
@[simp] lemma trans_symm (h : M ≃ₘ^n⟮I, J⟯ N) : h.trans h.symm = diffeomorph.refl I M n :=
ext h.symm_apply_apply
@[simp] lemma symm_trans (h : M ≃ₘ^n⟮I, J⟯ N) : h.symm.trans h = diffeomorph.refl J N n :=
ext h.apply_symm_apply
@[simp] lemma symm_trans' (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : M' ≃ₘ^n⟮I', J⟯ N) :
  (h₁.trans h₂).symm = h₂.symm.trans h₁.symm := rfl
@[simp] lemma symm_to_equiv (h : M ≃ₘ^n⟮I, J⟯ N) : h.symm.to_equiv = h.to_equiv.symm := rfl
@[simp, mfld_simps] lemma to_equiv_coe_symm (h : M ≃ₘ^n⟮I, J⟯ N) : ⇑h.to_equiv.symm = h.symm := rfl

lemma image_eq_preimage (h : M ≃ₘ^n⟮I, J⟯ N) (s : set M) : h '' s = h.symm ⁻¹' s :=
h.to_equiv.image_eq_preimage s
lemma symm_image_eq_preimage (h : M ≃ₘ^n⟮I, J⟯ N) (s : set N) : h.symm '' s = h ⁻¹' s :=
h.symm.image_eq_preimage s

@[simp, mfld_simps] lemma range_comp {α} (h : M ≃ₘ^n⟮I, J⟯ N) (f : α → M) :
  range (h ∘ f) = h.symm ⁻¹' (range f) :=
by rw [range_comp, image_eq_preimage]

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

@[simp] lemma times_cont_mdiff_within_at_comp_diffeomorph_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : N → M'}
  {s x} (hm : m ≤ n) :
  times_cont_mdiff_within_at I I' m (f ∘ h) s x ↔
    times_cont_mdiff_within_at J I' m f (h.symm ⁻¹' s) (h x) :=
begin
  split,
  { intro Hfh,
    rw [← h.symm_apply_apply x] at Hfh,
    simpa only [(∘), h.apply_symm_apply]
      using Hfh.comp (h x) (h.symm.times_cont_mdiff_within_at.of_le hm) (maps_to_preimage _ _) },
  { rw ← h.image_eq_preimage,
    exact λ hf, hf.comp x (h.times_cont_mdiff_within_at.of_le hm) (maps_to_image _ _) }
end

@[simp] lemma times_cont_mdiff_on_comp_diffeomorph_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : N → M'}
  {s} (hm : m ≤ n) :
  times_cont_mdiff_on I I' m (f ∘ h) s ↔ times_cont_mdiff_on J I' m f (h.symm ⁻¹' s) :=
h.to_equiv.forall_congr $ λ x, by simp only [hm, coe_to_equiv, symm_apply_apply,
  times_cont_mdiff_within_at_comp_diffeomorph_iff, mem_preimage]

@[simp] lemma times_cont_mdiff_at_comp_diffeomorph_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : N → M'} {x}
  (hm : m ≤ n) :
  times_cont_mdiff_at I I' m (f ∘ h) x ↔ times_cont_mdiff_at J I' m f (h x) :=
h.times_cont_mdiff_within_at_comp_diffeomorph_iff hm

@[simp] lemma times_cont_mdiff_comp_diffeomorph_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : N → M'}
  (hm : m ≤ n) :
  times_cont_mdiff I I' m (f ∘ h) ↔ times_cont_mdiff J I' m f :=
h.to_equiv.forall_congr $ λ x, (h.times_cont_mdiff_at_comp_diffeomorph_iff hm)

@[simp] lemma times_cont_mdiff_within_at_diffeomorph_comp_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : M' → M}
  (hm : m ≤ n) {s x} :
  times_cont_mdiff_within_at I' J m (h ∘ f) s x ↔ times_cont_mdiff_within_at I' I m f s x :=
⟨λ Hhf, by simpa only [(∘), h.symm_apply_apply]
  using (h.symm.times_cont_mdiff_at.of_le hm).comp_times_cont_mdiff_within_at _ Hhf,
  λ Hf, (h.times_cont_mdiff_at.of_le hm).comp_times_cont_mdiff_within_at _ Hf⟩

@[simp] lemma times_cont_mdiff_at_diffeomorph_comp_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : M' → M}
  (hm : m ≤ n) {x} :
  times_cont_mdiff_at I' J m (h ∘ f) x ↔ times_cont_mdiff_at I' I m f x :=
h.times_cont_mdiff_within_at_diffeomorph_comp_iff hm

@[simp] lemma times_cont_mdiff_on_diffeomorph_comp_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : M' → M}
  (hm : m ≤ n) {s} :
  times_cont_mdiff_on I' J m (h ∘ f) s ↔ times_cont_mdiff_on I' I m f s :=
forall_congr $ λ x, forall_congr $ λ hx, h.times_cont_mdiff_within_at_diffeomorph_comp_iff hm

@[simp] lemma times_cont_mdiff_diffeomorph_comp_iff {m} (h : M ≃ₘ^n⟮I, J⟯ N) {f : M' → M}
  (hm : m ≤ n) :
  times_cont_mdiff I' J m (h ∘ f) ↔ times_cont_mdiff I' I m f :=
forall_congr $ λ x, h.times_cont_mdiff_within_at_diffeomorph_comp_iff hm

lemma to_local_homeomorph_mdifferentiable (h : M ≃ₘ^n⟮I, J⟯ N) (hn : 1 ≤ n) :
  h.to_homeomorph.to_local_homeomorph.mdifferentiable I J :=
⟨h.mdifferentiable_on _ hn, h.symm.mdifferentiable_on _ hn⟩

variables [smooth_manifold_with_corners I M] [smooth_manifold_with_corners J N]

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

@[simp] lemma unique_diff_on_image (h : E ≃ₘ^n[𝕜] F) (hn : 1 ≤ n) {s : set E} :
  unique_diff_on 𝕜 (h '' s) ↔ unique_diff_on 𝕜 s :=
by simp only [← unique_mdiff_on_iff_unique_diff_on, unique_mdiff_on_image, hn]

@[simp] lemma unique_diff_on_preimage (h : E ≃ₘ^n[𝕜] F) (hn : 1 ≤ n) {s : set F} :
  unique_diff_on 𝕜 (h ⁻¹' s) ↔ unique_diff_on 𝕜 s :=
h.symm_image_eq_preimage s ▸ h.symm.unique_diff_on_image hn

end diffeomorph

namespace continuous_linear_equiv

variable (e : E ≃L[𝕜] E')

/-- A continuous linear equivalence between normed spaces is a diffeomorphism. -/
def to_diffeomorph : E ≃ₘ[𝕜] E' :=
{ times_cont_mdiff_to_fun := e.times_cont_diff.times_cont_mdiff,
  times_cont_mdiff_inv_fun := e.symm.times_cont_diff.times_cont_mdiff,
  to_equiv := e.to_linear_equiv.to_equiv }

@[simp] lemma coe_to_diffeomorph : ⇑e.to_diffeomorph = e := rfl
@[simp] lemma symm_to_diffeomorph : e.symm.to_diffeomorph = e.to_diffeomorph.symm := rfl
@[simp] lemma coe_to_diffeomorph_symm : ⇑e.to_diffeomorph.symm = e.symm := rfl

end continuous_linear_equiv

namespace model_with_corners

variables (I) (e : E ≃ₘ[𝕜] E')

/-- Apply a diffeomorphism (e.g., a continuous linear equivalence) to the model vector space. -/
def trans_diffeomorph (I : model_with_corners 𝕜 E H) (e : E ≃ₘ[𝕜] E') :
  model_with_corners 𝕜 E' H :=
{ to_local_equiv := I.to_local_equiv.trans e.to_equiv.to_local_equiv,
  source_eq := by simp,
  unique_diff' := by simp [range_comp e, I.unique_diff],
  continuous_to_fun := e.continuous.comp I.continuous,
  continuous_inv_fun := I.continuous_symm.comp e.symm.continuous }

@[simp, mfld_simps] lemma coe_trans_diffeomorph : ⇑(I.trans_diffeomorph e) = e ∘ I := rfl
@[simp, mfld_simps] lemma coe_trans_diffeomorph_symm :
  ⇑(I.trans_diffeomorph e).symm = I.symm ∘ e.symm := rfl

lemma trans_diffeomorph_range : range (I.trans_diffeomorph e) = e '' (range I) :=
range_comp e I

lemma coe_ext_chart_at_trans_diffeomorph (x : M) :
  ⇑(ext_chart_at (I.trans_diffeomorph e) x) = e ∘ ext_chart_at I x := rfl

lemma coe_ext_chart_at_trans_diffeomorph_symm (x : M) :
  ⇑(ext_chart_at (I.trans_diffeomorph e) x).symm = (ext_chart_at I x).symm ∘ e.symm := rfl

lemma ext_chart_at_trans_diffeomorph_target (x : M) :
  (ext_chart_at (I.trans_diffeomorph e) x).target = e.symm ⁻¹' (ext_chart_at I x).target :=
by simp only [range_comp e, e.image_eq_preimage, preimage_preimage] with mfld_simps

end model_with_corners

namespace diffeomorph

variables (e : E ≃ₘ[𝕜] F)

instance smooth_manifold_with_corners_trans_diffeomorph [smooth_manifold_with_corners I M] :
  smooth_manifold_with_corners (I.trans_diffeomorph e) M :=
begin
  refine smooth_manifold_with_corners_of_times_cont_diff_on  _ _ (λ e₁ e₂ h₁ h₂, _),
  refine e.times_cont_diff.comp_times_cont_diff_on
    (((times_cont_diff_groupoid ⊤ I).compatible h₁ h₂).1.comp
      e.symm.times_cont_diff.times_cont_diff_on _),
  mfld_set_tac
end

variables (I M)

/-- The identity diffeomorphism between a manifold with model `I` and the same manifold
with model `I.trans_diffeomorph e`. -/
def to_trans_diffeomorph (e : E ≃ₘ[𝕜] F) : M ≃ₘ⟮I, I.trans_diffeomorph e⟯ M :=
{ to_equiv := equiv.refl M,
  times_cont_mdiff_to_fun := λ x,
    begin
      refine times_cont_mdiff_within_at_iff.2 ⟨continuous_within_at_id, _⟩,
      refine e.times_cont_diff.times_cont_diff_within_at.congr' (λ y hy, _) _,
      { simp only [equiv.coe_refl, id, (∘), I.coe_ext_chart_at_trans_diffeomorph,
          (ext_chart_at I x).right_inv hy.1] },
      exact ⟨(ext_chart_at I x).map_source (mem_ext_chart_source I x), trivial,
        by simp only with mfld_simps⟩
    end,
  times_cont_mdiff_inv_fun := λ x,
    begin
      refine times_cont_mdiff_within_at_iff.2 ⟨continuous_within_at_id, _⟩,
      refine e.symm.times_cont_diff.times_cont_diff_within_at.congr' (λ y hy, _) _,
      { simp only [mem_inter_eq, I.ext_chart_at_trans_diffeomorph_target] at hy,
        simp only [equiv.coe_refl, equiv.refl_symm, id, (∘),
          I.coe_ext_chart_at_trans_diffeomorph_symm, (ext_chart_at I x).right_inv hy.1] },
      exact ⟨(ext_chart_at _ x).map_source (mem_ext_chart_source _ x), trivial,
        by simp only [e.symm_apply_apply, equiv.refl_symm, equiv.coe_refl] with mfld_simps⟩
    end }

variables {I M}

@[simp] lemma times_cont_mdiff_within_at_trans_diffeomorph_right {f : M' → M} {x s} :
  times_cont_mdiff_within_at I' (I.trans_diffeomorph e) n f s x ↔
    times_cont_mdiff_within_at I' I n f s x :=
(to_trans_diffeomorph I M e).times_cont_mdiff_within_at_diffeomorph_comp_iff le_top

@[simp] lemma times_cont_mdiff_at_trans_diffeomorph_right {f : M' → M} {x} :
  times_cont_mdiff_at I' (I.trans_diffeomorph e) n f x ↔ times_cont_mdiff_at I' I n f x :=
(to_trans_diffeomorph I M e).times_cont_mdiff_at_diffeomorph_comp_iff le_top

@[simp] lemma times_cont_mdiff_on_trans_diffeomorph_right {f : M' → M} {s} :
  times_cont_mdiff_on I' (I.trans_diffeomorph e) n f s ↔ times_cont_mdiff_on I' I n f s :=
(to_trans_diffeomorph I M e).times_cont_mdiff_on_diffeomorph_comp_iff le_top

@[simp] lemma times_cont_mdiff_trans_diffeomorph_right {f : M' → M} :
  times_cont_mdiff I' (I.trans_diffeomorph e) n f ↔ times_cont_mdiff I' I n f :=
(to_trans_diffeomorph I M e).times_cont_mdiff_diffeomorph_comp_iff le_top

@[simp] lemma smooth_trans_diffeomorph_right {f : M' → M} :
  smooth I' (I.trans_diffeomorph e) f ↔ smooth I' I f :=
times_cont_mdiff_trans_diffeomorph_right e

@[simp] lemma times_cont_mdiff_within_at_trans_diffeomorph_left {f : M → M'} {x s} :
  times_cont_mdiff_within_at (I.trans_diffeomorph e) I' n f s x ↔
    times_cont_mdiff_within_at I I' n f s x :=
((to_trans_diffeomorph I M e).times_cont_mdiff_within_at_comp_diffeomorph_iff le_top).symm

@[simp] lemma times_cont_mdiff_at_trans_diffeomorph_left {f : M → M'} {x} :
  times_cont_mdiff_at (I.trans_diffeomorph e) I' n f x ↔ times_cont_mdiff_at I I' n f x :=
((to_trans_diffeomorph I M e).times_cont_mdiff_at_comp_diffeomorph_iff le_top).symm

@[simp] lemma times_cont_mdiff_on_trans_diffeomorph_left {f : M → M'} {s} :
  times_cont_mdiff_on (I.trans_diffeomorph e) I' n f s ↔ times_cont_mdiff_on I I' n f s :=
((to_trans_diffeomorph I M e).times_cont_mdiff_on_comp_diffeomorph_iff le_top).symm

@[simp] lemma times_cont_mdiff_trans_diffeomorph_left {f : M → M'} :
  times_cont_mdiff (I.trans_diffeomorph e) I' n f ↔ times_cont_mdiff I I' n f :=
((to_trans_diffeomorph I M e).times_cont_mdiff_comp_diffeomorph_iff le_top).symm

@[simp] lemma smooth_trans_diffeomorph_left {f : M → M'} :
  smooth (I.trans_diffeomorph e) I' f ↔ smooth I I' f :=
e.times_cont_mdiff_trans_diffeomorph_left

end diffeomorph
