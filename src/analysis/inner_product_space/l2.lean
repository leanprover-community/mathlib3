/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.inner_product_space.projection
import analysis.normed_space.lp_space

/-!
# Identifications of a Hilbert space with `ℓ²`; Hilbert bases
-/

open is_R_or_C submodule filter
open_locale big_operators nnreal ennreal direct_sum

local attribute [instance] fact_one_le_two_ennreal

notation `ℓ²(` ι `,` 𝕜 `)` := lp (λ i : ι, 𝕜) 2

noncomputable theory

variables {ι : Type*} [dec_ι : decidable_eq ι]
variables {𝕜 : Type*} [is_R_or_C 𝕜] {E : Type*} [inner_product_space 𝕜 E] [cplt : complete_space E]
local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

namespace orthogonal_family
variables {G : ι → Type*} [Π i, inner_product_space 𝕜 (G i)] {V : Π i, G i →ₗᵢ[𝕜] E}
  (hV : orthogonal_family 𝕜 V) [dec_V : Π i (x : G i), decidable (x ≠ 0)]

include hV

protected lemma summable_of_lp [complete_space E] (f : lp G 2) : summable (λ i, V i (f i)) :=
begin
  rw hV.summable_iff_norm_sq_summable,
  convert (lp.mem_ℓp f).summable _,
  { norm_cast },
  { norm_num }
end

include cplt

/-- A mutually orthogonal family of subspaces of `E` induce a linear isometry from `lp 2` of the
subspaces into `E`. -/
protected def linear_isometry : lp G 2 →ₗᵢ[𝕜] E :=
{ to_fun := λ f, ∑' i, V i (f i),
  map_add' := λ f g, by simp [tsum_add (hV.summable_of_lp f) (hV.summable_of_lp g)],
  map_smul' := λ c f, by simpa using tsum_const_smul (hV.summable_of_lp f),
  norm_map' := λ f, begin
    classical, -- needed for lattice instance on `finset ι`, for `filter.at_top_ne_bot`
    have H : 0 < (2:ℝ≥0∞).to_real := by norm_num,
    suffices : ∥∑' (i : ι), V i (f i)∥ ^ ((2:ℝ≥0∞).to_real) = ∥f∥ ^ ((2:ℝ≥0∞).to_real),
    { exact real.rpow_left_inj_on H.ne' (norm_nonneg _) (norm_nonneg _) this },
    refine tendsto_nhds_unique  _ (lp.has_sum_norm H f),
    convert (hV.summable_of_lp f).has_sum.norm.rpow_const (or.inr H.le),
    ext s,
    exact_mod_cast (hV.norm_sum f s).symm,
  end }

protected lemma linear_isometry_apply (f : lp G 2) :
  hV.linear_isometry f = ∑' i, V i (f i) :=
rfl

protected lemma has_sum_linear_isometry (f : lp G 2) :
  has_sum (λ i, V i (f i)) (hV.linear_isometry f) :=
(hV.summable_of_lp f).has_sum

@[simp] protected lemma linear_isometry_apply_single [decidable_eq ι] {i : ι} (x : G i) :
  hV.linear_isometry (direct_sum.mk_lp (dfinsupp.single i x) 2) = V i x :=
begin
  let fx : lp G 2 := direct_sum.mk_lp (dfinsupp.single i x) 2,
  suffices : ∀ j ≠ i, V j (fx j) = 0,
  { simpa [hV.linear_isometry_apply] using tsum_eq_single i this },
  intros j hj,
  have : fx j = 0 := dfinsupp.single_eq_of_ne hj.symm,
  simp [this],
end

/-- The canonical linear isometry from the `lp 2` of a mutually orthogonal family of subspaces of
`E` into E, has range the closure of the span of the subspaces. -/
protected lemma range_linear_isometry [Π i, complete_space (G i)] :
  hV.linear_isometry.to_linear_map.range = (⨆ i, (V i).to_linear_map.range).topological_closure :=
begin
  classical,
  refine le_antisymm _ _,
  { rintros x ⟨f, rfl⟩,
    refine mem_closure_of_tendsto (hV.has_sum_linear_isometry f) (eventually_of_forall _),
    intros s,
    refine sum_mem (supr (λ i, (V i).to_linear_map.range)) _,
    intros i hi,
    refine mem_supr_of_mem i _,
    exact linear_map.mem_range_self _ (f i) },
  { apply topological_closure_minimal,
    { refine supr_le _,
      rintros i x ⟨x, rfl⟩,
      use direct_sum.mk_lp (dfinsupp.single i x) 2,
      { simp, } },
    exact hV.linear_isometry.isometry.uniform_inducing.is_complete_range.is_closed }
end

end orthogonal_family

namespace orthonormal
variables {v : ι → E} (hv : orthonormal 𝕜 v)

include cplt

-- why `by convert`?
@[simp] protected lemma linear_isometry_apply_single (i : ι) (x : 𝕜) :
  hv.orthogonal_family.linear_isometry (by convert finsupp.mk_lp (finsupp.single i x : ι →₀ 𝕜) 2)
  = x • v i :=
begin
  suffices : ∀ j, j ≠ i → finsupp.single i x j • v j = 0,
  { simpa [hv.orthogonal_family.linear_isometry_apply] using tsum_eq_single i this },
  intros j hj,
  have : finsupp.single i x j = 0 := finsupp.single_eq_of_ne hj.symm,
  simp [this],
end

/-- The canonical linear isometry from `ℓ²(ι, 𝕜)` to `E`, induced by an `ι`-indexed orthonormal
set of vectors in `E`, has range the closure of the span of the vectors. -/
protected lemma range_linear_isometry :
  hv.orthogonal_family.linear_isometry.to_linear_map.range
    = (span 𝕜 (set.range v)).topological_closure :=
begin
  rw hv.orthogonal_family.range_linear_isometry,
  simp [← linear_map.span_singleton_eq_range, ← submodule.span_Union],
end

end orthonormal


section
variables (ι) (𝕜) (E)

/-- A Hilbert basis on `ι` for an inner product space `E` is an identification of `E` with the `lp`
space `ℓ²(ι, 𝕜)`. -/
structure hilbert_basis := of_repr :: (repr : E ≃ₗᵢ[𝕜] ℓ²(ι, 𝕜))

end

-- move this
@[simp] lemma linear_isometry_equiv.coe_of_surjective {R : Type*} {R₂ : Type*} {E₂ : Type*}
  {F : Type*} [semiring R] [semiring R₂] {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R}
  [ring_hom_inv_pair σ₁₂ σ₂₁] [ring_hom_inv_pair σ₂₁ σ₁₂] [semi_normed_group E₂] [module R₂ E₂]
  [normed_group F] [module R F] (f : F →ₛₗᵢ[σ₁₂] E₂) (hfr : function.surjective f) :
  ⇑(linear_isometry_equiv.of_surjective f hfr) = f :=
by ext; refl


namespace hilbert_basis

/-- `b i` is the `i`th basis vector. -/
instance : has_coe_to_fun (hilbert_basis ι 𝕜 E) (λ _, ι → E) :=
{ coe := λ b i, begin
    classical,
    exact b.repr.symm (direct_sum.mk_lp (dfinsupp.single i (1:𝕜) : ⨁ i : ι, 𝕜) 2)
  end }

@[simp] protected lemma repr_self (b : hilbert_basis ι 𝕜 E) (i : ι) :
  b.repr (b i) = (by convert finsupp.mk_lp (finsupp.single i (1:𝕜)) 2 : ℓ²(ι, 𝕜)) :=
begin
  classical,
  show b.repr (b.repr.symm _) = _,
  simp only [direct_sum.to_finsupp_mk_lp, linear_isometry_equiv.apply_symm_apply, set_like.eta,
    set_coe_cast, eq_mpr_eq_cast, subtype.val_eq_coe],
  congr,
  convert dfinsupp.to_finsupp_single i (1:𝕜),
end

variables {v : ι → E} (hv : orthonormal 𝕜 v)
include hv cplt

/-- An orthonormal family of vectors whose span is dense in the whole module is a Hilbert basis. -/
protected def mk (hsp : (span 𝕜 (set.range v)).topological_closure = ⊤) :
  hilbert_basis ι 𝕜 E :=
hilbert_basis.of_repr $
linear_isometry_equiv.symm $
linear_isometry_equiv.of_surjective
hv.orthogonal_family.linear_isometry
begin
  refine linear_map.range_eq_top.mp _,
  rw ← hsp,
  exact hv.range_linear_isometry
end

@[simp] protected lemma mk_apply (hsp : (span 𝕜 (set.range v)).topological_closure = ⊤) (i : ι) :
  hilbert_basis.mk hv hsp i = v i :=
show (hilbert_basis.mk hv hsp).repr.symm _ = v i, by simp [hilbert_basis.mk]

@[simp] protected lemma coe_mk (hsp : (span 𝕜 (set.range v)).topological_closure = ⊤) :
  ⇑(hilbert_basis.mk hv hsp) = v :=
by ext; simp

/-- An orthonormal family of vectors whose span has trivial orthogonal complement is a Hilbert
basis. -/
protected def mk_of_orthogonal_eq_bot (hsp : (span 𝕜 (set.range v))ᗮ = ⊥) : hilbert_basis ι 𝕜 E :=
hilbert_basis.mk hv
(by rw [← orthogonal_orthogonal_eq_closure, orthogonal_eq_top_iff, hsp])

@[simp] protected lemma mk_of_orthogonal_eq_bot_apply (hsp : (span 𝕜 (set.range v))ᗮ = ⊥) (i : ι) :
  hilbert_basis.mk_of_orthogonal_eq_bot hv hsp i = v i :=
hilbert_basis.mk_apply hv _ _

@[simp] protected lemma coe_of_orthogonal_eq_bot_mk (hsp : (span 𝕜 (set.range v))ᗮ = ⊥) :
  ⇑(hilbert_basis.mk_of_orthogonal_eq_bot hv hsp) = v :=
hilbert_basis.coe_mk hv _

omit hv

/-- A Hilbert space admits a Hilbert basis extending a given orthonormal subset. -/
lemma _root_.orthonormal.exists_hilbert_basis_extension
  {s : set E} (hs : orthonormal 𝕜 (coe : s → E)) :
  ∃ (w : set E) (b : hilbert_basis w 𝕜 E), s ⊆ w ∧ ⇑b = (coe : w → E) :=
let ⟨w, hws, hw_ortho, hw_max⟩ := exists_maximal_orthonormal hs in
⟨ w,
  hilbert_basis.mk_of_orthogonal_eq_bot hw_ortho
    (by simpa [maximal_orthonormal_iff_orthogonal_complement_eq_bot hw_ortho] using hw_max),
  hws,
  hilbert_basis.coe_of_orthogonal_eq_bot_mk _ _ ⟩

/-- A Hilbert space admits a Hilbert basis. -/
lemma _root_.orthonormal.exists_hilbert_basis :
  ∃ (w : set E) (b : hilbert_basis w 𝕜 E), ⇑b = (coe : w → E) :=
let ⟨w, hw, hw', hw''⟩ := (orthonormal_empty 𝕜 E).exists_hilbert_basis_extension in ⟨w, hw, hw''⟩

end hilbert_basis
