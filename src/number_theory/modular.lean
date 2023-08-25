/-
Copyright (c) 2021 Alex Kontorovich and Heather Macbeth and Marc Masdeu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth, Marc Masdeu
-/

import analysis.complex.upper_half_plane.basic
import analysis.normed_space.finite_dimension
import linear_algebra.general_linear_group
import linear_algebra.matrix.general_linear_group

/-!
# The action of the modular group SL(2, ℤ) on the upper half-plane

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define the action of `SL(2,ℤ)` on `ℍ` (via restriction of the `SL(2,ℝ)` action in
`analysis.complex.upper_half_plane`). We then define the standard fundamental domain
(`modular_group.fd`, `𝒟`) for this action and show
(`modular_group.exists_smul_mem_fd`) that any point in `ℍ` can be
moved inside `𝒟`.

## Main definitions

The standard (closed) fundamental domain of the action of `SL(2,ℤ)` on `ℍ`, denoted `𝒟`:
`fd := {z | 1 ≤ (z : ℂ).norm_sq ∧ |z.re| ≤ (1 : ℝ) / 2}`

The standard open fundamental domain of the action of `SL(2,ℤ)` on `ℍ`, denoted `𝒟ᵒ`:
`fdo := {z | 1 < (z : ℂ).norm_sq ∧ |z.re| < (1 : ℝ) / 2}`

These notations are localized in the `modular` locale and can be enabled via `open_locale modular`.

## Main results

Any `z : ℍ` can be moved to `𝒟` by an element of `SL(2,ℤ)`:
`exists_smul_mem_fd (z : ℍ) : ∃ g : SL(2,ℤ), g • z ∈ 𝒟`

If both `z` and `γ • z` are in the open domain `𝒟ᵒ` then `z = γ • z`:
`eq_smul_self_of_mem_fdo_mem_fdo {z : ℍ} {g : SL(2,ℤ)} (hz : z ∈ 𝒟ᵒ) (hg : g • z ∈ 𝒟ᵒ) : z = g • z`

# Discussion

Standard proofs make use of the identity

`g • z = a / c - 1 / (c (cz + d))`

for `g = [[a, b], [c, d]]` in `SL(2)`, but this requires separate handling of whether `c = 0`.
Instead, our proof makes use of the following perhaps novel identity (see
`modular_group.smul_eq_lc_row0_add`):

`g • z = (a c + b d) / (c^2 + d^2) + (d z - c) / ((c^2 + d^2) (c z + d))`

where there is no issue of division by zero.

Another feature is that we delay until the very end the consideration of special matrices
`T=[[1,1],[0,1]]` (see `modular_group.T`) and `S=[[0,-1],[1,0]]` (see `modular_group.S`), by
instead using abstract theory on the properness of certain maps (phrased in terms of the filters
`filter.cocompact`, `filter.cofinite`, etc) to deduce existence theorems, first to prove the
existence of `g` maximizing `(g•z).im` (see `modular_group.exists_max_im`), and then among
those, to minimize `|(g•z).re|` (see `modular_group.exists_row_one_eq_and_min_re`).
-/

/- Disable these instances as they are not the simp-normal form, and having them disabled ensures
we state lemmas in this file without spurious `coe_fn` terms. -/
local attribute [-instance] matrix.special_linear_group.has_coe_to_fun
local attribute [-instance] matrix.general_linear_group.has_coe_to_fun

open complex (hiding abs_two)
open matrix (hiding mul_smul) matrix.special_linear_group upper_half_plane
noncomputable theory

local notation `SL(` n `, ` R `)`:= special_linear_group (fin n) R
local prefix `↑ₘ`:1024 := @coe _ (matrix (fin 2) (fin 2) ℤ) _

open_locale upper_half_plane complex_conjugate

local attribute [instance] fintype.card_fin_even

namespace modular_group

variables {g : SL(2, ℤ)} (z : ℍ)

section bottom_row

/-- The two numbers `c`, `d` in the "bottom_row" of `g=[[*,*],[c,d]]` in `SL(2, ℤ)` are coprime. -/
lemma bottom_row_coprime {R : Type*} [comm_ring R] (g : SL(2, R)) :
  is_coprime ((↑g : matrix (fin 2) (fin 2) R) 1 0) ((↑g : matrix (fin 2) (fin 2) R) 1 1) :=
begin
  use [- (↑g : matrix (fin 2) (fin 2) R) 0 1, (↑g : matrix (fin 2) (fin 2) R) 0 0],
  rw [add_comm, neg_mul, ←sub_eq_add_neg, ←det_fin_two],
  exact g.det_coe,
end

/-- Every pair `![c, d]` of coprime integers is the "bottom_row" of some element `g=[[*,*],[c,d]]`
of `SL(2,ℤ)`. -/
lemma bottom_row_surj {R : Type*} [comm_ring R] :
  set.surj_on (λ g : SL(2, R), @coe _ (matrix (fin 2) (fin 2) R) _ g 1) set.univ
    {cd | is_coprime (cd 0) (cd 1)} :=
begin
  rintros cd ⟨b₀, a, gcd_eqn⟩,
  let A := of ![![a, -b₀], cd],
  have det_A_1 : det A = 1,
  { convert gcd_eqn,
    simp [A, det_fin_two, (by ring : a * (cd 1) + b₀ * (cd 0) = b₀ * (cd 0) + a * (cd 1))] },
  refine ⟨⟨A, det_A_1⟩, set.mem_univ _, _⟩,
  ext; simp [A]
end

end bottom_row

section tendsto_lemmas

open filter continuous_linear_map
local attribute [simp] coe_smul

/-- The function `(c,d) → |cz+d|^2` is proper, that is, preimages of bounded-above sets are finite.
-/
lemma tendsto_norm_sq_coprime_pair :
  filter.tendsto (λ p : fin 2 → ℤ, ((p 0 : ℂ) * z + p 1).norm_sq)
  cofinite at_top :=
begin
  -- using this instance rather than the automatic `function.module` makes unification issues in
  -- `linear_equiv.closed_embedding_of_injective` less bad later in the proof.
  letI : module ℝ (fin 2 → ℝ) := normed_space.to_module,
  let π₀ : (fin 2 → ℝ) →ₗ[ℝ] ℝ := linear_map.proj 0,
  let π₁ : (fin 2 → ℝ) →ₗ[ℝ] ℝ := linear_map.proj 1,
  let f : (fin 2 → ℝ) →ₗ[ℝ] ℂ := π₀.smul_right (z:ℂ) + π₁.smul_right 1,
  have f_def : ⇑f = λ (p : fin 2 → ℝ), (p 0 : ℂ) * ↑z + p 1,
  { ext1,
    dsimp only [linear_map.coe_proj, real_smul,
      linear_map.coe_smul_right, linear_map.add_apply],
    rw mul_one, },
  have : (λ (p : fin 2 → ℤ), norm_sq ((p 0 : ℂ) * ↑z + ↑(p 1)))
    = norm_sq ∘ f ∘ (λ p : fin 2 → ℤ, (coe : ℤ → ℝ) ∘ p),
  { ext1,
    rw f_def,
    dsimp only [function.comp],
    rw [of_real_int_cast, of_real_int_cast], },
  rw this,
  have hf : f.ker = ⊥,
  { let g : ℂ →ₗ[ℝ] (fin 2 → ℝ) :=
      linear_map.pi ![im_lm, im_lm.comp ((z:ℂ) • ((conj_ae : ℂ →ₐ[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ))],
    suffices : ((z:ℂ).im⁻¹ • g).comp f = linear_map.id,
    { exact linear_map.ker_eq_bot_of_inverse this },
    apply linear_map.ext,
    intros c,
    have hz : (z:ℂ).im ≠ 0 := z.2.ne',
    rw [linear_map.comp_apply, linear_map.smul_apply, linear_map.id_apply],
    ext i,
    dsimp only [g, pi.smul_apply, linear_map.pi_apply, smul_eq_mul],
    fin_cases i,
    { show ((z : ℂ).im)⁻¹ * (f c).im = c 0,
      rw [f_def, add_im, of_real_mul_im, of_real_im, add_zero, mul_left_comm,
        inv_mul_cancel hz, mul_one], },
    { show ((z : ℂ).im)⁻¹ * ((z : ℂ) * conj (f c)).im = c 1,
      rw [f_def, ring_hom.map_add, ring_hom.map_mul, mul_add, mul_left_comm, mul_conj,
        conj_of_real, conj_of_real, ← of_real_mul, add_im, of_real_im, zero_add,
        inv_mul_eq_iff_eq_mul₀ hz],
      simp only [of_real_im, of_real_re, mul_im, zero_add, mul_zero] } },
  have hf' : closed_embedding f,
  { -- for some reason we get a timeout if we try and apply this lemma in a more sensible way
    have := @linear_equiv.closed_embedding_of_injective ℝ _ (fin 2 → ℝ) _ (id _) ℂ _ _ _ _,
    rotate 2,
    exact f,
    exact this hf },
  have h₂ : tendsto (λ p : fin 2 → ℤ, (coe : ℤ → ℝ) ∘ p) cofinite (cocompact _),
  { convert tendsto.pi_map_Coprod (λ i, int.tendsto_coe_cofinite),
    { rw Coprod_cofinite },
    { rw Coprod_cocompact } },
  exact tendsto_norm_sq_cocompact_at_top.comp (hf'.tendsto_cocompact.comp h₂),
end

/-- Given `coprime_pair` `p=(c,d)`, the matrix `[[a,b],[*,*]]` is sent to `a*c+b*d`.
  This is the linear map version of this operation.
-/
def lc_row0 (p : fin 2 → ℤ) : (matrix (fin 2) (fin 2) ℝ) →ₗ[ℝ] ℝ :=
((p 0:ℝ) • linear_map.proj 0 + (p 1:ℝ) • linear_map.proj 1 : (fin 2 → ℝ) →ₗ[ℝ] ℝ).comp
  (linear_map.proj 0)

@[simp] lemma lc_row0_apply (p : fin 2 → ℤ) (g : matrix (fin 2) (fin 2) ℝ) :
  lc_row0 p g = p 0 * g 0 0 + p 1 * g 0 1 :=
rfl

/-- Linear map sending the matrix [a, b; c, d] to the matrix [ac₀ + bd₀, - ad₀ + bc₀; c, d], for
some fixed `(c₀, d₀)`. -/
@[simps] def lc_row0_extend {cd : fin 2 → ℤ} (hcd : is_coprime (cd 0) (cd 1)) :
  (matrix (fin 2) (fin 2) ℝ) ≃ₗ[ℝ] matrix (fin 2) (fin 2) ℝ :=
linear_equiv.Pi_congr_right
![begin
    refine linear_map.general_linear_group.general_linear_equiv ℝ (fin 2 → ℝ)
      (general_linear_group.to_linear (plane_conformal_matrix (cd 0 : ℝ) (-(cd 1 : ℝ)) _)),
    norm_cast,
    rw neg_sq,
    exact hcd.sq_add_sq_ne_zero
  end,
  linear_equiv.refl ℝ (fin 2 → ℝ)]

/-- The map `lc_row0` is proper, that is, preimages of cocompact sets are finite in
`[[* , *], [c, d]]`.-/
theorem tendsto_lc_row0 {cd : fin 2 → ℤ} (hcd : is_coprime (cd 0) (cd 1)) :
  tendsto (λ g : {g : SL(2, ℤ) // ↑ₘg 1 = cd}, lc_row0 cd ↑(↑g : SL(2, ℝ)))
    cofinite (cocompact ℝ) :=
begin
  let mB : ℝ → (matrix (fin 2) (fin 2) ℝ) := λ t, of ![![t, (-(1:ℤ):ℝ)], coe ∘ cd],
  have hmB : continuous mB,
  { refine continuous_matrix _,
    simp only [fin.forall_fin_two, mB, continuous_const, continuous_id', of_apply,
      cons_val_zero, cons_val_one, and_self ] },
  refine filter.tendsto.of_tendsto_comp _ (comap_cocompact_le hmB),
  let f₁ : SL(2, ℤ) → matrix (fin 2) (fin 2) ℝ :=
    λ g, matrix.map (↑g : matrix _ _ ℤ) (coe : ℤ → ℝ),
  have cocompact_ℝ_to_cofinite_ℤ_matrix :
    tendsto (λ m : matrix (fin 2) (fin 2) ℤ, matrix.map m (coe : ℤ → ℝ)) cofinite (cocompact _),
  { simpa only [Coprod_cofinite, Coprod_cocompact]
      using tendsto.pi_map_Coprod (λ i : fin 2, tendsto.pi_map_Coprod
        (λ j : fin 2, int.tendsto_coe_cofinite)) },
  have hf₁ : tendsto f₁ cofinite (cocompact _) :=
    cocompact_ℝ_to_cofinite_ℤ_matrix.comp subtype.coe_injective.tendsto_cofinite,
  have hf₂ : closed_embedding (lc_row0_extend hcd) :=
    (lc_row0_extend hcd).to_continuous_linear_equiv.to_homeomorph.closed_embedding,
  convert hf₂.tendsto_cocompact.comp (hf₁.comp subtype.coe_injective.tendsto_cofinite) using 1,
  ext ⟨g, rfl⟩ i j : 3,
  fin_cases i; [fin_cases j, skip],
  -- the following are proved by `simp`, but it is replaced by `simp only` to avoid timeouts.
  { simp only [mB, mul_vec, dot_product, fin.sum_univ_two, _root_.coe_coe, coe_matrix_coe,
      int.coe_cast_ring_hom, lc_row0_apply, function.comp_app, cons_val_zero, lc_row0_extend_apply,
      linear_map.general_linear_group.coe_fn_general_linear_equiv,
      general_linear_group.to_linear_apply, coe_plane_conformal_matrix, neg_neg, mul_vec_lin_apply,
      cons_val_one, head_cons, of_apply] },
  { convert congr_arg (λ n : ℤ, (-n:ℝ)) g.det_coe.symm using 1,
    simp only [f₁, mul_vec, dot_product, fin.sum_univ_two, matrix.det_fin_two, function.comp_app,
      subtype.coe_mk, lc_row0_extend_apply, cons_val_zero,
      linear_map.general_linear_group.coe_fn_general_linear_equiv,
      general_linear_group.to_linear_apply, coe_plane_conformal_matrix, mul_vec_lin_apply,
      cons_val_one, head_cons, map_apply, neg_mul, int.cast_sub, int.cast_mul, neg_sub, of_apply],
    ring },
  { refl }
end

/-- This replaces `(g•z).re = a/c + *` in the standard theory with the following novel identity:
  `g • z = (a c + b d) / (c^2 + d^2) + (d z - c) / ((c^2 + d^2) (c z + d))`
  which does not need to be decomposed depending on whether `c = 0`. -/
lemma smul_eq_lc_row0_add {p : fin 2 → ℤ} (hp : is_coprime (p 0) (p 1)) (hg : ↑ₘg 1 = p) :
  ↑(g • z) = ((lc_row0 p ↑(g : SL(2, ℝ))) : ℂ) / (p 0 ^ 2 + p 1 ^ 2)
    + ((p 1 : ℂ) * z - p 0) / ((p 0 ^ 2 + p 1 ^ 2) * (p 0 * z + p 1)) :=
begin
  have nonZ1 : (p 0 : ℂ) ^ 2 + (p 1) ^ 2 ≠ 0 := by exact_mod_cast hp.sq_add_sq_ne_zero,
  have : (coe : ℤ → ℝ) ∘ p ≠ 0 := λ h, hp.ne_zero (by ext i; simpa using congr_fun h i),
  have nonZ2 : (p 0 : ℂ) * z + p 1 ≠ 0 := by simpa using linear_ne_zero _ z this,
  field_simp [nonZ1, nonZ2, denom_ne_zero, -upper_half_plane.denom, -denom_apply],
  rw (by simp : (p 1 : ℂ) * z - p 0 = ((p 1) * z - p 0) * ↑(det (↑g : matrix (fin 2) (fin 2) ℤ))),
  rw [←hg, det_fin_two],
  simp only [int.coe_cast_ring_hom, coe_matrix_coe, int.cast_mul, of_real_int_cast, map_apply,
  denom, int.cast_sub, _root_.coe_coe,coe_GL_pos_coe_GL_coe_matrix],
  ring,
end

lemma tendsto_abs_re_smul {p : fin 2 → ℤ} (hp : is_coprime (p 0) (p 1)) :
  tendsto (λ g : {g : SL(2, ℤ) // ↑ₘg 1 = p}, |((g : SL(2, ℤ)) • z).re|)
    cofinite at_top :=
begin
  suffices : tendsto (λ g : (λ g : SL(2, ℤ), ↑ₘg 1) ⁻¹' {p}, (((g : SL(2, ℤ)) • z).re))
    cofinite (cocompact ℝ),
  { exact tendsto_norm_cocompact_at_top.comp this },
  have : ((p 0 : ℝ) ^ 2 + p 1 ^ 2)⁻¹ ≠ 0,
  { apply inv_ne_zero,
    exact_mod_cast hp.sq_add_sq_ne_zero },
  let f := homeomorph.mul_right₀ _ this,
  let ff := homeomorph.add_right (((p 1:ℂ)* z - p 0) / ((p 0 ^ 2 + p 1 ^ 2) * (p 0 * z + p 1))).re,
  convert ((f.trans ff).closed_embedding.tendsto_cocompact).comp (tendsto_lc_row0 hp),
  ext g,
  change ((g : SL(2, ℤ)) • z).re = (lc_row0 p ↑(↑g : SL(2, ℝ))) / (p 0 ^ 2 + p 1 ^ 2)
  + (((p 1:ℂ )* z - p 0) / ((p 0 ^ 2 + p 1 ^ 2) * (p 0 * z + p 1))).re,
  exact_mod_cast (congr_arg complex.re (smul_eq_lc_row0_add z hp g.2))
end

end tendsto_lemmas

section fundamental_domain

local attribute [simp] coe_smul re_smul

/-- For `z : ℍ`, there is a `g : SL(2,ℤ)` maximizing `(g•z).im` -/
lemma exists_max_im :
  ∃ g : SL(2, ℤ), ∀ g' : SL(2, ℤ), (g' • z).im ≤ (g • z).im :=
begin
  classical,
  let s : set (fin 2 → ℤ) := {cd | is_coprime (cd 0) (cd 1)},
  have hs : s.nonempty := ⟨![1, 1], is_coprime_one_left⟩,
  obtain ⟨p, hp_coprime, hp⟩ :=
    filter.tendsto.exists_within_forall_le hs (tendsto_norm_sq_coprime_pair z),
  obtain ⟨g, -, hg⟩ := bottom_row_surj hp_coprime,
  refine ⟨g, λ g', _⟩,
  rw [special_linear_group.im_smul_eq_div_norm_sq, special_linear_group.im_smul_eq_div_norm_sq,
    div_le_div_left],
  { simpa [← hg] using hp (↑ₘg' 1) (bottom_row_coprime g') },
  { exact z.im_pos },
  { exact norm_sq_denom_pos g' z },
  { exact norm_sq_denom_pos g z },
end

/-- Given `z : ℍ` and a bottom row `(c,d)`, among the `g : SL(2,ℤ)` with this bottom row, minimize
  `|(g•z).re|`.  -/
lemma exists_row_one_eq_and_min_re {cd : fin 2 → ℤ} (hcd : is_coprime (cd 0) (cd 1)) :
  ∃ g : SL(2,ℤ), ↑ₘg 1 = cd ∧ (∀ g' : SL(2,ℤ), ↑ₘg 1 = ↑ₘg' 1 →
  |(g • z).re| ≤ |(g' • z).re|) :=
begin
  haveI : nonempty {g : SL(2, ℤ) // ↑ₘg 1 = cd} :=
    let ⟨x, hx⟩ := bottom_row_surj hcd in ⟨⟨x, hx.2⟩⟩,
  obtain ⟨g, hg⟩ := filter.tendsto.exists_forall_le (tendsto_abs_re_smul z hcd),
  refine ⟨g, g.2, _⟩,
  { intros g1 hg1,
    have : g1 ∈ ((λ g : SL(2, ℤ), ↑ₘg 1) ⁻¹' {cd}),
    { rw [set.mem_preimage, set.mem_singleton_iff],
      exact eq.trans hg1.symm (set.mem_singleton_iff.mp (set.mem_preimage.mp g.2)) },
    exact hg ⟨g1, this⟩ },
end

lemma coe_T_zpow_smul_eq {n : ℤ} : (↑((T^n) • z) : ℂ) = z + n :=
by simp [coe_T_zpow]

lemma re_T_zpow_smul (n : ℤ) : ((T^n) • z).re = z.re + n :=
by rw [←coe_re, coe_T_zpow_smul_eq, add_re, int_cast_re, coe_re]

lemma im_T_zpow_smul (n : ℤ) : ((T^n) • z).im = z.im :=
by rw [←coe_im, coe_T_zpow_smul_eq, add_im, int_cast_im, add_zero, coe_im]

lemma re_T_smul : (T • z).re = z.re + 1 := by simpa using re_T_zpow_smul z 1
lemma im_T_smul : (T • z).im = z.im := by simpa using im_T_zpow_smul z 1
lemma re_T_inv_smul : (T⁻¹ • z).re = z.re - 1 := by simpa using re_T_zpow_smul z (-1)
lemma im_T_inv_smul : (T⁻¹ • z).im = z.im := by simpa using im_T_zpow_smul z (-1)

variables {z}

-- If instead we had `g` and `T` of type `PSL(2, ℤ)`, then we could simply state `g = T^n`.
lemma exists_eq_T_zpow_of_c_eq_zero (hc : ↑ₘg 1 0 = 0) :
  ∃ (n : ℤ), ∀ (z : ℍ), g • z = T^n • z :=
begin
  have had := g.det_coe,
  replace had : ↑ₘg 0 0 * ↑ₘg 1 1 = 1, { rw [det_fin_two, hc] at had, linarith, },
  rcases int.eq_one_or_neg_one_of_mul_eq_one' had with ⟨ha, hd⟩ | ⟨ha, hd⟩,
  { use ↑ₘg 0 1,
    suffices : g = T^(↑ₘg 0 1), { intros z, conv_lhs { rw this, }, },
    ext i j, fin_cases i; fin_cases j;
    simp [ha, hc, hd, coe_T_zpow], },
  { use -↑ₘg 0 1,
    suffices : g = -T^(-↑ₘg 0 1), { intros z, conv_lhs { rw [this, SL_neg_smul], }, },
    ext i j, fin_cases i; fin_cases j;
    simp [ha, hc, hd, coe_T_zpow], },
end

/- If `c = 1`, then `g` factorises into a product terms involving only `T` and `S`. -/
lemma g_eq_of_c_eq_one (hc : ↑ₘg 1 0 = 1) :
  g = T^(↑ₘg 0 0) * S * T^(↑ₘg 1 1) :=
begin
  have hg := g.det_coe.symm,
  replace hg : ↑ₘg 0 1 = ↑ₘg 0 0 * ↑ₘg 1 1 - 1, { rw [det_fin_two, hc] at hg, linarith, },
  refine subtype.ext _,
  conv_lhs { rw matrix.eta_fin_two ↑ₘg },
  rw [hc, hg],
  simp only [coe_mul, coe_T_zpow, coe_S, mul_fin_two],
  congrm !![_, _; _, _]; ring
end

/-- If `1 < |z|`, then `|S • z| < 1`. -/
lemma norm_sq_S_smul_lt_one (h: 1 < norm_sq z) : norm_sq ↑(S • z) < 1 :=
by simpa [coe_S] using (inv_lt_inv z.norm_sq_pos zero_lt_one).mpr h

/-- If `|z| < 1`, then applying `S` strictly decreases `im`. -/
lemma im_lt_im_S_smul (h: norm_sq z < 1) : z.im < (S • z).im :=
begin
  have : z.im < z.im / norm_sq (z:ℂ),
  { have imz : 0 < z.im := im_pos z,
    apply (lt_div_iff z.norm_sq_pos).mpr,
    nlinarith },
  convert this,
  simp only [special_linear_group.im_smul_eq_div_norm_sq],
  field_simp [norm_sq_denom_ne_zero, norm_sq_ne_zero, S]
end

/-- The standard (closed) fundamental domain of the action of `SL(2,ℤ)` on `ℍ`. -/
def fd : set ℍ :=
{z | 1 ≤ (z : ℂ).norm_sq ∧ |z.re| ≤ (1 : ℝ) / 2}

/-- The standard open fundamental domain of the action of `SL(2,ℤ)` on `ℍ`. -/
def fdo : set ℍ :=
{z | 1 < (z : ℂ).norm_sq ∧ |z.re| < (1 : ℝ) / 2}

localized "notation (name := modular_group.fd) `𝒟` := modular_group.fd" in modular

localized "notation (name := modular_group.fdo) `𝒟ᵒ` := modular_group.fdo" in modular

lemma abs_two_mul_re_lt_one_of_mem_fdo (h : z ∈ 𝒟ᵒ) : |2 * z.re| < 1 :=
begin
  rw [abs_mul, abs_two, ← lt_div_iff' (zero_lt_two' ℝ)],
  exact h.2,
end

lemma three_lt_four_mul_im_sq_of_mem_fdo (h : z ∈ 𝒟ᵒ) : 3 < 4 * z.im^2 :=
begin
  have : 1 < z.re * z.re + z.im * z.im := by simpa [complex.norm_sq_apply] using h.1,
  have := h.2,
  cases abs_cases z.re;
  nlinarith,
end

/-- If `z ∈ 𝒟ᵒ`, and `n : ℤ`, then `|z + n| > 1`. -/
lemma one_lt_norm_sq_T_zpow_smul (hz : z ∈ 𝒟ᵒ) (n : ℤ) : 1 < norm_sq (((T^n) • z) : ℍ) :=
begin
  have hz₁ : 1 < z.re * z.re + z.im * z.im := hz.1,
  have hzn := int.nneg_mul_add_sq_of_abs_le_one n (abs_two_mul_re_lt_one_of_mem_fdo hz).le,
  have : 1 < (z.re + ↑n) * (z.re + ↑n) + z.im * z.im, { linarith, },
  simpa [coe_T_zpow, norm_sq],
end

lemma eq_zero_of_mem_fdo_of_T_zpow_mem_fdo {n : ℤ} (hz : z ∈ 𝒟ᵒ) (hg : (T^n) • z ∈ 𝒟ᵒ) : n = 0 :=
begin
  suffices : |(n : ℝ)| < 1,
  { rwa [← int.cast_abs, ← int.cast_one, int.cast_lt, int.abs_lt_one_iff] at this, },
  have h₁ := hz.2,
  have h₂ := hg.2,
  rw [re_T_zpow_smul] at h₂,
  calc |(n : ℝ)| ≤ |z.re| + |z.re + (n : ℝ)| : abs_add' (n : ℝ) z.re
             ... < 1/2 + 1/2 : add_lt_add h₁ h₂
             ... = 1 : add_halves 1,
end

/-- Any `z : ℍ` can be moved to `𝒟` by an element of `SL(2,ℤ)`  -/
lemma exists_smul_mem_fd (z : ℍ) : ∃ g : SL(2,ℤ), g • z ∈ 𝒟 :=
begin
  -- obtain a g₀ which maximizes im (g • z),
  obtain ⟨g₀, hg₀⟩ := exists_max_im z,
  -- then among those, minimize re
  obtain ⟨g, hg, hg'⟩ := exists_row_one_eq_and_min_re z (bottom_row_coprime g₀),
  refine ⟨g, _⟩,
  -- `g` has same max im property as `g₀`
  have hg₀' : ∀ (g' : SL(2,ℤ)), (g' • z).im ≤ (g • z).im,
  { have hg'' : (g • z).im = (g₀ • z).im,
    { rw [special_linear_group.im_smul_eq_div_norm_sq, special_linear_group.im_smul_eq_div_norm_sq,
      denom_apply, denom_apply, hg]},
    simpa only [hg''] using hg₀ },
  split,
  { -- Claim: `1 ≤ ⇑norm_sq ↑(g • z)`. If not, then `S•g•z` has larger imaginary part
    contrapose! hg₀',
    refine ⟨S * g, _⟩,
    rw mul_smul,
    exact im_lt_im_S_smul hg₀' },
  { show |(g • z).re| ≤ 1 / 2, -- if not, then either `T` or `T'` decrease |Re|.
    rw abs_le,
    split,
    { contrapose! hg',
      refine ⟨T * g, (T_mul_apply_one _).symm, _⟩,
      rw [mul_smul, re_T_smul],
      cases abs_cases ((g • z).re + 1); cases abs_cases (g • z).re; linarith },
    { contrapose! hg',
      refine ⟨T⁻¹ * g, (T_inv_mul_apply_one _).symm, _⟩,
      rw [mul_smul, re_T_inv_smul],
      cases abs_cases ((g • z).re - 1); cases abs_cases (g • z).re; linarith } }
end

section unique_representative

variables {z}

/-- An auxiliary result en route to `modular_group.c_eq_zero`. -/
lemma abs_c_le_one (hz : z ∈ 𝒟ᵒ) (hg : g • z ∈ 𝒟ᵒ) : |↑ₘg 1 0| ≤ 1 :=
begin
  let c' : ℤ := ↑ₘg 1 0,
  let c : ℝ := (c' : ℝ),
  suffices : 3 * c^2 < 4,
  { rw [← int.cast_pow, ← int.cast_three, ← int.cast_four, ← int.cast_mul, int.cast_lt] at this,
    replace this : c' ^ 2 ≤ 1 ^ 2, { linarith, },
    rwa [sq_le_sq, abs_one] at this },
  suffices : c ≠ 0 → 9 * c^4 < 16,
  { rcases eq_or_ne c 0 with hc | hc,
    { rw hc, norm_num, },
    { refine (abs_lt_of_sq_lt_sq' _ (by norm_num)).2,
      specialize this hc,
      linarith, }, },
  intros hc,
  replace hc : 0 < c^4, { rw pow_bit0_pos_iff; trivial, },
  have h₁ := mul_lt_mul_of_pos_right (mul_lt_mul'' (three_lt_four_mul_im_sq_of_mem_fdo hg)
      (three_lt_four_mul_im_sq_of_mem_fdo hz) (by linarith) (by linarith)) hc,
  have h₂ : (c * z.im) ^ 4 / norm_sq (denom ↑g z) ^ 2 ≤ 1 :=
    div_le_one_of_le (pow_four_le_pow_two_of_pow_two_le
      (upper_half_plane.c_mul_im_sq_le_norm_sq_denom z g)) (sq_nonneg _),
  let nsq := norm_sq (denom g z),
  calc 9 * c^4 < c^4 * z.im^2 * (g • z).im^2 * 16 : by linarith
           ... = c^4 * z.im^4 / nsq^2 * 16 : by { rw [special_linear_group.im_smul_eq_div_norm_sq,
            div_pow], ring, }
           ... ≤ 16 : by { rw ← mul_pow, linarith, },
end

/-- An auxiliary result en route to `modular_group.eq_smul_self_of_mem_fdo_mem_fdo`. -/
lemma c_eq_zero (hz : z ∈ 𝒟ᵒ) (hg : g • z ∈ 𝒟ᵒ) : ↑ₘg 1 0 = 0 :=
begin
  have hp : ∀ {g' : SL(2, ℤ)} (hg' : g' • z ∈ 𝒟ᵒ), ↑ₘg' 1 0 ≠ 1,
  { intros,
    by_contra hc,
    let a := ↑ₘg' 0 0,
    let d := ↑ₘg' 1 1,
    have had : T^(-a) * g' = S * T^d, { rw g_eq_of_c_eq_one hc, group, },
    let w := T^(-a) • (g' • z),
    have h₁ : w = S • (T^d • z), { simp only [w, ← mul_smul, had], },
    replace h₁ : norm_sq w < 1 := h₁.symm ▸ norm_sq_S_smul_lt_one (one_lt_norm_sq_T_zpow_smul hz d),
    have h₂ : 1 < norm_sq w := one_lt_norm_sq_T_zpow_smul hg' (-a),
    linarith, },
  have hn : ↑ₘg 1 0 ≠ -1,
  { intros hc,
    replace hc : ↑ₘ(-g) 1 0 = 1, { simp [← neg_eq_iff_eq_neg.mpr hc], },
    replace hg : (-g) • z ∈ 𝒟ᵒ := (SL_neg_smul g z).symm ▸ hg,
    exact hp hg hc, },
  specialize hp hg,
  rcases (int.abs_le_one_iff.mp $ abs_c_le_one hz hg);
  tauto,
end

/-- Second Main Fundamental Domain Lemma: if both `z` and `g • z` are in the open domain `𝒟ᵒ`,
where `z : ℍ` and `g : SL(2,ℤ)`, then `z = g • z`. -/
lemma eq_smul_self_of_mem_fdo_mem_fdo (hz : z ∈ 𝒟ᵒ) (hg : g • z ∈ 𝒟ᵒ) : z = g • z :=
begin
  obtain ⟨n, hn⟩ := exists_eq_T_zpow_of_c_eq_zero (c_eq_zero hz hg),
  rw hn at hg ⊢,
  simp [eq_zero_of_mem_fdo_of_T_zpow_mem_fdo hz hg, one_smul],
end

end unique_representative

end fundamental_domain

end modular_group
