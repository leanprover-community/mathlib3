/-
Copyright (c) 2021 Alex Kontorovich and Heather Macbeth and Marc Masdeu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth, Marc Masdeu
-/

import analysis.complex.upper_half_plane
import linear_algebra.general_linear_group
import analysis.matrix

/-!
# The action of the modular group SL(2, ℤ) on the upper half-plane

We define the action of `SL(2,ℤ)` on `ℍ` (via restriction of the `SL(2,ℝ)` action in
`analysis.complex.upper_half_plane`). We then define the standard fundamental domain
(`modular_group.fundamental_domain`, `𝒟`) for this action and show
(`modular_group.exists_smul_mem_fundamental_domain`) that any point in `ℍ` can be
moved inside `𝒟`.

## Main definitions

The standard (closed) fundamental domain of the action of `SL(2,ℤ)` on `ℍ`:
`fundamental_domain := {z | 1 ≤ (z : ℂ).norm_sq ∧ |z.re| ≤ (1 : ℝ) / 2}`

The standard open fundamental domain of the action of `SL(2,ℤ)` on `ℍ`:
`fundamental_domain_open := {z | 1 < (z : ℂ).norm_sq ∧ |z.re| < (1 : ℝ) / 2}`


## Main results

Any `z : ℍ` can be moved to `𝒟` by an element of `SL(2,ℤ)`:
`exists_smul_mem_fundamental_domain (z : ℍ) : ∃ g : SL(2,ℤ), g • z ∈ 𝒟`

If both `z` and `γ • z` are in the open domain `𝒟ᵒ` then `z = γ • z`:
`fun_dom_lemma₂ (z : ℍ) (g : SL(2,ℤ)) (hz : z ∈ 𝒟ᵒ) (hg : g • z ∈ 𝒟ᵒ) : z = g • z`

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

open complex matrix matrix.special_linear_group upper_half_plane
noncomputable theory

local notation `SL(` n `, ` R `)`:= special_linear_group (fin n) R
local prefix `↑ₘ`:1024 := @coe _ (matrix (fin 2) (fin 2) ℤ) _


open_locale upper_half_plane complex_conjugate

local attribute [instance] fintype.card_fin_even

namespace modular_group

section upper_half_plane_action

/-- For a subring `R` of `ℝ`, the action of `SL(2, R)` on the upper half-plane, as a restriction of
the `SL(2, ℝ)`-action defined by `upper_half_plane.mul_action`. -/
instance {R : Type*} [comm_ring R] [algebra R ℝ] : mul_action SL(2, R) ℍ :=
mul_action.comp_hom ℍ (map (algebra_map R ℝ))

lemma coe_smul (g : SL(2, ℤ)) (z : ℍ) : ↑(g • z) = num g z / denom g z := rfl
lemma re_smul (g : SL(2, ℤ)) (z : ℍ) : (g • z).re = (num g z / denom g z).re := rfl
@[simp] lemma smul_coe (g : SL(2, ℤ)) (z : ℍ) : (g : SL(2,ℝ)) • z = g • z := rfl

@[simp] lemma neg_smul (g : SL(2, ℤ)) (z : ℍ) : -g • z = g • z :=
show ↑(-g) • _ = _, by simp [neg_smul g z]

lemma im_smul (g : SL(2, ℤ)) (z : ℍ) : (g • z).im = (num g z / denom g z).im := rfl

lemma im_smul_eq_div_norm_sq (g : SL(2, ℤ)) (z : ℍ) :
  (g • z).im = z.im / (complex.norm_sq (denom g z)) :=
im_smul_eq_div_norm_sq g z

@[simp] lemma denom_apply (g : SL(2, ℤ)) (z : ℍ) : denom g z = ↑ₘg 1 0 * z + ↑ₘg 1 1 := by simp

end upper_half_plane_action

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
  let A := ![![a, -b₀], cd],
  have det_A_1 : det A = 1,
  { convert gcd_eqn,
    simp [A, det_fin_two, (by ring : a * (cd 1) + b₀ * (cd 0) = b₀ * (cd 0) + a * (cd 1))] },
  refine ⟨⟨A, det_A_1⟩, set.mem_univ _, _⟩,
  ext; simp [A]
end

end bottom_row

section tendsto_lemmas

open filter continuous_linear_map
local attribute [instance] matrix.normed_group matrix.normed_space
local attribute [simp] coe_smul

/-- The function `(c,d) → |cz+d|^2` is proper, that is, preimages of bounded-above sets are finite.
-/
lemma tendsto_norm_sq_coprime_pair (z : ℍ) :
  filter.tendsto (λ p : fin 2 → ℤ, ((p 0 : ℂ) * z + p 1).norm_sq)
  cofinite at_top :=
begin
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
      linear_map.pi ![im_lm, im_lm.comp ((z:ℂ) • (conj_ae  : ℂ →ₗ[ℝ] ℂ))],
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
  have h₁ := (linear_equiv.closed_embedding_of_injective hf).tendsto_cocompact,
  have h₂ : tendsto (λ p : fin 2 → ℤ, (coe : ℤ → ℝ) ∘ p) cofinite (cocompact _),
  { convert tendsto.pi_map_Coprod (λ i, int.tendsto_coe_cofinite),
    { rw Coprod_cofinite },
    { rw Coprod_cocompact } },
  exact tendsto_norm_sq_cocompact_at_top.comp (h₁.comp h₂)
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

lemma lc_row0_apply' (a b : ℝ) (c d : ℤ) (v : fin 2 → ℝ) :
  lc_row0 ![c, d] ![![a, b], v] = c * a + d * b :=
by simp

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
  let mB : ℝ → (matrix (fin 2) (fin 2)  ℝ) := λ t, ![![t, (-(1:ℤ):ℝ)], coe ∘ cd],
  have hmB : continuous mB,
  { simp only [continuous_pi_iff, fin.forall_fin_two],
    have : ∀ c : ℝ, continuous (λ x : ℝ, c) := λ c, continuous_const,
    exact ⟨⟨continuous_id, @this (-1 : ℤ)⟩, ⟨this (cd 0), this (cd 1)⟩⟩ },
  refine filter.tendsto.of_tendsto_comp _ (comap_cocompact hmB),
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
      cons_val_one, head_cons] },
  { convert congr_arg (λ n : ℤ, (-n:ℝ)) g.det_coe.symm using 1,
    simp only [f₁, mul_vec, dot_product, fin.sum_univ_two, matrix.det_fin_two, function.comp_app,
      subtype.coe_mk, lc_row0_extend_apply, cons_val_zero,
      linear_map.general_linear_group.coe_fn_general_linear_equiv,
      general_linear_group.to_linear_apply, coe_plane_conformal_matrix, mul_vec_lin_apply,
      cons_val_one, head_cons, map_apply, neg_mul, int.cast_sub, int.cast_mul, neg_sub],
    ring },
  { refl }
end

/-- This replaces `(g•z).re = a/c + *` in the standard theory with the following novel identity:

  `g • z = (a c + b d) / (c^2 + d^2) + (d z - c) / ((c^2 + d^2) (c z + d))`

  which does not need to be decomposed depending on whether `c = 0`. -/
lemma smul_eq_lc_row0_add {p : fin 2 → ℤ} (hp : is_coprime (p 0) (p 1)) (z : ℍ) {g : SL(2,ℤ)}
  (hg : ↑ₘg 1 = p) :
  ↑(g • z) = ((lc_row0 p ↑(g : SL(2, ℝ))) : ℂ) / (p 0 ^ 2 + p 1 ^ 2)
    + ((p 1 : ℂ) * z - p 0) / ((p 0 ^ 2 + p 1 ^ 2) * (p 0 * z + p 1)) :=
begin
  have nonZ1 : (p 0 : ℂ) ^ 2 + (p 1) ^ 2 ≠ 0 := by exact_mod_cast hp.sq_add_sq_ne_zero,
  have : (coe : ℤ → ℝ) ∘ p ≠ 0 := λ h, hp.ne_zero ((@int.cast_injective ℝ _ _ _).comp_left h),
  have nonZ2 : (p 0 : ℂ) * z + p 1 ≠ 0 := by simpa using linear_ne_zero _ z this,
  field_simp [nonZ1, nonZ2, denom_ne_zero, -upper_half_plane.denom, -denom_apply],
  rw (by simp : (p 1 : ℂ) * z - p 0 = ((p 1) * z - p 0) * ↑(det (↑g : matrix (fin 2) (fin 2) ℤ))),
  rw [←hg, det_fin_two],
  simp only [int.coe_cast_ring_hom, coe_matrix_coe, coe_fn_eq_coe,
    int.cast_mul, of_real_int_cast, map_apply, denom, int.cast_sub],
  ring,
end

lemma tendsto_abs_re_smul (z:ℍ) {p : fin 2 → ℤ} (hp : is_coprime (p 0) (p 1)) :
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
  exact_mod_cast (congr_arg complex.re (smul_eq_lc_row0_add hp z g.2))
end

end tendsto_lemmas

section fundamental_domain

local attribute [simp] coe_smul re_smul

/-- For `z : ℍ`, there is a `g : SL(2,ℤ)` maximizing `(g•z).im` -/
lemma exists_max_im (z : ℍ) :
  ∃ g : SL(2, ℤ), ∀ g' : SL(2, ℤ), (g' • z).im ≤ (g • z).im :=
begin
  classical,
  let s : set (fin 2 → ℤ) := {cd | is_coprime (cd 0) (cd 1)},
  have hs : s.nonempty := ⟨![1, 1], is_coprime_one_left⟩,
  obtain ⟨p, hp_coprime, hp⟩ :=
    filter.tendsto.exists_within_forall_le hs (tendsto_norm_sq_coprime_pair z),
  obtain ⟨g, -, hg⟩ := bottom_row_surj hp_coprime,
  refine ⟨g, λ g', _⟩,
  rw [im_smul_eq_div_norm_sq, im_smul_eq_div_norm_sq, div_le_div_left],
  { simpa [← hg] using hp (↑ₘg' 1) (bottom_row_coprime g') },
  { exact z.im_pos },
  { exact norm_sq_denom_pos g' z },
  { exact norm_sq_denom_pos g z },
end

/-- Given `z : ℍ` and a bottom row `(c,d)`, among the `g : SL(2,ℤ)` with this bottom row, minimize
  `|(g•z).re|`.  -/
lemma exists_row_one_eq_and_min_re (z:ℍ) {cd : fin 2 → ℤ} (hcd : is_coprime (cd 0) (cd 1)) :
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

/-- The matrix `T = [[1,1],[0,1]]` as an element of `SL(2,ℤ)` -/
def T : SL(2,ℤ) := ⟨![![1, 1], ![0, 1]], by norm_num [matrix.det_fin_two]⟩

/-- The matrix `T' (= T⁻¹) = [[1,-1],[0,1]]` as an element of `SL(2,ℤ)` -/
def T' : SL(2,ℤ) := ⟨![![1, -1], ![0, 1]], by norm_num [matrix.det_fin_two]⟩

/-- The matrix `S = [[0,-1],[1,0]]` as an element of `SL(2,ℤ)` -/
def S : SL(2,ℤ) := ⟨![![0, -1], ![1, 0]], by norm_num [matrix.det_fin_two]⟩

lemma coe_T : ↑ₘT = ![![1, 1], ![0, 1]] := rfl

lemma coe_T_inv : ↑ₘ(T⁻¹) = ![![1, -1], ![0, 1]] :=
begin
  rw [coe_inv, coe_T, adjugate_fin_two],
  simp,
end

/-- `coe_T_zpow` is the matrix `T` raised to the power `n : ℤ`. -/
lemma coe_T_zpow (n : ℤ) : ↑ₘ(T ^ n) = ![![1, n], ![0,1]] :=
begin
  induction n using int.induction_on with n h n h,
  { rw [zpow_zero, coe_one],  ext i j,
    fin_cases i; fin_cases j; simp, },
  { rw [zpow_add, zpow_one, coe_mul, h, coe_T], ext i j,
    fin_cases i; fin_cases j; simp [matrix.mul, dot_product, fin.sum_univ_succ]; ring, },
  { rw [zpow_sub, zpow_one, coe_mul, h, coe_T_inv], ext i j,
    fin_cases i; fin_cases j; simp [matrix.mul, dot_product, fin.sum_univ_succ]; ring, },
end

/- If `c = 1`, then `g = [[1,a],[0,1]] * S * [[1,d],[0,1]]`. -/
lemma g_eq_of_c_eq_one (g : SL(2,ℤ)) (hc : ↑ₘg 1 0 = 1) :
  g = T^(↑ₘg 0 0) * S * T^(↑ₘg 1 1) :=
begin
  ext i j, fin_cases i; fin_cases j,
  { simp [S, coe_T_zpow, matrix.mul_apply, fin.sum_univ_succ] },
  { have g_det : (1:ℤ) = ↑ₘg 0 0 * ↑ₘg 1 1 - 1 * ↑ₘg 0 1,
    { convert det_fin_two ↑ₘg using 1,
      { rw g.det_coe },
      rw hc,
      ring },
    simp [S, coe_T_zpow, matrix.mul_apply, fin.sum_univ_succ],
    rw g_det,
    simp, },
  { simpa [S, coe_T_zpow, matrix.mul_apply, fin.sum_univ_succ] using hc },
  { simp [S, coe_T_zpow, matrix.mul_apply, fin.sum_univ_succ], },
end

/-- If `c=1`, then `[[1,-a],[0,1]]*g = S * [[1,d],[0,1]]`. -/
lemma coe_T_zpow_mul_g_eq_S_mul_coe_T_zpow_of_c_eq_one (g : SL(2,ℤ))
  (hc : ↑ₘg 1 0 = 1) : T^(- ↑ₘg 0 0) * g = S * T^(↑ₘg 1 1) :=
begin
  rw g_eq_of_c_eq_one g hc,
  ext i,
  fin_cases i; fin_cases j,
  { simp [coe_T_zpow, S, matrix.mul_apply, fin.sum_univ_succ], },
  { simp [coe_T_zpow, S, matrix.mul_apply, fin.sum_univ_succ],
    ring },
  { simp [coe_T_zpow, S, matrix.mul_apply, fin.sum_univ_succ], },
  { simp [coe_T_zpow, S, matrix.mul_apply, fin.sum_univ_succ], },
end

/-- If `1 < |z|`, then `|S•z| < 1` -/
lemma norm_sq_S_smul_lt_one {z : ℍ} (h: 1 < norm_sq z) : norm_sq ↑(S • z) < 1 :=
by simpa [S] using (inv_lt_inv z.norm_sq_pos zero_lt_one).mpr h

/-- If `|z| < 1`, then applying `S` strictly decreases `im` -/
lemma im_lt_im_S_smul {z : ℍ} (h: norm_sq z < 1) : z.im < (S • z).im :=
begin
  have : z.im < z.im / norm_sq (z:ℂ),
  { have imz : 0 < z.im := im_pos z,
    apply (lt_div_iff z.norm_sq_pos).mpr,
    nlinarith },
  convert this,
  simp only [im_smul_eq_div_norm_sq],
  field_simp [norm_sq_denom_ne_zero, norm_sq_ne_zero, S]
end

/-- The standard (closed) fundamental domain of the action of `SL(2,ℤ)` on `ℍ` -/
def fundamental_domain : set ℍ :=
{z | 1 ≤ (z : ℂ).norm_sq ∧ |z.re| ≤ (1 : ℝ) / 2}

/-- The standard open fundamental domain of the action of `SL(2,ℤ)` on `ℍ` -/
def fundamental_domain_open : set ℍ :=
{z | 1 < (z : ℂ).norm_sq ∧ |z.re| < (1 : ℝ) / 2}

localized "notation `𝒟` := modular_group.fundamental_domain" in modular

localized "notation `𝒟ᵒ` := fundamental_domain_open" in modular

lemma three_lt_four_mul_im_sq_of_mem_fdo {z : ℍ} (h : z ∈ 𝒟ᵒ) : 3 < 4 * z.im^2 :=
begin
  have : 1 < z.re * z.re + z.im * z.im := by simpa [complex.norm_sq_apply] using h.1,
  have := h.2,
  cases abs_cases z.re;
  nlinarith,
end

/-- Any `z : ℍ` can be moved to `𝒟` by an element of `SL(2,ℤ)`  -/
lemma exists_smul_mem_fundamental_domain (z : ℍ) : ∃ g : SL(2,ℤ), g • z ∈ 𝒟 :=
begin
  -- obtain a g₀ which maximizes im (g • z),
  obtain ⟨g₀, hg₀⟩ := exists_max_im z,
  -- then among those, minimize re
  obtain ⟨g, hg, hg'⟩ := exists_row_one_eq_and_min_re z (bottom_row_coprime g₀),
  refine ⟨g, _⟩,
  -- `g` has same max im property as `g₀`
  have hg₀' : ∀ (g' : SL(2,ℤ)), (g' • z).im ≤ (g • z).im,
  { have hg'' : (g • z).im = (g₀ • z).im,
    { rw [im_smul_eq_div_norm_sq, im_smul_eq_div_norm_sq, denom_apply, denom_apply, hg] },
    simpa only [hg''] using hg₀ },
  split,
  { -- Claim: `1 ≤ ⇑norm_sq ↑(g • z)`. If not, then `S•g•z` has larger imaginary part
    contrapose! hg₀',
    refine ⟨S * g, _⟩,
    rw mul_action.mul_smul,
    exact im_lt_im_S_smul hg₀' },
  { show |(g • z).re| ≤ 1 / 2, -- if not, then either `T` or `T'` decrease |Re|.
    rw abs_le,
    split,
    { contrapose! hg',
      refine ⟨T * g, by simp [T, matrix.mul, matrix.dot_product, fin.sum_univ_succ], _⟩,
      rw mul_action.mul_smul,
      have : |(g • z).re + 1| < |(g • z).re| :=
        by cases abs_cases ((g • z).re + 1); cases abs_cases (g • z).re; linarith,
      convert this,
      simp [T] },
    { contrapose! hg',
      refine ⟨T' * g, by simp [T', matrix.mul, matrix.dot_product, fin.sum_univ_succ], _⟩,
      rw mul_action.mul_smul,
      have : |(g • z).re - 1| < |(g • z).re| :=
        by cases abs_cases ((g • z).re - 1); cases abs_cases (g • z).re; linarith,
      convert this,
      simp [T', sub_eq_add_neg] } }
end

/-- If `z∈𝒟ᵒ`, and `n:ℤ`, then `|z+n|>1`. -/
lemma move_by_T {z : ℍ} (hz : z ∈ 𝒟ᵒ) (n : ℤ) : 1 < norm_sq (((T^n) • z) : ℍ) :=
begin
  have hz₁ : 1 < z.re * z.re + z.im * z.im := hz.1,
  have hz₂ : |2 * z.re| ≤ 1,
  { rw [_root_.abs_mul, _root_.abs_two, ← le_div_iff' (@two_pos ℝ _ _)],
    exact hz.2.le, },
  have hzn := int.nneg_mul_add_sq_of_abs_le_one n (2*z.re) hz₂,
  suffices : 1 < (z.re + ↑n) * (z.re + ↑n) + z.im * z.im, { simpa [coe_T_zpow, norm_sq], },
  linarith,
end

section unique_representative

variables {z : ℍ} {g : SL(2,ℤ)} (hz : z ∈ 𝒟ᵒ) (hg : g • z ∈ 𝒟ᵒ)
include hz hg

lemma abs_c_le_one : |↑ₘg 1 0| ≤ 1 :=
begin
  let c' : ℤ := ↑ₘg 1 0,
  let c : ℝ := (c' : ℝ),
  suffices : 3 * c^2 < 4,
  { rw [← int.cast_pow, ← int.cast_three, ← int.cast_four, ← int.cast_mul, int.cast_lt] at this,
    replace this : c'^2 ≤ 1^2, { linarith, },
    rw ← _root_.abs_one,
    exact abs_le_abs_of_sq_le_sq this, },
  suffices : c ≠ 0 → 9 * c^4 < 16,
  { rcases eq_or_ne c 0 with hc | hc,
    { rw hc, norm_num, },
    { refine (abs_lt_of_sq_lt_sq' _ (by norm_num)).2,
      specialize this hc,
      linarith, }, },
  intros hc,
  replace hc : 0 < c^4, { rw pow_bit0_pos_iff; trivial, },
  have hgz : (c * z.im) ^ 4 / norm_sq (denom ↑g z) ^ 2 ≤ 1 :=
    div_le_one_of_le (pow_four_le_pow_two_of_pow_two_le
      (upper_half_plane.c_mul_im_sq_le_norm_sq_denom z g)) (sq_nonneg _),
  calc 9 * c^4 < c^4 * z.im^2 * (g • z).im^2 * 16 : _
           ... = c^4 * z.im^4 / (norm_sq (denom g z))^2 * 16 : _
           ... ≤ 16 : by { rw ← mul_pow, linarith, },
  { have := mul_lt_mul_of_pos_right (mul_lt_mul'' (three_lt_four_mul_im_sq_of_mem_fdo hg)
      (three_lt_four_mul_im_sq_of_mem_fdo hz) (by linarith) (by linarith)) hc,
    linarith, },
  { rw [im_smul_eq_div_norm_sq g z, div_pow],
    ring, },
end

/-- If both `z` and `g•z` are in `𝒟ᵒ`, then `c` can't be `1`. -/
lemma c_ne_one : ↑ₘg 1 0 ≠ 1 :=
begin
  by_contra hc,
  let z₁ := T^(↑ₘg 1 1) • z,
  let w₁ := T^(- ↑ₘg 0 0) • (g • z),
  have w₁_norm : 1 < norm_sq w₁ := move_by_T hg (- ↑ₘg 0 0),
  have z₁_norm : 1 < norm_sq z₁ := move_by_T hz (↑ₘg 1 1),
  have w₁_S_z₁ : w₁ = S • z₁,
  { dsimp only [w₁, z₁],
    rw [← mul_action.mul_smul, coe_T_zpow_mul_g_eq_S_mul_coe_T_zpow_of_c_eq_one g hc,
      ← mul_action.mul_smul], },
  have := norm_sq_S_smul_lt_one z₁_norm,
  rw ← w₁_S_z₁ at this,
  linarith,
end

/-- Second Main Fundamental Domain Lemma: If both `z` and `g•z` are in the open domain `𝒟ᵒ`, where
  `z:ℍ` and `g:SL(2,ℤ)`, then `z = g • z`. -/
lemma eq_smul_self_of_mem_fdo_mem_fdo : z = g • z :=
begin
/-  The argument overview is: either `c=0`, in which case the action is translation, which must be
  by `0`, OR
  `c=±1`, which gives a contradiction from considering `im z`, `im(g•z)`, and `norm_sq(T^* z)`. -/
  have g_det : matrix.det ↑ₘg = (↑ₘg 0 0) * (↑ₘg 1 1) - (↑ₘg 1 0) * (↑ₘg 0 1),
  { convert det_fin_two ↑ₘg using 1,
    ring, },
  by_cases (↑ₘg 1 0 = 0),
  { -- case `c=0`
    have := g_det,
    rw h at this,
    simp only [det_coe, zero_mul, sub_zero] at this,
    have := int.eq_one_or_neg_one_of_mul_eq_one' (this.symm),
    have gzIs : ∀ (gg : SL(2,ℤ)), ↑ₘgg 1 0 = 0 → ↑ₘgg 0 0 = 1 → ↑ₘgg 1 1 = 1 →
      ↑(gg • z : ℍ) = (z : ℂ) + ↑ₘgg 0 1,
    { intros gg h₀ h₁ h₂,
      simp [h₀, h₁, h₂], },
    have gIsId : ∀ (gg : SL(2,ℤ)), gg • z ∈ 𝒟ᵒ → ↑ₘgg 1 0 = 0 → ↑ₘgg 0 0 = 1 → ↑ₘgg 1 1 = 1
      → gg = 1,
    { intros gg hh h₀ h₁ h₂,
      ext i,
      fin_cases i; fin_cases j,
      simp only [h₁, coe_one, one_apply_eq],
      { simp only [nat.one_ne_zero, coe_one, fin.zero_eq_one_iff, ne.def, not_false_iff,
          one_apply_ne],
        by_contra hhh,
        have reZ : |z.re| < 1/2,
        { exact_mod_cast hz.2, },
        have reGz : |((gg • z):ℍ ).re| < 1/2,
        { exact_mod_cast hh.2, },
        have reZpN : |z.re + ↑ₘgg 0 1| < 1/2,
        { convert reGz using 2,
          rw (by simp : z.re + ↑ₘgg 0 1 = ((z:ℂ )+ ↑ₘgg 0 1).re),
          apply congr_arg complex.re,
          exact_mod_cast (gzIs gg h₀ h₁ h₂).symm, },
        have move_by_large : ∀ x y : ℝ, |x| < 1/2 → |x+y|<1/2 → 1 ≤ |y| → false := λ x y hx hxy hy,
          by cases abs_cases x; cases abs_cases y; cases abs_cases (x+y); linarith,
        refine move_by_large _ _ reZ reZpN _,
        exact_mod_cast  int.one_le_abs hhh, },
      simp only [h₀, nat.one_ne_zero, coe_one, fin.one_eq_zero_iff, ne.def, not_false_iff,
        one_apply_ne],
      simp only [h₂, coe_one, one_apply_eq], },
    have zIsGz : ∀ (gg : SL(2,ℤ)), ↑ₘgg 1 0 = 0 → ↑ₘgg 0 0 = 1 → ↑ₘgg 1 1 = 1 → gg • z ∈ 𝒟ᵒ
      → z = gg • z,
    { intros gg h₀ h₁ h₂ hh,
      have := gIsId gg hh h₀ h₁ h₂,
      rw this,
      simp, },
    cases this,
    { -- case `a = d = 1`
      exact zIsGz g h this_1.1 this_1.2 hg, },
    { -- case `a = d = -1`
      rw ← neg_smul,
      apply zIsGz; simp,
      exact_mod_cast h,
      simp only [this_1, neg_neg],
      simp only [this_1, neg_neg],
      exact hg, }, },
  { -- case `c ≠ 0`
    exfalso,
    -- argue first that `c=± 1`
    -- then show this is impossible
    rcases (int.abs_le_one_iff.mp $ abs_c_le_one hz hg) with hc | hc | hc,
    { contradiction, },
    { -- `c = 1`
      exact c_ne_one hz hg  hc, },
    { -- `c = -1`
      have neg_c_one : ↑ₘ(-g) 1 0 = 1,
      { have := eq_neg_of_eq_neg hc,
        simp [hc], },
      have neg_g_𝒟 : (-g) • z ∈ 𝒟ᵒ,
      { convert hg using 1,
        simp, },
      exact c_ne_one hz neg_g_𝒟 neg_c_one, }, },
end

end unique_representative

end fundamental_domain

end modular_group
