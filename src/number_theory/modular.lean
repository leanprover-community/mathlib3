/-
Copyright (c) 2021 Alex Kontorovich and Heather Macbeth and Marc Masdeu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth, Marc Masdeu
-/
import analysis.complex.upper_half_plane

/-!
# The action of the modular group SL(2, ℤ) on the upper half-plane

  We define the action of `SL(2,ℤ)` on `ℍ` (via restriction of the `SL(2,ℝ)` action in
  `analysis.complex.upper_half_plane`). We then define the standard fundamental domain
  (`modular_group.fundamental_domain`, `𝒟`) for this action and show
  (`modular_group.exists_smul_mem_fundamental_domain`) that any point in `ℍ` can be
  moved inside `𝒟`.

  Standard proofs make use of the identity

  `g • z = a / c - 1 / (c (cz + d))`

  for `g = [[a, b], [c, d]]` in `SL(2)`, but this requires separate handling of whether `c = 0`.
  Instead, our proof makes use of the following perhaps novel identity (see
  `modular_group.smul_eq_acbd_add`):

  `g • z = (a c + b d) / (c^2 + d^2) + (d z - c) / ((c^2 + d^2) (c z + d))`

  where there is no issue of division by zero.

  Another feature is that we delay until the very end the consideration of special matrices
  `T=[[1,1],[0,1]]` (see `modular_group.T`) and `S=[[0,-1],[1,0]]` (see `modular_group.S`), by
  instead using abstract theory on the properness of certain maps (phrased in terms of the filters
  `filter.cocompact`, `filter.cofinite`, etc) to deduce existence theorems, first to prove the
  existence of `g` maximizing `(g•z).im` (see `modular_group.exists_g_with_max_im`), and then among
  those, to minimize `|(g•z).re|` (see `modular_group.exists_g_with_given_cd_and_min_re`).
-/

open complex matrix matrix.special_linear_group upper_half_plane
noncomputable theory

local notation `SL(` n `, ` R `)`:= special_linear_group (fin n) R
local prefix `↑ₘ`:1024 := @coe _ (matrix (fin 2) (fin 2) ℤ) _


open_locale upper_half_plane

local attribute [instance] fintype.card_fin_even

namespace modular_group

section upper_half_plane_action

/-- The action of `SL(2, ℤ)` on the upper half-plane, as a restriction of the `SL(2, ℝ)`-action. -/
instance : mul_action SL(2, ℤ) ℍ :=
mul_action.comp_hom ℍ (map (int.cast_ring_hom ℝ))

@[simp] lemma coe_smul (g : SL(2, ℤ)) (z : ℍ) : ↑(g • z) = num g z / denom g z := rfl
@[simp] lemma re_smul (g : SL(2, ℤ)) (z : ℍ) : (g • z).re = (num g z / denom g z).re := rfl
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
lemma bottom_row_coprime (g : SL(2, ℤ)) : is_coprime (↑ₘg 1 0) (↑ₘg 1 1) :=
begin
  use [- g 0 1, g 0 0],
  have := det_fin_two g,
  have := g.det_coe,
  simp only [coe_fn_eq_coe] at *,
  linarith
end

/-- Every pair `![c, d]` of coprime integers is the "bottom_row" of some element `g=[[*,*],[c,d]]`
of `SL(2,ℤ)`. -/
lemma bottom_row_surj :
  set.surj_on (λ g : SL(2, ℤ), ↑ₘg 1) set.univ {cd | is_coprime (cd 0) (cd 1)} :=
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

/-- The function `(c,d) → |cz+d|^2` is proper, that is, preimages of bounded-above sets are finite.
-/
lemma tendsto_norm_sq_coprime_pair (z : ℍ) :
  filter.tendsto (λ p : fin 2 → ℤ, ((p 0 : ℂ) * z + p 1).norm_sq)
  cofinite at_top :=
begin
  let f : (fin 2 → ℝ) →ₗ[ℝ] ℂ := (linear_map.proj 0 : (fin 2 → ℝ) →ₗ[ℝ] ℝ).smul_right (z:ℂ)
    + (linear_map.proj 1 : (fin 2 → ℝ) →ₗ[ℝ] ℝ).smul_right 1,
  have : (λ (p : fin 2 → ℤ), norm_sq ((p 0 : ℂ) * ↑z + ↑(p 1)))
    = norm_sq ∘ f ∘ (λ p : fin 2 → ℤ, (coe : ℤ → ℝ) ∘ p),
  { ext,
    simp only [linear_map.coe_proj, mul_one, real_smul, function.comp_app, of_real_int_cast,
      linear_map.coe_smul_right, linear_map.add_apply] },
  rw this,
  have hf : f.ker = ⊥,
  { let g : ℂ →ₗ[ℝ] (fin 2 → ℝ) :=
      linear_map.pi ![im_lm, im_lm.comp ((z:ℂ) • (conj_ae  : ℂ →ₗ[ℝ] ℂ))],
    suffices : ((z:ℂ).im⁻¹ • g).comp f = linear_map.id,
    { exact linear_map.ker_eq_bot_of_inverse this },
    apply linear_map.ext,
    intros c,
    have hz : 0 < (z:ℂ).im := z.2,
    have : (z:ℂ).im ≠ 0 := hz.ne',
    ext i,
    fin_cases i,
    { field_simp },
    dsimp [g],
    field_simp,
    ring },
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
def acbd (p : fin 2 → ℤ) : (matrix (fin 2) (fin 2) ℝ) →ₗ[ℝ] ℝ :=
(p 0 • linear_map.proj 0 + p 1 • linear_map.proj 1 : (fin 2 → ℝ) →ₗ[ℝ] ℝ).comp (linear_map.proj 0)

@[simp] lemma acbd_apply (p : fin 2 → ℤ) (g : matrix (fin 2) (fin 2) ℝ) :
  acbd p g = p 0 * g 0 0 + p 1 * g 0 1 :=
by simp [acbd]


/-- Linear map sending the matrix [a b; c d] to `(ac₀+bd₀ , ad₀ - bc₀, c, d)`, for some fixed
  `(c₀, d₀)`.
-/
def acbd_extend (cd : fin 2 → ℤ) : (matrix (fin 2) (fin 2) ℝ) →ₗ[ℝ] ((fin 2 → ℝ) × (fin 2 → ℝ)) :=
((matrix.mul_vec_lin ![![(cd 0:ℝ), cd 1], ![cd 1,-cd 0]]).comp
  (linear_map.proj 0 : (matrix (fin 2) (fin 2) ℝ) →ₗ[ℝ] _)).prod
  (linear_map.proj 1)

lemma acbd_extend_ker_eq_bot {cd : fin 2 → ℤ} (hcd : is_coprime (cd 0) (cd 1)) :
  (acbd_extend cd).ker = ⊥ :=
begin
  rw linear_map.ker_eq_bot,
  have nonZ : ((cd 0)^2+(cd 1)^2:ℝ) ≠ 0,
  { norm_cast,
    exact hcd.sq_add_sq_ne_zero },
  let F : matrix (fin 2) (fin 2) ℝ := ((cd 0)^2+(cd 1)^2:ℝ)⁻¹ • ![![cd 0, cd 1], ![cd 1, -cd 0]],
  let f₁ : (fin 2 → ℝ) → (fin 2 → ℝ) := F.mul_vec_lin,
  let f : (fin 2 → ℝ) × (fin 2 → ℝ) → matrix (fin 2) (fin 2) ℝ := λ ⟨x , cd⟩, ![f₁ x, cd],
  have : function.left_inverse f (acbd_extend cd),
  { intros g,
    simp [acbd_extend, f, f₁, F, vec_head, vec_tail], -- squeeze_simp times out!
    ext i j,
    fin_cases i,
    { fin_cases j,
      { change (↑(cd 0) ^ 2 + ↑(cd 1) ^ 2)⁻¹ * ↑(cd 0)
          * (↑(cd 0) * g 0 0 + ↑(cd 1) * g 0 1)
        + (↑(cd 0) ^ 2 + ↑(cd 1) ^ 2)⁻¹ * ↑(cd 1)
          * (↑(cd 1) * g 0 0 + -(↑(cd 0) * g 0 1)) = _,
        field_simp,
        ring },
      { change (↑(cd 0) ^ 2 + ↑(cd 1) ^ 2)⁻¹ * ↑(cd 1)
          * (↑(cd 0) * g 0 0 + ↑(cd 1) * g 0 1)
        + -((↑(cd 0) ^ 2 + ↑(cd 1) ^ 2)⁻¹ * ↑(cd 0)
          * (↑(cd 1) * g 0 0 + -(↑(cd 0) * g 0 1))) = _,
        field_simp,
        ring } },
    { fin_cases j; refl } },
  exact this.injective,
end

/-- The map `acbd` is proper, that is, preimages of cocompact sets are finite in `[[*,*],[c,d]]`.-/
theorem tendsto_acbd {cd : fin 2 → ℤ} (hcd : is_coprime (cd 0) (cd 1)) :
  tendsto (λ g : {g : SL(2, ℤ) // g 1 = cd}, acbd cd ↑(↑g : SL(2, ℝ))) cofinite (cocompact ℝ) :=
begin
  let mB : ℝ → ((fin 2 → ℝ) × (fin 2 → ℝ)) := λ t, (![t, 1], coe ∘ cd),
  have hmB : continuous mB,
  { refine continuous.prod_mk (continuous_pi _) continuous_const,
    intros i,
    fin_cases i,
    { exact continuous_id },
    { simpa using continuous_const } },
  convert filter.tendsto.of_tendsto_comp _ (comap_cocompact hmB),
  let f₁ : SL(2, ℤ) → matrix (fin 2) (fin 2) ℝ :=
    λ g, matrix.map (↑g : matrix _ _ ℤ) (coe : ℤ → ℝ),
  have cocompact_ℝ_to_cofinite_ℤ_matrix :
    tendsto (λ m : matrix (fin 2) (fin 2) ℤ, matrix.map m (coe : ℤ → ℝ)) cofinite (cocompact _),
  { convert tendsto.pi_map_Coprod (λ i, tendsto.pi_map_Coprod (λ j, int.tendsto_coe_cofinite)),
    { simp [Coprod_cofinite] },
    { simp only [Coprod_cocompact],
      refl } },
  have hf₁ : tendsto f₁ cofinite (cocompact _) :=
    cocompact_ℝ_to_cofinite_ℤ_matrix.comp subtype.coe_injective.tendsto_cofinite,
  have hf₂ := (linear_equiv.closed_embedding_of_injective
    (acbd_extend_ker_eq_bot hcd)).tendsto_cocompact,
  convert hf₂.comp (hf₁.comp subtype.coe_injective.tendsto_cofinite) using 1,
  funext g,
  obtain ⟨g, hg⟩ := g,
  simp [mB, f₁, acbd_extend], -- squeeze_simp fails here for some reason
  split,
  { ext i,
    fin_cases i,
    { simp [vec_head, vec_tail] },
    { have : (1:ℝ) = ↑(g 1 1) * ↑(g 0 0) + -(↑(g 1 0) * ↑(g 0 1)),
      { norm_cast,
        simp only [← g.det_coe, det_fin_two, coe_fn_eq_coe],
        ring },
      simpa [← hg, vec_head, vec_tail] using this } },
  { rw ← hg,
    ext i,
    fin_cases i; refl }
end

/-- This replaces `(g•z).re = a/c + *` in the standard theory with the following novel identity:

  `g • z = (a c + b d) / (c^2 + d^2) + (d z - c) / ((c^2 + d^2) (c z + d))`

  which does not
  need to be decomposed depending on whether `c = 0`. -/
lemma smul_eq_acbd_add {p : fin 2 → ℤ} (hp : is_coprime (p 0) (p 1)) (z : ℍ) {g : SL(2,ℤ)}
  (hg : ↑ₘg 1 = p) :
  ↑(g • z) = ((acbd p ↑(g : SL(2, ℝ))) : ℂ) / (p 0 ^ 2 + p 1 ^ 2)
    + ((p 1 : ℂ) * z - p 0) / ((p 0 ^ 2 + p 1 ^ 2) * (p 0 * z + p 1)) :=
begin
  have nonZ1 : (p 0 : ℂ) ^ 2 + (p 1) ^ 2 ≠ 0 := by exact_mod_cast hp.sq_add_sq_ne_zero,
  have : (coe : ℤ → ℝ) ∘ p ≠ 0 := λ h, (hp.ne_zero ∘ (@int.cast_injective ℝ _ _ _).comp_left) h,
  have nonZ2 : (p 0 : ℂ) * z + p 1 ≠ 0 := by simpa using linear_ne_zero _ z this,
  field_simp [nonZ1, nonZ2, denom_ne_zero, -upper_half_plane.denom, -denom_apply],
  rw (by simp : (p 1 : ℂ) * z - p 0 = ((p 1) * z - p 0) * ↑(det (↑g : matrix (fin 2) (fin 2) ℤ))),
  rw [←hg, det_fin_two],
  simp only [int.coe_cast_ring_hom, coe_matrix_coe, coe_fn_eq_coe,
    int.cast_mul, of_real_int_cast, map_apply, denom, int.cast_sub],
  ring,
end

lemma tendsto_abs_re_smul (z:ℍ) {p : fin 2 → ℤ} (hp : is_coprime (p 0) (p 1)) :
  tendsto (λ g : {g : SL(2, ℤ) // g 1 = p}, |((g : SL(2, ℤ)) • z).re|)
    cofinite at_top :=
begin
  suffices : tendsto (λ g : (λ g : SL(2, ℤ), g 1) ⁻¹' {p}, (((g : SL(2, ℤ)) • z).re))
    cofinite (cocompact ℝ),
  { exact tendsto_norm_cocompact_at_top.comp this },
  have : ((p 0 : ℝ) ^ 2 + p 1 ^ 2)⁻¹ ≠ 0,
  { apply inv_ne_zero,
    exact_mod_cast hp.sq_add_sq_ne_zero },
  let f := homeomorph.mul_right₀ _ this,
  let ff := homeomorph.add_right (((p 1:ℂ)* z - p 0) / ((p 0 ^ 2 + p 1 ^ 2) * (p 0 * z + p 1))).re,
  convert ((f.trans ff).closed_embedding.tendsto_cocompact).comp (tendsto_acbd hp),
  ext g,
  change ((g : SL(2, ℤ)) • z).re = (acbd p ↑(↑g : SL(2, ℝ))) / (p 0 ^ 2 + p 1 ^ 2)
  + (((p 1:ℂ )* z - p 0) / ((p 0 ^ 2 + p 1 ^ 2) * (p 0 * z + p 1))).re,
  exact_mod_cast (congr_arg complex.re (smul_eq_acbd_add hp z g.2))
end

end tendsto_lemmas

section fundamental_domain

/-- For `z : ℍ`, there is a `g : SL(2,ℤ)` maximizing `(g•z).im` -/
lemma exists_g_with_max_im (z : ℍ) :
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
  { simpa [← hg] using hp (g' 1) (bottom_row_coprime g') },
  { exact z.im_pos },
  { exact norm_sq_denom_pos g' z },
  { exact norm_sq_denom_pos g z },
end

/-- Given `z : ℍ` and a bottom row `(c,d)`, among the `g : SL(2,ℤ)` with this bottom row, minimize
  `|(g•z).re|`.  -/
lemma exists_g_with_given_cd_and_min_re (z:ℍ) {cd : fin 2 → ℤ} (hcd : is_coprime (cd 0) (cd 1)) :
  ∃ g : SL(2,ℤ), ↑ₘg 1 = cd ∧ (∀ g' : SL(2,ℤ), ↑ₘg 1 = ↑ₘg' 1 →
  |(g • z).re| ≤ |(g' • z).re|) :=
begin
  haveI : nonempty {g : SL(2, ℤ) // g 1 = cd} := let ⟨x, hx⟩ := bottom_row_surj hcd in ⟨⟨x, hx.2⟩⟩,
  obtain ⟨g, hg⟩ := filter.tendsto.exists_forall_le (tendsto_abs_re_smul z hcd),
  refine ⟨g, g.2, _⟩,
  { intros g1 hg1,
    have : g1 ∈ ((λ g : SL(2, ℤ), g 1) ⁻¹' {cd}),
    { rw [set.mem_preimage, set.mem_singleton_iff],
      exact eq.trans hg1.symm (set.mem_singleton_iff.mp (set.mem_preimage.mp g.2)) },
    exact hg ⟨g1, this⟩ },
end

/-- The matrix `T = [[1,1],[0,1]]` as an element of `SL(2,ℤ)` -/
def T : SL(2,ℤ) := ⟨![![1, 1], ![0, 1]], by simp [matrix.det_fin_two]⟩

/-- The matrix `T' (= T⁻¹) = [[1,-1],[0,1]]` as an element of `SL(2,ℤ)` -/
def T' : SL(2,ℤ) := ⟨![![1, -1], ![0, 1]], by simp [matrix.det_fin_two]⟩

/-- The matrix `S = [[0,-1],[1,0]]` as an element of `SL(2,ℤ)` -/
def S : SL(2,ℤ) := ⟨![![0, -1], ![1, 0]], by simp [matrix.det_fin_two]⟩

/-- The standard (closed) fundamental domain of the action of `SL(2,ℤ)` on `ℍ` -/
def fundamental_domain : set ℍ :=
{z | 1 ≤ (complex.norm_sq z) ∧ |z.re| ≤ (1 : ℝ) / 2}

notation `𝒟` := fundamental_domain

/-- If `|z|<1`, then applying `S` strictly decreases `im` -/
lemma im_lt_im_S {z : ℍ} (h: norm_sq z < 1) : z.im < (S • z).im :=
begin
  have : z.im < z.im / norm_sq (z:ℂ),
  { have imz : 0 < z.im := im_pos z,
    apply (lt_div_iff z.norm_sq_pos).mpr,
    nlinarith },
  convert this,
  simp only [im_smul_eq_div_norm_sq],
  field_simp [norm_sq_denom_ne_zero, norm_sq_ne_zero, S]
end

/-- Any `z : ℍ` can be moved to `𝒟` by an element of `SL(2,ℤ)`  -/
lemma exists_smul_mem_fundamental_domain (z : ℍ) : ∃ g : SL(2,ℤ), g • z ∈ 𝒟 :=
begin
  -- obtain a g₀ which maximizes im (g • z),
  obtain ⟨g₀, hg₀⟩ := exists_g_with_max_im z,
  -- then among those, minimize re
  obtain ⟨g, hg, hg'⟩ := exists_g_with_given_cd_and_min_re z (bottom_row_coprime g₀),
  refine ⟨g, _⟩,
  -- `g` has same max im property as `g₀`
  have hg₀' : ∀ (g' : SL(2,ℤ)), (g' • z).im ≤ (g • z).im,
  { have hg'' : (g • z).im = (g₀ • z).im,
    { rw [im_smul_eq_div_norm_sq, im_smul_eq_div_norm_sq, denom_apply, denom_apply, hg] },
    simpa only [hg''] using hg₀ },
  split,
  { -- Claim: `|g•z| > 1`. If not, then `S•g•z` has larger imaginary part
    contrapose! hg₀',
    refine ⟨S * g, _⟩,
    rw mul_action.mul_smul,
    exact im_lt_im_S hg₀' },
  { -- Claim: `|Re(g•z)| < 1/2`; if not, then either `T` or `T'` decrease |Re|.
    rw abs_le,
    split,
    { contrapose! hg',
      refine ⟨T * g, _, _⟩,
      { -- goal: `bottom_row (T * g) = bottom_row g`.
        simp [T, vec_head, vec_tail], },
      rw mul_action.mul_smul,
      change (g • z).re < _ at hg',
      have : |(g • z).re + 1| < |(g • z).re| :=
        by cases abs_cases ((g • z).re + 1); cases abs_cases (g • z).re; linarith,
      convert this,
      -- goal: `(T • g • z).re = (g • z).re + 1`.
      simp [T] },
    { contrapose! hg',
      refine ⟨T' * g, _, _⟩,
      { -- goal: `bottom_row (T' * g) = bottom_row g`.
        simp [T', vec_head, vec_tail] },
      rw mul_action.mul_smul,
      change _ < (g • z).re at hg',
      have : |(g • z).re - 1| < |(g • z).re| :=
        by cases abs_cases ((g • z).re - 1); cases abs_cases (g • z).re; linarith,
      convert this,
      -- goal: `(T' • g • z).re = (g • z).re - 1`.
      simp [T', sub_eq_add_neg] } }
end

end fundamental_domain

end modular_group
