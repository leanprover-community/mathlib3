/-
Copyright (c) 2021 Alex Kontorovich and Heather Macbeth and Marc Masdeu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth, Marc Masdeu
-/
import analysis.complex.upper_half_plane analysis.special_functions.pow

/-!
# The action of the modular group SL(2, ℤ) on the upper half-plane

  We define the action of `SL(2,ℤ)` on `ℍ` (via restriction of the `SL(2,ℝ)` action in
  `analysis.complex.upper_half_plane`). We then define the standard fundamental domain
  (`modular_group.fundamental_domain`, `𝒟`) for this action and show
  (`modular_group.exists_smul_mem_fundamental_domain`) that any point in `ℍ` can be
  moved inside `𝒟`.

  Standard proofs make use of the identity

  `g•z = a/c - 1/(c(cz+d))`

  for `g=[[a,b],[c,d]]` in `SL(2)`, but this requires separate handling of whether `c = 0`.
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

local notation `|` x `|` := _root_.abs x
local notation `SL(` n `, ` R `)`:= special_linear_group (fin n) R

open_locale upper_half_plane

local attribute [instance] fintype.card_fin_even

namespace modular_group

section upper_half_plane_action

/-- The action of `SL(2, ℤ)` on the upper half-plane, as a restriction of the `SL(2, ℝ)`-action. -/
instance : mul_action SL(2, ℤ) ℍ :=
mul_action.comp_hom ℍ (map (int.cast_ring_hom ℝ))

@[simp] lemma coe_smul (g : SL(2, ℤ)) (z : ℍ) : ↑(g • z) = top g z / bottom g z := rfl
@[simp] lemma re_smul (g : SL(2, ℤ)) (z : ℍ) : (g • z).re = (top g z / bottom g z).re := rfl
@[simp] lemma smul_coe (g : SL(2, ℤ)) (z : ℍ) : (g : SL(2,ℝ)) • z = g • z := rfl

@[simp] lemma neg_smul (g : SL(2, ℤ)) (z : ℍ) : -g • z = g • z :=
show ↑(-g) • _ = _, by simp [neg_smul g z]

lemma im_smul (g : SL(2, ℤ)) (z : ℍ) : (g • z).im = (top g z / bottom g z).im := rfl

lemma im_smul_eq_div_norm_sq (g : SL(2, ℤ)) (z : ℍ) :
  (g • z).im = z.im / (complex.norm_sq (bottom g z)) :=
im_smul_eq_div_norm_sq g z

end upper_half_plane_action

section bottom_row

/-- The `bottom_row` of `g=[[*,*],[c,d]]` in `SL(2,ℤ)` is the `coprime_pair` `(c,d)`. -/
def bottom_row (g : SL(2, ℤ)) : coprime_pair :=
coprime_pair.mk
  (@coe _ (matrix (fin 2) (fin 2) ℤ) _ g 1 0, @coe _ (matrix (fin 2) (fin 2) ℤ) _ g 1 1)
  begin
    use [- g 0 1, g 0 0],
    have := det_fin_two g,
    have := g.det_coe,
    simp only [coe_fn_eq_coe] at *,
    linarith
  end

lemma bottom_row_surj : function.surjective bottom_row :=
begin
  intros cd,
  obtain ⟨b₀, a, gcd_eqn⟩ := cd.is_coprime,
  let A := ![![a, -b₀], ![cd.c, cd.d]],
  have det_A_1 : det A = 1,
  { convert gcd_eqn,
    simp [A, det_fin_two, (by ring : a * cd.d + b₀ * cd.c = b₀ * cd.c + a * cd.d)] },
  use ⟨A, det_A_1⟩,
  ext; simp [A, bottom_row]
end

lemma bottom_eq_mul_bottom_row_add_bottom_row (g : SL(2, ℤ)) (z : ℍ) :
  bottom g z = (bottom_row g).c * z + (bottom_row g).d :=
by simp [bottom_row]

lemma bottom_eq_of_bottom_row_eq {g h : SL(2,ℤ)} (z : ℍ) (bot_eq : bottom_row g = bottom_row h) :
  bottom g z = bottom h z :=
by simp [bottom_eq_mul_bottom_row_add_bottom_row, bot_eq]

end bottom_row

section tendsto_lemmas

open filter continuous_linear_map

/-- The function `(c,d) → |cz+d|^2` is proper, that is, preimages of bounded-above sets are finite.
  The proof would work for `ℤ×ℤ` but is pharsed for `coprime_pair` since this is needed later in
  the main argument.
 -/
lemma tendsto_norm_sq_coprime_pair (z : ℍ) :
  filter.tendsto (λ p : coprime_pair, ((p.c : ℂ) * z + p.d).norm_sq)
  cofinite at_top :=
begin
  let f : ℝ × ℝ →ₗ[ℝ] ℂ := (linear_map.fst ℝ ℝ ℝ).smul_right (z:ℂ)
    + (linear_map.snd ℝ ℝ ℝ).smul_right 1,
  have hf : f.ker = ⊥,
  { let g : ℂ →ₗ[ℝ] ℝ × ℝ := im_lm.prod (im_lm.comp (((z:ℂ) • conj_ae ))),
    suffices : ((z:ℂ).im⁻¹ • g).comp f = linear_map.id,
    { exact linear_map.ker_eq_bot_of_inverse this },
    apply linear_map.ext,
    rintros ⟨c₁, c₂⟩,
    have hz : 0 < (z:ℂ).im := z.2,
    have : (z:ℂ).im ≠ 0 := hz.ne.symm,
    field_simp,
    ring },
  have h₁ := (linear_equiv.closed_embedding_of_injective hf).tendsto_cocompact,
  have h₂ : tendsto (λ p : ℤ × ℤ, ((p.1 : ℝ), (p.2 : ℝ))) cofinite (cocompact _),
  { convert int.tendsto_coe_cofinite.prod_map_coprod int.tendsto_coe_cofinite;
    simp [coprod_cocompact, coprod_cofinite] },
  convert tendsto_norm_sq_cocompact_at_top.comp
    (h₁.comp (h₂.comp coprime_pair.coe_injective.tendsto_cofinite)),
  ext,
  simp [f],
end


/-- Given `coprime_pair` `p=(c,d)`, the matrix `[[a,b],[*,*]]` is sent to `a*c+b*d`.
  This is the linear map version of this operation.
-/
def acbd (p : coprime_pair) : (matrix (fin 2) (fin 2) ℝ) →ₗ[ℝ] ℝ :=
(p.c • linear_map.proj 0 + p.d • linear_map.proj 1 : (fin 2 → ℝ) →ₗ[ℝ] ℝ).comp (linear_map.proj 0)

@[simp] lemma acbd_apply (p : coprime_pair) (g : matrix (fin 2) (fin 2) ℝ) :
  acbd p g = p.c * g 0 0 + p.d * g 0 1 :=
by simp [acbd]


/-- Linear map sending the matrix [a b; c d] to `(ac₀+bd₀ , ad₀ - bc₀, c, d)`, for some fixed
  `(c₀, d₀)`.
-/
def acbd_extend (cd : coprime_pair) : (matrix (fin 2) (fin 2) ℝ) →ₗ[ℝ] ((fin 2 → ℝ) × (fin 2 → ℝ))
:= ((matrix.mul_vec_lin ![![(cd.c:ℝ), cd.d], ![cd.d,-cd.c]]).comp
  (linear_map.proj 0 : (matrix (fin 2) (fin 2) ℝ) →ₗ[ℝ] _)).prod
  (linear_map.proj 1)

lemma acbd_extend_ker_eq_bot (cd : coprime_pair) : (acbd_extend cd).ker = ⊥ :=
begin
  rw linear_map.ker_eq_bot,
  have nonZ : ((cd.c)^2+(cd.d)^2:ℝ) ≠ 0,
  { norm_cast,
    exact cd.sq_add_sq_ne_zero },
  let F : matrix (fin 2) (fin 2) ℝ := ((cd.c)^2+(cd.d)^2:ℝ)⁻¹ • ![![cd.c, cd.d], ![cd.d, -cd.c]],
  let f₁ : (fin 2 → ℝ) → (fin 2 → ℝ) := F.mul_vec_lin,
  let f : (fin 2 → ℝ) × (fin 2 → ℝ) → matrix (fin 2) (fin 2) ℝ := λ ⟨x , cd⟩, ![f₁ x, cd],
  have : function.left_inverse f (acbd_extend cd),
  { intros g,
    simp [acbd_extend, f, f₁, F, vec_head, vec_tail], -- squeeze_simp times out!
    ext i j,
    fin_cases i,
    { fin_cases j,
      { change (↑(cd.c) ^ 2 + ↑(cd.d) ^ 2)⁻¹ * ↑(cd.c) * (↑(cd.c) * g 0 0 + ↑(cd.d) * g 0 1) +
          (↑(cd.c) ^ 2 + ↑(cd.d) ^ 2)⁻¹ * ↑(cd.d) * (↑(cd.d) * g 0 0 + -(↑(cd.c) * g 0 1)) = _,
        field_simp,
        ring },
      { change (↑(cd.c) ^ 2 + ↑(cd.d) ^ 2)⁻¹ * ↑(cd.d) * (↑(cd.c) * g 0 0 + ↑(cd.d) * g 0 1) +
          -((↑(cd.c) ^ 2 + ↑(cd.d) ^ 2)⁻¹ * ↑(cd.c) * (↑(cd.d) * g 0 0 + -(↑(cd.c) * g 0 1))) = _,
        field_simp,
        ring } },
    { fin_cases j; refl } },
  exact this.injective,
end

/-- The map `acbd` is proper, that is, preimages of cocompact sets are finite in `[[*,*],[c,d]]`.-/
theorem tendsto_acbd (cd : coprime_pair) :
  tendsto (λ g : bottom_row ⁻¹' {cd}, acbd cd ↑(↑g : SL(2, ℝ))) cofinite (cocompact ℝ) :=
begin
  let mB : ℝ → ((fin 2 → ℝ) × (fin 2 → ℝ)) := λ t, (![t, 1], ![(cd.c:ℝ), cd.d]),
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
    (acbd_extend_ker_eq_bot cd)).tendsto_cocompact,
  convert hf₂.comp (hf₁.comp subtype.coe_injective.tendsto_cofinite) using 1,
  funext g,
  obtain ⟨g, hg⟩ := g,
  simp [mB, f₁, acbd_extend], -- squeeze_simp fails here for some reason
  simp only [bottom_row, set.mem_preimage, set.mem_singleton_iff] at hg,
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
lemma smul_eq_acbd_add (p : coprime_pair) (z : ℍ) {g : SL(2,ℤ)} (hg : bottom_row g = p) :
  ↑(g • z) = ((acbd p ↑(g : SL(2, ℝ))) : ℂ ) / (p.c ^ 2 + p.d ^ 2)
    + ((p.d : ℂ) * z - p.c) / ((p.c ^ 2 + p.d ^ 2) * (p.c * z + p.d)) :=
begin
  have nonZ1 : (p.c : ℂ) ^ 2 + (p.d) ^ 2 ≠ 0 := by exact_mod_cast p.sq_add_sq_ne_zero,
  have : (coe : ℤ → ℝ) ∘ ![p.c, p.d] ≠ 0 :=
    λ h, (p.ne_zero ∘ (@int.cast_injective ℝ _ _ _).comp_left) h,
  have nonZ2 : (p.c : ℂ) * z + p.d ≠ 0 := by simpa using linear_ne_zero _ z this,
  field_simp [nonZ1, nonZ2, bottom_ne_zero, -upper_half_plane.bottom],
  rw (by simp : (p.d : ℂ) * z - p.c = ((p.d) * z - p.c) * ↑(det (↑g : matrix (fin 2) (fin 2) ℤ))),
  rw [←hg, det_fin_two],
  simp only [bottom_row, int.coe_cast_ring_hom, coprime_pair.d_mk, coe_matrix_coe, coe_fn_eq_coe,
    int.cast_mul, of_real_int_cast, coprime_pair.c_mk, map_apply, bottom, int.cast_sub],
  ring,
end

lemma tendsto_abs_re_smul (z:ℍ) (p : coprime_pair) :
  tendsto (λ g : bottom_row ⁻¹' {p}, _root_.abs (((g : SL(2, ℤ)) • z).re)) cofinite at_top :=
begin
  suffices : tendsto (λ g : bottom_row ⁻¹' {p}, (((g : SL(2, ℤ)) • z).re)) cofinite (cocompact ℝ),
  { exact tendsto_norm_cocompact_at_top.comp this },
  have : ((p.c : ℝ) ^ 2 + p.d ^ 2)⁻¹ ≠ 0,
  { apply inv_ne_zero,
    exact_mod_cast p.sq_add_sq_ne_zero },
  let f := homeomorph.mul_right' _ this,
  let ff := homeomorph.add_right (((p.d:ℂ)* z - p.c) / ((p.c ^ 2 + p.d ^ 2) * (p.c * z + p.d))).re,
  convert ((f.trans ff).closed_embedding.tendsto_cocompact).comp (tendsto_acbd p),
  ext g,
  change ((g : SL(2, ℤ)) • z).re = (acbd p ↑(↑g : SL(2, ℝ))) / (p.c ^ 2 + p.d ^ 2)
  + (((p.d:ℂ )* z - p.c) / ((p.c ^ 2 + p.d ^ 2) * (p.c * z + p.d))).re,
  exact_mod_cast (congr_arg complex.re (smul_eq_acbd_add p z g.2))
end

end tendsto_lemmas

section fundamental_domain

/-- For `z : ℍ`, there is a `g : SL(2,ℤ)` maximizing `(g•z).im` -/
lemma exists_g_with_max_im (z : ℍ) :
  ∃ g : SL(2,ℤ), ∀ g' : SL(2,ℤ), (g' • z).im ≤ (g • z).im :=
begin
  obtain ⟨p, hp⟩ := (tendsto_norm_sq_coprime_pair z).exists_forall_le,
  obtain ⟨g, hg⟩ := bottom_row_surj p,
  use g,
  intros g',
  rw [im_smul_eq_div_norm_sq, im_smul_eq_div_norm_sq, div_le_div_left],
  { simpa [← hg] using hp (bottom_row g') },
  { exact z.im_pos },
  { exact normsq_bottom_pos g' z },
  { exact normsq_bottom_pos g z },
end

/-- Given `z : ℍ` and a bottom row `(c,d)`, among the `g : SL(2,ℤ)` with this bottom row, minimize
  `|(g•z).re|`.  -/
lemma exists_g_with_given_cd_and_min_re (z:ℍ) (cd : coprime_pair) :
  ∃ g : SL(2,ℤ), bottom_row g = cd ∧ (∀ g' : SL(2,ℤ), bottom_row g = bottom_row g' →
  _root_.abs ((g • z).re) ≤ _root_.abs ((g' • z).re)) :=
begin
  haveI : nonempty (bottom_row ⁻¹' {cd}) := let ⟨x, hx⟩ := bottom_row_surj cd in ⟨⟨x, hx⟩⟩,
  obtain ⟨g, hg⟩  := filter.tendsto.exists_forall_le (tendsto_abs_re_smul z cd),
  refine ⟨g, g.2, _⟩,
  { intros g1 hg1,
    have : g1 ∈ (bottom_row ⁻¹' {cd}),
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
  field_simp [normsq_bottom_ne_zero, norm_sq_ne_zero, S]
end

/-- If `1<|z|`, then `|S•z|<1` *********** ????????????? *********** -/
lemma normsq_S_lt_of_normsq {z : ℍ} (h: 1 < norm_sq z) : norm_sq (S • z) < 1 :=
begin
  sorry,
  have : z.im < z.im / norm_sq (z:ℂ),
  { have imz : 0 < z.im := im_pos z,
    apply (lt_div_iff z.norm_sq_pos).mpr,
    nlinarith },
  convert this,
  simp only [im_smul_eq_div_norm_sq],
  field_simp [normsq_bottom_ne_zero, norm_sq_ne_zero, S]
end


/-- Any `z : ℍ` can be moved to `𝒟` by an element of `SL(2,ℤ)`  -/
lemma exists_smul_mem_fundamental_domain (z : ℍ) : ∃ g : SL(2,ℤ), g • z ∈ 𝒟 :=
begin
  -- obtain a g₀ which maximizes im (g • z),
  obtain ⟨g₀, hg₀⟩ := exists_g_with_max_im z,
  -- then among those, minimize re
  obtain ⟨g, hg, hg'⟩ := exists_g_with_given_cd_and_min_re z (bottom_row g₀),
  use g,
  -- `g` has same max im property as `g₀`
  have hg₀' : ∀ (g' : SL(2,ℤ)), (g' • z).im ≤ (g • z).im,
  { have hg'' : (g • z).im = (g₀ • z).im,
    { rw [im_smul_eq_div_norm_sq, im_smul_eq_div_norm_sq,
        bottom_eq_of_bottom_row_eq _ hg] },
    simpa only [hg''] using hg₀ },
  split,
  { -- Claim: `|g•z| > 1`. If not, then `S•g•z` has larger imaginary part
    contrapose! hg₀',
    use S * g,
    rw mul_action.mul_smul,
    exact im_lt_im_S hg₀' },
  { -- Claim: `|Re(g•z)| < 1/2`; if not, then either `T` or `T'` decrease |Re|.
    rw abs_le,
    split,
    { contrapose! hg',
      refine ⟨T * g, _, _⟩,
      { -- goal: `bottom_row (T * g) = bottom_row g`.
        simp [bottom_row, T, vec_head, vec_tail], },
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
        simp [bottom_row, T', vec_head, vec_tail] },
      rw mul_action.mul_smul,
      change _ < (g • z).re at hg',
      have : |(g • z).re - 1| < |(g • z).re| :=
        by cases abs_cases ((g • z).re - 1); cases abs_cases (g • z).re; linarith,
      convert this,
      -- goal: `(T' • g • z).re = (g • z).re - 1`.
      simp [T', sub_eq_add_neg] } }
end





/-- MOVE TO INT SOMEWHERE -/
lemma int.eq_one_or_neg_one_of_mul_eq_one {z w : ℤ} (h : z * w = 1) : z = 1 ∨ z = -1 :=
int.is_unit_iff.mp (is_unit_of_mul_eq_one z w h)

lemma int.eq_one_or_neg_one_of_mul_eq_one' {z w : ℤ} (h : z * w = 1) : (z = 1 ∧ w = 1) ∨
(z = -1 ∧ w = -1) :=
begin
  cases int.eq_one_or_neg_one_of_mul_eq_one h,
  { left,
    split,
    assumption,
    rw h_1 at h,
    rw one_mul at h,
    exact h },
  { right,
    split,
    assumption,
    rw h_1 at h,
    rw [neg_mul_eq_neg_mul_symm, one_mul] at h,
    exact eq_neg_of_eq_neg (eq.symm h),
  },
end

lemma int.le_one_zero (z : ℤ) (h: _root_.abs z < 1) : z = 0 :=
begin
  rw int.eq_zero_iff_abs_lt_one at h,
  exact h,
end

lemma int.ne_zero_ge_one {z : ℤ} (h₀: ¬ z = 0) : 1 ≤ |z| :=
begin
--  library_search,
  by_contra,
  push_neg at h,
  exact h₀ (int.eq_zero_iff_abs_lt_one.mp h),
end

lemma junk (z w : ℂ ) (h: w = z) : w.re = z.re :=
begin
  exact congr_arg re h,
end

lemma move_by_large {x y : ℝ} (h : |x| < 1/2) (h₁ : |x+y|<1/2) (h₂ : 1≤ |y|) : false :=
begin
  cases abs_cases x;
  cases abs_cases y;
  cases abs_cases (x+y);
  linarith,
end


lemma junk1 ( x y z: ℝ ): (x < y) → (0 < z) → x*z < y*z :=
begin
  intros hxy hz,
  exact (mul_lt_mul_right hz).mpr hxy,
end



/-- The standard open fundamental domain of the action of `SL(2,ℤ)` on `ℍ` -/
def fundamental_domain_open : set ℍ :=
{z | 1 < (complex.norm_sq z) ∧ |z.re| < (1 : ℝ) / 2}

notation `𝒟ᵒ` := fundamental_domain_open


lemma ineq_1 (z : ℍ) (g: SL(2,ℤ)) (hz : z ∈ 𝒟ᵒ) (hg: g • z ∈ 𝒟ᵒ) (c_ne_z : g 1 0 ≠ 0) :
  (3 : ℝ)/4 < 4/ (3* (g 1 0)^4) :=
begin
  have z_im := z.im_ne_zero,
  have c_2_pos : (0 : ℝ) < (g 1 0)^2,
    exact_mod_cast pow_even_pos c_ne_z (by simp: even 2),
  have c_4_pos : (0 : ℝ) < (g 1 0)^4,
    exact_mod_cast pow_even_pos c_ne_z (by simp: even 4),
  have ImGeInD : ∀ (w : ℍ), w ∈ 𝒟ᵒ → 3/4 < (w.im)^2,
  {
    intros w hw,
    have : 1 < w.re * w.re + w.im * w.im := by simpa [complex.norm_sq_apply] using hw.1,
    have := hw.2,
    cases abs_cases w.re; nlinarith,
  },

  have czPdGecy : (g 1 0 : ℝ)^2 * (z.im)^2 ≤ norm_sq (bottom g z) :=
    calc
    (g 1 0 : ℝ)^2 * (z.im)^2 ≤ (g 1 0 : ℝ)^2 * (z.im)^2 + (g 1 0 * z.re + g 1 1)^2 : by nlinarith
    ... = norm_sq (bottom g z) : by simp [norm_sq, bottom]; ring,

  have zIm : (3 : ℝ) / 4 < (z.im)^2 := ImGeInD _ hz,
  have zIm' : (3 : ℝ) < 4 * (z.im)^2 := by nlinarith,

  calc
  (3 : ℝ)/4 < ((g • z).im)^2 : ImGeInD _ hg
  ... = (z.im)^2 / (norm_sq (bottom g z))^2 : _
  ... ≤ (1 : ℝ)/((g 1 0)^4 * (z.im)^2) : _
  ... < (4 : ℝ)/ (3* (g 1 0)^4) : _,

  {
    convert congr_arg (λ (x:ℝ), x^2) (im_smul_eq_div_norm_sq g z) using 1,
    exact (div_pow _ _ 2).symm,
  },

  {
    rw div_le_div_iff,
    convert pow_le_pow_of_le_left _ czPdGecy 2 using 1;
    ring,
    { nlinarith, },
    {
      exact pow_two_pos_of_ne_zero _ (normsq_bottom_ne_zero g z),
    },
    { nlinarith, },
  },

  {
    rw div_lt_div_iff,
    nlinarith,
    nlinarith,
    nlinarith,
  },
end

lemma nat.is_zero_or_one_of_le_one {n : ℕ} (h: n ≤ 1) : n = 0 ∨ n = 1 :=
begin
  cases n,
  left, refl,
  right,
  rw [nat.succ_le_succ_iff, le_zero_iff] at h,
  rw h,
end

lemma int.is_zero_or__pm_one_of_le_one {n : ℤ} (h: |n| ≤ 1) : n = -1 ∨ n = 0 ∨ n = 1 :=
begin
  cases abs_cases n,
  { right,
    rw h_1.1 at h,
    lift n to ℕ using h_1.2,
    norm_cast at h,
    norm_cast,
    exact nat.is_zero_or_one_of_le_one h, },
  { left,
    rw h_1.1 at h,
    linarith, },
end


lemma junk12 (n : ℕ) (h : |(n:ℤ)| ≤ 1) : n ≤ 1 :=
begin
cases abs_cases (n:ℤ),
nlinarith,
nlinarith,
end


lemma real.self_of_pow_inv_pow {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : (x^((1:ℝ)/y))^y = x :=
begin
  have : 0 < x^((1:ℝ)/y) ,
  {
    rw real.rpow_def_of_pos hx,
    exact real.exp_pos _,
  },
  rw real.rpow_def_of_pos this,
  rw real.log_rpow hx,
  rw ( _ : (1:ℝ) / y * real.log x * y = real.log x),
  exact real.exp_log hx,

  -- ring, ?!?
  rw mul_comm,
  rw ← mul_assoc,
  rw ( _ : y * (1 / y) = 1),
  ring,
  simp,
  field_simp,
  refine div_self _,
  nlinarith,
end

lemma real.lt_of_pow_lt_pow {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x^z < y^ z) :
x < y :=
begin
  rw real.rpow_def_of_pos hx at h,
  rw real.rpow_def_of_pos hy at h,
  rw real.exp_lt_exp at h,
  apply (real.log_lt_log_iff hx hy).mp,
  nlinarith,
end

lemma real.floor_eq_or_lt (y : ℝ ) :  (⌊y⌋ : ℝ) = y ∨ (⌊y⌋ : ℝ) < y
 := le_iff_eq_or_lt.mp (floor_le y)

lemma int.le_floor_of_lt {x : ℤ} {y : ℝ} (hx : (x : ℝ) < y) : (x:ℝ) ≤ (⌊y⌋:ℝ) :=
begin
  norm_cast,
  rw le_floor,
  exact le_of_lt hx,
end

lemma junk1234' (x : ℕ) (h : ¬ x ≤ 1) : 2 ≤ x :=
begin
  linarith,
end

lemma int.is_le_one_or_ge_two (x : ℤ) : |x| ≤ 1 ∨ 2 ≤ |x| :=
begin
  by_cases (|x| ≤ 1),
  left, assumption, right,
  let n:= int.to_nat (|x|),
  have n_is : (n:ℤ) = |x|,
  {
    sorry,
  },
  have hn : ¬ n ≤ 1,
  {
    sorry,
  },
  have := junk1234' n hn,
  linarith,
end

lemma ineq_2 (x : ℤ) (hx₁ : (3 : ℝ)/4 < 4/ (3* x^4)) (hx₂ : x ≠ 0) : x = 1 ∨ x = -1 :=
begin
  cases (int.is_le_one_or_ge_two x),
  {
    cases abs_cases x,
    {
      left,
    --linarith,
      sorry,
    },
    { right,
      linarith,
    },
  },
  {
    have : (2:ℝ)^4 ≤ x^4,
    {
      norm_cast,
      sorry,
    },
    have := (div_lt_div_iff _ _).mp hx₁,
    linarith,
    linarith,
    linarith,
  },
end

def T_pow (n : ℤ) : SL(2,ℤ) := ⟨ ![![1, n],![0,1]],
begin
  simp,
  sorry,
end
⟩

lemma g_is_of_c_is_one (g : SL(2,ℤ)) (hc : g 1 0 = 1) : g = (T_pow (g 0 0)) * S * (T_pow (g 1 1))
:=
begin
  rw T_pow,
  rw T_pow,
  ext i,
  fin_cases i;
  fin_cases j,
  { simp [vec_head, vec_tail, S], },
  {
    simp [vec_head, vec_tail, S],
    have g_det : g.val.det = (g 0 0)*(g 1 1)-(g 1 0)*(g 0 1),
    {
      sorry,
    },
    rw hc at g_det,
    rw g.2 at g_det,
    rw g_det,
    norm_cast,
    ring,
    sorry,
  },
  {
    simp [vec_head, vec_tail, S, hc],
    exact_mod_cast hc,
  },
  { simp [vec_head, vec_tail, S], },
end

lemma fun_dom_lemma₂ (z : ℍ) (g : SL(2,ℤ)) (hz : z ∈ 𝒟ᵒ) (hg : g • z ∈ 𝒟ᵒ) : z = g • z :=
begin
/-
  either c=0 in which case, translation, in which case translation by 0
  or im (y) > Sqrt(3)/2 -> c=±1 and compute...
-/
  -- ext,
  have g_det : matrix.det g = (g 0 0)*(g 1 1)-(g 1 0)*(g 0 1),
  {
    sorry,
  },

  by_cases (g 1 0 = 0),
  {
    have := g_det,
    rw h at this,
    --rw g.det_coe_fun at this,
    simp at this,
    have := int.eq_one_or_neg_one_of_mul_eq_one' (this.symm),
    have gzIs : ∀ (gg : SL(2,ℤ)), gg 1 0 = 0 → gg 0 0 = 1 → gg 1 1 = 1 → ↑(gg • z : ℍ) = (z : ℂ) + gg 0 1,
    {
      intros gg h₀ h₁ h₂,
      simp only [coe_fn_eq_coe] at h₀ h₁ h₂,
      simp [h₀, h₁, h₂],
    },
    have gIsId : ∀ (gg : SL(2,ℤ)), gg • z ∈ 𝒟ᵒ → gg 1 0 = 0 → gg 0 0 = 1 → gg 1 1 = 1 → gg = 1,
    {
      intros gg hh h₀ h₁ h₂,
      simp only [coe_fn_eq_coe] at h₀ h₁ h₂,
      ext i,
      fin_cases i;
      fin_cases j,
      simp only [h₁, coe_one, one_apply_eq],
      {
        simp only [nat.one_ne_zero, coe_one, fin.zero_eq_one_iff, ne.def, not_false_iff, one_apply_ne],
--        apply int.eq_zero_iff_abs_lt_one.mp,
        by_contra hhh,
        have reZ : |z.re| < 1/2,
        {
          exact_mod_cast hz.2,
        },
        have reGz : |((gg • z):ℍ ).re| < 1/2,
        {
          exact_mod_cast hh.2,
        },
        have reZpN : |z.re + gg 0 1| < 1/2,
        {
          convert reGz using 2,
--          apply congr_arg _root_.abs,
          rw (by simp : z.re + gg 0 1 = ((z:ℂ )+ gg 0 1).re),
          apply congr_arg complex.re,
          exact_mod_cast (gzIs gg h₀ h₁ h₂).symm,
        },

        refine move_by_large reZ reZpN _,
        exact_mod_cast  int.ne_zero_ge_one hhh,
      },
      simp only [h₀, nat.one_ne_zero, coe_one, fin.one_eq_zero_iff, ne.def, not_false_iff, one_apply_ne],
      simp only [h₂, coe_one, one_apply_eq],
    },
    have zIsGz : ∀ (gg : SL(2,ℤ)), gg 1 0 = 0 → gg 0 0 = 1 → gg 1 1 = 1 → gg • z ∈ 𝒟ᵒ → z = gg • z,
    {
      intros gg h₀ h₁ h₂ hh,
      have := gIsId gg hh h₀ h₁ h₂,
      rw this,
      simp,
    },
    cases this,
    { -- case a = d = 1
      exact zIsGz g h this_1.1 this_1.2 hg,
    },
    { -- case a = d = -1
      rw ← neg_smul,
      apply zIsGz; simp,
      exact_mod_cast h,
      simp only [this_1, neg_neg],
      simp only [this_1, neg_neg],
      --simp only [has_neg_coe_mat, dmatrix.neg_apply, coe_fn_eq_coe, neg_eq_zero],
      exact hg,
    },
  },
  {
    -- want to argue first that c=± 1
    -- then show this is impossible
    have := ineq_2 _ (ineq_1 z g hz hg h) h,

    cases this with hc,
    {
      have := g_is_of_c_is_one g hc,
      let z₁ := T_pow (g 1 1) • z,
      let w₁ := T_pow (- g 0 0) • (g • z),
      have w_1_S_z_1 : w_1 = S • z_1,
      {
        sorry,
      },
      have w_1_norm : 1 < norm_sq w_1,
      {
        sorry,
      },
      have z_1_norm : 1 < norm_sq z_1,
      {
        sorry,
      },

      have := normsq_S_lt_of_normsq z_1_norm,

      linarith,

      sorry,
    },
    {
      sorry,
    },

    sorry,
  },
 -- ALEX homework
end






    lemma fundom_no_repeats (z z' : H) (h : ∃ g : SL(2,ℤ), z' = g • z) (hz : z ∈ 𝒟) (hz' : z' ∈ 𝒟) :
      (z = z') ∨
      (z.val.re = -1/2 ∧ z' = T • z) ∨
      (z'.val.re = -1/2 ∧ z = T • z') ∨
      (z.val.abs = 1 ∧ z'.val.abs = 1 ∧ z' = S • z ∧ z = S • z') :=
    begin
      wlog hwlog : z.val.im ≤ z'.val.im,
      {
        by_cases hne : z = z', tauto,
        right,
        replace h := sign_coef h,
        obtain ⟨g, hcpos, hac, hg⟩ := h,
        set a := g.1 0 0,
        set b := g.1 0 1,
        set c := g.1 1 0 with ←cdf,
        set d := g.1 1 1 with ←ddf,
        have hcd : complex.norm_sq (c * z + d) ≤ 1,
        {
          have himzpos : 0 < z.val.im := im_pos_of_in_H',
          have hnz : 0 < complex.norm_sq (c * z + d),
          {
            rw norm_sq_pos,
            intro hcontra,
            rw [← cdf, ← ddf, ← bottom_def] at hcontra,
            exact czPd_nonZ_CP (ne.symm (ne_of_lt himzpos)) hcontra,
          },
          suffices: z.val.im * complex.norm_sq (c * z + d) ≤ z.val.im, nlinarith,
          rw [hg, im_smul_SL',cdf,ddf, le_div_iff hnz] at hwlog,
          exact hwlog,
        },
        have hc : _root_.abs c ≤ 1,
        {
          sorry
        },
        replace hc : c = 0 ∨ c = 1,
        {

          rw abs_le at hc,
          exact namedIsZ c hc.2 hcpos,
        },
        rcases hc with  hc | hc ,
        {     case c = 0
          have ha : a = 1 := (hac hc).2,
          have hd : d = 1 := (hac hc).1,
          have hgT : g = T^b,
          {
            rw T_pow,
            apply subtype.eq,
            simp,
            tauto,
          },
          have hb : _root_.abs c ≤ 1,
          {
            sorry
          },
          replace hb : b = -1 ∨ b = 0 ∨ b = 1,
          {
            sorry
          },
          rcases hb with hb | hb | hb,
          all_goals {rw hb at hgT, rw hgT at hg, clear hb, clear hgT, simp at hg},
          {
            right, left,
            rw ←inv_smul_eq_iff at hg,
            rw ←hg at hz,
            rw fundom_aux_1 hz' hz,
            tauto,
          },
          { tauto },
          {
            left,
            rw hg at hz',
            rw fundom_aux_1 hz hz',
            tauto,
          }
        },
        {     case c = 1
          sorry
        }
      },
      obtain ⟨g, hg⟩ := h,
      have hh : ∃ g : SL(2,ℤ), z = g • z' := ⟨g⁻¹, by {simp [eq_inv_smul_iff, hg]}⟩,
      specialize this hh hz' hz,
      tauto,
    end

end fundamental_domain

end modular_group
