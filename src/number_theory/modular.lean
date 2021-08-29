/-
Copyright (c) 2021 Alex Kontorovich and Heather Macbeth and Marc Masdeu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth, Marc Masdeu
-/
import analysis.complex.upper_half_plane analysis.special_functions.pow
import analysis.convex.basic

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

lemma S_apply (z : ℍ) : ((S • z:ℍ):ℂ) = (-1 : ℂ)/z := by simp [S]

/-- If `|z|<1`, then applying `S` strictly decreases `im` -/
lemma im_lt_im_S {z : ℍ} (h: norm_sq z < 1) : z.im < (S • z).im :=
begin
  rw [im_smul_eq_div_norm_sq, bottom],
  simp only [S, int.coe_cast_ring_hom, coe_matrix_coe, add_zero, int.cast_zero, one_mul, cons_val_one, coe_fn_eq_coe, of_real_zero,
  coe_mk, int.cast_one, map_apply, of_real_one, cons_val_zero, head_cons],
  apply (lt_div_iff z.norm_sq_pos).mpr,
  have : 0 < z.im := im_pos z,
  nlinarith,
end

/-- If `1 < |z|`, then `|S•z| < 1` -/
lemma normsq_S_lt_of_normsq {z : ℍ} (h: 1 < norm_sq z) : norm_sq ((S • z):ℍ) < 1 :=
begin
  rw [S_apply, (by simp : norm_sq ((-1:ℂ) / z) = norm_sq ((1:ℂ) / z)),
    (by simp: norm_sq ((1:ℂ) / z) = 1 / norm_sq z)],
  convert one_div_lt_one_div_of_lt _ h; simp,
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


/-- The standard open fundamental domain of the action of `SL(2,ℤ)` on `ℍ` -/
def fundamental_domain_open : set ℍ :=
{z | 1 < ((z:ℂ).norm_sq) ∧ |z.re| < (1 : ℝ) / 2}

notation `𝒟ᵒ` := fundamental_domain_open

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
    rw [h_1, one_mul] at h,
    exact h },
  { right,
    split,
    assumption,
    rw [h_1, neg_mul_eq_neg_mul_symm, one_mul] at h,
    exact eq_neg_of_eq_neg (eq.symm h), },
end

lemma int.ne_zero_ge_one {z : ℤ} (h₀: ¬ z = 0) : 1 ≤ |z| :=
begin
  by_contra,
  push_neg at h,
  exact h₀ (int.eq_zero_iff_abs_lt_one.mp h),
end

lemma move_by_large {x y : ℝ} (h : |x| < 1/2) (h₁ : |x+y|<1/2) (h₂ : 1≤ |y|) : false :=
  by cases abs_cases x; cases abs_cases y; cases abs_cases (x+y); linarith

/-- Crucial lemma showing that if `c≠0`, then `3/4 < 4/(3c^4)` -/
lemma ineq_1 (z : ℍ) (g: SL(2,ℤ)) (hz : z ∈ 𝒟ᵒ) (hg: g • z ∈ 𝒟ᵒ) (c_ne_z : g 1 0 ≠ 0) :
  (3 : ℝ)/4 < 4/ (3* (g 1 0)^4) :=
begin
  have z_im := z.im_ne_zero,
  have c_4_pos : (0 : ℝ) < (g 1 0)^4,
    exact_mod_cast pow_even_pos c_ne_z (by simp: even 4),
  /- Any point `w∈𝒟ᵒ` has imaginary part at least `sqrt (3/4)` -/
  have ImGeInD : ∀ (w : ℍ), w ∈ 𝒟ᵒ → 3/4 < (w.im)^2,
  { intros w hw,
    have : 1 < w.re * w.re + w.im * w.im := by simpa [complex.norm_sq_apply] using hw.1,
    have := hw.2,
    cases abs_cases w.re; nlinarith, },
  /- The next argument is simply that `c^2 y^2 ≤ |c z + d|^2`. -/
  have czPdGecy : (g 1 0 : ℝ)^2 * (z.im)^2 ≤ norm_sq (bottom g z) :=
    calc
    (g 1 0 : ℝ)^2 * (z.im)^2 ≤ (g 1 0 : ℝ)^2 * (z.im)^2 + (g 1 0 * z.re + g 1 1)^2 : by nlinarith
    ... = norm_sq (bottom g z) : by simp [norm_sq, bottom]; ring,
  have zIm : (3 : ℝ) / 4 < (z.im)^2 := ImGeInD _ hz,
  /- This is the main calculation:
  `sqrt 3 / 2 < Im(g•z) = Im(z)/|cz+d|^2 ≤ y/(c^2 y^2) < 2/(c^2 sqrt 3)`
  -/
  calc
  (3 : ℝ) / 4 < ((g • z).im) ^ 2 : ImGeInD _ hg
  ... = (z.im) ^ 2 / (norm_sq (bottom g z)) ^ 2 : _
  ... ≤ (1 : ℝ) / ((g 1 0) ^ 4 * (z.im) ^ 2) : _
  ... < (4 : ℝ) / (3 * (g 1 0) ^ 4) : _,
  { convert congr_arg (λ (x:ℝ), x ^ 2) (im_smul_eq_div_norm_sq g z) using 1,
    exact (div_pow _ _ 2).symm, },
  { rw div_le_div_iff,
    convert pow_le_pow_of_le_left _ czPdGecy 2 using 1;
    ring,
    { nlinarith, },
    { exact pow_two_pos_of_ne_zero _ (normsq_bottom_ne_zero g z), },
    { nlinarith, }, },
  { rw div_lt_div_iff,
    repeat {nlinarith}, },
end

lemma nat.is_zero_or_one_of_le_one {n : ℕ} (h: n ≤ 1) : n = 0 ∨ n = 1 :=
begin
  cases n,
  { left, refl, },
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

lemma int.is_le_one_or_ge_two (x : ℤ) : |x| ≤ 1 ∨ 2 ≤ |x| :=
begin
  cases le_or_gt (|x|) 1,
  left, assumption, right,
  exact h,
end

lemma int.fourth_le_fourth {a b : ℤ} (hab : |a| ≤ |b|) : a ^ 4 ≤ b ^ 4 :=
begin
  have := sq_le_sq hab,
  rw [(by simp only [pow_bit0_abs, abs_pow] : a ^ 2 = |a ^ 2|),
   (by simp only [pow_bit0_abs, abs_pow] : b ^ 2 = |b ^ 2|)] at this,
  convert sq_le_sq this using 1; ring,
end

/-- Knowing that `3/4<4/(3c^4)` from `ineq_1`, and `c≠0`, we conclude that `c=1` or `c=-1`. -/
lemma ineq_2 (c : ℤ) (hc₁ : (3 : ℝ)/4 < 4/ (3* c^4)) (hc₂ : c ≠ 0) : c = 1 ∨ c = -1 :=
begin
  cases (int.is_le_one_or_ge_two c),
  { -- case |c| ≤ 1
     cases int.is_zero_or__pm_one_of_le_one h, -- either c = 1 or c = 0 or c = -1
    { right, assumption, },
    { cases h_1,
      { exfalso,
        exact hc₂ h_1, },
      left, assumption, }, },
  { -- case 2 ≤ |c|
    exfalso,
    have : 2^4 ≤ c^4,
    { refine int.fourth_le_fourth _,
      convert h using 1, },
    have : (2:ℝ)^4 ≤ c^4,
    { norm_cast,
      convert this using 1, },
    have := (div_lt_div_iff _ _).mp hc₁,
    repeat {linarith}, },
end


/-- Definition: `T_pow` is the matrix `T` raised to the power `n:ℤ`. -/
def T_pow (n : ℤ) : SL(2,ℤ) := ⟨ ![![1, n],![0,1]],
begin
  rw matrix.det_fin_two,
  simp,
end ⟩


/- If c=1, then `g=[[1,a],[0,1]] * S * [[1,d],[0,1]]` -/
lemma g_is_of_c_is_one (g : SL(2,ℤ)) (hc : g 1 0 = 1) : g = (T_pow (g 0 0)) * S * (T_pow (g 1 1))
:=
begin
  rw [T_pow, T_pow],
  ext i,
  fin_cases i; fin_cases j,
  { simp [vec_head, vec_tail, S], },
  { simp only [vec_head, vec_tail, S, matrix.special_linear_group.coe_fn_eq_coe,
      modular_group.S.equations._eqn_1, matrix.special_linear_group.coe_mul,
      matrix.special_linear_group.coe_mk, matrix.cons_mul, matrix.vec_mul_cons,
      matrix.vec_head.equations._eqn_1, matrix.cons_val_zero, matrix.smul_cons, mul_zero,
      mul_neg_eq_neg_mul_symm, mul_one, matrix.smul_empty, matrix.vec_tail.equations._eqn_1,
      function.comp_app, fin.succ_zero_eq_one, matrix.cons_val_one, matrix.cons_val_fin_one,
      matrix.empty_vec_mul, matrix.cons_add, pi.zero_apply, add_zero, pi.zero_comp,
      matrix.zero_empty, matrix.empty_add_empty, matrix.add_cons],
    have g_det : g.val.det = (g 0 0)*(g 1 1)-(g 1 0)*(g 0 1),
    { convert det_fin_two g using 1,
      ring, },
    rw [hc, g.2] at g_det,
    rw g_det,
    simp, },
  { simp only [vec_head, vec_tail, S, hc, matrix.special_linear_group.coe_fn_eq_coe,
      modular_group.S.equations._eqn_1, matrix.special_linear_group.coe_mul,
      matrix.special_linear_group.coe_mk, matrix.cons_mul, matrix.vec_mul_cons,
      matrix.vec_head.equations._eqn_1, matrix.cons_val_zero, matrix.smul_cons, mul_zero,
      mul_neg_eq_neg_mul_symm, mul_one, matrix.smul_empty, matrix.vec_tail.equations._eqn_1,
      function.comp_app, fin.succ_zero_eq_one, matrix.cons_val_one, matrix.cons_val_fin_one,
      matrix.empty_vec_mul, matrix.cons_add, pi.zero_apply, add_zero, pi.zero_comp,
      matrix.zero_empty, matrix.empty_add_empty, matrix.add_cons],
    exact_mod_cast hc, },
  { simp [vec_head, vec_tail, S], },
end

/-- Nontrivial lemma: if `|x|<1/2` and `n:ℤ`, then `2nx+n^2≥0`. (False for `n:ℝ`!) -/
lemma int.non_neg_of_lt_half (n : ℤ) (x : ℝ) (hx : |x| < 1/2) : (0:ℝ) ≤ 2 * n * x + n * n :=
begin
  rw abs_lt at hx,
  have : (0:ℝ) ≤ n*n := by nlinarith,
  cases n,
  { -- n ≥ 0
    have : (n:ℝ) = (int.of_nat n) := by simp,
    have : (0:ℝ) ≤ n := by simp,
    cases lt_or_ge x 0,
    {  -- x < 0
      cases n,
      { simp, },
      { -- n ≥ 1
        have eq1 : (1:ℝ) ≤ int.of_nat n.succ := by simp,
        have eq2 : (1:ℝ) ≤ (int.of_nat n.succ) * (int.of_nat n.succ) := by nlinarith,
        have eq3 : (-1:ℝ) ≤ 2 * x := by nlinarith,
        have eq4 : (0:ℝ) ≤ 2 * x + int.of_nat n.succ := by linarith,
        have eq5 : (0:ℝ) ≤ (2 * x + int.of_nat n.succ)*(int.of_nat n.succ) := by nlinarith,
        convert eq5 using 1,
        ring, }, },
    { -- x ≥ 0
      have : (0:ℝ) ≤ 2*n*x := by nlinarith,
      nlinarith, }, },
  { -- n ≤ -1
    have := int.neg_succ_of_nat_coe n,
    set k := int.neg_succ_of_nat n,
    have eq1 : k ≤ -1,
    { have : 1 ≤ 1 + n := by simp,
      have :  -((1:ℤ) + n) ≤ -1,
      { have : 0 ≤ n := by simp,
        linarith, },
      convert this using 1,
      simp [this_1],
      ring, },
    have eq1' : (k:ℝ) ≤ -1 := by exact_mod_cast eq1,
    cases lt_or_ge x 0,
    { -- x < 0
      have : (0:ℝ) ≤ 2*k*x := by nlinarith,
      have eq2 : 1 ≤ k*k  := by nlinarith,
      linarith, },
    { -- x ≥ 0
      have eq2 : (2:ℝ) * x + k ≤ 0 := by nlinarith,
      nlinarith, }, },
end

/-- If `z∈𝒟ᵒ`, and `n:ℤ`, then `|z+n|>1`.   -/
lemma move_by_T {z : ℍ} (hz : z ∈ 𝒟ᵒ) (n : ℤ) : 1 < norm_sq (((T_pow n) • z) : ℍ) :=
begin
  rw T_pow,
  simp only [zero_add, div_one, modular_group.coe_smul, upper_half_plane.top.equations._eqn_1,
    matrix.special_linear_group.coe_fn_eq_coe, matrix.special_linear_group.coe_matrix_coe,
    matrix.special_linear_group.coe_mk, int.coe_cast_ring_hom, matrix.map_apply, matrix.cons_val',
    matrix.cons_val_zero, matrix.cons_val_fin_one, int.cast_one, complex.of_real_one, one_mul,
    matrix.cons_val_one, matrix.vec_head.equations._eqn_1, complex.of_real_int_cast,
    upper_half_plane.bottom.equations._eqn_1, int.cast_zero, complex.of_real_zero, zero_mul],
  rw complex.norm_sq_apply,
  have hz1 : 1 < z.re * z.re + z.im * z.im,
  { have := hz.1,
    rw norm_sq at this,
    convert this using 1, },
  rw (by simp : ((z:ℂ) + n).im = z.im),
  rw (by simp : ((z:ℂ) + n).re = z.re + n),
  rw (by ring : (z.re + ↑n) * (z.re + ↑n) = z.re * z.re + 2 * n * z.re + n * n),
  have : 0 ≤  2 * ↑n * z.re + ↑n * ↑n := int.non_neg_of_lt_half n (z.re) hz.2,
  convert add_lt_add_of_le_of_lt this hz1 using 1,
  { simp, },
  { ring_nf, },
end

/-- If `c=1`, then `[[1,-a],[0,1]]*g = S * [[1,d],[0,1]]`. -/
lemma T_pow_S_of_g (g : SL(2,ℤ)) (hc : g 1 0 = 1) : T_pow (- g 0 0) * g = S * T_pow (g 1 1) :=
begin
  rw g_is_of_c_is_one g hc,
  ext i,
  fin_cases i; fin_cases j,
  { simp [vec_head, vec_tail, T_pow, S], },
  { simp only [add_zero, fin.succ_zero_eq_one, function.comp_app, matrix.add_cons, matrix.cons_add,
    matrix.cons_mul, matrix.cons_val_fin_one, matrix.cons_val_one, matrix.cons_val_zero,
    matrix.empty_add_empty, matrix.empty_vec_mul, matrix.smul_cons, matrix.smul_empty,
    matrix.special_linear_group.coe_fn_eq_coe, matrix.special_linear_group.coe_mk,
    matrix.special_linear_group.coe_mul, matrix.vec_head.equations._eqn_1, matrix.vec_mul_cons,
    matrix.vec_tail.equations._eqn_1, matrix.zero_empty, modular_group.S.equations._eqn_1,
    modular_group.T_pow.equations._eqn_1, mul_neg_eq_neg_mul_symm, mul_one, mul_zero,
    pi.zero_apply, pi.zero_comp, zero_add],
    ring,
  },
  { simp [vec_head, vec_tail, T_pow, S], },
  { simp [vec_head, vec_tail, T_pow, S], },
end

/-- If both `z` and `g•z` are in `𝒟ᵒ`, then `c` can't be `1`. -/
lemma false_of_c_eq_one {z : ℍ} {g : SL(2,ℤ)} (hc : g 1 0 = 1) (hz : z ∈ 𝒟ᵒ) (hg : g • z ∈ 𝒟ᵒ) :
false :=
begin
  let z₁ := T_pow (g 1 1) • z,
  let w₁ := T_pow (- g 0 0) • (g • z),
  have w₁_norm : 1 < norm_sq w₁ := move_by_T hg (- g 0 0),
  have z₁_norm : 1 < norm_sq z₁ := move_by_T hz (g 1 1),
  have w₁_S_z₁ : w₁ = S • z₁,
  { rw (_ : w₁ = T_pow (- g 0 0) • g • z),
    rw (_ : z₁ = T_pow (g 1 1) • z),
    convert (congr_arg (λ (g:SL(2,ℤ)), g • z) (T_pow_S_of_g g hc)) using 1,
    { convert (upper_half_plane.mul_smul' (T_pow (-g 0 0)) g z).symm using 1,
      -- refl, ** Failed???**
      sorry, },
    { convert (upper_half_plane.mul_smul' S (T_pow (g 1 1)) z).symm using 1,
      sorry, },
    refl,
    refl, },
  have := normsq_S_lt_of_normsq z₁_norm,
  rw ← w₁_S_z₁ at this,
  linarith,
end

/-- Second Main Fundamental Domain Lemma: If both `z` and `g•z` are in the open domain `𝒟ᵒ`, where
  `z:ℍ` and `g:SL(2,ℤ)`, then `z = g • z`. -/
lemma fun_dom_lemma₂ (z : ℍ) (g : SL(2,ℤ)) (hz : z ∈ 𝒟ᵒ) (hg : g • z ∈ 𝒟ᵒ) : z = g • z :=
begin
/-  The argument overview is: either `c=0`, in which case the action is translation, which must be
  by `0`, OR
  `c=±1`, which gives a contradiction from considering `im z`, `im(g•z)`, and `norm_sq(T^* z)`. -/
  have g_det : matrix.det g = (g 0 0)*(g 1 1)-(g 1 0)*(g 0 1),
  { convert det_fin_two g using 1,
    ring, },
  by_cases (g 1 0 = 0),
  { -- case c=0
    have := g_det,
    rw h at this,
    simp only [matrix.special_linear_group.coe_fn_eq_coe, matrix.special_linear_group.det_coe,
      zero_mul, sub_zero] at this,
    have := int.eq_one_or_neg_one_of_mul_eq_one' (this.symm),
    have gzIs : ∀ (gg : SL(2,ℤ)), gg 1 0 = 0 → gg 0 0 = 1 → gg 1 1 = 1 →
      ↑(gg • z : ℍ) = (z : ℂ) + gg 0 1,
    { intros gg h₀ h₁ h₂,
      simp only [coe_fn_eq_coe] at h₀ h₁ h₂,
      simp [h₀, h₁, h₂], },
    have gIsId : ∀ (gg : SL(2,ℤ)), gg • z ∈ 𝒟ᵒ → gg 1 0 = 0 → gg 0 0 = 1 → gg 1 1 = 1 → gg = 1,
    { intros gg hh h₀ h₁ h₂,
      simp only [coe_fn_eq_coe] at h₀ h₁ h₂,
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
        have reZpN : |z.re + gg 0 1| < 1/2,
        { convert reGz using 2,
          rw (by simp : z.re + gg 0 1 = ((z:ℂ )+ gg 0 1).re),
          apply congr_arg complex.re,
          exact_mod_cast (gzIs gg h₀ h₁ h₂).symm, },
        refine move_by_large reZ reZpN _,
        exact_mod_cast  int.ne_zero_ge_one hhh, },
      simp only [h₀, nat.one_ne_zero, coe_one, fin.one_eq_zero_iff, ne.def, not_false_iff,
        one_apply_ne],
      simp only [h₂, coe_one, one_apply_eq], },
    have zIsGz : ∀ (gg : SL(2,ℤ)), gg 1 0 = 0 → gg 0 0 = 1 → gg 1 1 = 1 → gg • z ∈ 𝒟ᵒ → z = gg • z,
    { intros gg h₀ h₁ h₂ hh,
      have := gIsId gg hh h₀ h₁ h₂,
      rw this,
      simp, },
    cases this,
    { -- case a = d = 1
      exact zIsGz g h this_1.1 this_1.2 hg, },
    { -- case a = d = -1
      rw ← neg_smul,
      apply zIsGz; simp,
      exact_mod_cast h,
      simp only [this_1, neg_neg],
      simp only [this_1, neg_neg],
      exact hg, }, },
  { -- case c ≠ 0
    exfalso,
    -- argue first that c=± 1
    have := ineq_2 _ (ineq_1 z g hz hg h) h,
    -- then show this is impossible
    cases this with hc,
    { -- c = 1
      exact false_of_c_eq_one hc hz hg, },
    { -- c = -1
      have neg_c_one : (-g) 1 0 = 1,
      { have := eq_neg_of_eq_neg this,
        simp [this], },
      have neg_g_𝒟 : (-g) • z ∈ 𝒟ᵒ,
      { convert hg using 1,
        simp, },
      exact false_of_c_eq_one neg_c_one hz neg_g_𝒟, }, },
end

end fundamental_domain

end modular_group
