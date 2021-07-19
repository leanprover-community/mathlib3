import analysis.complex.automorphisms_half_plane

open complex matrix matrix.special_linear_group
noncomputable theory

local notation `|` x `|` := _root_.abs x
local notation `SL(` n `, ` R `)`:= special_linear_group (fin n) R

open_locale upper_half_plane

local attribute [instance] fintype.card_fin_even

namespace upper_half_plane

/-- The action of `SL(2, ℤ)` on the upper half-plane, as a restriction of the `SL(2, ℝ)`-action. -/
instance int_action : mul_action SL(2, ℤ) ℍ :=
mul_action.comp_hom ℍ (map (int.cast_ring_hom ℝ))

@[simp] lemma coe_smul_int (g : SL(2, ℤ)) (z : ℍ) : ↑(g • z) = top g z / bottom g z := rfl
@[simp] lemma re_smul_int (g : SL(2, ℤ)) (z : ℍ) : (g • z).re = (top g z / bottom g z).re := rfl
@[simp] lemma smul_coe_int (g : SL(2, ℤ)) (z : ℍ) : (g : SL(2,ℝ)) • z = g • z := rfl

@[simp] lemma smul_neg_int (g : SL(2, ℤ)) (z : ℍ) : -g • z = g • z :=
show ↑(-g) • _ = _, by simp [smul_neg g z]

lemma im_smul_int (g : SL(2, ℤ)) (z : ℍ) : (g • z).im = (top g z / bottom g z).im := rfl

lemma im_smul_int_eq_div_norm_sq (g : SL(2, ℤ)) (z : ℍ) :
  (g • z).im = z.im / (complex.norm_sq (bottom g z)) :=
im_smul_eq_div_norm_sq g z

end upper_half_plane

open upper_half_plane

/-! It is useful to develop basic theory for an object `coprime_ints`, consisting of two integers
and a proof that they satisfy `is_coprime`. -/

@[ext] structure coprime_ints :=
(c : ℤ)
(d : ℤ)
(is_coprime : is_coprime c d)

namespace coprime_ints

instance : has_coe coprime_ints (ℤ × ℤ) := ⟨λ p, (p.c, p.d)⟩

instance : nonempty coprime_ints := ⟨⟨1, 1, is_coprime_one_left⟩⟩

@[simp] lemma fst_coe (p : coprime_ints) : (p : ℤ × ℤ).1 = p.c := rfl
@[simp] lemma snd_coe (p : coprime_ints) : (p : ℤ × ℤ).2 = p.d := rfl

lemma coe_injective : function.injective (coe : coprime_ints → ℤ × ℤ) :=
λ p q hpq, ext p q (by simpa using congr_arg prod.fst hpq) (by simpa using congr_arg prod.snd hpq)

lemma ne_zero (p : coprime_ints) : p.c ≠ 0 ∨ p.d ≠ 0 :=
begin
  rw ← not_and_distrib,
  rintros ⟨c_eq_zero, d_eq_zero⟩,
  simpa [c_eq_zero, d_eq_zero] using p.is_coprime
end

lemma junk (x y z w :ℂ) (h: ![x,y]=![z,w]) : x=z :=
begin
  sorry,
/-  simp [vec_cons, vec_empty, fin_zero_elim] at h,
  rw vec_cons at h,
  rw vec_cons at h,
  rw vec_cons at h,
  rw vec_cons at h,
  rw vec_empty at h,
  -/
-- library_search,
end

lemma junk1 (x y :ℂ) (h1 : ![x,y]=![0,0]) : x=0 := junk x y 0 0 h1

lemma ne_zero' (p : coprime_ints) : ![(p.c:ℂ ),p.d] ≠ 0 :=
begin
  by_contra,
  push_neg at h,
  have cd_eq_z: p.c=0 ∧ p.d=0,
  {
    split,
    have := junk1 (p.c:ℂ ) (p.d:ℂ ) ,
--    have := this h,
   -- have := h 1,
    sorry,
    sorry,
  },
  exact not_and_distrib.mpr (ne_zero p) (cd_eq_z)
end

lemma sum_sq_ne_zero (p : coprime_ints) : p.c ^ 2 + p.d ^ 2 ≠ 0 :=
begin
  intros h,
  have c_eq_zero : p.c = 0 := by nlinarith,
  have d_eq_zero : p.d = 0 := by nlinarith,
  cases p.ne_zero with hc hd; contradiction
end

end coprime_ints

lemma det_SL2ℤ (g : SL(2,ℤ)) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 :=
begin
    calc _ = matrix.det g : _
    ... = 1 : by rw g.det_coe_fun,
    simp [matrix.det_succ_row_zero, fin.sum_univ_succ],
    ring,
end

@[simps] def bottom_row (g : SL(2, ℤ)) : coprime_ints :=
{ c := g 1 0,
  d := g 1 1,
  is_coprime := begin
    rw is_coprime,
    use [( - g 0 1), (g 0 0)],
    convert det_SL2ℤ g using 1,
    ring,
  end }



lemma bottom_row_surj : function.surjective bottom_row :=
begin
  intros cd,
  obtain ⟨b₀, a, gcd_eqn⟩ := cd.is_coprime,
  let A := ![![a, -b₀], ![cd.c, cd.d]],
  have det_A_1 : det A = 1,
  { convert gcd_eqn,
    simp [A, matrix.det_succ_row_zero, fin.sum_univ_succ,
      (by ring : a * cd.d + b₀ * cd.c = b₀ * cd.c + a * cd.d)] },
  use ⟨A, det_A_1⟩,
  simp only [bottom_row, A, cons_apply_one, cons_val_one, cons_val_zero, head_cons],
  ext; refl,
end

lemma bottom_eq_of_bottom_row_eq {g h : SL(2,ℤ)} (z : ℍ) (bot_eq : bottom_row g = bottom_row h) :
  bottom g z = bottom h z :=
by simp [← bottom_row_c, ← bottom_row_d, bot_eq]


section tendsto_lemmas
/-! This is an attempt to do the maximin argument using more abstract existence theory. -/

open filter continuous_linear_map

lemma finite_pairs (z : ℍ) :
  filter.tendsto (λ p : coprime_ints, ((p.c : ℂ) * z + p.d).norm_sq)
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
    (h₁.comp (h₂.comp coprime_ints.coe_injective.tendsto_cofinite)),
  ext,
  simp [f],
end


/- generalize to arbitrary matrix index sets and move to matrix file -/
def matrix.coord (i j : fin 2) : (matrix (fin 2) (fin 2) ℝ) →ₗ[ℝ] ℝ :=
(linear_map.proj j : (fin 2 → ℝ) →ₗ[ℝ] _).comp (linear_map.proj i)

def acbd (p : coprime_ints) : (matrix (fin 2) (fin 2) ℝ) →ₗ[ℝ] ℝ :=
p.c • matrix.coord 0 0 + p.d • matrix.coord 0 1

@[simp]lemma acbd_apply (p : coprime_ints) (g : matrix (fin 2) (fin 2) ℝ) :
  acbd p g = p.c * g 0 0 + p.d * g 0 1 :=
by simp [acbd, matrix.coord]


/-- Map sending the matrix [a b; c d] to `(ac₀+bd₀ , ad₀ - bc₀, c, d)`, for some fixed `(c₀, d₀)`.
-/
def line_map (cd : coprime_ints) : (matrix (fin 2) (fin 2) ℝ) →ₗ[ℝ] ((fin 2 → ℝ) × (fin 2 → ℝ)) :=
((matrix.mul_vec_lin ![![(cd.c:ℝ), cd.d], ![cd.d,-cd.c]]).comp
  (linear_map.proj 0 : (matrix (fin 2) (fin 2) ℝ) →ₗ[ℝ] _)).prod
  (linear_map.proj 1)

lemma lin_indep_acbd (cd : coprime_ints) : (line_map cd).ker = ⊥ :=
begin
  rw linear_map.ker_eq_bot,
  have nonZ : ((cd.c)^2+(cd.d)^2:ℝ) ≠ 0,
  { norm_cast,
    exact cd.sum_sq_ne_zero },
  let F : matrix (fin 2) (fin 2) ℝ := ((cd.c)^2+(cd.d)^2:ℝ)⁻¹ • ![![cd.c, cd.d], ![cd.d, -cd.c]],
  let f₁ : (fin 2 → ℝ) → (fin 2 → ℝ) := F.mul_vec_lin,
  let f : (fin 2 → ℝ) × (fin 2 → ℝ) → matrix (fin 2) (fin 2) ℝ := λ ⟨x , cd⟩, ![f₁ x, cd],
  have : function.left_inverse f (line_map cd),
  { intros g,
    simp [line_map, f, f₁, F, vec_head, vec_tail],
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

/-- Big filter theorem -/
theorem big_thm (cd : coprime_ints) :
  tendsto (λ g : bottom_row ⁻¹' {cd}, acbd cd ↑g) cofinite (cocompact ℝ) :=
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
  have hf₂ := (linear_equiv.closed_embedding_of_injective (lin_indep_acbd cd)).tendsto_cocompact,
  convert hf₂.comp (hf₁.comp subtype.coe_injective.tendsto_cofinite) using 1,
  funext g,
  obtain ⟨g, hg⟩ := g,
  simp [mB, f₁, line_map, matrix.coord],
  simp [bottom_row] at hg,
  split,
  { ext i,
    fin_cases i,
    { simp only [add_left_inj, add_zero, eq_self_iff_true, fin.succ_zero_eq_one,
        function.comp_app, function.eval_apply, gsmul_eq_mul, int.cast_eq_zero, int.cast_inj,
        linear_map.add_apply, linear_map.coe_comp, linear_map.coe_proj, linear_map.smul_apply,
        matrix.cons_dot_product, matrix.cons_mul_vec, matrix.cons_val_zero,
        matrix.dot_product_empty, matrix.empty_mul_vec, matrix.map_apply, mul_eq_mul_left_iff,
        neg_mul_eq_neg_mul_symm, true_or, acbd, matrix.coord, matrix.vec_head,
        matrix.vec_tail],
      refl },
    { simp only [← hg, vec_head, vec_tail, add_zero, function.comp_app, gsmul_eq_mul,
        linear_map.add_apply, linear_map.smul_apply, matrix.cons_dot_product, matrix.cons_mul_vec,
        matrix.cons_val_fin_one, matrix.cons_val_one, matrix.dot_product_empty,
        matrix.empty_mul_vec, matrix.map_apply, acbd],
      norm_cast,
      convert g.det_coe_matrix.symm using 1,
      simp only [fin.coe_succ, fin.coe_zero, fin.default_eq_zero, fin.succ_succ_above_zero,
        fin.succ_zero_eq_one, fin.sum_univ_succ, fin.zero_succ_above, finset.sum_singleton,
        matrix.det_fin_zero, matrix.det_succ_row_zero, matrix.minor_apply, matrix.minor_empty,
        matrix.special_linear_group.coe_matrix_apply, mul_one, ne.def, neg_mul_eq_neg_mul_symm,
        one_mul, pow_one, pow_zero, univ_unique, zero_add],
      ring } },
  { rw ← hg,
    ext i,
    fin_cases i; refl }
end

lemma something2 (p : coprime_ints) (z : ℍ) :
  ∃ (w : ℂ), ∀ g : bottom_row ⁻¹' {p},
  ↑((g : SL(2, ℤ)) • z) = ((acbd p ↑g) : ℂ ) / (p.c ^ 2 + p.d ^ 2) + w :=
begin
  use ((p.d:ℂ )* z - p.c) /
    ((p.c ^ 2 + p.d ^ 2) * (p.c * z + p.d)),
  have nonZ1 : (p.c : ℂ) ^ 2 + (p.d) ^ 2 ≠ 0 := by exact_mod_cast p.sum_sq_ne_zero,
  have nonZ2 : (p.c : ℂ) * z + p.d ≠ 0 := by simpa using (linear_ne_zero (![p.c,p.d]) z sorry),-- z (p.ne_zero')),
  intro g,
  let acbdpg := acbd p ((((g: SL(2,ℤ)) : SL(2,ℝ )) : matrix (fin 2) (fin 2) ℝ)),
  field_simp [nonZ1, nonZ2, bottom_ne_zero, -upper_half_plane.bottom_def],
  rw (_ : (p.d:ℂ)*z - p.c = ((p.d)*z - p.c)*(g 0 0 * g 1 1 - g 0 1 * g 1 0)),
  simp,
  rw (_ : p.c = g 1 0),
  rw (_ : p.d = g 1 1),
  simp only [coe_fn_coe_base],
  -- simp,
  ring,
  { convert bottom_row_d g,
    have : p = bottom_row g := g.2.symm,
    exact this },
  { convert bottom_row_c g,
    have : p = bottom_row g := g.2.symm,
    exact this },
  { rw (_ : (g 0 0 : ℂ) * ↑(g 1 1) - ↑(g 0 1) * ↑(g 1 0) = 1),
    ring,
    norm_cast,
    convert det_SL2ℤ g using 1 },
end

lemma something1 (p : coprime_ints) (z : ℍ) :
  ∃ w, ∀ g : bottom_row ⁻¹' {p},
  ((g : SL(2, ℤ)) • z).re = (acbd p ↑g) / (p.c ^ 2 + p.d ^ 2) + w :=
begin
  obtain ⟨w, hw⟩ := something2 p z,
  use w.re,
  intros g,
  have := hw g,
  apply_fun complex.re at this,
  exact_mod_cast this,
end

/- final filter lemma, deduce from previous two results -/
lemma something' (z:ℍ) (p : coprime_ints) :
  tendsto (λ g : bottom_row ⁻¹' {p}, _root_.abs (((g : SL(2, ℤ)) • z).re)) cofinite at_top :=
begin
  suffices : tendsto (λ g : bottom_row ⁻¹' {p}, (((g : SL(2, ℤ)) • z).re)) cofinite (cocompact ℝ),
  { exact tendsto_norm_cocompact_at_top.comp this },
  obtain ⟨w, hw⟩ := something1 p z,
  have : ((p.c : ℝ) ^ 2 + p.d ^ 2)⁻¹ ≠ 0,
  { apply inv_ne_zero,
    exact_mod_cast p.sum_sq_ne_zero },
  let f := homeomorph.mul_right' _ this,
  let ff := homeomorph.add_right w,
  convert ((f.trans ff).closed_embedding.tendsto_cocompact).comp (big_thm p),
  ext g,
  convert hw g,
end

end tendsto_lemmas

/- the upshot of all the filter stuff is the following two lemmas -/

lemma exists_g_with_max_Im (z : ℍ) :
  ∃ g : SL(2,ℤ), ∀ g' : SL(2,ℤ), (g' • z).im ≤ (g • z).im :=
begin
  obtain ⟨p, hp⟩ := (finite_pairs z).exists_forall_le,
  obtain ⟨g, hg⟩ := bottom_row_surj p,
  use g,
  intros g',
  rw [im_smul_int_eq_div_norm_sq, im_smul_int_eq_div_norm_sq, div_le_div_left],
  { simpa [← hg] using hp (bottom_row g') },
  { exact z.im_pos },
  { exact normsq_bottom_pos g' z },
  { exact normsq_bottom_pos g z },
end

lemma exists_g_with_given_cd_and_min_re (z:ℍ) (cd : coprime_ints) :
  ∃ g : SL(2,ℤ), bottom_row g = cd ∧ (∀ g' : SL(2,ℤ), bottom_row g = bottom_row g' →
  _root_.abs ((g • z).re) ≤ _root_.abs ((g' • z).re)) :=
begin
  haveI : nonempty (bottom_row ⁻¹' {cd}) := let ⟨x, hx⟩ := bottom_row_surj cd in ⟨⟨x, hx⟩⟩,
  obtain ⟨g, hg⟩  := filter.tendsto.exists_forall_le (something' z cd),
  refine ⟨g, g.2, _⟩,
  { intros g1 hg1,
    have : g1 ∈ (bottom_row ⁻¹' {cd}),
    { rw [set.mem_preimage, set.mem_singleton_iff],
      exact eq.trans hg1.symm (set.mem_singleton_iff.mp (set.mem_preimage.mp g.2)) },
    exact hg ⟨g1, this⟩ },
end


def T : SL(2,ℤ) := { val := ![![1, 1], ![0, 1]], property :=
by simp [matrix.det_succ_row_zero, fin.sum_univ_succ] }

def T' : SL(2,ℤ) := { val := ![![1, -1], ![0, 1]], property :=
by simp [matrix.det_succ_row_zero, fin.sum_univ_succ] }

def S : SL(2,ℤ) := { val := ![![0, -1], ![1, 0]], property :=
by simp [matrix.det_succ_row_zero, fin.sum_univ_succ] }


def fundamental_domain : set ℍ :=
{ z | 1 ≤ (complex.norm_sq z) ∧ |(complex.re z)| ≤ (1 :ℝ)/ 2 }

def fundamental_domain_open : set ℍ :=
{ z | 1 < (complex.norm_sq z) ∧ |(complex.re z)| < (1 :ℝ)/ 2 }

notation `𝒟` := fundamental_domain

notation `𝒟ᵒ` := fundamental_domain_open

lemma whatever : 𝒟 = closure 𝒟ᵒ :=
sorry


lemma im_lt_im_S {z : ℍ} (h: norm_sq z < 1) : z.im < (S • z).im :=
begin
  have : z.im < z.im / norm_sq (z:ℂ),
  { have imz : 0 < z.im := im_pos z,
    apply (lt_div_iff z.norm_sq_pos).mpr,
    nlinarith },
  convert this,
  simp only [im_smul_int_eq_div_norm_sq],
  field_simp [normsq_bottom_ne_zero, norm_sq_nonzero, S, bottom, map_cons, comp_cons,
    cons_apply_one, cons_apply_zero],
end

lemma fun_dom_lemma₁ (z : ℍ) : ∃ g : SL(2,ℤ), g • z ∈ 𝒟 :=
begin
  -- filtery stuff tells us that we maximize im,
  obtain ⟨g₀, hg₀⟩ := exists_g_with_max_Im z,
  -- then among those, minimize re
  obtain ⟨g, hg, hg'⟩ := exists_g_with_given_cd_and_min_re z (bottom_row g₀),
  use g,
  -- `g` has same max im property as `g₀`
  have hg₀' : ∀ (g' : SL(2,ℤ)), (g' • z).im ≤ (g • z).im,
  { have hg'' : (g • z).im = (g₀ • z).im,
    { rw [im_smul_int_eq_div_norm_sq, im_smul_int_eq_div_norm_sq,
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
      { -- `bottom_row (T * g) = bottom_row g`.  Prove by a big (slow) `simp`
        simp only [bottom_row, T, vec_head, vec_tail, special_linear_group.mul_apply, mul_apply',
        cons_apply_one, cons_val_fin_one, cons_dot_product, dot_product_empty, function.comp_app,
        fin.succ_zero_eq_one, zero_mul, one_mul, add_zero, zero_add, eq_self_iff_true, and_self] },
      rw mul_action.mul_smul,
      change (g • z).re < _ at hg',
      have : |(g • z).re + 1| < |(g • z).re| :=
        by cases abs_cases ((g • z).re + 1); cases abs_cases (g • z).re; linarith,
      convert this,
      -- `(T • g • z).re = (g • z).re + 1`.  Prove by a big (slow) `simp`
      simp only [T, add_left_inj, complex.add_re, complex.of_real_int_cast,
        complex.of_real_one,  complex.of_real_zero, complex.one_re, div_one, int.cast_one,
        int.cast_zero, int.coe_cast_ring_hom, matrix.cons_val',
        matrix.cons_val_fin_one, matrix.cons_val_one, matrix.cons_val_zero, matrix.head_cons,
        matrix.map_apply, matrix.special_linear_group.coe_fun_coe,
        matrix.special_linear_group.coe_matrix_apply, one_mul, subtype.coe_mk,
        upper_half_plane.bottom_def, upper_half_plane.coe_smul_int, upper_half_plane.re_smul_int,
        upper_half_plane.top_def, zero_add, zero_mul], },
    { contrapose! hg',
      refine ⟨T' * g, _, _⟩,
      { -- `bottom_row (T' * g) = bottom_row g`.  Prove by a big (slow) `simp`
        simp only [bottom_row, T', vec_head, vec_tail, special_linear_group.mul_apply, mul_apply',
        cons_apply_one, cons_val_fin_one, cons_dot_product, dot_product_empty, function.comp_app,
        fin.succ_zero_eq_one, zero_mul, one_mul, add_zero, zero_add, eq_self_iff_true, and_self] },
      rw mul_action.mul_smul,
      change _ < (g • z).re at hg',
      have : |(g • z).re - 1| < |(g • z).re| :=
        by cases abs_cases ((g • z).re - 1); cases abs_cases (g • z).re; linarith,
      convert this,
      -- `(T' • g • z).re = (g • z).re - 1`.  Prove by a big (slow) `simp`
      simp only [T', add_left_inj, complex.add_re, complex.neg_re, complex.of_real_int_cast,
        complex.of_real_neg, complex.of_real_one, complex.of_real_zero, complex.one_re, div_one,
        eq_self_iff_true, int.cast_neg, int.cast_one,
        int.cast_zero, int.coe_cast_ring_hom, matrix.cons_val',
        matrix.cons_val_fin_one, matrix.cons_val_one, matrix.cons_val_zero, matrix.head_cons,
        matrix.map_apply, matrix.special_linear_group.coe_fun_coe,
        matrix.special_linear_group.coe_matrix_apply, one_mul, sub_eq_add_neg, subtype.coe_mk,
        upper_half_plane.bottom_def, upper_half_plane.coe_smul_int, upper_half_plane.re_smul_int,
        upper_half_plane.top_def, zero_add, zero_mul] } }
end

lemma fun_dom_lemma₂ (z : ℍ) (g : SL(2,ℤ)) (hz : z ∈ 𝒟ᵒ) (hg : g • z ∈ 𝒟ᵒ) : (z -- :ℂ
) = (g • z) :=
begin
/-
  either c=0 in which case, translation, in which case translation by 0
  or im (y) > Sqrt(3)/2 -> c=±1 and compute...
-/
  -- ext,
  have g_det : g.val.det = (g 0 0)*(g 1 1)-(g 1 0)*(g 0 1),
  {
    simp [matrix.det_succ_row_zero, fin.sum_univ_succ],
    ring,
  },

  by_cases (g 0 1 = 0),
  {
    have : ∃ (n:ℤ), g = ⟨![![1,n],![0,1]],_⟩ ∨ g = ⟨![![-1,n],![0,-1]],_⟩,
    {
      use (g 0 1),
      ext,
      have := g.2,
      rw [g_det, h, h₁.1, h₁.2] at this,

      have := g.det_coe_fun,
      sorry,
    },
    --obtain ⟨ n, hn⟩ := this,
    -- have : ((g • z):ℂ ) = z+n,

    suffices h₁ : (g 0 0 = 1 ∧ g 1 1 = 1) ∨ (g 0 0 = -1 ∧ g 1 1 = -1),
    {
      cases h₁,

    },
    -- want to argue that g=± (1 n),(0,1), so gz=z+n, and n=0
    have := g.2,

    sorry,
  },
  {
    -- want to argue first that c=± 1
    -- then show this is impossible
    sorry,
  },
 -- ALEX homework
end



-- define fundamental domain
-- open region, g.z=w -> g=1
-- all z in H, exists g in G such that g.z in closure F

-- define std domain {|z|>1, |z.re| <1/2}

-- proof std domain is a fund dom for G

-- define modular form1

-- define Eisenstein series

-- prove E-sereis are modular

-- E(z,k):= sum _{(c,d)∈ Z^2\ {0,0}} 1/(cz+d)^k


--   human:
--   d/ dz E(z,k):= sum _{(c,d)∈ Z^2\ {0,0}}  d/ dz 1/(cz+d)^k

--   OR

--   E(z,k) - E(w,k)
--   =
--   sum _{(c,d)∈ Z^2\ {0,0}}  ( 1/(cz+d)^k -  1/(cw+d)^k)
-- =
-- (z-w)   *
--   sum _{(c,d)∈ Z^2\ {0,0}}  ( 1/(cz+d)^k -  1/(cw+d)^k)

-- -

-- - define Ramanujan delta

-- -



----- THE REST is superfluous ??

-- lemma fun_dom_lemma (z:ℍ) (h: z∉𝒟) : ∃ (g: SL(2,ℤ)),
-- (|(g • z).re| < |z.re|) ∨ (complex.abs ↑(g • z) > complex.abs z) :=
-- begin
--   have : 1/2 < |z.re| ∨
-- end


-- -- keep contents but not lemma
-- lemma re_ge_half_of_act_T {z : ℍ}
-- (h: 1/2 < |(z:ℂ).re|
-- :
-- (|(T • z).re| < |z.re|) ∨
-- (|(T' • z).re| < |z.re|)
-- :=
-- begin
--   rw T_action,
--   rw T_inv_action,
--   let x := z.val.re,
--   simp,
--   rw lt_abs at h,
--   cases h,
--   { right,
--     convert (half_ge_x_T_inv ((z:ℂ).re) h),
--     exact _root_.abs_of_nonneg (by linarith) },
--   { left,
--     exact half_le_neg_x_T (z:ℂ).re h },
-- end

-- lemma is_fundom {z : ℍ} : ∃ g : SL(2,ℤ), g • z ∈ 𝒟 :=
-- begin
--   obtain ⟨g, hg2⟩ := exists_g_with_max_Im z,
--   obtain ⟨n, hn⟩ := find_appropriate_T ((g : SL(2,ℤ)) • z),
--   use (T^n * g),
--   have hS : S ∈ G' := by {apply subgroup.mem_closure', simp},
--   have hT : T ∈ G' := by {apply subgroup.mem_closure', simp},
--   have hTn : T^n ∈ G' := by {apply subgroup.gpow_mem G' hT},
-- --  have hTng : T^n * g ∈ G' := G'.mul_mem hTn hg1,
-- --  have hSTg : S * T^n * g ∈ G' := G'.mul_mem (G'.mul_mem hS hTn) hg1,
--   replace hg2 := hg2 (S * T^n * g), -- hSTg,
--   set z' := (T^n * g) • z with z'df,
--   have imz' : z'.val.im = ((g : SL(2,ℤ)) • z).val.im,
--   { rw [z'df, ← smul_smul, im_Tn_z] },
--   rw smul_smul at hn,
--   change |z'.val.re| ≤ 1 / 2 at hn,
--   suffices : 1 ≤ z'.1.norm_sq,
--   -- by exact ⟨hTn,⟨this, hn⟩⟩,
--   {
--     exact ⟨this, hn⟩,
--   },

--   set w := (S * T^n * g) • z with hw,
--   apply norm_sq_ge_one_of_act_S,
--   replace hw : w = S•z',
--   {rw [hw, z'df, smul_smul, mul_assoc]},
--   rw [imz', ← hw],
--   exact hg2,
-- end

-- @[simp]
-- lemma fundom_aux_1 {z : ℍ} (hz : z ∈ 𝒟) (h' : T • z ∈ 𝒟) : z.val.re = -1/2 := sorry

-- @[simp]
-- lemma fundom_aux_2 {z : ℍ} (hz : z ∈ 𝒟) (h' : T⁻¹ • z ∈ 𝒟) : z.val.re = 1/2 := sorry

-- @[simp]
-- lemma fundom_aux_3 {z : ℍ} (hz : z ∈ 𝒟) (h' : S • z ∈ 𝒟) : z.val.abs = 1 := sorry

-- - Why is this not doable by linarith directly? -
-- example {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : a ≤ a / b) : b ≤ 1 :=
-- begin
--   suffices: a * b ≤ a, nlinarith,
--   rw le_div_iff hb at h,
--   exact h,
-- end

-- lemma namedIs (c :ℕ ) (h: c≤ 1) :  c=0 ∨ c=1 :=
-- begin
--   cases nat.of_le_succ h,
--   {
--     left,
--     exact le_zero_iff.mp h_1,
--   },
--   right,
--   exact h_1,
-- end

-- -
-- lemma namedIsZ (c :ℤ  ) (h: c≤ 1) (h2: 0≤ c) :  c=0 ∨ c=1 :=
-- begin
--   --lift n to ℕ using hn
--   lift c to ℕ using h2,
--   norm_cast,
--   refine namedIs _ _ ,
--   exact_mod_cast h,
-- end

-- -- Describe closure of D as union of boundary segments and interior.
-- -- Then the lemma goes by cases on where z and z'

-- lemma fundom_no_repeats' (z z' : H) (h : ∃ g : SL(2,ℤ), z' = g • z) (hz : z ∈ 𝒟') (hz' : z' ∈ 𝒟') :
--   (z = z') :=
-- begin
--   sorry,
-- end

-- lemma is_fundom'' {z : H} : ∃ g : SL(2,ℤ), g • z ∈ closure fundamental_domain' :=
-- begin
--   sorry,
-- end


-- lemma fundom_no_repeats (z z' : H) (h : ∃ g : SL(2,ℤ), z' = g • z) (hz : z ∈ 𝒟) (hz' : z' ∈ 𝒟) :
--   (z = z') ∨
--   (z.val.re = -1/2 ∧ z' = T • z) ∨
--   (z'.val.re = -1/2 ∧ z = T • z') ∨
--   (z.val.abs = 1 ∧ z'.val.abs = 1 ∧ z' = S • z ∧ z = S • z') :=
-- begin
--   wlog hwlog : z.val.im ≤ z'.val.im,
--   {
--     by_cases hne : z = z', tauto,
--     right,
--     replace h := sign_coef h,
--     obtain ⟨g, hcpos, hac, hg⟩ := h,
--     set a := g.1 0 0,
--     set b := g.1 0 1,
--     set c := g.1 1 0 with ←cdf,
--     set d := g.1 1 1 with ←ddf,
--     have hcd : complex.norm_sq (c * z + d) ≤ 1,
--     {
--       have himzpos : 0 < z.val.im := im_pos_of_in_H',
--       have hnz : 0 < complex.norm_sq (c * z + d),
--       {
--         rw norm_sq_pos,
--         intro hcontra,
--         rw [← cdf, ← ddf, ← bottom_def] at hcontra,
--         exact czPd_nonZ_CP (ne.symm (ne_of_lt himzpos)) hcontra,
--       },
--       suffices: z.val.im * complex.norm_sq (c * z + d) ≤ z.val.im, nlinarith,
--       rw [hg, im_smul_SL',cdf,ddf, le_div_iff hnz] at hwlog,
--       exact hwlog,
--     },
--     have hc : _root_.abs c ≤ 1,
--     {
--       sorry
--     },
--     replace hc : c = 0 ∨ c = 1,
--     {

--       rw abs_le at hc,
--       exact namedIsZ c hc.2 hcpos,
--     },
--     rcases hc with  hc | hc ,
--     { -- case c = 0
--       have ha : a = 1 := (hac hc).2,
--       have hd : d = 1 := (hac hc).1,
--       have hgT : g = T^b,
--       {
--         rw T_pow,
--         apply subtype.eq,
--         simp,
--         tauto,
--       },
--       have hb : _root_.abs c ≤ 1,
--       {
--         sorry
--       },
--       replace hb : b = -1 ∨ b = 0 ∨ b = 1,
--       {
--         sorry
--       },
--       rcases hb with hb | hb | hb,
--       all_goals {rw hb at hgT, rw hgT at hg, clear hb, clear hgT, simp at hg},
--       {
--         right, left,
--         rw ←inv_smul_eq_iff at hg,
--         rw ←hg at hz,
--         rw fundom_aux_1 hz' hz,
--         tauto,
--       },
--       { tauto },
--       {
--         left,
--         rw hg at hz',
--         rw fundom_aux_1 hz hz',
--         tauto,
--       }
--     },
--     { -- case c = 1
--       sorry
--     }
--   },
--   obtain ⟨g, hg⟩ := h,
--   have hh : ∃ g : SL(2,ℤ), z = g • z' := ⟨g⁻¹, by {simp [eq_inv_smul_iff, hg]}⟩,
--   specialize this hh hz' hz,
--   tauto,
-- end




-- lemma bot_row_eq_diff_by_unipotent (g g' : SL(2,ℝ)) (h : bottom_row g = bottom_row g') :
-- ∃ (x:ℝ), g = (![![1,x],![0,1]],_) * g' :=
-- begin
--   -- human proof: g= a,b,c,d, g' = a' b' c d (same c d!)
--   -- then g*g⁻¹ = (a b c d)(d -b' -c a') = (1 * 0 1)

-- --  let ![![a,b],![c,d]] := g.1,
--   let Tn := g * g'⁻¹,
--   sorry,

-- end
