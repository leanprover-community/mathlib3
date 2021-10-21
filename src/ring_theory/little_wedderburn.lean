import ring_theory.integral_domain
import group_theory.group_action.conj_act
import ring_theory.polynomial.cyclotomic
import tactic.by_contra

noncomputable theory
open_locale classical nnreal big_operators

-- move this
lemma fintype.card_pos (X : Type*) [h : nonempty X] [fintype X] : 0 < fintype.card X :=
fintype.card_pos_iff.mpr h

-- move this
@[simps] def complex.abs_hom : ℂ →* ℝ :=
{ to_fun := complex.abs,
  map_one' := complex.abs_one,
  map_mul' := complex.abs_mul }

@[simp] lemma complex.abs_prod {ι : Type*} (s : finset ι) (f : ι → ℂ) :
  complex.abs (s.prod f) = s.prod (λ i, complex.abs (f i)) :=
complex.abs_hom.map_prod _ _

lemma complex.sq_abs (z : ℂ) : z.abs ^ 2 = z.re ^ 2 + z.im ^ 2 :=
by { rw [complex.abs, real.sq_sqrt, complex.norm_sq_apply, pow_two, pow_two],
  exact complex.norm_sq_nonneg _ }

@[simp] lemma complex.nnnorm_coe_real (r : ℝ) : ∥(r : ℂ)∥₊ = ∥r∥₊ :=
by { ext, simp only [complex.norm_real, coe_nnnorm], }

@[simp] lemma complex.nnnorm_nat_cast (n : ℕ) : ∥(n : ℂ)∥₊ = n :=
by { rw [← real.nnnorm_coe_nat, ← complex.nnnorm_coe_real], norm_cast, }

@[simp] lemma complex.nnnorm_int_cast (n : ℤ) : ∥(n : ℂ)∥₊ = ∥n∥₊ :=
begin
  by_cases hn : 0 ≤ n,
  { lift n to ℕ using hn,
    rw [int.cast_coe_nat, complex.nnnorm_nat_cast, ← nnreal.coe_nat_abs, int.nat_abs_of_nat], },
  { lift -n to ℕ with k hk, swap, { push_neg at hn, rw neg_nonneg, exact hn.le },
    rw [← nnnorm_neg, ← int.cast_neg, ← hk, ← nnnorm_neg n, ← hk],
    rw [int.cast_coe_nat, complex.nnnorm_nat_cast, ← nnreal.coe_nat_abs, int.nat_abs_of_nat], },
end

lemma complex.nnnorm_eq_one_of_pow_eq_one {ζ : ℂ} {n : ℕ} (h : ζ ^ n = 1) (hn : n ≠ 0) :
  ∥ζ∥₊ = 1 :=
begin
  refine (@pow_left_inj ℝ≥0 _ _ _ _ zero_le' zero_le' hn.bot_lt).mp _,
  rw [← normed_field.nnnorm_pow, h, nnnorm_one, one_pow],
end

lemma complex.norm_eq_one_of_pow_eq_one {ζ : ℂ} {n : ℕ} (h : ζ ^ n = 1) (hn : n ≠ 0) :
  ∥ζ∥ = 1 :=
congr_arg coe (complex.nnnorm_eq_one_of_pow_eq_one h hn)

lemma is_primitive_root.norm_eq_one {ζ : ℂ} {n : ℕ} (h : is_primitive_root ζ n) (hn : n ≠ 0) :
  ∥ζ∥ = 1 :=
complex.norm_eq_one_of_pow_eq_one h.pow_eq_one hn

lemma fintype.card_conj_act (G : Type*) [fintype G] : fintype.card (conj_act G) = fintype.card G :=
rfl

namespace polynomial

lemma cyclotomic_dvd_X_pow_sub_one (n : ℕ) (hn : n ≠ 0) (R : Type*) [comm_ring R] :
  cyclotomic n R ∣ X ^ n - 1 :=
begin
  rw ← prod_cyclotomic_eq_X_pow_sub_one hn.bot_lt R,
  apply finset.dvd_prod_of_mem,
  rw nat.mem_divisors,
  exact ⟨dvd_rfl, hn⟩
end

end polynomial

namespace little_wedderburn

section cyclotomic
open polynomial

lemma nat_cast_pow_eq_one (R : Type*) [comm_semiring R] [char_zero R]
  (q : ℕ) (n : ℕ) (hn : n ≠ 0) :
  (q : R) ^ n = 1 ↔ q = 1 :=
begin
  split, swap, { rintro rfl, rw [nat.cast_one, one_pow], },
  intro H, have : q ^ n = 1 ^ n, { rw one_pow, exact_mod_cast H },
  rwa pow_left_inj (nat.zero_le _) (nat.zero_le _) hn.bot_lt at this,
end

lemma sub_one_lt_nat_abs_cyclotomic_eval (n : ℕ) (q : ℕ) (hn : 1 < n) (hq : 2 ≤ q) :
  q - 1 < int.nat_abs ((cyclotomic n ℤ).eval ↑q) :=
begin
  rw ← @nat.cast_lt ℝ≥0,
  calc ↑(q - 1)
      < ∥(cyclotomic n ℂ).eval ↑q∥₊ : _
  ... = (int.nat_abs ((cyclotomic n ℤ).eval ↑q) : ℝ≥0) : _,
  swap,
  { rw [← map_cyclotomic_int, eval_map, eval₂_at_nat_cast, ring_hom.eq_int_cast,
      int.nat_cast_eq_coe_nat, nnreal.coe_nat_abs, complex.nnnorm_int_cast], },
  have hn' : 0 < n := zero_lt_one.trans hn,
  let ζ := complex.exp (2 * ↑real.pi * complex.I / ↑n),
  have hζ : is_primitive_root ζ n := complex.is_primitive_root_exp n hn'.ne',
  have hζ' : ζ ∈ primitive_roots n ℂ, { rwa mem_primitive_roots hn', },
  have norm_ζ : ∥ζ∥ = 1 := hζ.norm_eq_one hn'.ne',
  rw [cyclotomic_eq_prod_X_sub_primitive_roots hζ, eval_prod, normed_field.nnnorm_prod],
  simp only [eval_C, eval_X, ring_hom.eq_int_cast, eval_sub],
  rw [← finset.prod_sdiff (finset.singleton_subset_iff.mpr hζ'), finset.prod_singleton],
  rw ← one_mul ↑(q - 1), swap, apply_instance,
  have aux : 1 ≤ ∏ (x : ℂ) in primitive_roots n ℂ \ {ζ}, ∥↑q - x∥₊,
  { apply finset.one_le_prod',
    intros x hx,
    rw ← nnreal.coe_le_coe,
    refine le_trans _ (norm_sub_norm_le _ _),
    simp only [finset.mem_sdiff, finset.mem_singleton, mem_primitive_roots hn'] at hx,
    simp only [nonneg.coe_one, complex.norm_nat, hx.1.norm_eq_one hn'.ne', le_sub_iff_add_le],
    exact_mod_cast hq, },
  refine mul_lt_mul' aux _ zero_le' (lt_of_lt_of_le zero_lt_one aux),
  rw [← nnreal.coe_lt_coe, coe_nnnorm, nnreal.coe_nat_cast, complex.norm_eq_abs],
  refine lt_of_lt_of_le _ (complex.re_le_abs _),
  rw [nat.cast_sub (one_le_two.trans hq), nat.cast_one, complex.sub_re],
  simp only [complex.nat_cast_re, sub_lt_sub_iff_left],
  rw [complex.norm_eq_abs, complex.abs,
    real.sqrt_eq_iff_sq_eq (complex.norm_sq_nonneg _) zero_le_one,
    one_pow, complex.norm_sq_apply] at norm_ζ,
  rcases lt_trichotomy ζ.re 1 with (H|H|H),
  { exact H },
  { simp only [H, mul_one, self_eq_add_right, or_self, mul_eq_zero] at norm_ζ,
    have : ζ = 1, { ext, assumption' }, rw this at hζ,
    refine (hζ.pow_ne_one_of_pos_of_lt zero_lt_one hn _).elim, rw pow_one },
  { refine (ne_of_lt _ norm_ζ).elim, nlinarith }
end

end cyclotomic

variables (D : Type*) [division_ring D] [fintype D]
variables {D}

@[simps]
def center_units_to_center (u : subgroup.center (units D)) : subring.center D :=
⟨u, λ r,
begin
  by_cases hr : r = 0, { subst r, rw [mul_zero, zero_mul] },
  exact congr_arg coe (u.2 (units.mk0 r hr)),
end⟩

def center_units_to_units_center (u : subgroup.center (units D)) : units (subring.center D) :=
⟨center_units_to_center u, center_units_to_center u⁻¹,
by { ext, simp only [subring.coe_mul, subring.coe_one, units.coe_inv', subgroup.coe_inv,
  units.mul_inv', center_units_to_center_coe, coe_coe], },
by { ext, simp only [subring.coe_mul, subring.coe_one, units.coe_inv', units.inv_mul',
  subgroup.coe_inv, center_units_to_center_coe, coe_coe], }⟩

variables (D)

-- move this
@[simps]
def center_units_equiv_units_center :
  subgroup.center (units D) ≃* units (subring.center D) :=
{ to_fun := center_units_to_units_center,
  inv_fun := λ u, ⟨units.map (subring.center D).subtype.to_monoid_hom u, λ r,
    by { ext, simp only [subring.coe_subtype, units.coe_map, ring_hom.coe_monoid_hom,
      ring_hom.to_monoid_hom_eq_coe, units.coe_mul],
      exact u.1.2 _ }⟩,
  left_inv := λ u, by { ext, refl },
  right_inv := λ u, by { ext, refl },
  map_mul' := λ x y, by { ext, refl } }

def induction_hyp : Prop :=
∀ R : subring D, R < ⊤ → ∀ ⦃x y⦄, x ∈ R → y ∈ R → x * y = y * x

namespace induction_hyp
open finite_dimensional polynomial

variables {D}

protected def field (hD : induction_hyp D) (R : subring D) (hR : R < ⊤) : field R :=
{ mul_comm := λ x y, subtype.ext $ hD R hR x.2 y.2,
  ..(show division_ring R, from division_ring_of_domain R)}

lemma center_eq_top (hD : induction_hyp D) : subring.center D = ⊤ :=
begin
  set Z := subring.center D,
  by_contra hZ, replace hZ := ne.lt_top hZ,
  letI : field Z := hD.field Z hZ,
  set q := fintype.card Z with card_Z,
  have hq : 2 ≤ q, { rw card_Z, exact fintype.one_lt_card },
  have h1q : 1 ≤ q := one_le_two.trans hq,
  let n := finrank Z D,
  have hn : 1 < n,
  { by_contra' hn : n ≤ 1,
    rw finrank_le_one_iff at hn,
    rcases hn with ⟨x, hx⟩,
    refine not_le_of_lt hZ _,
    rintro y - z,
    obtain ⟨r, rfl⟩ := hx y, obtain ⟨s, rfl⟩ := hx z,
    show (s.1 * x) * (r.1 * x) = (r.1 * x) * (s.1 * x),
    rw [← r.2, ← s.2, mul_assoc, mul_assoc, ← r.2, ← s.2, mul_assoc, mul_assoc, r.2], },
  have h0n : 0 < n := zero_lt_one.trans hn,
  have card_D : fintype.card D = q ^ n := card_eq_pow_finrank,
  have h1qn : 1 ≤ q ^ n, { rw ← card_D, exact fintype.card_pos _ },
  have key := class_equation (units D),
  simp only [nat.card_eq_fintype_card] at key,
  rw [fintype.card_congr (center_units_equiv_units_center D).to_equiv,
    finite_field.card_units, ← card_Z, finite_field.card_units, card_D] at key,
  let Φ := cyclotomic n ℤ,
  have aux : Φ.eval q ∣ q^n - 1,
  { simpa only [eval_X, eval_one, eval_pow, eval_sub, coe_eval_ring_hom] using
      (eval_ring_hom (q : ℤ)).map_dvd (cyclotomic_dvd_X_pow_sub_one n h0n.ne' ℤ), },
  apply_fun (coe : ℕ → ℤ) at key,
  simp only [nat.cast_one, nat.cast_pow,
    ←int.nat_cast_eq_coe_nat, nat.cast_add, nat.cast_sub h1qn] at key aux,
  rw [← key, ← dvd_add_iff_left, ← int.nat_abs_dvd, ← int.dvd_nat_abs] at aux,
  simp only [int.nat_cast_eq_coe_nat, int.nat_abs_of_nat, int.coe_nat_dvd] at aux,
  { refine not_lt_of_ge (nat.le_of_dvd _ aux) (sub_one_lt_nat_abs_cyclotomic_eval _ _ hn hq),
    exact nat.sub_pos_of_lt hq },
  suffices : Φ.eval q ∣ ↑∑ x in (conj_classes.noncenter (units D)).to_finset,fintype.card x.carrier,
  { simp only [int.nat_cast_eq_coe_nat] at this ⊢,
    convert this using 2, convert finsum_cond_eq_sum_of_cond_iff _ _,
    simp only [iff_self, set.mem_to_finset, implies_true_iff] },
  simp only [← int.nat_cast_eq_coe_nat, nat.cast_sum],
  apply finset.dvd_sum,
  rintro ⟨x⟩ hx,
  simp only [int.nat_cast_eq_coe_nat, conj_classes.quot_mk_eq_mk],
  rw [card_carrier, fintype.card_conj_act, finite_field.card_units, card_D],
  sorry
end

end induction_hyp

end little_wedderburn
