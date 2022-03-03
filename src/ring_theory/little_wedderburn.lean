/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import group_theory.group_action.conj_act
import ring_theory.polynomial.cyclotomic.eval
import ring_theory.centralizer
import tactic.by_contra

/-!
# Little Wedderburn TODO
-/

open_locale nnreal big_operators polynomial

section pr12428

@[simp] lemma complex.nnnorm_coe_real (r : ℝ) : ∥(r : ℂ)∥₊ = ∥r∥₊ :=
subtype.ext $ by simp only [complex.norm_real, coe_nnnorm]

@[simp] lemma complex.nnnorm_nat_cast (n : ℕ) : ∥(n : ℂ)∥₊ = n :=
by rw [← real.nnnorm_coe_nat, ← complex.nnnorm_coe_real, complex.of_real_nat_cast]

@[simp] lemma complex.nnnorm_int_cast (n : ℤ) : ∥(n : ℂ)∥₊ = ∥n∥₊ :=
begin
  obtain ⟨k, rfl | rfl⟩ := int.eq_coe_or_neg n,
  { rw [int.cast_coe_nat, complex.nnnorm_nat_cast, ← nnreal.coe_nat_abs, int.nat_abs_of_nat] },
  { rw [int.cast_neg, nnnorm_neg, nnnorm_neg, int.cast_coe_nat, complex.nnnorm_nat_cast,
        ←nnreal.coe_nat_abs, int.nat_abs_of_nat], },
end

lemma complex.nnnorm_eq_one_of_pow_eq_one {ζ : ℂ} {n : ℕ} (h : ζ ^ n = 1) (hn : n ≠ 0) :
  ∥ζ∥₊ = 1 :=
begin
  refine (@pow_left_inj ℝ≥0 _ _ _ _ zero_le' zero_le' hn.bot_lt).mp _,
  rw [←nnnorm_pow, h, nnnorm_one, one_pow],
end

lemma complex.norm_eq_one_of_pow_eq_one {ζ : ℂ} {n : ℕ} (h : ζ ^ n = 1) (hn : n ≠ 0) :
  ∥ζ∥ = 1 :=
congr_arg coe (complex.nnnorm_eq_one_of_pow_eq_one h hn)

lemma is_primitive_root.nnnorm_eq_one {ζ : ℂ} {n : ℕ} (h : is_primitive_root ζ n) (hn : n ≠ 0) :
  ∥ζ∥ = 1 :=
complex.norm_eq_one_of_pow_eq_one h.pow_eq_one hn

end pr12428

/-- The ring homomorphism associated to an inclusion of subrings. -/
def subring.inclusion' {R : Type*} [ring R] {S T : subring R} (h : S ≤ T) : S →+* T :=
S.subtype.cod_restrict' _ (λ x, h x.2)

namespace little_wedderburn

section cyclotomic
open polynomial

lemma sub_one_lt_nat_abs_cyclotomic_eval (n : ℕ) (q : ℕ) (hn' : 1 < n) (hq' : q ≠ 1) :
  q - 1 < ((cyclotomic n ℤ).eval ↑q).nat_abs :=
begin
  have : _ ∨ 2 ≤ q := (iff_iff_not_or_and_or_not.mp nat.one_lt_iff_ne_zero_and_ne_one).2.symm,
  simp only [not_and_distrib, ne.def, not_not] at this,
  rcases this with (rfl | rfl) | hq,
  { rw [zero_tsub, int.coe_nat_zero, ←coeff_zero_eq_eval_zero, cyclotomic_coeff_zero _ hn'],
    norm_num },
  { exact (hq' rfl).elim },
  rw [←@nat.cast_lt ℝ≥0],
  calc ↑(q - 1)
      < ∥(cyclotomic n ℂ).eval ↑q∥₊ : _
  ... = (int.nat_abs ((cyclotomic n ℤ).eval ↑q) : ℝ≥0) :
  by rw [← map_cyclotomic_int, eval_map, eval₂_at_nat_cast, ring_hom.eq_int_cast,
         int.nat_cast_eq_coe_nat, nnreal.coe_nat_abs, complex.nnnorm_int_cast],
  have hn : 0 < n := pos_of_gt hn',
  let ζ := complex.exp (2 * ↑real.pi * complex.I / ↑n),
  have hζ : is_primitive_root ζ n := complex.is_primitive_root_exp n hn.ne',
  have norm_ζ : ∥ζ∥ = 1 := hζ.nnnorm_eq_one hn.ne',
  rw [cyclotomic_eq_prod_X_sub_primitive_roots hζ, eval_prod, nnnorm_prod],
  simp only [eval_C, eval_X, ring_hom.eq_int_cast, eval_sub],
  rw [←finset.prod_sdiff (finset.singleton_subset_iff.mpr $ (mem_primitive_roots hn).mpr hζ),
      finset.prod_singleton, ←one_mul (↑(q - 1) : ℝ≥0)],
  have aux : 1 ≤ ∏ (x : ℂ) in primitive_roots n ℂ \ {ζ}, ∥↑q - x∥₊,
  { apply finset.one_le_prod',
    intros x hx,
    rw ← nnreal.coe_le_coe,
    refine le_trans _ (norm_sub_norm_le _ _),
    simp only [finset.mem_sdiff, finset.mem_singleton, mem_primitive_roots hn] at hx,
    simp only [nonneg.coe_one, complex.norm_nat, hx.1.nnnorm_eq_one hn.ne', le_sub_iff_add_le],
    exact_mod_cast hq },
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
    have : ζ = 1, { ext, assumption' },
    rw this at hζ,
    exact (hζ.pow_ne_one_of_pos_of_lt zero_lt_one hn' $ by rw pow_one).elim },
  { refine (ne_of_lt _ norm_ζ).elim,
    nlinarith }
end

-- #12426
lemma cyclotomic_dvd_geom_sum_of_dvd {R} [comm_ring R] [is_domain R] {d n : ℕ} (hdn : d ∣ n)
  (hd : d ≠ 1) : cyclotomic d R ∣ geom_sum X n :=
begin
  rcases n.eq_zero_or_pos with rfl | hn,
  { simp },
  rw ←prod_cyclotomic_eq_geom_sum hn,
  apply finset.dvd_prod_of_mem,
  simp [hd, hdn, hn.ne']
end

-- #12426
lemma X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd {R : Type*} [comm_ring R] {d n : ℕ}
  (hd : d ∣ n) (hdn : d < n) : (X ^ d - 1) * cyclotomic n R ∣ X ^ n - 1 :=
begin
  rcases n.eq_zero_or_pos with rfl | h0n,
  { simp },
  rcases d.eq_zero_or_pos with rfl | h0d,
  { linarith [eq_zero_of_zero_dvd hd] },
  rw [←prod_cyclotomic_eq_X_pow_sub_one h0d, ←prod_cyclotomic_eq_X_pow_sub_one h0n,
      mul_comm, ←finset.prod_insert $ λ h, hdn.not_le $ nat.divisor_le h],
  refine finset.prod_dvd_prod_of_subset _ _ _ (λ k hk, _),
  rcases finset.mem_insert.mp hk with (rfl | hkd),
  { exact k.mem_divisors_self h0n.ne' },
  { exact nat.divisors_subset_of_dvd h0n.ne' hd hkd }
end

-- todo: move into proof
lemma cyclotomic_eval_dvd_pow_sub_one_div_pow_sub_one_of_dvd (q d n : ℕ)
  (hd : d ∣ n) (hdn : d < n) : (cyclotomic n ℤ).eval q ∣ (q ^ n - 1) / (q ^ d - 1) :=
begin
  apply int.dvd_div_of_mul_dvd,
  have aux : ∀ {k : ℕ}, ((X : ℤ[X]) ^ k - 1).eval q = q ^ k - 1,
  { simp only [eval_X, eval_one, eval_pow, eval_sub, eq_self_iff_true, forall_const] },
  rw [← aux, ← aux, ← eval_mul],
  exact (eval_ring_hom ↑q).map_dvd (X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd hd hdn),
end

end cyclotomic

variables (D : Type*) [division_ring D] [fintype D]
variables {R : Type*} [ring R]
variables {D}

def units_centralizer_to_stabilizer (x : units D) :
  units (subring.centralizer (x : D)) → mul_action.stabilizer (conj_act $ units D) x :=
λ u, ⟨conj_act.to_conj_act (units.map (subring.centralizer (x:D)).subtype.to_monoid_hom u),
  by { show _ • _ = _, rw conj_act.smul_def,
    simp only [conj_act.of_conj_act_to_conj_act, ring_hom.to_monoid_hom_eq_coe],
    rw mul_inv_eq_iff_eq_mul, ext, exact u.1.2.symm, }⟩

def stabilizer_units_to_centralizer (x : units D) :
  mul_action.stabilizer (conj_act $ units D) x → subring.centralizer (x : D) :=
λ u, ⟨↑(conj_act.of_conj_act u.1 : units D),
  by { show _ = _, have : _ • _ = _ := u.2,
    rw [conj_act.smul_def, mul_inv_eq_iff_eq_mul, units.ext_iff] at this,
    exact this.symm }⟩

def stabilizer_units_to_units_centralizer (x : units D) :
  mul_action.stabilizer (conj_act $ units D) x → units (subring.centralizer (x : D)) :=
λ u, ⟨stabilizer_units_to_centralizer x u,
      stabilizer_units_to_centralizer x u⁻¹,
      by { ext, simp only [stabilizer_units_to_centralizer, conj_act.of_conj_act_inv,
        subring.coe_mul, set_like.coe_mk, subring.coe_one, units.coe_inv',
        subgroup.coe_inv, units.mul_inv', subtype.val_eq_coe], },
      by { ext, simp only [stabilizer_units_to_centralizer, conj_act.of_conj_act_inv,
        subring.coe_mul, set_like.coe_mk, subring.coe_one, units.coe_inv',
        units.inv_mul', subgroup.coe_inv, subtype.val_eq_coe], }⟩

def units_centralizer_equiv (x : units D) :
  units (subring.centralizer (x : D)) ≃* mul_action.stabilizer (conj_act $ units D) x :=
{ to_fun := units_centralizer_to_stabilizer x,
  inv_fun := stabilizer_units_to_units_centralizer x,
  left_inv := λ u, by { ext, refl },
  right_inv := λ u, by { ext, refl },
  map_mul' := λ x y, by { ext, refl } }

lemma mem_center_units_of_coe_mem_center (x : units R) (h : (x : R) ∈ subring.center R) :
  x ∈ subgroup.center (units R) :=
λ y, units.ext $ h y

@[simps]
def center_units_to_center (u : subgroup.center (units D)) : subring.center D :=
⟨u, λ r,
begin
  rcases eq_or_ne r 0 with rfl | hr,
  { rw [mul_zero, zero_mul] },
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

open_locale classical

protected noncomputable def field (hD : induction_hyp D) (R : subring D) (hR : R < ⊤) : field R :=
{ mul_comm := λ x y, subtype.ext $ hD R hR x.2 y.2,
  ..(show division_ring R, from fintype.division_ring_of_is_domain R)}

lemma center_eq_top (hD : induction_hyp D) : subring.center D = ⊤ :=
begin
  set Z := subring.center D,
  by_contra hZ,
  replace hZ := ne.lt_top hZ,
  letI : field Z := hD.field Z hZ,
  set q := fintype.card Z with card_Z,
  have hq : 1 < q, { rw card_Z, exact fintype.one_lt_card },
  have h1q : 1 ≤ q := one_le_two.trans hq,
  let n := finrank Z D,
  cases le_or_lt n 1 with hn hn,
  { rw finrank_le_one_iff at hn,
    rcases hn with ⟨x, hx⟩,
    refine not_le_of_lt hZ _,
    rintro y - z,
    obtain ⟨r, rfl⟩ := hx y, obtain ⟨s, rfl⟩ := hx z,
    show (s.1 * x) * (r.1 * x) = (r.1 * x) * (s.1 * x),
    rw [← r.2, ← s.2, mul_assoc, mul_assoc, ← r.2, ← s.2, mul_assoc, mul_assoc, r.2] },
  have card_D : fintype.card D = q ^ n := card_eq_pow_finrank,
  have h1qn : 1 ≤ q ^ n, { rw ← card_D, exact fintype.card_pos },
  have key := class_equation (units D),
  simp only [nat.card_eq_fintype_card] at key,
  rw [fintype.card_congr (center_units_equiv_units_center D).to_equiv,
    fintype.card_units, ← card_Z, fintype.card_units, card_D] at key,
  let Φ := cyclotomic n ℤ,
  have aux : Φ.eval q ∣ q ^ n - 1,
  { simpa only [eval_X, eval_one, eval_pow, eval_sub, coe_eval_ring_hom]
    using (eval_ring_hom (q : ℤ)).map_dvd (cyclotomic.dvd_X_pow_sub_one n ℤ) },
  apply_fun (coe : ℕ → ℤ) at key,
  simp only [nat.cast_one, nat.cast_pow,
    ←int.nat_cast_eq_coe_nat, nat.cast_add, nat.cast_sub h1qn] at key aux,
  rw [← key, ← dvd_add_iff_left, ← int.nat_abs_dvd, ← int.dvd_nat_abs] at aux,
  simp only [int.nat_cast_eq_coe_nat, int.nat_abs_of_nat, int.coe_nat_dvd] at aux,
  { refine not_lt_of_ge (nat.le_of_dvd _ aux) (sub_one_lt_nat_abs_cyclotomic_eval _ _ hn hq.ne'),
    exact nat.sub_pos_of_lt hq },
  suffices : Φ.eval q ∣ ↑∑ x in (conj_classes.noncenter (units D)).to_finset,fintype.card x.carrier,
  { simp only [int.nat_cast_eq_coe_nat] at this ⊢,
    convert this using 2, convert finsum_cond_eq_sum_of_cond_iff _ _,
    simp only [iff_self, set.mem_to_finset, implies_true_iff] },
  simp only [← int.nat_cast_eq_coe_nat, nat.cast_sum],
  apply finset.dvd_sum,
  rintro ⟨x⟩ hx,
  simp only [int.nat_cast_eq_coe_nat, conj_classes.quot_mk_eq_mk],
  rw [card_carrier, conj_act.card, fintype.card_units, card_D,
      ←fintype.card_congr (units_centralizer_equiv x).to_equiv],
  set Zx := subring.centralizer (x:D),
  have hZx : Zx < ⊤,
  { rw lt_top_iff_ne_top,
    intro hZx,
    have Hx := mem_center_units_of_coe_mem_center _
      (subring.mem_center_of_centralizer_eq_top hZx),
    simp only [set.mem_to_finset, conj_classes.quot_mk_eq_mk] at hx,
    exact (conj_classes.mk_bij_on (units D)).1 Hx hx },
  letI : field Zx := hD.field _ hZx,
  letI : algebra Z Zx := (subring.inclusion' $ subring.center_le_centralizer (x : D)).to_algebra,
  let d := finrank Z Zx,
  have card_Zx : fintype.card Zx = q ^ d := card_eq_pow_finrank,
  have h1qd : 1 ≤ q ^ d, { rw ← card_Zx, exact fintype.card_pos },
  haveI : is_scalar_tower Z Zx D := ⟨λ x y z, mul_assoc _ _ _⟩,
  have hdn : d ∣ n := ⟨_, (finrank_mul_finrank Z Zx D).symm⟩,
  rw [fintype.card_units, card_Zx, int.coe_nat_div],
  simp only [←int.nat_cast_eq_coe_nat, nat.cast_sub h1qd, nat.cast_sub h1qn,
    nat.cast_one, nat.cast_pow],
  simp only [int.nat_cast_eq_coe_nat],
  apply cyclotomic_eval_dvd_pow_sub_one_div_pow_sub_one_of_dvd _ _ _ hdn,
  rw [← (nat.pow_right_strict_mono hq).lt_iff_lt],
  dsimp,
  rw [← card_D, ← card_Zx],
  obtain ⟨b, -, hb⟩ := set_like.exists_of_lt hZx,
  refine fintype.card_lt_of_injective_of_not_mem _ subtype.val_injective _,
  exact b,
  simp only [not_exists, set.mem_range, subtype.val_eq_coe],
  rintro y rfl, exact hb y.2
end

end induction_hyp

lemma center_eq_top : subring.center D = ⊤ :=
begin
  classical,
  suffices : ∀ (n : ℕ) (D : Type*) [division_ring D] [fintype D],
    by exactI fintype.card D ≤ n → subring.center D = ⊤,
  { exact this _ D le_rfl },
  unfreezingI { clear_dependent D },
  intro n, apply nat.strong_induction_on n, clear n,
  introsI n IH D _D_dr _D_fin hD,
  apply induction_hyp.center_eq_top,
  intros R hR x y hx hy,
  suffices : (⟨y,hy⟩ : R) ∈ subring.center R,
  { exact congr_arg subtype.val (this ⟨x, hx⟩), },
  letI R_dr : division_ring R := fintype.division_ring_of_is_domain R,
  rw IH (fintype.card R) _ R le_rfl, { trivial },
  obtain ⟨b, -, hb⟩ := set_like.exists_of_lt hR,
  refine (fintype.card_lt_of_injective_of_not_mem _ subtype.val_injective _).trans_le hD,
  { exact b },
  simp only [not_exists, set.mem_range, subtype.val_eq_coe],
  rintro y rfl,
  exact hb y.2
end

end little_wedderburn

def little_wedderburn (D : Type*) [hD : division_ring D] [fintype D] :
  field D :=
{ mul_comm := λ x y,
  suffices y ∈ subring.center D, from this x,
  by { rw little_wedderburn.center_eq_top, trivial },
  .. hD }
