/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import group_theory.group_action.class_formula
import group_theory.group_action.conj_act
import ring_theory.polynomial.cyclotomic.eval
import ring_theory.centralizer
import tactic.by_contra

/-!
# Little Wedderburn TODO
-/

open_locale nnreal big_operators polynomial

namespace little_wedderburn

variables (D : Type*) [division_ring D]
variables {R : Type*} [ring R]
variables {D}

def units_centralizer_to_stabilizer (x : units D) :
  units (subring.centralizer ({x} : set D)) → mul_action.stabilizer (conj_act $ units D) x :=
λ u, ⟨conj_act.to_conj_act (units.map (subring.centralizer ({x} : set D)).subtype.to_monoid_hom u),
  by { show _ • _ = _, rw conj_act.smul_def,
    simp only [conj_act.of_conj_act_to_conj_act, ring_hom.to_monoid_hom_eq_coe],
    rw mul_inv_eq_iff_eq_mul, ext,
    exact (u.1.2 x (set.mem_singleton x)).symm }⟩

def stabilizer_units_to_centralizer (x : units D) :
  mul_action.stabilizer (conj_act $ units D) x → subring.centralizer ({x} : set D) :=
λ u, ⟨↑(conj_act.of_conj_act u.1 : units D),
  by { rintro x ⟨rfl⟩, have : _ • _ = _ := u.2,
    rw [conj_act.smul_def, mul_inv_eq_iff_eq_mul, units.ext_iff] at this,
    exact this.symm }⟩

def stabilizer_units_to_units_centralizer (x : units D) :
  mul_action.stabilizer (conj_act $ units D) x → units (subring.centralizer ({x} : set D)) :=
λ u, ⟨stabilizer_units_to_centralizer x u,
      stabilizer_units_to_centralizer x u⁻¹,
      by { ext, simp only [stabilizer_units_to_centralizer, conj_act.of_conj_act_inv,
        subring.coe_mul, set_like.coe_mk, subring.coe_one, units.coe_inv,
        subgroup.coe_inv, units.mul_inv', subtype.val_eq_coe], },
      by { ext, simp only [stabilizer_units_to_centralizer, conj_act.of_conj_act_inv,
        subring.coe_mul, set_like.coe_mk, subring.coe_one, units.coe_inv,
        units.inv_mul', subgroup.coe_inv, subtype.val_eq_coe], }⟩

def units_centralizer_equiv (x : units D) :
  units (subring.centralizer ({x} : set D)) ≃* mul_action.stabilizer (conj_act $ units D) x :=
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
by { ext, simp only [subring.coe_mul, subring.coe_one, units.coe_inv, subgroup.coe_inv,
  units.mul_inv', center_units_to_center_coe, coe_coe], },
by { ext, simp only [subring.coe_mul, subring.coe_one, units.coe_inv, units.inv_mul',
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

variables {D} [fintype D]

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
  simp only [nat.cast_one, nat.cast_pow, nat.cast_add, nat.cast_sub h1qn] at key aux,
  rw [← key, dvd_add_left, ← int.nat_abs_dvd, ← int.dvd_nat_abs] at aux,
  simp only [int.nat_abs_of_nat, int.coe_nat_dvd] at aux,
  { refine (nat.le_of_dvd _ aux).not_lt (sub_one_lt_nat_abs_cyclotomic_eval hn hq.ne'),
    exact tsub_pos_of_lt hq },
  suffices : Φ.eval q ∣ ↑∑ x in (conj_classes.noncenter (units D)).to_finset,fintype.card x.carrier,
  { convert this using 2,
    convert finsum_cond_eq_sum_of_cond_iff _ _,
    simp only [iff_self, set.mem_to_finset, implies_true_iff] },
  simp only [nat.cast_sum],
  apply finset.dvd_sum,
  rintro ⟨x⟩ hx,
  simp only [conj_classes.quot_mk_eq_mk],
  rw [card_carrier, conj_act.card, fintype.card_units, card_D,
      ←fintype.card_congr (units_centralizer_equiv x).to_equiv],
  set Zx := subring.centralizer ({x} : set D),
  have hZx : Zx < ⊤,
  { rw lt_top_iff_ne_top,
    intro hZx,
    have Hx := mem_center_units_of_coe_mem_center _
      (subring.mem_center_of_centralizer_eq_top hZx),
    simp only [set.mem_to_finset, conj_classes.quot_mk_eq_mk] at hx,
    exact (conj_classes.mk_bij_on (units D)).1 Hx hx },
  letI : field Zx := hD.field _ hZx,
  letI : algebra Z Zx :=
    (subring.inclusion $ subring.center_le_centralizer ({x} : set D)).to_algebra,
  let d := finrank Z Zx,
  have card_Zx : fintype.card Zx = q ^ d := card_eq_pow_finrank,
  have h1qd : 1 ≤ q ^ d, { rw ← card_Zx, exact fintype.card_pos },
  haveI : is_scalar_tower Z Zx D := ⟨λ x y z, mul_assoc _ _ _⟩,
  have hdn : d ∣ n := ⟨_, (finrank_mul_finrank Z Zx D).symm⟩,
  rw [fintype.card_units, card_Zx, int.coe_nat_div],
  simp only [nat.cast_sub h1qd, nat.cast_sub h1qn, nat.cast_one, nat.cast_pow],
  suffices hd : d < n,
  { apply int.dvd_div_of_mul_dvd,
    have aux : ∀ {k : ℕ}, ((X : ℤ[X]) ^ k - 1).eval q = q ^ k - 1,
    { simp only [eval_X, eval_one, eval_pow, eval_sub, eq_self_iff_true, forall_const] },
    rw [← aux, ← aux, ← eval_mul],
    refine (eval_ring_hom ↑q).map_dvd (X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd ℤ _),
    exact nat.mem_proper_divisors.mpr ⟨hdn, hd⟩ },
  rw [← (nat.pow_right_strict_mono hq).lt_iff_lt],
  dsimp,
  rw [← card_D, ← card_Zx],
  obtain ⟨b, -, hb⟩ := set_like.exists_of_lt hZx,
  refine fintype.card_lt_of_injective_of_not_mem _ subtype.val_injective (_ : b ∉ _),
  simp only [not_exists, set.mem_range, subtype.val_eq_coe],
  rintro y rfl,
  exact hb y.2
end

end induction_hyp

lemma center_eq_top [fintype D] : subring.center D = ⊤ :=
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

def little_wedderburn (D : Type*) [hD : division_ring D] [fintype D] : field D :=
{ mul_comm := λ x y,
  suffices y ∈ subring.center D, from this x,
  by { rw little_wedderburn.center_eq_top, trivial },
  .. hD }
