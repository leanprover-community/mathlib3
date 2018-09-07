import data.nat.totient data.zmod data.polynomial group_theory.order_of_element linear_algebra.prod_module group_theory.quotient_group

set_option trace.simplify.rewrite true

open function

def units_of_nonzero {α : Type*} [field α] {a : α} (ha : a ≠ 0) : units α :=
⟨a, a⁻¹, mul_inv_cancel ha, inv_mul_cancel ha⟩

@[simp] lemma units.coe_pow {α : Type*} [monoid α] (u : units α) (n : ℕ) :
  ((u ^ n : units α) : α) = u ^ n :=
by induction n; simp [*, pow_succ]

@[simp] lemma units_of_nonzero_inj {α : Type*} [field α] {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) :
  units_of_nonzero ha = units_of_nonzero hb ↔ a = b :=
⟨λ h, by injection h, λ h, units.ext h⟩

@[simp] lemma coe_units_of_nonzero {α : Type*} [field α] {a : α} (ha : a ≠ 0) :
  (units_of_nonzero ha : α) = a := rfl

def units_equiv_ne_zero (α : Type*) [field α] : units α ≃ {a : α | a ≠ 0} :=
⟨λ a, ⟨a.1, units.ne_zero _⟩, λ a, units_of_nonzero a.2, λ ⟨_, _, _, _⟩, units.ext rfl, λ ⟨_, _⟩, rfl⟩

@[simp] lemma coe_units_equiv_ne_zero {α : Type*} [field α] (a : units α) :
  ((units_equiv_ne_zero α a) : α) = a := rfl

lemma coe_units_ne_zero {α : Type*} [nonzero_comm_ring α] (u : units α) : (u : α) ≠ 0 :=
λ h : u.1 = 0, by simpa [h, zero_ne_one] using u.3

instance units.fintype {α : Type*} [field α] [fintype α] [decidable_eq α] : fintype (units α) :=
by haveI := set_fintype {a : α | a ≠ 0}; exact
fintype.of_equiv _ (units_equiv_ne_zero α).symm

instance univ_decidable {α : Sort*} : decidable_pred (@set.univ α) :=
λ x, is_true trivial

lemma two_le_card_fintype_domain (α : Type*) [domain α] [fintype α] : 2 ≤ fintype.card α :=
nat.succ_le_of_lt (lt_of_not_ge (mt fintype.card_le_one_iff.1 (λ h, zero_ne_one (h _ _))))

lemma card_units {α : Type*} [field α] [fintype α] [decidable_eq α] :
  fintype.card (units α) = fintype.card α - 1 :=
begin
  rw [eq_comm, nat.sub_eq_iff_eq_add (nat.le_of_succ_le (two_le_card_fintype_domain α))],
  haveI := set_fintype {a : α | a ≠ 0},
  haveI := set_fintype (@set.univ α),
  rw [fintype.card_congr (units_equiv_ne_zero _),
    ← @set.card_insert _ _ {a : α | a ≠ 0} _ (not_not.2 (eq.refl (0 : α)))
    (set.fintype_insert _ _), fintype.card_congr (equiv.set.univ α).symm],
  congr; simp [set.ext_iff, classical.em]
end

lemma two_mul_odd_div_two {n : ℕ} (hn : n % 2 = 1) : 2 * (n / 2) = n - 1 :=
by conv {to_rhs, rw [← nat.mod_add_div n 2, hn, nat.add_sub_cancel_left]}

open polynomial finset nat

lemma sum_card_order_of_eq_card_pow_eq_one {α : Type*} [fintype α] [group α] [decidable_eq α] {n : ℕ} (hn : 0 < n) :
  ((range n.succ).filter (∣ n)).sum (λ m, (univ.filter (λ a : α, order_of a = m)).card)
  = (univ.filter (λ a : α, a ^ n = 1)).card :=
calc ((range n.succ).filter (∣ n)).sum (λ m, (univ.filter (λ a : α, order_of a = m)).card)
    = _ : (card_bind (by simp [finset.ext]; cc)).symm
... = _ : congr_arg card (finset.ext.2 (begin
  assume a,
  suffices : order_of a ≤ n ∧ order_of a ∣ n ↔ a ^ n = 1,
  { simpa [-range_succ, lt_succ_iff] },
  exact ⟨λ h, let ⟨m, hm⟩ := h.2 in by rw [hm, pow_mul, pow_order_of_eq_one, _root_.one_pow],
    λ h, ⟨order_of_le_of_pow_eq_one hn h, order_of_dvd_of_pow_eq_one h⟩⟩
end))

lemma order_of_pow {α : Type*} [group α] [fintype α] [decidable_eq α] (a : α) (n : ℕ) :
  order_of (a ^ n) = order_of a / gcd (order_of a) n :=
dvd_antisymm
(order_of_dvd_of_pow_eq_one
  (by rw [← pow_mul, ← nat.mul_div_assoc _ (gcd_dvd_left _ _), mul_comm,
    nat.mul_div_assoc _ (gcd_dvd_right _ _), pow_mul, pow_order_of_eq_one, _root_.one_pow]))
(have gcd_pos : 0 < gcd (order_of a) n, from gcd_pos_of_pos_left n (order_of_pos a),
  have hdvd : order_of a ∣ n * order_of (a ^ n),
    from order_of_dvd_of_pow_eq_one (by rw [pow_mul, pow_order_of_eq_one]),
  coprime.dvd_of_dvd_mul_right (coprime_div_gcd_div_gcd gcd_pos)
    (dvd_of_mul_dvd_mul_right gcd_pos
      (by rwa [nat.div_mul_cancel (gcd_dvd_left _ _), mul_assoc,
          nat.div_mul_cancel (gcd_dvd_right _ _), mul_comm])))

lemma card_nth_roots_units {α : Type*} [fintype α] [field α] [decidable_eq α] {n : ℕ} (hn : 0 < n)
  (a : units α) : (univ.filter (λ b, b ^ n = a)).card = (nth_roots n (a : α)).card :=
card_congr (λ a _, a)
  (by simp [mem_nth_roots hn, (units.coe_pow _ _).symm, -units.coe_pow, units.ext_iff.symm])
  (by simp [units.ext_iff.symm])
  (λ b hb, have hb0 : b ≠ 0, from λ h,
    coe_units_ne_zero a $ by rwa [mem_nth_roots hn, h, _root_.zero_pow hn, eq_comm] at hb,
    ⟨units_of_nonzero hb0, by simp [units.ext_iff, (mem_nth_roots hn).1 hb]⟩)

local notation `φ` := totient

lemma card_pow_eq_one_eq_order_of {α : Type*} [fintype α] [field α] [decidable_eq α] (a : units α) :
  (univ.filter (λ b : units α, b ^ order_of a = 1)).card = order_of a :=
le_antisymm
(by rw card_nth_roots_units (order_of_pos a) 1; exact card_nth_roots _ _)
(calc order_of a = @fintype.card (gpowers a) (id _) : order_eq_card_gpowers
  ... ≤ @fintype.card (↑(univ.filter (λ b : units α, b ^ order_of a = 1)) : set (units α))
    (set.fintype_of_finset _ (λ _, iff.rfl)) :
  @fintype.card_le_of_injective (gpowers a) (↑(univ.filter (λ b : units α, b ^ order_of a = 1)) : set (units α))
    (id _) (id _) (λ b, ⟨b.1, mem_filter.2 ⟨mem_univ _,
    let ⟨i, hi⟩ := b.2 in
    by rw [← hi, ← gpow_coe_nat, ← gpow_mul, mul_comm, gpow_mul, gpow_coe_nat,
      pow_order_of_eq_one, one_gpow]⟩⟩) (λ _ _ h, subtype.eq (subtype.mk.inj h))
  ... = (univ.filter (λ b : units α, b ^ order_of a = 1)).card : set.card_fintype_of_finset _ _)

private lemma card_order_of_eq_totient_aux {α : Type*} [fintype α] [field α] [decidable_eq α] :
  ∀ {d : ℕ}, d ∣ fintype.card (units α) → 0 < (univ.filter (λ a : units α, order_of a = d)).card →
  (univ.filter (λ a : units α, order_of a = d)).card = φ d
| 0     := λ hd hd0, absurd hd0 (mt card_pos.1
  (by simp [finset.ext, nat.pos_iff_ne_zero.1 (order_of_pos _)]))
| (d+1) := λ hd hd0,
let ⟨a, ha⟩ := exists_mem_of_ne_empty (card_pos.1 hd0) in
have ha : order_of a = d.succ, from (mem_filter.1 ha).2,
have h : ((range d.succ).filter (∣ d.succ)).sum
    (λ m, (univ.filter (λ a : units α, order_of a = m)).card) =
    ((range d.succ).filter (∣ d.succ)).sum φ, from
  finset.sum_congr rfl
    (λ m hm, have hmd : m < d.succ, from mem_range.1 (mem_filter.1 hm).1,
      have hm : m ∣ d.succ, from (mem_filter.1 hm).2,
      card_order_of_eq_totient_aux (dvd.trans hm hd) (finset.card_pos.2
        (ne_empty_of_mem (show a ^ (d.succ / m) ∈ _,
          from mem_filter.2 ⟨mem_univ _,
          by rw [order_of_pow, ha, gcd_eq_right (div_dvd_of_dvd hm),
            nat.div_div_self hm (succ_pos _)]⟩)))),
have hinsert : insert d.succ ((range d.succ).filter (∣ d.succ))
    = (range d.succ.succ).filter (∣ d.succ),
  from (finset.ext.2 $ λ x, ⟨λ h, (mem_insert.1 h).elim (λ h, by simp [h])
    (by clear _let_match; simp; tauto), by clear _let_match; simp {contextual := tt}; tauto⟩),
have hinsert₁ : d.succ ∉ (range d.succ).filter (∣ d.succ),
  by simp [-range_succ, mem_range, zero_le_one, le_succ],
(add_right_inj (((range d.succ).filter (∣ d.succ)).sum
  (λ m, (univ.filter (λ a : units α, order_of a = m)).card))).1
  (calc _ = (insert d.succ (filter (∣ d.succ) (range d.succ))).sum
        (λ m, (univ.filter (λ (a : units α), order_of a = m)).card) :
  eq.symm (finset.sum_insert (by simp [-range_succ, mem_range, zero_le_one, le_succ]))
  ... = ((range d.succ.succ).filter (∣ d.succ)).sum (λ m,
      (univ.filter (λ a : units α, order_of a = m)).card) :
  sum_congr hinsert (λ _ _, rfl)
  ... = (univ.filter (λ a : units α, a ^ d.succ = 1)).card :
  sum_card_order_of_eq_card_pow_eq_one (succ_pos d)
  ... = ((range d.succ.succ).filter (∣ d.succ)).sum φ :
  ha ▸ (card_pow_eq_one_eq_order_of a).symm ▸ (sum_totient _).symm
  ... = _ : by rw [h, ← sum_insert hinsert₁];
    exact finset.sum_congr hinsert.symm (λ _ _, rfl))

lemma card_order_of_eq_totient {α : Type*} [field α] [fintype α] [decidable_eq α] {d : ℕ}
  (hd : d ∣ fintype.card (units α)) : (univ.filter (λ a : units α, order_of a = d)).card = φ d :=
by_contradiction $ λ h,
have h0 : (univ.filter (λ a : units α, order_of a = d)).card = 0 :=
  not_not.1 (mt nat.pos_iff_ne_zero.2 (mt (card_order_of_eq_totient_aux hd) h)),
let c := fintype.card (units α) in
have hc0 : 0 < c, from fintype.card_pos_iff.2 ⟨1⟩,
lt_irrefl c $
  calc c = (univ.filter (λ a : units α, a ^ c = 1)).card :
  congr_arg card $ by simp [finset.ext]
  ... = ((range c.succ).filter (∣ c)).sum
      (λ m, (univ.filter (λ a : units α, order_of a = m)).card) :
  (sum_card_order_of_eq_card_pow_eq_one hc0).symm
  ... = (((range c.succ).filter (∣ c)).erase d).sum
      (λ m, (univ.filter (λ a : units α, order_of a = m)).card) :
  eq.symm (sum_subset (erase_subset _ _) (λ m hm₁ hm₂,
    have m = d, by simp at *; cc,
    by simp [*, finset.ext] at *))
  ... ≤ (((range c.succ).filter (∣ c)).erase d).sum φ :
  sum_le_sum (λ m hm,
    have hmc : m ∣ c, by simp at hm; tauto,
    (imp_iff_not_or.1 (card_order_of_eq_totient_aux hmc)).elim
      (λ h, by simp [nat.le_zero_iff.1 (le_of_not_gt h), nat.zero_le])
      (by simp [le_refl] {contextual := tt}))
  ... < φ d + (((range c.succ).filter (∣ c)).erase d).sum φ :
  lt_add_of_pos_left _ (totient_pos (nat.pos_of_ne_zero
    (λ h, nat.pos_iff_ne_zero.1 hc0 (eq_zero_of_zero_dvd $ h ▸ hd))))
  ... = (insert d (((range c.succ).filter (∣ c)).erase d)).sum φ : eq.symm (sum_insert (by simp))
  ... = ((range c.succ).filter (∣ c)).sum φ : finset.sum_congr
    (finset.insert_erase (mem_filter.2 ⟨mem_range.2 (lt_succ_of_le (le_of_dvd hc0 hd)), hd⟩)) (λ _ _, rfl)
  ... = c : sum_totient _

class is_cyclic (α : Type*) [group α] : Prop :=
(exists_generator : ∃ g : α, ∀ x, x ∈ gpowers g)

local attribute [instance] set_fintype

lemma is_cyclic_of_order_of_eq_card {α : Type*} [group α] [fintype α] [decidable_eq α]
  (x : α) (hx : order_of x = fintype.card α) : is_cyclic α :=
⟨⟨x, set.eq_univ_iff_forall.1 $ set.eq_of_subset_of_card_le
  (set.subset_univ _)
  (by rw [fintype.card_congr (equiv.set.univ α), ← hx, order_eq_card_gpowers])⟩⟩

lemma order_of_eq_card_of_forall_mem_gppowers {α : Type*} [group α] [fintype α] [decidable_eq α]
  {g : α} (hx : ∀ x, x ∈ gpowers g) : order_of g = fintype.card α :=
by rw [← fintype.card_congr (equiv.set.univ α), order_eq_card_gpowers];
  simp [hx]; congr

instance {α : Type*} [fintype α] [field α] : is_cyclic (units α) :=
by haveI := classical.dec_eq α; exact
have ∃ x, x ∈ univ.filter (λ a : units α, order_of a = fintype.card (units α)),
from exists_mem_of_ne_empty (card_pos.1 $
  by rw [card_order_of_eq_totient (dvd_refl _)];
  exact totient_pos (fintype.card_pos_iff.2 ⟨1⟩)),
let ⟨x, hx⟩ := this in
is_cyclic_of_order_of_eq_card x (mem_filter.1 hx).2

variables {p q : ℕ} (hp : prime p) (hq : prime q)

instance : fintype (zmodp p hp) := fin.fintype _

@[simp] lemma card_zmodp : fintype.card (zmodp p hp) = p := fintype.card_fin _

lemma card_units_zmodp : fintype.card (units (zmodp p hp)) = p - 1 :=
by rw [card_units, card_zmodp]

@[simp] theorem fermat_little {p : ℕ} (hp : nat.prime p) {a : zmodp p hp} (ha : a ≠ 0) : a ^ (p - 1) = 1 :=
by rw [← coe_units_of_nonzero ha, ← @units.one_coe (zmodp p hp), ← units.coe_pow, ← units.ext_iff,
    ← card_units_zmodp hp, pow_card_eq_one]

lemma powers_eq_gpowers {α : Type*} [group α] [fintype α] (a : α) : powers a = gpowers a :=
by haveI := classical.dec_eq α; exact
set.ext (λ x, ⟨λ ⟨n, hn⟩, ⟨n, by simp * at *⟩,
  λ ⟨i, hi⟩, ⟨(i % order_of a).nat_abs,
    by rwa [← gpow_coe_nat, int.nat_abs_of_nonneg (int.mod_nonneg _
      (int.coe_nat_ne_zero_iff_pos.2 (order_of_pos _))), ← gpow_eq_mod_order_of]⟩⟩)

lemma euler_criterion_units {x : units (zmodp p hp)} :
  (∃ y : units (zmodp p hp), y ^ 2 = x) ↔ x ^ (p / 2) = 1 :=
hp.eq_two_or_odd.elim
  (λ h, by subst h; revert x; exact dec_trivial)
  (λ hp1, let ⟨g, hg⟩ := is_cyclic.exists_generator (units (zmodp p hp)) in
    let ⟨n, hn⟩ := show x ∈ powers g, from (powers_eq_gpowers g).symm ▸ hg x in
    ⟨λ ⟨y, hy⟩, by rw [← hy, ← pow_mul, two_mul_odd_div_two hp1,
        ← card_units_zmodp hp, pow_card_eq_one],
    λ hx, have 2 * (p / 2) ∣ n * (p / 2),
        by rw [two_mul_odd_div_two hp1, ← card_units_zmodp hp, ← order_of_eq_card_of_forall_mem_gppowers hg];
        exact order_of_dvd_of_pow_eq_one (by rwa [pow_mul, hn]),
      let ⟨m, hm⟩ := dvd_of_mul_dvd_mul_right (nat.div_pos hp.ge_two dec_trivial) this in
      ⟨g ^ m, by rwa [← pow_mul, mul_comm, ← hm]⟩⟩)

lemma euler_criterion {x : zmodp p hp} (hx : x ≠ 0) :
  (∃ y : zmodp p hp, y ^ 2 = x) ↔ x ^ (p / 2) = 1 :=
⟨λ ⟨y, hy⟩,
  have hy0 : y ≠ 0, from λ h, by simp [h, _root_.zero_pow (succ_pos 1)] at hy; cc,
  by simpa using (units.ext_iff.1 $ (euler_criterion_units hp).1 ⟨units_of_nonzero hy0, show _ = units_of_nonzero hx,
    by rw [units.ext_iff]; simpa⟩),
λ h, let ⟨y, hy⟩ := (euler_criterion_units hp).2 (show units_of_nonzero hx ^ (p / 2) = 1, by simpa [units.ext_iff]) in
  ⟨y, by simpa [units.ext_iff] using hy⟩⟩

lemma units.inv_eq_self_iff {α : Type*} [integral_domain α] (u : units α) : u⁻¹ = u ↔ u = 1 ∨ u = -1 :=
by conv {to_lhs, rw [inv_eq_iff_mul_eq_one, ← mul_one (1 : units α), units.ext_iff, units.mul_coe,
  units.mul_coe, mul_self_eq_mul_self_iff, ← units.ext_iff, ← units.coe_neg, ← units.ext_iff] }

lemma prod_finset_distinct_inv {α : Type*} [comm_group α] {s : finset α} :
  (∀ x ∈ s, x⁻¹ ∈ s) → (∀ x ∈ s, x⁻¹ ≠ x) → s.prod (λ x, x) = 1 :=
by haveI := classical.dec_eq α; exact
finset.strong_induction_on s
  (λ s ih h₁ h₂, (classical.em (s = ∅)).elim
    (by simp {contextual := tt})
    (λ hs, let ⟨x, hx⟩ := exists_mem_of_ne_empty hs in
      have ih' : ((s.erase x).erase x⁻¹).prod (λ x, x) = 1,
        from ih ((s.erase x).erase x⁻¹)
          ⟨λ x, by simp {contextual := tt}, λ h, by simpa using h hx⟩
          (λ y hy, by simp [*, eq_inv_iff_eq_inv] at *; cc)
          (by simp; tauto),
      by rw [← insert_erase hx, ← insert_erase (mem_erase.2 ⟨h₂ x hx, h₁ x hx⟩),
          prod_insert, prod_insert, ih'];
        simp [ne.symm (h₂ x hx)]))

/-- generalization of Wilson's lemma -/
lemma prod_univ_units_finite_field {α : Type*} [fintype α] [field α] [decidable_eq α] : univ.prod (λ x, x) = (-1 : units α) :=
have h₁ : ∀ x : units α, x ∈ (univ.erase (-1 : units α)).erase 1 → x⁻¹ ∈ (univ.erase (-1 : units α)).erase 1,
  from λ x, by rw [mem_erase, mem_erase, mem_erase, mem_erase, ne.def, ne.def, ne.def,
    ne.def, inv_eq_iff_inv_eq, one_inv, inv_eq_iff_inv_eq]; simp; cc,
have h₂ : ∀ x : units α, x ∈ (univ.erase (-1 : units α)).erase 1 → x⁻¹ ≠ x,
  from λ x, by  rw [ne.def, units.inv_eq_self_iff]; finish,
calc univ.prod (λ x, x) = (insert (1 : units α) (insert (-1 : units α) ((univ.erase (-1 : units α)).erase 1))).prod (λ x, x) :
  by congr; simp [finset.ext]; tauto
... = -((univ.erase (-1 : units α)).erase 1).prod (λ x, x) :
  if h : (1 : units α) = -1
  then by rw [insert_eq_of_mem, prod_insert]; simp *; cc
  else by rw [prod_insert, prod_insert]; simp *
... = -1 : by rw [prod_finset_distinct_inv h₁ h₂]

@[simp] lemma range_prod_id_eq_fact (n : ℕ) : ((range n.succ).erase 0).prod (λ x, x) = fact n :=
calc ((range n.succ).erase 0).prod (λ x, x) = (range n).prod succ :
eq.symm (prod_bij (λ x _, succ x)
  (λ a h₁, mem_erase.2 ⟨succ_ne_zero _, mem_range.2 $ succ_lt_succ $ by simpa using h₁⟩)
  (by simp) (λ _ _ _ _, succ_inj)
  (λ b h,
    have b.pred.succ = b, from succ_pred_eq_of_pos $
      by simp [nat.pos_iff_ne_zero] at *; tauto,
    ⟨pred b, mem_range.2 $ lt_of_succ_lt_succ (by simp [*, - range_succ] at *), this.symm⟩))
... = fact n : by induction n; simp *

lemma wilsons_lemma {p : ℕ} (hp : prime p) : (fact (p - 1) : zmodp p hp) = -1 :=
begin
  rw [← range_prod_id_eq_fact, ← @units.one_coe (zmodp p hp), ← units.coe_neg,
    ← @prod_univ_units_finite_field (zmodp p hp),
    ← prod_hom (coe : units (zmodp p hp) → zmodp p hp) units.one_coe units.mul_coe,
    ← prod_hom (coe : ℕ → zmodp p hp) nat.cast_one nat.cast_mul],
  exact eq.symm (prod_bij
    (λ a _, (a : zmodp p hp).1) (λ a ha, mem_erase.2
      ⟨λ h, coe_units_ne_zero a $ by rw [← nat.cast_zero, ← h]; simp,
      by rw [mem_range, ← succ_sub hp.pos, succ_sub_one]; exact a.1.2⟩)
    (λ a _, by simp) (λ _ _ _ _, units.ext_iff.2 ∘ fin.eq_of_veq)
    (λ b hb,
      have b ≠ 0 ∧ b < p, by rwa [mem_erase, mem_range, ← succ_sub hp.pos, succ_sub_one] at hb,
      ⟨units_of_nonzero (show (b : zmodp p hp) ≠ 0, from fin.ne_of_vne $
        by rw [zmod.val_cast_nat, ← @nat.cast_zero (zmodp p hp), zmod.val_cast_nat];
        simp [mod_eq_of_lt this.2, this.1]), mem_univ _,
      by simp [zmodp.val_cast_of_lt hp this.2]⟩))
end

lemma range_prod_erase_zero {p : ℕ} (hp : prime p) : ((range p).erase 0).prod (λ x, (x : zmodp p hp)) = -1 :=
by conv in (range p) { rw [← succ_sub_one p, succ_sub hp.pos] };
  rw [prod_hom (coe : ℕ → zmodp p hp) nat.cast_one nat.cast_mul, range_prod_id_eq_fact, wilsons_lemma]

open quotient_group zmodp

instance : decidable_eq (zmodp p hp) := fin.decidable_eq _

instance {n : ℕ+} : decidable_linear_order (zmod n) :=
fin.decidable_linear_order

lemma ne_neg_self (hp1 : p % 2 = 1) {n : zmodp p hp} (hn : n ≠ 0) : n ≠ -n :=
by rw [ne.def, eq_neg_iff_add_eq_zero, ← cast_val hp n,
   ← @nat.cast_zero (zmodp p hp), ← nat.cast_add, eq_iff_modeq_nat, ← two_mul, nat.modeq.modeq_zero_iff];
  exact mt (prime.dvd_mul hp).1 (not_or_distrib.2 ⟨mt (prime_two.2 _)
    (not_or_distrib.2 ⟨λ h, not_prime_one (h ▸ hp), (λ h, by rw h at hp1; exact nat.no_confusion hp1)⟩),
    mt nat.modeq.modeq_zero_iff.2 (mt (eq_iff_modeq_nat hp).2 (by simpa))⟩)

@[simp] lemma units.neg_eq_neg {α : Type*} [ring α] {a b : units α} : -a = -b ↔ a = b :=
by rw [units.ext_iff, units.ext_iff]; simp

lemma prod_prod_mk {α β γ : Type*} [comm_monoid α] [comm_monoid β] (s : finset γ)
  (f : γ → α × β) : s.prod f = (s.prod (λ x, (f x).1), s.prod (λ x, (f x).2)) :=
by haveI := classical.dec_eq γ; exact
finset.induction_on s rfl (by simp [prod.ext_iff] {contextual := tt})

lemma prod_pow {α β : Type} [comm_monoid β] (s : finset α) (n : ℕ) (f : α → β) :
  s.prod (λ x, f x ^ n) = s.prod f ^ n :=
by haveI := classical.dec_eq α; exact
finset.induction_on s (by simp) (by simp [_root_.mul_pow] {contextual := tt})

lemma nat.prod_pow {α : Type*} (s : finset α) (n : ℕ) (f : α → ℕ) :
  s.prod (λ x, f x ^ n) = s.prod f ^ n :=
by haveI := classical.dec_eq α; exact
finset.induction_on s (by simp) (by simp [nat.mul_pow] {contextual := tt})

lemma zmod.lt_neg_iff_le {n : ℕ+} (hn : (n : ℕ) % 2 = 1)
  {x : zmod n} (hx0 : x ≠ 0) : x.1 ≤ (n / 2 : ℕ) ↔
  (n / 2 : ℕ) < (-x).1 :=
have hn2 : (n : ℕ) / 2 < n := nat.div_lt_of_lt_mul ((lt_mul_iff_one_lt_left n.pos).2 dec_trivial),
have hn2' : (n : ℕ) - n / 2 = n / 2 + 1,
  by conv {to_lhs, congr, rw [← succ_sub_one n, succ_sub n.pos]};
  rw [← two_mul_odd_div_two hn, two_mul, ← succ_add, nat.add_sub_cancel],
have hxn : (n : ℕ) - x.val < n,
  begin
    rw [nat.sub_lt_iff (le_of_lt x.2) (le_refl _), nat.sub_self],
    rw ← zmod.cast_val x at hx0,
    exact nat.pos_of_ne_zero (λ h, by simpa [h] using hx0)
  end,
by conv {to_rhs, rw [← nat.succ_le_iff, succ_eq_add_one, ← hn2', ← zero_add (- x), ← zmod.cast_self_eq_zero,
  ← sub_eq_add_neg, ← zmod.cast_val x, ← nat.cast_sub (le_of_lt x.2),
  zmod.val_cast_nat, mod_eq_of_lt hxn, nat.sub_le_sub_left_iff (le_of_lt x.2)] }

lemma zmodp.lt_neg_iff_le {p : ℕ} (hp : prime p) (hp1 : p % 2 = 1)
  {x : zmodp p hp} (hx0 : x ≠ 0) : x.1 ≤ (p / 2 : ℕ) ↔ (p / 2 : ℕ) < (-x).1 :=
@zmod.lt_neg_iff_le ⟨p, hp.pos⟩ hp1 _ hx0

@[simp] lemma zmod.cast_mul_right_val_cast {n m : ℕ+} (a : ℕ) :
  ((a : zmod (m * n)).val : zmod m) = (a : zmod m) :=
zmod.eq_iff_modeq_nat.2 (by rw zmod.val_cast_nat;
  exact nat.modeq.modeq_of_modeq_mul_right _ (nat.mod_mod _ _))

lemma zmod.cast_val_cast_of_dvd {n m : ℕ+} (h : (m : ℕ) ∣ n) (a : ℕ) :
  ((a : zmod n).val : zmod m) = (a : zmod m) :=
let ⟨k , hk⟩ := h in
zmod.eq_iff_modeq_nat.2 (nat.modeq.modeq_of_modeq_mul_right k
    (by rw [← hk, zmod.val_cast_nat]; exact nat.mod_mod _ _))

@[simp] lemma zmod.cast_mul_left_val_cast {n m : ℕ+} (a : ℕ) :
  ((a : zmod (n * m)).val : zmod m) = (a : zmod m) :=
zmod.eq_iff_modeq_nat.2 (by rw zmod.val_cast_nat;
  exact nat.modeq.modeq_of_modeq_mul_left _ (nat.mod_mod _ _))

def foo {n m : ℕ+} (h : (n : ℕ) ∣ m) (a : zmod m) : zmod n := a.val

instance {n m : ℕ+} (h : (n : ℕ) ∣ m) : is_ring_hom (foo h) :=
let ⟨x, hx⟩ := h in
{ map_add := begin
      rintros ⟨a, ha⟩ ⟨b, hb⟩,
      dsimp [foo];
      rw [zmod.mk_eq_cast, zmod.mk_eq_cast, ← nat.cast_add, zmod.cast_val_cast_of_dvd h],
      simp [zmod.cast_val_cast_of_dvd h]
    end,
  map_mul := begin
      rintros ⟨a, ha⟩ ⟨b, hb⟩,
      dsimp [foo];
      rw [zmod.mk_eq_cast, zmod.mk_eq_cast, ← nat.cast_mul, zmod.cast_val_cast_of_dvd h],
      simp [zmod.cast_val_cast_of_dvd h]
    end,
  map_one := begin
    dsimp [foo],
    rw [← nat.cast_one, zmod.cast_val_cast_of_dvd h, nat.cast_one]
  end }

def chinese_remainder_equiv {n m : ℕ+} (h : coprime n m) : zmod (n * m) ≃ (zmod n × zmod m) :=
have right_inv : function.right_inverse
  (λ x : zmod n × zmod m, (nat.modeq.chinese_remainder h x.1.val x.2.val : zmod (n * m)))
  (λ x : zmod (n * m), (⟨x.val, x.val⟩ : zmod n × zmod m)),
  from λ ⟨x, y⟩,
    have _ := (nat.modeq.chinese_remainder h x.1 y.1).2,
    (begin
      dsimp,
      conv {to_rhs, rw [← zmod.cast_val x, ← zmod.cast_val y]},
      rw [zmod.cast_mul_right_val_cast, ← zmod.eq_iff_modeq_nat.2 this.1,
        zmod.cast_mul_left_val_cast, ← zmod.eq_iff_modeq_nat.2 this.2],
      refl
    end),
{ to_fun := λ x, ⟨foo (show (n : ℕ) ∣ (n * m : ℕ+), by simp) x,
   foo (show (m : ℕ) ∣ (n * m : ℕ+), by simp) x⟩,
  inv_fun := λ x, nat.modeq.chinese_remainder h x.1.val x.2.val,
  left_inv := left_inverse_of_surjective_of_right_inverse
    ((fintype.injective_iff_surjective_of_equiv
      (classical.choice $ by rw [← fintype.card_eq, fintype.card_prod];
      simp [zmod.card_zmod])).1 (injective_of_has_left_inverse ⟨_, right_inv⟩)) right_inv,
  right_inv := right_inv }

def is_ring_hom_prod {α β γ : Type*} [ring α] [ring β] [ring γ] (f : α → β) (g : α → γ)
  [is_ring_hom f] [is_ring_hom g] : is_ring_hom (λ a : α, ((f a, g a) : β × γ)) :=
{ map_add := λ x y, prod.ext (is_ring_hom.map_add f) (is_ring_hom.map_add g),
  map_mul := λ x y, prod.ext (is_ring_hom.map_mul f) (is_ring_hom.map_mul g),
  map_one :=        prod.ext (is_ring_hom.map_one f) (is_ring_hom.map_one g) }

instance {n m : ℕ+} (h : coprime n m) : is_ring_hom (chinese_remainder_equiv h) :=
is_ring_hom_prod _ _

lemma coprime_of_mul_modeq_one (b : ℕ) {a n : ℕ} (h : a * b ≡ 1 [MOD n]) : coprime a n :=
nat.coprime_of_dvd' (λ k ⟨ka, hka⟩ ⟨kb, hkb⟩, int.coe_nat_dvd.1 begin
  rw [hka, hkb, nat.modeq.modeq_iff_dvd] at h,
  cases h with z hz,
  rw [sub_eq_iff_eq_add] at hz,
  rw [hz, int.coe_nat_mul, mul_assoc, mul_assoc, int.coe_nat_mul, ← mul_add],
  exact dvd_mul_right _ _,
end)

def units_equiv_coprime {n : ℕ+} : units (zmod n) ≃ {x : zmod n // nat.coprime x.1 n} :=
{ to_fun := λ x, ⟨x, coprime_of_mul_modeq_one (x⁻¹).1.1 begin
    have := units.ext_iff.1 (mul_right_inv x),
    rwa [← zmod.cast_val ((1 : units (zmod n)) : zmod n), units.one_coe, zmod.one_val,
      ← zmod.cast_val ((x * x⁻¹ : units (zmod n)) : zmod n),
      units.mul_coe, zmod.mul_val, zmod.cast_mod_nat, zmod.cast_mod_nat,
      zmod.eq_iff_modeq_nat] at this
    end⟩,
  inv_fun := λ x,
    have x.val * ↑(gcd_a ((x.val).val) ↑n) = 1,
      by rw [← zmod.cast_val x.1, ← int.cast_coe_nat, ← int.cast_one, ← int.cast_mul,
          zmod.eq_iff_modeq_int, ← int.coe_nat_one, ← (show nat.gcd _ _ = _, from x.2)];
        simpa using gcd_a_modeq x.1.1 n,
    ⟨x.1, gcd_a x.1.1 n, this, by simpa [mul_comm] using this⟩,
  left_inv := λ ⟨_, _, _, _⟩, units.ext rfl,
  right_inv := λ ⟨_, _⟩, rfl }

instance zmod.units.fintype {n : ℕ+} : fintype (units (zmod n)) :=
fintype.of_equiv _ units_equiv_coprime.symm

lemma nat.odd_mul_odd {n m : ℕ} (hn1 : n % 2 = 1) (hm1 : m % 2 = 1) : (n * m) % 2 = 1 :=
show (n * m) % 2 = (1 * 1) % 2, from nat.modeq.modeq_mul hn1 hm1

def bar {α β : Type*} [monoid α] [monoid β] (f : α → β) (hf1 : f 1 = 1) (hfmul : ∀ x y, f (x * y) = f x * f y)
  (u : units α) : units β :=
⟨f u.1, f u.2, by rw [← hfmul, u.3, hf1], by rw [← hfmul, u.4, hf1]⟩

set_option trace.simplify.rewrite true

lemma card_union_add_card_inter {α : Type*} (s t : finset α) [decidable_eq α] :
  (s ∪ t).card + (s ∩ t).card = s.card + t.card :=
finset.induction_on t (by simp) (λ a, by by_cases a ∈ s; simp * {contextual := tt})

lemma finset.card_union_le {α : Type*} (s t : finset α) [decidable_eq α] :
  (s ∪ t).card ≤ s.card + t.card :=
card_union_add_card_inter s t ▸ le_add_right _ _

lemma finset.card_bind_le {α β : Type*} {s : finset α} {t : α → finset β} [decidable_eq β] :
  (s.bind t).card ≤ s.sum (λ a, (t a).card) :=
by haveI := classical.dec_eq α; exact
finset.induction_on s (by simp)
  (λ a s has ih,
    calc ((insert a s).bind t).card ≤ (t a).card + (s.bind t).card :
    by rw bind_insert; exact finset.card_union_le _ _
    ... ≤ (insert a s).sum (λ a, card (t a)) :
    by rw sum_insert has; exact add_le_add_left ih _)

lemma injective_add_right {α : Type*} [add_right_cancel_semigroup α] (a : α) :
  function.injective (+ a) := λ _ _, add_right_cancel

lemma nat.injective_mul_right {n : ℕ} (hn : 0 < n) : function.injective (* n) :=
λ _ _, (nat.mul_right_inj hn).1

lemma range_filter_dvd_eq (n : ℕ) {m : ℕ} (hm : 0 < m) :
  (range n.succ).filter (λ x, m ∣ x) = (range (n / m).succ).image (* m) :=
finset.ext.2 $ λ x, ⟨λ h, let ⟨k, hk⟩ := (mem_filter.1 h).2 in mem_image.2
  ⟨k, mem_range.2 $ (mul_lt_mul_left hm).1 begin
    rw [mul_succ, ← hk],
    refine lt_of_lt_of_le (mem_range.1  (mem_filter.1 h).1) _,
    conv {to_lhs, rw [← mod_add_div n m, add_comm, ← add_succ]},
    refine add_le_add_left (succ_le_of_lt (mod_lt _ hm)) _,
  end, by rwa [mul_comm, eq_comm]⟩,
λ h, let ⟨k, hk₁, hk₂⟩ := mem_image.1 h in
  mem_filter.2 ⟨mem_range.2 $ hk₂ ▸
  if hk0 : k = 0 then by simp [hk0, succ_pos] else
  calc k * m ≤ (n / m) * m : (mul_le_mul_right hm).2 (le_of_lt_succ (mem_range.1 hk₁))
  ... < n.succ : lt_succ_of_le (by conv {to_rhs, rw [← mod_add_div n m, mul_comm]};
    exact nat.le_add_left _ _),
  hk₂ ▸ dvd_mul_left _ _⟩⟩

lemma odd_mul_odd_div_two {m n : ℕ} (hm1 : m % 2 = 1) (hn1 : n % 2 = 1) :
  (m * n) / 2 = m * (n / 2) + m / 2 :=
have hm0 : 0 < m := nat.pos_of_ne_zero (λ h, by simp * at *),
have hn0 : 0 < n := nat.pos_of_ne_zero (λ h, by simp * at *),
(nat.mul_left_inj (show 0 < 2, from dec_trivial)).1 $
by rw [mul_add, two_mul_odd_div_two hm1, mul_left_comm, two_mul_odd_div_two hn1,
  two_mul_odd_div_two (nat.odd_mul_odd hm1 hn1), nat.mul_sub_left_distrib, mul_one,
  ← nat.add_sub_assoc hm0, nat.sub_add_cancel (le_mul_of_ge_one_right' (nat.zero_le _) hn0)]

lemma range_p_mul_q_eq (hp : prime p) (hq : prime q) (hp1 : p % 2 = 1) (hq1 : q % 2 = 1) :
  (range ((p * q) / 2).succ).filter (coprime p) =
  (range (q / 2)).bind (λ x, (erase (range p) 0).image (+ p * x))
  ∪ (erase (range (succ (p / 2))) 0).image (+ q / 2 * p) :=
finset.ext.2 $ λ x,
⟨λ h, have hxp0 : x % p ≠ 0, by rw [ne.def, ← dvd_iff_mod_eq_zero, ← hp.coprime_iff_not_dvd];
    exact (mem_filter.1 h).2,
  mem_union.2 $ or_iff_not_imp_right.2 (λ h₁, mem_bind.2
  ⟨x / p, mem_range.2 $ nat.div_lt_of_lt_mul (by_contradiction
    (λ h₂,
      let ⟨c, hc⟩ := le_iff_exists_add.1 (le_of_not_gt h₂) in
      have hcp : c ≤ p / 2, from @nat.le_of_add_le_add_left (p * (q / 2)) _ _
        (by rw [← hc, ← odd_mul_odd_div_two hp1 hq1]; exact le_of_lt_succ (mem_range.1 (mem_filter.1 h).1)),
      h₁ $ mem_image.2 ⟨c, mem_erase.2 ⟨λ h, hxp0 $ by simp [h, hc],
            mem_range.2 $ lt_succ_of_le $ hcp⟩, by rw hc; simp [mul_comm]⟩)),
    mem_image.2 ⟨x % p, mem_erase.2 $
      by rw [ne.def, ← dvd_iff_mod_eq_zero, ← hp.coprime_iff_not_dvd, mem_range];
      exact ⟨(mem_filter.1 h).2, mod_lt _ hp.pos⟩, nat.mod_add_div _ _⟩⟩),
λ h, mem_filter.2 $
  (mem_union.1 h).elim
  (λ h, let ⟨m, hm₁, hm₂⟩ := mem_bind.1 h in
    let ⟨k, hk₁, hk₂⟩ := mem_image.1 hm₂ in
    ⟨mem_range.2 $ hk₂ ▸ (mul_lt_mul_left (show 0 < 2, from dec_trivial)).1 begin
      rw [mul_succ, two_mul_odd_div_two (nat.odd_mul_odd hp1 hq1), mul_add],
      clear _let_match _let_match,
      exact calc 2 * k + 2 * (p * m) < 2 * p + 2 * (p * m) :
        add_lt_add_right ((mul_lt_mul_left dec_trivial).2 (by simp at hk₁; tauto)) _
      ... = 2 * (p * (m + 1)) : by simp [mul_add, mul_assoc, mul_comm, mul_left_comm]
      ... ≤ 2 * (p * (q / 2)) : (mul_le_mul_left (show 0 < 2, from dec_trivial)).2
        ((mul_le_mul_left hp.pos).2 $ succ_le_of_lt $ mem_range.1 hm₁)
      ... ≤ _ : by rw [mul_left_comm, two_mul_odd_div_two hq1, nat.mul_sub_left_distrib,
            ← nat.sub_add_comm (mul_pos hp.pos hq.pos), add_succ, succ_eq_add_one, nat.add_sub_cancel];
          exact le_trans (nat.sub_le_self _ _) (nat.le_add_right _ _),
    end,
  by rw [prime.coprime_iff_not_dvd hp, ← hk₂, ← nat.dvd_add_iff_left (dvd_mul_right _ _),
       dvd_iff_mod_eq_zero, mod_eq_of_lt]; clear _let_match _let_match; simp at hk₁; tauto⟩)
  (λ h, let ⟨m, hm₁, hm₂⟩ := mem_image.1 h in ⟨mem_range.2 $ hm₂ ▸ begin
    refine (mul_lt_mul_left (show 0 < 2, from  dec_trivial)).1 _,
    rw [mul_succ, two_mul_odd_div_two (nat.odd_mul_odd hp1 hq1), mul_add, ← mul_assoc 2, two_mul_odd_div_two hq1],
    exact calc 2 * m + (q - 1) * p ≤ 2 * (p / 2) + (q - 1) * p :
      add_le_add_right ((mul_le_mul_left dec_trivial).2 (le_of_lt_succ (mem_range.1 (by simp * at *)))) _
    ... < _ : begin rw [two_mul_odd_div_two hp1, nat.mul_sub_right_distrib, one_mul],
      rw [← nat.sub_add_comm hp.pos, nat.add_sub_cancel' (le_mul_of_ge_one_left' (nat.zero_le _) hq.pos), mul_comm],
      exact lt_add_of_pos_right _ dec_trivial
    end,
  end,
  by rw [hp.coprime_iff_not_dvd, dvd_iff_mod_eq_zero, ← hm₂, nat.add_mul_mod_self_right, mod_eq_of_lt
      (lt_of_lt_of_le _ (nat.div_lt_self hp.pos (show 1 < 2, from dec_trivial)))];
    simp [-range_succ] at hm₁; clear _let_match; tauto⟩)⟩

lemma nat.add_mul_div (a b : ℕ) {c : ℕ} (hc : 0 < c) : (a + b * c) / c = a / c + b :=
by rw [← nat.mul_left_inj hc, ← add_left_inj ((a + b * c) % c), nat.mod_add_div,
  nat.add_mul_mod_self_right, mul_add, ← add_assoc, nat.mod_add_div, mul_comm]

lemma nat.div_eq_zero_iff {a b : ℕ} (hb : 0 < b) : a / b = 0 ↔ a < b :=
⟨λ h, by rw [← mod_add_div a b, h, mul_zero, add_zero]; exact mod_lt _ hb,
  λ h, by rw [← nat.mul_left_inj hb, ← add_left_inj (a % b), mod_add_div,
    mod_eq_of_lt h, mul_zero, add_zero]⟩

lemma prod_range_p_mul_q_eq (hp : prime p) (hq : prime q) (hp1 : p % 2 = 1) (hq1 : q % 2 = 1) :
  (range (q / 2)).prod (λ n, ((range p).erase 0).prod (+ p * n)) *
  ((range (p / 2).succ).erase 0).prod (+ (q / 2) * p) =
  ((range ((p * q) / 2).succ).filter (coprime p)).prod (λ x, x) :=
calc (range (q / 2)).prod (λ n, ((range p).erase 0).prod (+ p * n)) *
  ((range (p / 2).succ).erase 0).prod (+ (q / 2) * p)
    = (range (q / 2)).prod (λ n, (((range p).erase 0).image (+ p * n)).prod (λ x, x)) *
  (((range (p / 2).succ).erase 0).image (+ (q / 2) * p)).prod (λ x, x) :
by simp only [prod_image (λ _ _ _ _ h, injective_add_right _ h)]; refl
... = ((range (q / 2)).bind (λ x, (erase (range p) 0).image (+ p * x))
         ∪ (erase (range (succ (p / 2))) 0).image (+ q / 2 * p)).prod (λ x, x) :
have h₁ : finset.bind (range (q / 2)) (λ x, ((range p).erase 0).image (+ p * x)) ∩
    image (+ q / 2 * p) (erase (range (succ (p / 2))) 0) = ∅ :=
    eq_empty_iff_forall_not_mem.2 $ λ x, begin
    suffices : ∀ a, a ≠ 0 → a ≤ p / 2 → a + q / 2 * p = x → ∀ b, b < q / 2 →
      ∀ c, c ≠ 0 → c < p → ¬c + p * b = x,
    { simpa [- range_succ, lt_succ_iff] },
    assume a ha0 hap ha b hbq c hc0 hcp hc,
    rw mul_comm at ha,
    rw [← ((nat.div_mod_unique hp.pos).2 ⟨hc, hcp⟩).1,
      ← ((nat.div_mod_unique hp.pos).2 ⟨ha, lt_of_le_of_lt hap
      (nat.div_lt_self hp.pos dec_trivial)⟩).1] at hbq,
    exact lt_irrefl _ hbq
  end,
have h₂ : ∀ x, x ∈ range (q / 2) → ∀ y, y ∈ range (q / 2) → x ≠ y →
    (erase (range p) 0).image (+ p * x) ∩ image (+ p * y) (erase (range p) 0) = ∅ :=
  λ x hx y hy hxy, begin
    suffices : ∀ z a, a ≠ 0 → a < p → a + p * x = z → ∀ b, b ≠ 0 → b < p → b + p * y ≠ z,
    { simpa [finset.ext] },
    assume z a ha0 hap ha b hb0 hbp hb,
    have : (a + p * x) / p = (b + p * y) / p,
    { rw [ha, hb] },
    rw [mul_comm p, mul_comm p, nat.add_mul_div _ _ hp.pos, nat.add_mul_div _ _ hp.pos,
      (nat.div_eq_zero_iff hp.pos).2 hap, (nat.div_eq_zero_iff hp.pos).2 hbp] at this,
    simpa [hxy]
  end,
by rw [prod_union h₁, prod_bind h₂]
... = (((range ((p * q) / 2).succ)).filter (coprime p)).prod (λ x, x) :
prod_congr (range_p_mul_q_eq hp hq hp1 hq1).symm (λ _ _, rfl)

lemma prod_range_p_mul_q_mod_p_eq (hq : prime q) (hp1 : p % 2 = 1) (hq1 : q % 2 = 1) :
  ((((range ((p * q) / 2).succ).filter (coprime p)).prod (λ x, x) : ℕ) : zmodp p hp)
  = (-1) ^ (q / 2) * ((range (p / 2).succ).erase 0).prod (λ x, x) :=
begin
  rw [← prod_range_p_mul_q_eq hp hq hp1 hq1, nat.cast_mul,
    ← prod_hom (coe : ℕ → zmodp p hp) nat.cast_one nat.cast_mul,
    ← prod_hom (coe : ℕ → zmodp p hp) nat.cast_one nat.cast_mul],
  conv in ((finset.prod (erase (range p) 0) _ : ℕ) : zmodp p hp)
  { rw ← prod_hom (coe : ℕ → zmodp p hp) nat.cast_one nat.cast_mul },
  simp [range_prod_erase_zero, card_range]
end

lemma pow_div_two_eq_neg_one_or_one {n : zmodp p hp} (hn : n ≠ 0) : n ^ (p / 2) = 1 ∨ n ^ (p / 2) = -1 :=
hp.eq_two_or_odd.elim
  (λ h, by revert n hn; subst h; exact dec_trivial)
  (λ hp1, by rw [← mul_self_eq_one_iff, ← _root_.pow_add, ← two_mul, two_mul_odd_div_two hp1];
    exact fermat_little hp hn)

lemma prod_range_p_mul_q_filter_not_coprime_eq (hq : prime q) (hp1 : p % 2 = 1) (hq1 : q % 2 = 1) (hpq : p ≠ q) :
  (((((range ((p * q) / 2).succ).filter (coprime p)).filter (λ x, ¬ coprime q x)).prod (λ x, x) : ℕ) : zmodp p hp) =
  q ^ (p / 2) * ((range (p / 2).succ).erase 0).prod (λ x, x) :=
have hcard : ((range (p / 2).succ).erase 0).card = p / 2 :=
  by rw [card_erase_of_mem (mem_range.2 (succ_pos _)), card_range, pred_succ],
begin
  conv in ((q : zmodp p hp) ^ (p / 2)) { rw ← hcard },
  rw [← prod_const, ← prod_mul_distrib, ← prod_hom (coe : ℕ → zmodp p hp) nat.cast_one nat.cast_mul],
  exact eq.symm (prod_bij (λ a _, a * q)
    (λ a ha,
      have ha' : a ≤ p / 2 ∧ a > 0,
        by simp [nat.pos_iff_ne_zero, -range_succ, lt_succ_iff] at *; tauto,
      mem_filter.2 ⟨mem_filter.2 ⟨mem_range.2 $ lt_succ_of_le $
        (calc a * q ≤ q * (p / 2) :
            by rw mul_comm; exact mul_le_mul_left _ ha'.1
          ... ≤ _ : by rw [mul_comm p, odd_mul_odd_div_two hq1 hp1];
            exact nat.le_add_right _ _),
        by rw [hp.coprime_iff_not_dvd, hp.dvd_mul, not_or_distrib];
          refine ⟨λ hpa, not_le_of_gt (show p / 2 < p, from nat.div_lt_self hp.pos dec_trivial)
            (le_trans (le_of_dvd ha'.2 hpa) ha'.1), by rwa [← hp.coprime_iff_not_dvd, coprime_primes hp hq]⟩⟩,
      by simp [hq.coprime_iff_not_dvd]⟩)
    (by simp [mul_comm])
    (by simp [nat.mul_right_inj hq.pos])
    (λ b hb, have hb' : (b ≤ p * q / 2 ∧ coprime p b) ∧ q ∣ b,
        by simpa [hq.coprime_iff_not_dvd, -range_succ, lt_succ_iff] using hb,
      have hb0 : b > 0, from nat.pos_of_ne_zero (λ hb0, by simpa [hb0, hp.coprime_iff_not_dvd] using hb'),
      ⟨b / q, mem_erase.2 ⟨nat.pos_iff_ne_zero.1 (nat.div_pos (le_of_dvd hb0 hb'.2) hq.pos),
        mem_range.2 $ lt_succ_of_le $
          by rw [mul_comm, odd_mul_odd_div_two hq1 hp1] at hb';
          have := @nat.div_le_div_right _ _ hb'.1.1 q;
          rwa [add_comm, mul_comm q, nat.add_mul_div _ _ hq.pos,
      ((nat.div_eq_zero_iff hq.pos).2 (nat.div_lt_self hq.pos (lt_succ_self _))), zero_add] at this⟩,
        by rw nat.div_mul_cancel hb'.2⟩))
end

lemma prime_ne_zero (hq : prime q) (hpq : p ≠ q) : (q : zmodp p hp) ≠ 0 :=
by rwa [← nat.cast_zero, ne.def, zmodp.eq_iff_modeq_nat, nat.modeq.modeq_zero_iff,
  ← hp.coprime_iff_not_dvd, coprime_primes hp hq]

lemma prod_range_p_mul_q_filter_coprime_mod_p (hq : prime q) (hp1 : p % 2 = 1) (hq1 : q % 2 = 1) (hpq : p ≠ q) :
  ((((range ((p * q) / 2).succ).filter (coprime (p * q))).prod (λ x, x) : ℕ) : zmodp p hp) =
  (-1) ^ (q / 2) * q ^ (p / 2) :=
have hq0 : (q : zmodp p hp) ≠ 0, by rwa [← nat.cast_zero, ne.def, zmodp.eq_iff_modeq_nat, nat.modeq.modeq_zero_iff,
  ← hp.coprime_iff_not_dvd, coprime_primes hp hq],
(domain.mul_right_inj
  (show (q ^ (p / 2) * ((range (p / 2).succ).erase 0).prod (λ x, x) : zmodp p hp) ≠ 0,
    from mul_ne_zero
      (pow_ne_zero _ hq0)
        (suffices h : ∀ (x : ℕ), ¬x = 0 → x ≤ p / 2 → ¬(x : zmodp p hp) = 0,
            by simpa [prod_eq_zero_iff, -range_succ, lt_succ_iff],
          assume x hx0 hxp,
          by rwa [← @nat.cast_zero (zmodp p hp), zmodp.eq_iff_modeq_nat, nat.modeq,
            zero_mod, mod_eq_of_lt (lt_of_le_of_lt hxp (nat.div_lt_self hp.pos (lt_succ_self _)))]))).1 $
have h₁ : (range (succ (p * q / 2))).filter (coprime (p * q)) ∩
      filter (λ x, ¬coprime q x) (filter (coprime p) (range (succ (p * q / 2)))) = ∅,
  by have := @coprime.coprime_mul_left p q; simp [finset.ext, *] at * {contextual := tt},
calc ((((range ((p * q) / 2).succ).filter (coprime (p * q))).prod (λ x, x) : ℕ) : zmodp p hp)
     * (q ^ (p / 2) * ((range (p / 2).succ).erase 0).prod (λ x, x) : zmodp p hp)
   = (((range (succ (p * q / 2))).filter (coprime (p * q)) ∪
     filter (λ x, ¬coprime q x) (filter (coprime p) (range (succ (p * q / 2))))).prod (λ x, x) : ℕ) :
by rw [← prod_range_p_mul_q_filter_not_coprime_eq hp hq hp1 hq1 hpq, ← nat.cast_mul, ← prod_union h₁]
... = (((range ((p * q) / 2).succ).filter (coprime p)).prod (λ x, x) : ℕ) :
congr_arg coe (prod_congr (by simp [finset.ext, coprime_mul_iff_left]; tauto) (λ _ _, rfl))
... = _ : by rw [prod_range_p_mul_q_mod_p_eq hp hq hp1 hq1];
  cases pow_div_two_eq_neg_one_or_one hp hq0; simp [h, _root_.pow_succ]

instance : has_repr (zmodp p hp) := fin.has_repr _

lemma zmod.eq_zero_iff_dvd (n : ℕ+) (m : ℕ) : (m : zmod n) = 0 ↔ (n : ℕ) ∣ m :=
by rw [← @nat.cast_zero (zmod n), zmod.eq_iff_modeq_nat, nat.modeq.modeq_zero_iff]

lemma zmodp.eq_zero_iff_dvd (n : ℕ) : (n : zmodp p hp) = 0 ↔ p ∣ n :=
@zmod.eq_zero_iff_dvd ⟨p, hp.pos⟩ _

lemma prod_range_p_mul_q_eq_prod_product (hp1 : p % 2 = 1) (hq1 : q % 2 = 1) (hpq : p ≠ q) :
  ((range ((p * q) / 2).succ).filter (coprime (p * q))).prod
    (λ x, if (x : zmodp q hq).1 ≤ (q / 2) then ((x : zmodp p hp), (x : zmodp q hq))
      else -((x : zmodp p hp), (x : zmodp q hq))) =
  (((range p).erase 0).product ((range (q / 2).succ).erase 0)).prod
    (λ x, ((x.1 : zmodp p hp), (x.2 : zmodp q hq))) :=
have hpqpnat : (((⟨p * q, mul_pos hp.pos hq.pos⟩ : ℕ+) : ℕ) : ℤ) = (p * q : ℤ), by simp,
have hpqpnat' : ((⟨p * q, mul_pos hp.pos hq.pos⟩ : ℕ+) : ℕ) = p * q, by simp,
have hpq1 : ((⟨p * q, mul_pos hp.pos hq.pos⟩ : ℕ+) : ℕ) % 2 = 1,
  from nat.odd_mul_odd hp1 hq1,
have hpq1' : p * q > 1, from one_lt_mul hp.pos hq.gt_one,
prod_bij (λ x _, if (x : zmodp q hq).1 ≤ (q / 2) then ((x : zmodp p hp).val, (x : zmodp q hq).val)
      else ((-x : zmodp p hp).val, (-x : zmodp q hq).val))
  (λ x, have hxp : ∀ {p : ℕ} (hp : prime p), (x : zmodp p hp).val = 0 ↔ p ∣ x,
      from λ p hp, by rw [zmodp.val_cast_nat, nat.dvd_iff_mod_eq_zero],
    have hxpneg : ∀ {p : ℕ} (hp : prime p), (-x : zmodp p hp).val = 0 ↔ p ∣ x,
      from λ p hp, by rw [← int.cast_coe_nat x, ← int.cast_neg, ← int.coe_nat_inj',
        zmodp.coe_val_cast_int, int.coe_nat_zero, ← int.dvd_iff_mod_eq_zero, dvd_neg, int.coe_nat_dvd],
    have hxplt : (x : zmodp p hp).val < p := (x : zmodp p hp).2,
    have hxpltneg : (-x : zmodp p hp).val < p := (-x : zmodp p hp).2,
    have hneglt : ¬(x : zmodp q hq).val ≤ q / 2 → (x : zmodp q hq) ≠ 0 → (-x : zmodp q hq).val ≤ q / 2,
      from λ hx₁ hx0, by rwa [zmodp.lt_neg_iff_le hq hq1 hx0, not_lt] at hx₁,
    by split_ifs;
      simp [zmodp.eq_zero_iff_dvd hq, (x : zmodp p hp).2, coprime_mul_iff_left,
        -range_succ, lt_succ_iff, h, *, hp.coprime_iff_not_dvd,
        hq.coprime_iff_not_dvd] {contextual := tt})
  (λ a ha, by split_ifs; simp [*, prod.ext_iff] at *)
  (λ a b ha hb h,
    have ha' : a ≤ (p * q) / 2 ∧ coprime (p * q) a,
      by simpa [-range_succ, lt_succ_iff] using ha,
    have hapq' : a < ((⟨p * q, mul_pos hp.pos hq.pos⟩ : ℕ+) : ℕ) :=
      lt_of_le_of_lt ha'.1 (div_lt_self (mul_pos hp.pos hq.pos) dec_trivial),
    have hb' : b ≤ (p * q) / 2 ∧ coprime (p * q) b,
      by simpa [-range_succ, lt_succ_iff, coprime_mul_iff_left] using hb,
    have hbpq' : b < ((⟨p * q, mul_pos hp.pos hq.pos⟩ : ℕ+) : ℕ) :=
      lt_of_le_of_lt hb'.1 (div_lt_self (mul_pos hp.pos hq.pos) dec_trivial),
    have val_inj : ∀ {p : ℕ} (hp : prime p) (x y : zmodp p hp), x.val = y.val ↔ x = y,
      from λ _ _ _ _, ⟨fin.eq_of_veq, fin.veq_of_eq⟩,
    have hbpq0 : (b : zmod (⟨p * q, mul_pos hp.pos hq.pos⟩)) ≠ 0,
      by rw [ne.def, zmod.eq_zero_iff_dvd];
        exact λ h, not_coprime_of_dvd_of_dvd hpq1' (dvd_refl (p * q)) h hb'.2,
    have habneg : ¬((a : zmodp p hp) = -b ∧ (a : zmodp q hq) = -b),
      begin
        rw [← int.cast_coe_nat a, ← int.cast_coe_nat b, ← int.cast_coe_nat a, ← int.cast_coe_nat b,
          ← int.cast_neg, ← int.cast_neg, zmodp.eq_iff_modeq_int, zmodp.eq_iff_modeq_int,
          @int.modeq.modeq_and_modeq_iff_modeq_mul _ _ p q ((coprime_primes hp hq).2 hpq), ← hpqpnat,
          ← zmod.eq_iff_modeq_int, int.cast_coe_nat, int.cast_neg, int.cast_coe_nat],
        assume h,
        rw [← hpqpnat', ← zmod.val_cast_of_lt hbpq', zmod.lt_neg_iff_le hpq1 hbpq0,
          ← h, zmod.val_cast_of_lt hapq', ← not_le] at hb',
        exact hb'.1 ha'.1,
      end,
    have habneg' : ¬((-a : zmodp p hp) = b ∧ (-a : zmodp q hq) = b),
      by rwa [← neg_inj', neg_neg, ← @neg_inj' _ _ (-a : zmodp q hq), neg_neg],
    suffices (a : zmodp p hp) = b ∧ (a : zmodp q hq) = b,
      by rw [← mod_eq_of_lt hapq', ← mod_eq_of_lt hbpq'];
        rwa [zmodp.eq_iff_modeq_nat, zmodp.eq_iff_modeq_nat,
          nat.modeq.modeq_and_modeq_iff_modeq_mul ((coprime_primes hp hq).2 hpq)] at this,
    by split_ifs at h; simp * at *)
  (λ ⟨x, y⟩ hxy, let ⟨k, hk⟩ := nat.modeq.chinese_remainder ((coprime_primes hp hq).2 hpq) x y in
    have hxy : x ≠ 0 ∧ x < p ∧ y ≠ 0 ∧ y ≤ q / 2,
      by simpa [and.assoc, -range_succ, lt_succ_iff] using hxy,
    have hkx : x = k % p := mod_eq_of_lt hxy.2.1 ▸ hk.1.symm,
    have hky : y = k % q := mod_eq_of_lt (lt_of_le_of_lt hxy.2.2.2
      (div_lt_self hq.pos (lt_succ_self 1))) ▸ hk.2.symm,
    have hkpqmod : 0 ≤ (- k : ℤ) % (p * q), from int.mod_nonneg _
      (mul_ne_zero (int.coe_nat_ne_zero_iff_pos.2 hp.pos) (int.coe_nat_ne_zero_iff_pos.2 hq.pos)),
    have hpqk0 : ((- k : ℤ) : zmod (⟨p * q, mul_pos hp.pos hq.pos⟩ : ℕ+)) ≠ 0,
      by rw [int.cast_neg, neg_ne_zero, int.cast_coe_nat, ne.def, zmod.eq_zero_iff_dvd];
        exact mt (dvd.trans (dvd_mul_right p q)) (by rw [dvd_iff_mod_eq_zero, ← hkx]; exact hxy.1),
    ⟨if k % (p * q) ≤ (p * q) / 2 then k % (p * q) else ((- k : ℤ) % (p * q)).nat_abs,
    begin
      split_ifs with h,
      { refine mem_filter.2 ⟨mem_range.2 (lt_succ_of_le h), _⟩,
        rw [coprime_mul_iff_left, hp.coprime_iff_not_dvd, hq.coprime_iff_not_dvd,
          dvd_iff_mod_eq_zero, dvd_iff_mod_eq_zero]; simp * at *; tauto },
      { refine mem_filter.2 ⟨mem_range.2 _, _⟩,
        { rwa [← hpqpnat', ← int.coe_nat_lt, int.nat_abs_of_nonneg hkpqmod, ← hpqpnat, ← zmod.coe_val_cast_int,
            int.coe_nat_lt, lt_succ_iff, zmod.lt_neg_iff_le hpq1 hpqk0,
            ← int.cast_neg, neg_neg, int.cast_coe_nat, zmod.val_cast_nat, hpqpnat', ← not_le] },
        { rw [coprime_mul_iff_left, hp.coprime_iff_not_dvd, ← int.coe_nat_dvd, int.dvd_nat_abs,
            int.dvd_iff_mod_eq_zero, int.mod_mul_right_mod, ← int.dvd_iff_mod_eq_zero, dvd_neg_iff_dvd,
            int.coe_nat_dvd, dvd_iff_mod_eq_zero, ← hkx, hq.coprime_iff_not_dvd, ← int.coe_nat_dvd, int.dvd_nat_abs,
            int.dvd_iff_mod_eq_zero, int.mod_mul_left_mod, ← int.dvd_iff_mod_eq_zero, dvd_neg_iff_dvd,
            int.coe_nat_dvd, dvd_iff_mod_eq_zero, ← hky]; cc } }
      end,
    have hkq0 : ((k : ℤ) : zmodp q hq) ≠ 0,
        by rw [int.cast_coe_nat, ne.def, zmodp.eq_zero_iff_dvd, dvd_iff_mod_eq_zero, ← hky];
        exact hxy.2.2.1,
      have hkpq : ¬ int.nat_abs (-↑k % (↑p * ↑q)) % q ≤ q / 2 :=
        by rw [not_le, ← int.coe_nat_lt, int.coe_nat_mod, int.nat_abs_of_nonneg hkpqmod,
            int.mod_mul_left_mod, ← zmodp.coe_val_cast_int hq, int.coe_nat_lt, int.cast_neg,
            ← zmodp.lt_neg_iff_le hq hq1 hkq0, int.cast_coe_nat, zmodp.val_cast_nat, ← hky];
          exact hxy.2.2.2,
      have hneg_neg : (-(int.nat_abs (-↑k % (↑p * ↑q))) : zmodp p hp).val = k % p :=
      by rw [← int.cast_coe_nat, int.nat_abs_of_nonneg hkpqmod, ← int.cast_neg, ← int.coe_nat_inj',
          zmodp.coe_val_cast_int hp, int.coe_nat_mod];
        exact int.modeq.modeq_of_modeq_mul_right q
          (int.modeq.trans (int.modeq.modeq_neg (int.modeq.mod_modeq _ _)) (by simp)),
      have hneg_neg' : (-(int.nat_abs (-↑k % (↑p * ↑q))) : zmodp q hq).val = k % q :=
        by rw [← int.cast_coe_nat, int.nat_abs_of_nonneg hkpqmod, ← int.cast_neg, ← int.coe_nat_inj',
          zmodp.coe_val_cast_int hq, int.coe_nat_mod];
        exact int.modeq.modeq_of_modeq_mul_left p
          (int.modeq.trans (int.modeq.modeq_neg (int.modeq.mod_modeq _ _)) (by simp)),
      by split_ifs; simp [zmodp.val_cast_nat, *, -not_le, -not_lt] at *⟩)

lemma prod_erase_range_div_two_zero (hp1 : p % 2 = 1) :
  ((range (p / 2).succ).erase 0).prod (λ x, (x : zmodp p hp)) ^ 2 * (-1) ^ (p / 2) = -1 :=
have hcard : card (erase (range (succ (p / 2))) 0) = p / 2,
  by rw [card_erase_of_mem (mem_range.2 (succ_pos _)), card_range, pred_succ],
have hp2 : p / 2 < p, from div_lt_self hp.pos dec_trivial,
have h₁ : (range (p / 2).succ).erase 0 = ((range p).erase 0).filter (λ x, (x : zmodp p hp).val ≤ p / 2) :=
  finset.ext.2 (λ a,
  ⟨λ h, mem_filter.2 $ by rw [mem_erase, mem_range, lt_succ_iff] at h;
    exact ⟨mem_erase.2 ⟨h.1, mem_range.2 (lt_of_le_of_lt h.2 hp2)⟩,
      by rw zmodp.val_cast_of_lt hp (lt_of_le_of_lt h.2 hp2); exact h.2⟩,
  λ h, mem_erase.2 ⟨by simp at h; tauto,
    by rw [mem_filter, mem_erase, mem_range] at h;
    rw [mem_range, lt_succ_iff, ← zmodp.val_cast_of_lt hp h.1.2]; exact h.2⟩⟩),
have hmem : ∀ x ∈ (range (p / 2).succ).erase 0, x ≠ 0 ∧ x ≤ p / 2,
  from λ x hx, by simpa [-range_succ, lt_succ_iff] using hx,
have hmemv : ∀ x ∈ (range (p / 2).succ).erase 0, (x : zmodp p hp).val = x,
  from λ x hx, zmodp.val_cast_of_lt hp (lt_of_le_of_lt (hmem x hx).2 hp2),
have hmem0 : ∀ x ∈ (range (p / 2).succ).erase 0, (x : zmodp p hp) ≠ 0,
  from λ x hx, fin.ne_of_vne $ by simp [hmemv x hx, (hmem x hx).1],
have hmem0' : ∀ x ∈ (range (p / 2).succ).erase 0, (-x : zmodp p hp) ≠ 0,
  from λ x hx, neg_ne_zero.2 (hmem0 x hx),
have h₂ : ((range (p / 2).succ).erase 0).prod (λ x : ℕ, (x : zmodp p hp) * -1) =
    (((range p).erase 0).filter (λ x : ℕ, ¬(x : zmodp p hp).val ≤ p / 2)).prod (λ x, (x : zmodp p hp)) :=
  prod_bij (λ a _, (-a : zmodp p hp).1)
    (λ a ha,  mem_filter.2 ⟨mem_erase.2 ⟨fin.vne_of_ne (hmem0' a ha), mem_range.2 (-a : zmodp p hp).2⟩,
        by simp [zmodp.lt_neg_iff_le hp hp1 (hmem0' a ha), hmemv a ha, (hmem a ha).2]; tauto⟩)
    (by simp)
    (λ a₁ a₂ ha₁ ha₂ h,
      by rw [← hmemv a₁ ha₁, ← hmemv a₂ ha₂]; exact fin.veq_of_eq (by rw neg_inj (fin.eq_of_veq h)))
    (λ b hb,
      have hb' : (b ≠ 0 ∧ b < p) ∧ (¬(b : zmodp p hp).1 ≤ p / 2), by simpa using hb,
      have hbv : (b : zmodp p hp).1 = b, from zmodp.val_cast_of_lt hp hb'.1.2,
      have hb0 : (b : zmodp p hp) ≠ 0, from fin.ne_of_vne $ by simp [hbv, hb'.1.1],
    ⟨(-b : zmodp p hp).1, mem_erase.2 ⟨fin.vne_of_ne (neg_ne_zero.2 hb0 : _),
      mem_range.2 $ lt_succ_of_le $ by rw [← not_lt, ← zmodp.lt_neg_iff_le hp hp1 hb0]; exact hb'.2⟩,
      by simp [hbv]⟩),
calc ((((range (p / 2).succ).erase 0).prod (λ x, (x : zmodp p hp)) ^ 2)) * (-1) ^ (p / 2) =
  ((range (p / 2).succ).erase 0).prod (λ x, (x : zmodp p hp)) *
  ((range (p / 2).succ).erase 0).prod (λ x, (x : zmodp p hp) * -1) :
by rw prod_mul_distrib; simp [_root_.pow_two, -range_succ, hcard, mul_assoc]
... = (((range p).erase 0).filter (λ x : ℕ, (x : zmodp p hp).val ≤ p / 2)).prod (λ x, (x : zmodp p hp)) *
    (((range p).erase 0).filter (λ x : ℕ, ¬(x : zmodp p hp).val ≤ p / 2)).prod (λ x, (x : zmodp p hp)) :
by rw [h₂, h₁]
... = ((range p).erase 0).prod (λ x, (x : zmodp p hp)) :
  begin
    rw ← prod_union,
    { exact finset.prod_congr (by simp [finset.ext, -not_lt, -not_le]; tauto) (λ _ _, rfl) },
    { simp [finset.ext, -not_lt, - not_le]; tauto }
  end
... = -1 : range_prod_erase_zero hp

lemma nat.pred_eq_sub_one (n : ℕ) : n.pred = n - 1 := rfl

lemma range_p_product_range_q_div_two_prod (hp1 : p % 2 = 1) (hq1 : q % 2 = 1):
  (((range p).erase 0).product ((range (q / 2).succ).erase 0)).prod
    (λ x, ((x.1 : zmodp p hp), (x.2 : zmodp q hq))) =
  ((-1) ^ (q / 2), (-1) ^ (p / 2) * (-1) ^ (p / 2 * (q / 2))) :=
have hcard : card (erase (range (succ (q / 2))) 0) = q / 2,
  by rw [card_erase_of_mem (mem_range.2 (succ_pos _)), card_range, pred_succ],
have finset.prod (erase (range (succ (q / 2))) 0) (λ x : ℕ, (x : zmodp q hq)) ^ 2 = -((-1 : zmodp q hq) ^ (q / 2)),
  from (domain.mul_right_inj (show (-1 : zmodp q hq) ^ (q / 2) ≠ 0, from pow_ne_zero _ (neg_ne_zero.2 zero_ne_one.symm))).1 $
  by rw [prod_erase_range_div_two_zero hq hq1, ← neg_mul_eq_neg_mul, ← _root_.pow_add, ← two_mul,
    pow_mul, _root_.pow_two]; simp,
have finset.prod (erase (range (succ (q / 2))) 0) (λ x, (x : zmodp q hq)) ^ card (erase (range p) 0) =
  (- 1) ^ (p / 2) * ((-1) ^ (p / 2 * (q / 2))),
 by rw [card_erase_of_mem (mem_range.2 hp.pos), card_range, nat.pred_eq_sub_one,
   ← two_mul_odd_div_two hp1, pow_mul, this, mul_comm (p / 2), pow_mul, ← _root_.mul_pow]; simp,
by simp [prod_product, prod_prod_mk, prod_pow, -range_succ, nat.prod_pow, prod_const,
    *, range_prod_erase_zero]

lemma prod_range_p_mul_q_ite_eq (hp1 : p % 2 = 1) (hq1 : q % 2 = 1) (hpq : p ≠ q) :
  ((range ((p * q) / 2).succ).filter (coprime (p * q))).prod
  (λ x, if (x : zmodp q hq).1 ≤ (q / 2) then ((x : zmodp p hp), (x : zmodp q hq))
    else -((x : zmodp p hp), (x : zmodp q hq))) =
  ((range ((p * q) / 2).succ).filter (coprime (p * q))).prod (λ x, if (x : zmodp q hq).1 ≤ q / 2 then 1 else -1) *
  ((-1) ^ (q / 2) * q ^ (p / 2), (-1) ^ (p / 2) * p ^ (q / 2)) :=
calc ((range ((p * q) / 2).succ).filter (coprime (p * q))).prod
  (λ x, if (x : zmodp q hq).1 ≤ (q / 2) then ((x : zmodp p hp), (x : zmodp q hq))
    else -((x : zmodp p hp), (x : zmodp q hq))) =
  ((range ((p * q) / 2).succ).filter (coprime (p * q))).prod
  (λ x, (if (x : zmodp q hq).1 ≤ (q / 2) then 1 else -1) * ((x : zmodp p hp), (x : zmodp q hq))) :
prod_congr rfl (λ _ _, by split_ifs; simp)
... = _ : by rw [prod_mul_distrib, prod_prod_mk _ (λ x : ℕ, ((x : zmodp p hp), (x : zmodp q hq))),
    prod_hom (coe : ℕ → zmodp p hp) nat.cast_one nat.cast_mul,
    prod_range_p_mul_q_filter_coprime_mod_p hp hq hp1 hq1 hpq,
    prod_hom (coe : ℕ → zmodp q hq) nat.cast_one nat.cast_mul,
    mul_comm p q, prod_range_p_mul_q_filter_coprime_mod_p hq hp hq1 hp1 hpq.symm]

def legendre_sym (a p : ℕ) (hp : prime p) : ℤ :=
if (a : zmodp p hp) = 0 then 0 else if ∃ b : zmodp p hp, b ^ 2 = a then 1 else -1

lemma legendre_sym_eq_pow (a p : ℕ) (hp : prime p) : (legendre_sym a p hp : zmodp p hp) = (a ^ (p / 2)) :=
if ha : (a : zmodp p hp) = 0 then by simp [*, legendre_sym, _root_.zero_pow (nat.div_pos hp.ge_two (succ_pos 1))]
else
(prime.eq_two_or_odd hp).elim
  (λ hp2, begin subst hp2,
    suffices : ∀ a : zmodp 2 prime_two,
      (((ite (a = 0) 0 (ite (∃ (b : zmodp 2 hp), b ^ 2 = a) 1 (-1))) : ℤ) : zmodp 2 prime_two) = a ^ (2 / 2),
    { exact this a },
    exact dec_trivial,
   end)
  (λ hp1, have _ := euler_criterion hp ha,
    have (-1 : zmodp p hp) ≠ 1, from (ne_neg_self hp hp1 zero_ne_one.symm).symm,
    by cases pow_div_two_eq_neg_one_or_one hp ha; simp [legendre_sym, *] at *)

lemma quadratic_reciprocity (hp : prime p) (hq : prime q) (hp1 : p % 2 = 1) (hq1 : q % 2 = 1) (hpq : p ≠ q) :
  legendre_sym p q hq * legendre_sym q p hp = (-1) ^ (p / 2) * (-1) ^ (q / 2) :=
have hneg_one_or_one : ((range (p * q / 2).succ).filter (coprime (p * q))).prod
    (λ (x : ℕ), if (x : zmodp q hq).val ≤ q / 2 then (1 : zmodp p hp × zmodp q hq) else -1) = 1 ∨
    ((range (p * q / 2).succ).filter (coprime (p * q))).prod
    (λ (x : ℕ), if (x : zmodp q hq).val ≤ q / 2 then (1 : zmodp p hp × zmodp q hq) else -1) = -1 :=
  finset.induction_on ((range (p * q / 2).succ).filter (coprime (p * q))) (or.inl rfl)
    (λ a s h, by simp [prod_insert h]; split_ifs; finish),
have h : (((-1) ^ (q / 2), (-1) ^ (p / 2) * (-1) ^ (p / 2 * (q / 2))) : zmodp p hp × zmodp q hq) =
   ((-1) ^ (q / 2) * q ^ (p / 2), (-1) ^ (p / 2) * p ^ (q / 2)) ∨
   (((-1) ^ (q / 2), (-1) ^ (p / 2) * (-1) ^ (p / 2 * (q / 2))) : zmodp p hp × zmodp q hq) =
   - ((-1) ^ (q / 2) * q ^ (p / 2), (-1) ^ (p / 2) * p ^ (q / 2)) :=
begin
  have := prod_range_p_mul_q_eq_prod_product hp hq hp1 hq1 hpq,
  rw [prod_range_p_mul_q_ite_eq hp hq hp1 hq1 hpq,
    range_p_product_range_q_div_two_prod hp hq hp1 hq1] at this,
  cases hneg_one_or_one with h h; simp * at *
end,
begin



end
