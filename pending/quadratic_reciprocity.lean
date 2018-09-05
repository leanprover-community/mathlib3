import tactic.explode data.nat.totient data.zmod data.polynomial group_theory.order_of_element linear_algebra.prod_module group_theory.quotient_group

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
by unfold set.univ; apply_instance

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

@[simp] lemma pow_card_eq_one {α : Type*} [group α] [fintype α] [decidable_eq α]
  (a : α) : a ^ fintype.card α = 1 :=
let ⟨m, hm⟩ := @order_of_dvd_card_univ _ a _ _ _ in
by simp [hm, pow_mul, pow_order_of_eq_one]

open polynomial finset nat

lemma order_of_dvd_of_pow_eq_one {α : Type*} [fintype α] [group α] [decidable_eq α] {a : α}
  {n : ℕ} (h : a ^ n = 1) : order_of a ∣ n :=
by_contradiction
  (λ h₁, nat.find_min _ (show n % order_of a < order_of a,
    from nat.mod_lt _ (order_of_pos _))
      ⟨nat.pos_of_ne_zero (mt nat.dvd_of_mod_eq_zero h₁), by rwa ← pow_eq_mod_order_of⟩)

lemma order_of_le_of_pow_eq_one {α : Type*} [fintype α] [group α] [decidable_eq α] {a : α}
  {n : ℕ} (hn : 0 < n) (h : a ^ n = 1) : order_of a ≤ n :=
nat.find_min' (exists_pow_eq_one a) ⟨hn, h⟩

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

lemma div_dvd_of_dvd {a b : ℕ} (h : b ∣ a) : (a / b) ∣ a :=
⟨b, (nat.div_mul_cancel h).symm⟩

lemma nat.div_pos {a b : ℕ} (hba : b ≤ a) (hb : 0 < b) : 0 < a / b :=
nat.pos_of_ne_zero (λ h, lt_irrefl a
  (calc a = a % b : by simpa [h] using (mod_add_div a b).symm
      ... < b : nat.mod_lt a hb
      ... ≤ a : hba))

lemma div_div_self : ∀ {a b : ℕ}, b ∣ a → 0 < a → a / (a / b) = b
| a     0     h₁ h₂ := by rw eq_zero_of_zero_dvd h₁; refl
| 0     b     h₁ h₂ := absurd h₂ dec_trivial
| (a+1) (b+1) h₁ h₂ :=
(nat.mul_right_inj (nat.div_pos (le_of_dvd (succ_pos a) h₁) (succ_pos b))).1 $
  by rw [nat.div_mul_cancel (div_dvd_of_dvd h₁), nat.mul_div_cancel' h₁]

lemma zero_pow {α : Type*} [semiring α] {n : ℕ} : 0 < n → (0 : α) ^ n = 0 :=
by cases n; simp [_root_.pow_succ, lt_irrefl]

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
            div_div_self hm (succ_pos _)]⟩)))),
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

lemma card_le_of_subset {α : Type*} {s t : set α} [fintype s] [fintype t] (hsub : s ⊆ t) :
  fintype.card s ≤ fintype.card t :=
calc fintype.card s = s.to_finset.card : set.card_fintype_of_finset' _ (by simp)
... ≤ t.to_finset.card : finset.card_le_of_subset (λ x hx, by simp [set.subset_def, *] at *)
... = fintype.card t : eq.symm (set.card_fintype_of_finset' _ (by simp))

lemma set.eq_of_subset_of_card_le {α : Type*} {s t : set α} [fintype s] [fintype t]
   (hsub : s ⊆ t) (hcard : fintype.card t ≤ fintype.card s) : s = t :=
classical.by_contradiction (λ h, lt_irrefl (fintype.card t)
  (have fintype.card s < fintype.card t := set.card_lt_card ⟨hsub, h⟩,
    by rwa [le_antisymm (card_le_of_subset hsub) hcard] at this))

local attribute [instance] set_fintype

lemma is_cyclic_of_order_of_eq_card {α : Type*} [group α] [fintype α] [decidable_eq α]
  (x : α) (hx : order_of x = fintype.card α) : is_cyclic α :=
⟨⟨x, set.eq_univ_iff_forall.1 $ set.eq_of_subset_of_card_le
  (set.subset_univ _)
  (by rw [fintype.card_congr (equiv.set.univ α), ← hx, order_eq_card_gpowers])⟩⟩

lemma is_cyclic.order_of_generator {α : Type*} [group α] [fintype α] [decidable_eq α] [is_cyclic α]
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

lemma gpowers_eq_powers {α : Type*} [group α] [fintype α] (a : α) : gpowers a = powers a :=
by haveI := classical.dec_eq α; exact
set.ext (λ x, ⟨λ ⟨i, hi⟩, ⟨(i % order_of a).nat_abs,
  by rwa [← gpow_coe_nat, int.nat_abs_of_nonneg (int.mod_nonneg _
      (int.coe_nat_ne_zero_iff_pos.2 (order_of_pos _))), ← gpow_eq_mod_order_of]⟩,
λ ⟨n, hn⟩, ⟨n, by simp * at *⟩⟩)

lemma nat.prime.eq_two_or_odd {p : ℕ} (hp : prime p) : p = 2 ∨ p % 2 = 1 :=
(nat.mod_two_eq_zero_or_one p).elim
  (λ h, or.inl ((hp.2 2 (dvd_of_mod_eq_zero h)).resolve_left dec_trivial).symm)
  or.inr

lemma euler_criterion {x : units (zmodp p hp)} :
  (∃ y : units (zmodp p hp), y ^ 2 = x) ↔ x ^ (p / 2) = 1 :=
hp.eq_two_or_odd.elim
  (λ h, by subst h; revert x; exact dec_trivial)
  (λ hp1, let ⟨g, hg⟩ := is_cyclic.exists_generator (units (zmodp p hp)) in
    let ⟨n, hn⟩ := show x ∈ powers g, from gpowers_eq_powers g ▸ hg x in
    ⟨λ ⟨y, hy⟩, by rw [← hy, ← pow_mul, two_mul_odd_div_two hp1,
        ← card_units_zmodp hp, pow_card_eq_one],
    λ hx, have 2 * (p / 2) ∣ n * (p / 2),
        by rw [two_mul_odd_div_two hp1, ← card_units_zmodp hp, ← is_cyclic.order_of_generator hg];
        exact order_of_dvd_of_pow_eq_one (by rwa [pow_mul, hn]),
      let ⟨m, hm⟩ := dvd_of_mul_dvd_mul_right (nat.div_pos hp.ge_two dec_trivial) this in
      ⟨g ^ m, by rwa [← pow_mul, mul_comm, ← hm]⟩⟩)

lemma nat.div_lt_of_lt_mul {m n k : ℕ} (h : m < n * k) : m / n < k :=
lt_of_mul_lt_mul_left
  (calc n * (m / n) ≤ m % n + n * (m / n) : nat.le_add_left _ _
  ... = m : nat.mod_add_div _ _
  ... < n * k : h)
  (nat.zero_le n)

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
    (λ a _, by simp [id.def]) (λ _ _ _ _, units.ext_iff.2 ∘ fin.eq_of_veq)
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

instance {p : ℕ} (hp : prime p) : decidable_linear_order (zmodp p hp) :=
fin.decidable_linear_order

def one_neg_one : set (units (zmodp p hp)) := {1, -1}

instance : normal_subgroup (one_neg_one hp) :=
by refine_struct { .. }; finish [one_neg_one]

instance : decidable_pred (one_neg_one hp) :=
λ x, show decidable (x ∈ one_neg_one hp), by simp [one_neg_one]; apply_instance

instance decidable_rel_of_decidable_pred {α : Type*} [group α] (S : set α) [h : decidable_pred S] [is_subgroup S] :
  by haveI := left_rel S; exact decidable_rel ((≈) : α → α → Prop) := λ x y, h _

instance quotient_on_neg_one.fintype : fintype (quotient (one_neg_one hp)) :=
quotient.fintype _

instance quotient_on_neg_one.comm_group : comm_group (quotient (one_neg_one hp)) :=
by apply_instance

instance l : decidable_eq (units (zmodp p hp) × units (zmodp q hq)) := by apply_instance

def one_neg_one' : set (units (zmodp p hp) × units (zmodp q hq)) := {(1, 1), (-1, -1)}

instance : decidable_pred (one_neg_one' hp hq) :=
λ x, show decidable (x ∈ one_neg_one' hp hq), by simp [one_neg_one']; apply_instance

instance : normal_subgroup (one_neg_one' hp hq) :=
by refine_struct { .. }; finish [one_neg_one', prod.ext_iff]

instance quotient_one_neg_one'.fintype : fintype (quotient (one_neg_one' hp hq)) :=
by letI := left_rel (one_neg_one' hp hq);
haveI : decidable_rel ((≈) : (units (zmodp p hp) × units (zmodp q hq))
  → (units (zmodp p hp) × units (zmodp q hq)) → Prop) :=
  decidable_rel_of_decidable_pred _;
unfold quotient_group.quotient; apply_instance

instance quotient_on_neg_one'.comm_group : comm_group (quotient (one_neg_one' hp hq)) :=
by apply_instance

lemma ne_neg_self (hp1 : p % 2 = 1) (n : units (zmodp p hp)) : n ≠ -n :=
by rw [ne.def, units.ext_iff, units.coe_neg, eq_neg_iff_add_eq_zero, ← cast_val hp n,
   ← @nat.cast_zero (zmodp p hp), ← nat.cast_add, eq_iff_modeq_nat, ← two_mul, nat.modeq.modeq_zero_iff];
  exact mt (prime.dvd_mul hp).1 (not_or_distrib.2 ⟨mt (prime_two.2 _)
    (not_or_distrib.2 ⟨λ h, not_prime_one (h ▸ hp), (λ h, by rw h at hp1; exact nat.no_confusion hp1)⟩),
    mt nat.modeq.modeq_zero_iff.2 (mt (eq_iff_modeq_nat hp).2 (by simp))⟩)

@[simp] lemma units.neg_eq_neg {α : Type*} [ring α] {a b : units α} : -a = -b ↔ a = b :=
by rw [units.ext_iff, units.ext_iff]; simp

noncomputable def f : quotient (one_neg_one hp) × (units (zmodp q hq)) → quotient (one_neg_one' hp hq) :=
λ x, mk (quotient.out' x.1, x.2)

lemma f_surjective : function.surjective (f hp hq) :=
λ x, quotient.induction_on' x (λ ⟨x, y⟩,
⟨if h : quotient.out' (quotient.mk' x : quotient (one_neg_one hp)) = x
then (quotient.mk' x, y)
else (quotient.mk' x, -y),
have (quotient.out' (quotient.mk' x : quotient (one_neg_one hp)))⁻¹ * x ∈ one_neg_one hp,
  from @quotient.mk_out' _ (left_rel (one_neg_one hp)) x,
quotient.sound' $ show _ ∈ _,
  by split_ifs;
    simp [*, prod.ext_iff, mul_eq_one_iff_eq_inv, one_neg_one, f, one_neg_one'] at *⟩)

lemma card_one_neg_one (hp1 : p % 2 = 1) : fintype.card (one_neg_one hp) = 2 :=
let s : finset (units (zmodp p hp)) := ⟨(1 :: -1 :: 0), by simp [ne_neg_self hp hp1]⟩ in
show fintype.card (one_neg_one hp) = s.card, from set.card_fintype_of_finset' s (by simp [s, one_neg_one, or.comm])

lemma card_quotient_one_neg_one (hp1 : p % 2 = 1) : fintype.card (quotient (one_neg_one hp)) = p / 2 :=
(nat.mul_left_inj (show 2 > 0, from dec_trivial)).1 $
  by rw [two_mul_odd_div_two hp1, ← card_one_neg_one hp hp1, mul_comm, ← fintype.card_prod, ← card_units_zmodp hp,
    fintype.card_congr (@is_subgroup.group_equiv_quotient_times_subgroup _ _ (one_neg_one hp) _)]

@[simp] lemma quotient.out_inj' {α : Type*} {s : setoid α} {x y : quotient s} : quotient.out' x = quotient.out' y ↔ x = y :=
⟨λ h, by simpa [quotient.out_eq'] using congr_arg (quotient.mk' : α → quotient s) h,
  λ h, congr_arg _ h⟩

lemma prod_univ_quotient_one_neg_one (hp1 : p % 2 = 1) :
  (univ : finset (quotient (one_neg_one hp))).prod quotient.out' ^ 2 = -((-1) ^ (p / 2)) :=
calc (@univ (quotient (one_neg_one hp)) _).prod quotient.out' ^ 2 = (@univ (quotient (one_neg_one hp)) _).prod quotient.out' *
  ((@univ (quotient (one_neg_one hp)) _).prod (λ n, -quotient.out' n) * (-1 : units (zmodp p hp)) ^ (p / 2)) :
by rw [← card_quotient_one_neg_one hp hp1, fintype.card, ← prod_const, ← prod_mul_distrib];
  simp [_root_.pow_two]
... = univ.prod (λ x : quotient (one_neg_one hp), quotient.out' x * -quotient.out' x) * (-1) ^ (p / 2) :
by rw [← mul_assoc, ← prod_mul_distrib]
... = univ.prod (λ x : quotient (one_neg_one hp), finset.prod {quotient.out' x, -quotient.out' x} (λ x, x)) * (-1) ^ (p / 2) :
(mul_right_inj _).2 $ prod_congr rfl $ λ x,
  by rw [has_insert_eq_insert, prod_insert];
  simpa [eq_comm] using ne_neg_self hp hp1 (quotient.out' x)
... = (univ.bind (λ x : quotient (one_neg_one hp), {quotient.out' x, -quotient.out' x})).prod (λ x, x) * (-1) ^ (p / 2) :
(mul_right_inj _).2 (eq.symm (prod_bind (λ x _ y _, quotient.induction_on₂' x y
  (λ x y h, begin
      have : x⁻¹ * y ∉ _, from mt quotient_group.eq.2 h,
      have : (quotient.out' (quotient.mk' x : quotient (one_neg_one hp)))⁻¹ * x ∈ one_neg_one hp,
        from @quotient.mk_out' _ (left_rel (one_neg_one hp)) x,
      have : (quotient.out' (quotient.mk' y))⁻¹ * y ∈ one_neg_one hp,
        from @quotient.mk_out' _ (left_rel (one_neg_one hp)) y,
      simp [inv_mul_eq_iff_eq_mul, one_neg_one, finset.ext] at *,
    end))))
... = univ.prod (λ x, x) * (-1) ^ (p/2) :
(mul_right_inj _).2 (prod_congr (eq_univ_iff_forall.2 (λ x, mem_bind.2 ⟨quotient.mk' x, mem_univ _,
have (quotient.out' (quotient.mk' x))⁻¹ * x ∈ one_neg_one hp,
  from @quotient.mk_out' _ (left_rel (one_neg_one hp)) x,
by finish [one_neg_one, inv_mul_eq_iff_eq_mul]⟩)) (λ _ _, rfl))
... = _ : by rw prod_univ_units_finite_field; simp

instance ahf : decidable_eq (quotient (one_neg_one hp) × (units (zmodp q hq))) := by apply_instance

noncomputable instance afho : decidable_eq (quotient (one_neg_one' hp hq)) := classical.dec_eq _

lemma prod_product' {α β γ : Type*} [comm_monoid α] [comm_monoid β] (s : finset γ)
  (f : γ → α × β) : s.prod f = (s.prod (λ x, (f x).1), s.prod (λ x, (f x).2)) :=
by haveI := classical.dec_eq γ; exact
finset.induction_on s rfl (by simp [prod.ext_iff] {contextual := tt})

lemma prod_pow {α β : Type} [comm_monoid β] (s : finset α) (n : ℕ) (f : α → β) :
  s.prod (λ x, f x ^ n) = s.prod f ^ n :=
by haveI := classical.dec_eq α; exact
finset.induction_on s (by simp) (by simp [_root_.mul_pow] {contextual := tt})

lemma prod_quotient_one_neg_one₁ (hp1 : p % 2 = 1) (hq1 : q % 2 = 1) :
  (@univ (quotient (one_neg_one' hp hq)) _).prod (λ x, x)
  = mk (-((-1) ^ (p / 2)) ^ (q / 2), (-1) ^ (p / 2)) :=
calc (@univ (quotient (one_neg_one' hp hq)) _).prod (λ x, x)
   = ((@univ (quotient (one_neg_one hp) × (units (zmodp q hq))) _).image (f hp hq)).prod (λ x, x) :
prod_congr (eq.symm (eq_univ_iff_forall.2 (λ x, mem_image.2 (by simpa using f_surjective hp hq x)))) (λ _ _, rfl)
... = univ.prod (λ x : quotient (one_neg_one hp) × units (zmodp q hq),
  mk (quotient.out' x.1, x.2)) : prod_image sorry
... = mk (univ.prod (λ x : quotient (one_neg_one hp) × units (zmodp q hq), (quotient.out' x.1, x.2))) :
prod_hom mk (is_group_hom.one _) (is_group_hom.mul _)
... = mk ((finset.product _ _).prod (λ x : quotient (one_neg_one hp) × units (zmodp q hq), quotient.out' x.1),
  (finset.product _ _).prod (λ x : quotient (one_neg_one hp) × units (zmodp q hq), x.2)) :
congr_arg mk (prod_product' _ _)
... = mk (univ.prod quotient.out' ^ fintype.card (units (zmodp q hq)),
  univ.prod (λ x, x) ^ fintype.card (quotient (one_neg_one hp))) :
by simp [prod_product, prod_pow, fintype.card]
... = mk (-((-1) ^ (p / 2)) ^ (q / 2), (-1) ^ (p / 2)) :
by rw [prod_univ_units_finite_field, card_quotient_one_neg_one _ hp1,
   card_units_zmodp, ← two_mul_odd_div_two hq1, pow_mul, prod_univ_quotient_one_neg_one _ hp1]

lemma lt_neg_iff_le {n : ℕ+} (hn : (n : ℕ) % 2 = 1)
  {x : zmod n} (hx0 : x ≠ 0) (hx : x.1 ≤ (n / 2 : ℕ)) :
  ((n / 2 : ℕ) : zmod n) < (-x).1 :=
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
begin
  rw [← zero_add (-x), ← zmod.cast_self_eq_zero],
  show ((n / 2 : ℕ) : zmod n).val < _,
  rwa [zmod.cast_val, zmod.val_cast_of_lt hn2, ← zmod.cast_val x, ← sub_eq_add_neg,
    ← nat.cast_sub (le_of_lt x.2), zmod.val_cast_of_lt hxn, nat.lt_sub_left_iff_add_lt (le_of_lt x.2),
    ← nat.lt_sub_right_iff_add_lt (le_of_lt hn2), hn2', lt_succ_iff]
end

lemma modeq_of_modeq_mul_right {a b m : ℕ} (n : ℕ)
  (h : a ≡ b [MOD m * n]) : a ≡ b [MOD m] :=
by rw [nat.modeq.modeq_iff_dvd] at *;
  exact dvd.trans (dvd_mul_right (m : ℤ) (n : ℤ)) h

lemma modeq_of_modeq_mul_left {a b m : ℕ} (n : ℕ)
  (h : a ≡ b [MOD n * m]) : a ≡ b [MOD m] :=
by rw mul_comm at h; exact modeq_of_modeq_mul_right _ h

@[simp] lemma zmod.cast_mul_right_val_cast {n m : ℕ+} (a : ℕ) :
  ((a : zmod (m * n)).val : zmod m) = (a : zmod m) :=
zmod.eq_iff_modeq_nat.2 (by rw zmod.val_cast_nat;
  exact modeq_of_modeq_mul_right _ (nat.mod_mod _ _))

lemma zmod.cast_val_cast_of_dvd {n m : ℕ+} (h : (m : ℕ) ∣ n) (a : ℕ) :
  ((a : zmod n).val : zmod m) = (a : zmod m) :=
let ⟨k , hk⟩ := h in
zmod.eq_iff_modeq_nat.2 (modeq_of_modeq_mul_right k
    (by rw [← hk, zmod.val_cast_nat]; exact nat.mod_mod _ _))

@[simp] lemma zmod.cast_mul_left_val_cast {n m : ℕ+} (a : ℕ) :
  ((a : zmod (n * m)).val : zmod m) = (a : zmod m) :=
zmod.eq_iff_modeq_nat.2 (by rw zmod.val_cast_nat;
  exact modeq_of_modeq_mul_left _ (nat.mod_mod _ _))

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

lemma nat.sub_le_self (n m : ℕ) : n - m ≤ n :=
nat.sub_le_left_of_le_add (nat.le_add_left _ _)

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

lemma coprime_mul_iff_left {k m n : ℕ} : coprime (m * n) k ↔ coprime m k ∧ coprime n k :=
⟨λ h, ⟨coprime.coprime_mul_right h, coprime.coprime_mul_left h⟩,
  λ ⟨h, _⟩, by rwa [coprime, coprime.gcd_mul_left_cancel n h]⟩

lemma coprime_mul_iff_right {k m n : ℕ} : coprime k (m * n) ↔ coprime m k ∧ coprime n k :=
by rw [coprime, nat.gcd_comm]; exact coprime_mul_iff_left

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

lemma prod_quotient_one_neg_one₂ (hp1 : p % 2 = 1) (hq1 : q % 2 = 1) :
  (@univ (quotient (one_neg_one' hp hq)) _).prod (λ x, x)
  = mk (-((-1) ^ (p / 2)) ^ (q / 2), (-1) ^ (p / 2)) :=
begin end
-- calc (@univ (quotient (one_neg_one' hp hq)) _).prod (λ x, x)
--     = mk (((((range ((p * q) / 2).succ).filter (coprime (p * q))).prod (λ x, x) : ℕ) : zmodp p hp),
--       ((((range ((p * q) / 2).succ).filter (coprime (p * q))).prod (λ x, x) : ℕ) : zmodp q hq)) :
