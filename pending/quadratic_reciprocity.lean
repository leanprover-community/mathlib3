import data.zmod data.polynomial group_theory.order_of_element linear_algebra.prod_module group_theory.quotient_group
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

def equiv_univ (α : Type*) : α ≃ @set.univ α :=
⟨λ a, ⟨a, trivial⟩, λ a, a.1, λ _, rfl, λ ⟨_, _⟩, rfl⟩

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
    (set.fintype_insert _ _), fintype.card_congr (equiv_univ α)],
  congr; simp [set.ext_iff, classical.em]
end

lemma two_mul_odd_div_two {n : ℕ} (hn : n % 2 = 1) : 2 * (n / 2) = n - 1 :=
by conv {to_rhs, rw [← nat.mod_add_div n 2, hn, nat.add_sub_cancel_left]}

@[simp] lemma pow_card_eq_one {α : Type*} [group α] [fintype α] [decidable_eq α]
  (a : α) : a ^ fintype.card α = 1 :=
let ⟨m, hm⟩ := @order_of_dvd_card_univ _ a _ _ _ in
by simp [hm, pow_mul, pow_order_of_eq_one]

-- @[simp] lemma fermat_little (p : ℕ) {a : zmod p} (ha : a ≠ 0) : a ^ (p - 1) = 1 :=
-- have p - 1 = fintype.card (units (zmod p)) := by rw [card_units, zmod.card_zmod],
-- by rw [← coe_units_of_nonzero ha, ← @units.one_coe (zmod p), ← units.coe_pow, ← units.ext_iff,
--   this, pow_card_eq_one]

open polynomial finset nat

def totient (n : ℕ) : ℕ := ((range n).filter (nat.coprime n)).card

local notation `φ` := totient

lemma totient_le (n : ℕ) : φ n ≤ n :=
calc totient n ≤ (range n).card : card_le_of_subset (filter_subset _)
           ... = n              : card_range _

lemma totient_pos : ∀ {n : ℕ}, 0 < n → 0 < φ n
| 0 := dec_trivial
| 1 := dec_trivial
| (n+2) := λ h, card_pos.2 (mt eq_empty_iff_forall_not_mem.1
(not_forall_of_exists_not ⟨1, not_not.2 $ mem_filter.2 ⟨mem_range.2 dec_trivial, by simp [coprime]⟩⟩))

lemma sum_totient (n : ℕ) : ((range n.succ).filter (∣ n)).sum φ = n :=
if hn0 : n = 0 then by rw hn0; refl
else
calc ((range n.succ).filter (∣ n)).sum φ
    = ((range n.succ).filter (∣ n)).sum (λ d, ((range (n / d)).filter (λ m, gcd (n / d) m = 1)).card) :
eq.symm $ sum_bij (λ d _, n / d)
  (λ d hd, mem_filter.2 ⟨mem_range.2 $ lt_succ_of_le $ nat.div_le_self _ _,
    by conv {to_rhs, rw ← nat.mul_div_cancel' (mem_filter.1 hd).2}; simp⟩)
  (λ _ _, rfl)
  (λ a b ha hb h,
    have ha : a * (n / a) = n, from nat.mul_div_cancel' (mem_filter.1 ha).2,
    have (n / a) > 0, from nat.pos_of_ne_zero (λ h, by simp [*, lt_irrefl] at *),
    by rw [← nat.mul_right_inj this, ha, h, nat.mul_div_cancel' (mem_filter.1 hb).2])
  (λ b hb,
    have hb : b < n.succ ∧ b ∣ n, by simpa [-range_succ] using hb,
    have hbn : (n / b) ∣ n, from ⟨b, by rw nat.div_mul_cancel hb.2⟩,
    have hnb0 : (n / b) ≠ 0, from λ h, by simpa [h, ne.symm hn0] using nat.div_mul_cancel hbn,
    ⟨n / b, mem_filter.2 ⟨mem_range.2 $ lt_succ_of_le $ nat.div_le_self _ _, hbn⟩,
      by rw [← nat.mul_right_inj (nat.pos_of_ne_zero hnb0),
        nat.mul_div_cancel' hb.2, nat.div_mul_cancel hbn]⟩)
... = ((range n.succ).filter (∣ n)).sum (λ d, ((range n).filter (λ m, gcd n m = d)).card) :
sum_congr rfl (λ d hd,
  have hd : d ∣ n, from (mem_filter.1 hd).2,
  have hd0 : 0 < d, from nat.pos_of_ne_zero (λ h, hn0 (eq_zero_of_zero_dvd $ h ▸ hd)),
  card_congr (λ m hm, d * m)
    (λ m hm, have hm : m < n / d ∧ gcd (n / d) m = 1, by simpa using hm,
      mem_filter.2 ⟨mem_range.2 $ nat.mul_div_cancel' hd ▸
        (mul_lt_mul_left hd0).2 hm.1,
        by rw [← nat.mul_div_cancel' hd, gcd_mul_left, hm.2, mul_one]⟩)
    (λ a b ha hb h, (nat.mul_left_inj hd0).1 h)
    (λ b hb, have hb : b < n ∧ gcd n b = d, by simpa using hb,
      ⟨b / d, mem_filter.2 ⟨mem_range.2 ((mul_lt_mul_left (show 0 < d, from hb.2 ▸ hb.2.symm ▸ hd0)).1
          (by rw [← hb.2, nat.mul_div_cancel' (gcd_dvd_left _ _),
            nat.mul_div_cancel' (gcd_dvd_right _ _)]; exact hb.1)),
              hb.2 ▸ coprime_div_gcd_div_gcd (hb.2.symm ▸ hd0)⟩,
        hb.2 ▸ nat.mul_div_cancel' (gcd_dvd_right _ _)⟩))
... = ((filter (∣ n) (range n.succ)).bind (λ d, (range n).filter (λ m, gcd n m = d))).card :
(card_bind (by simp [finset.ext]; cc)).symm
... = (range n).card :
congr_arg card (finset.ext.2 (λ m, ⟨by finish,
  λ hm, have h : m < n, from mem_range.1 hm,
    mem_bind.2 ⟨gcd n m, mem_filter.2 ⟨mem_range.2 (lt_succ_of_le (le_of_dvd (lt_of_le_of_lt (zero_le _) h)
      (gcd_dvd_left _ _))), gcd_dvd_left _ _⟩, mem_filter.2 ⟨hm, rfl⟩⟩⟩))
... = n : card_range _

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
  (calc a = a % b : by simpa [h] using (nat.mod_add_div a b).symm
      ... < b : nat.mod_lt a hb
      ... ≤ a : hba))

lemma div_div_self : ∀ {a b : ℕ}, b ∣ a → 0 < a → a / (a / b) = b
| a     0     h₁ h₂ := by rw eq_zero_of_zero_dvd h₁; refl
| 0     b     h₁ h₂ := absurd h₂ dec_trivial
| (a+1) (b+1) h₁ h₂ :=
(nat.mul_right_inj (nat.div_pos (le_of_dvd (succ_pos a) h₁) (succ_pos b))).1 $
  by rw [nat.div_mul_cancel (div_dvd_of_dvd h₁), nat.mul_div_cancel' h₁]

lemma zero_pow {α : Type*} [semiring α] {n : ℕ} (hn : 0 < n) : (0 : α) ^ n = 0 :=
by cases n; simpa [_root_.pow_succ, lt_irrefl] using hn

lemma card_nth_roots_units {α : Type*} [fintype α] [field α] [decidable_eq α] {n : ℕ} (hn : 0 < n)
  (a : units α) : (univ.filter (λ b, b ^ n = a)).card = (nth_roots n (a : α)).card :=
card_congr (λ a _, a)
  (by simp [mem_nth_roots hn, (units.coe_pow _ _).symm, -units.coe_pow, units.ext_iff.symm])
  (by simp [units.ext_iff.symm])
  (λ b hb, have hb0 : b ≠ 0, from λ h,
    coe_units_ne_zero a $ by rwa [mem_nth_roots hn, h, _root_.zero_pow hn, eq_comm] at hb,
    ⟨units_of_nonzero hb0, by simp [units.ext_iff, (mem_nth_roots hn).1 hb]⟩)

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

lemma gpowers_eq_powers {α : Type*} [group α] [fintype α] (a : α) : gpowers a = powers a :=
by haveI := classical.dec_eq α; exact
set.ext (λ x, ⟨λ ⟨i, hi⟩, ⟨(i % order_of a).nat_abs,
  by rwa [← gpow_coe_nat, int.nat_abs_of_nonneg (int.mod_nonneg _
      (int.coe_nat_ne_zero_iff_pos.2 (order_of_pos _))), ← gpow_eq_mod_order_of]⟩,
λ ⟨n, hn⟩, ⟨n, by simp * at *⟩⟩)

lemma euler_criterion (hp1 : p % 2 = 1) {x : units (zmodp p hp)} :
  (∃ y : units (zmodp p hp), y ^ 2 = x) ↔ x ^ (p / 2) = 1 :=
let ⟨g, hg⟩ := is_cyclic.exists_generator (units (zmodp p hp)) in
let ⟨n, hn⟩ := show x ∈ powers g, from gpowers_eq_powers g ▸ hg x in
⟨λ ⟨y, hy⟩, by rw [← hy, ← pow_mul, two_mul_odd_div_two hp1,
    ← card_units_zmodp hp, pow_card_eq_one],
λ hx, have 2 * (p / 2) ∣ n * (p / 2),
    by rw [two_mul_odd_div_two hp1, ← card_units_zmodp hp, ← is_cyclic.order_of_generator hg];
    exact order_of_dvd_of_pow_eq_one (by rwa [pow_mul, hn]),
  let ⟨m, hm⟩ := dvd_of_mul_dvd_mul_right (nat.div_pos hp.ge_two dec_trivial) this in
  ⟨g ^ m, by rwa [← pow_mul, mul_comm, ← hm]⟩⟩

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
  (∀ x ∈ s, x⁻¹ ∈ s) → (∀ x ∈ s, x⁻¹ ≠ x) → s.prod id = 1 :=
by haveI := classical.dec_eq α; exact
finset.strong_induction_on s
  (λ s ih h₁ h₂, (classical.em (s = ∅)).elim
    (by simp {contextual := tt})
    (λ hs, let ⟨x, hx⟩ := exists_mem_of_ne_empty hs in
    have ih' : ((s.erase x).erase x⁻¹).prod id = 1,
      from ih ((s.erase x).erase x⁻¹)
        ⟨λ x, by simp {contextual := tt}, λ h, by simpa using h hx⟩
        (λ y hy, by simp [*, eq_inv_iff_eq_inv] at *; cc)
        (by simp; tauto),
    by rw [← insert_erase hx, ← insert_erase (mem_erase.2 ⟨h₂ x hx, h₁ x hx⟩),
         prod_insert, prod_insert, ih'];
       simp [ne.symm (h₂ x hx)]))

/-- generalization of Wilson's lemma -/
lemma prod_univ_units_finite_field {α : Type*} [fintype α] [field α] [decidable_eq α] : univ.prod id = (-1 : units α) :=
have h₁ : ∀ x : units α, x ∈ (univ.erase (-1 : units α)).erase 1 → x⁻¹ ∈ (univ.erase (-1 : units α)).erase 1,
  from λ x, by rw [mem_erase, mem_erase, mem_erase, mem_erase, ne.def, ne.def, ne.def,
    ne.def, inv_eq_iff_inv_eq, one_inv, inv_eq_iff_inv_eq]; simp; cc,
have h₂ : ∀ x : units α, x ∈ (univ.erase (-1 : units α)).erase 1 → x⁻¹ ≠ x,
  from λ x, by  rw [ne.def, units.inv_eq_self_iff]; finish,
calc univ.prod id = (insert (1 : units α) (insert (-1 : units α) ((univ.erase (-1 : units α)).erase 1))).prod id :
  by congr; simp [finset.ext]; tauto
... = -((univ.erase (-1 : units α)).erase 1).prod id :
  if h : (1 : units α) = -1
  then by rw [insert_eq_of_mem, prod_insert]; simp *; cc
  else by rw [prod_insert, prod_insert]; simp *
... = -1 : by rw [prod_finset_distinct_inv h₁ h₂]

open quotient_group zmodp

instance : decidable_eq (zmodp p hp) := fin.decidable_eq _

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

@[simp] lemma units.neg_eq_neg {α : Type*} [ring α] {a b : units α} : -a = - b ↔ a = b :=
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
  begin
    split_ifs;
    simp [*, prod.ext_iff, mul_eq_one_iff_eq_inv, one_neg_one, f, one_neg_one'] at *
  end⟩)

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
... = univ.prod (λ x : quotient (one_neg_one hp), finset.prod {quotient.out' x, -quotient.out' x} id) * (-1) ^ (p / 2) :
(mul_right_inj _).2 $ prod_congr rfl $ λ x,
  by rw [has_insert_eq_insert, prod_insert];
  simpa [eq_comm] using ne_neg_self hp hp1 (quotient.out' x)
... = (univ.bind (λ x : quotient (one_neg_one hp), {quotient.out' x, -quotient.out' x})).prod id * (-1) ^ (p / 2) :
(mul_right_inj _).2 (eq.symm (prod_bind (λ x _ y _, quotient.induction_on₂' x y
  (λ x y h, begin have : x⁻¹ * y ∉ _, from mt quotient_group.eq.2 h,
    -- have : x⁻¹ * (quotient.out' (quotient.mk' x : quotient (one_neg_one hp))) ∈ one_neg_one hp,
    --   from sorry,
    have : (quotient.out' (quotient.mk' y))⁻¹ * y ∈ one_neg_one hp,
      from @quotient.mk_out' _ (left_rel (one_neg_one hp)) y,
  sorry end))))
... = univ.prod id * (-1) ^ (p/2) :
(mul_right_inj _).2 (prod_congr (eq_univ_iff_forall.2 (λ x, mem_bind.2 ⟨quotient.mk' x, mem_univ _,
have (quotient.out' (quotient.mk' x))⁻¹ * x ∈ one_neg_one hp,
  from @quotient.mk_out' _ (left_rel (one_neg_one hp)) x,
by finish [one_neg_one, inv_mul_eq_iff_eq_mul]⟩)) (λ _ _, rfl))
... = _ : by rw prod_univ_units_finite_field; simp

def thing : ℕ → Type := λ n : ℕ, 
well_founded.fix nat.lt_wf (λ (x) (ih : Π (y : ℕ), nat.lt y x → Type), 
  Π (m : fin x), ih m.1 m.2 → bool) n

lemma thing_eq : thing = 
  (λ n, (Π m : fin n, thing m.1 → bool)) :=
begin
  funext,
  rw [thing],
  dsimp, 
  rw [well_founded.fix_eq]
end

instance : ∀ n : ℕ, fintype (thing n)
| 0 := ⟨finset.singleton (begin rw thing_eq, exact λ ⟨m, hm⟩, (nat.not_lt_zero _ hm).elim end),
  λ x, mem_singleton.2 (funext $ λ ⟨m, hm⟩, (nat.not_lt_zero _ hm).elim)⟩
| (n+1) := begin
  haveI : ∀ m : fin (n + 1), fintype (thing m.1) := 
    λ m, have m.1 < n + 1, from m.2, thing.fintype m.1,
  rw thing_eq,
  apply_instance
end

#eval fintype.card (thing 4)

example (n : nat) : thing n = sorry := 
begin
  rw thing_eq, rw thing_eq, rw thing_eq, rw thing_eq, rw thing_eq, rw thing_eq,
  dsimp,
end

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
  (@univ (quotient (one_neg_one' hp hq)) _).prod id
  = mk (-((-1) ^ (p / 2)) ^ (q / 2), (-1) ^ (p / 2)) :=
calc (@univ (quotient (one_neg_one' hp hq)) _).prod id
   = ((@univ (quotient (one_neg_one hp) × (units (zmodp q hq))) _).image (f hp hq)).prod id :
prod_congr (eq.symm (eq_univ_iff_forall.2 (λ x, mem_image.2 (by simpa using f_surjective hp hq x)))) (λ _ _, rfl)
... = univ.prod (λ x : quotient (one_neg_one hp) × units (zmodp q hq),
  mk (quotient.out' x.1, x.2)) : prod_image sorry
... = mk (univ.prod (λ x : quotient (one_neg_one hp) × units (zmodp q hq), (quotient.out' x.1, x.2))) :
prod_hom mk (is_group_hom.one _) (is_group_hom.mul _)
... = mk ((finset.product _ _).prod (λ x : quotient (one_neg_one hp) × units (zmodp q hq), quotient.out' x.1),
  (finset.product _ _).prod (λ x : quotient (one_neg_one hp) × units (zmodp q hq), x.2)) :
congr_arg mk (prod_product' _ _)
... = mk (univ.prod quotient.out' ^ fintype.card (units (zmodp q hq)),
  univ.prod id ^ fintype.card (quotient (one_neg_one hp))) :
by simp [prod_product, prod_pow, fintype.card]
... = mk (-((-1) ^ (p / 2)) ^ (q / 2), (-1) ^ (p / 2)) :
by rw [prod_univ_units_finite_field, card_quotient_one_neg_one _ hp1,
   card_units_zmodp, ← two_mul_odd_div_two hq1, pow_mul, prod_univ_quotient_one_neg_one _ hp1]

lemma prod_quotient_one_neg_one₂ (hp1 : p % 2 = 1) (hq1 : q % 2 = 1) :
  (@univ (quotient (one_neg_one' hp hq)) _).prod id = 
  mk ((-1) ^ (p / 2) * (units_of_nonzero (show q ≠ 0)) ^ (q / 2), (-1) ^ (p / 2)) := sorry
