/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Chris Hughes

Define the p-adic valuation on ℤ and ℚ, and the p-adic norm on ℚ
-/

import data.rat data.int.gcd algebra.field_power data.nat.enat
import ring_theory.unique_factorization_domain
import tactic.ring tactic.abel

universe u
open nat roption



attribute [class] nat.prime

private lemma exi_div (p : ℕ) (n : ℤ) : ∃ k : ℕ, k ≤ n.nat_abs ∧ ↑(p ^ k) ∣ n :=
⟨0, nat.zero_le _, by simp⟩

private lemma bound {p : ℕ} (hp : p > 1) {n : ℤ} (hn : n ≠ 0) :
  ∀ k : ℕ, k > n.nat_abs → ¬ (↑(p ^ k) ∣ n) :=
assume k (hkn : k > n.nat_abs),
have n.nat_abs < p^k, from lt.trans (lt_pow_self hp _) (pow_lt_pow_of_lt_right hp hkn),
assume hdvd : ↑(p ^ k) ∣ n,
have hdvd' : (p ^ k) ∣ n.nat_abs, from int.dvd_nat_abs_of_of_nat_dvd hdvd,
let hle := le_of_dvd (int.nat_abs_pos_of_ne_zero hn) hdvd' in
not_le_of_gt this hle

variables {α : Type*}

def padic_val [comm_semiring α] [decidable_rel ((∣) : α → α → Prop)] (a b : α) : enat :=
⟨∃ n : ℕ, ¬a ^ (n + 1) ∣ b, λ h, nat.find h⟩

namespace padic_val

section comm_semiring
variables [comm_semiring α] [decidable_rel ((∣) : α → α → Prop)]

@[reducible] def finite (a b : α) : Prop := (padic_val a b).dom

lemma finite_def {a b : α} : finite a b ↔ ∃ n : ℕ, ¬a ^ (n + 1) ∣ b := iff.rfl

lemma not_finite_iff_forall {a b : α} : (¬ finite a b) ↔ ∀ n : ℕ, a ^ n ∣ b :=
⟨λ h n, nat.cases_on n (one_dvd _) (by simpa [finite, padic_val] using h),
  by simp [finite, padic_val]; tauto⟩

lemma not_unit_of_finite {a b : α} (h : finite a b) : ¬is_unit a :=
let ⟨n, hn⟩ := h in mt (is_unit_iff_forall_dvd.1 ∘ is_unit_pow (n + 1)) $
λ h, hn (h b)

lemma ne_zero_of_finite {a b : α} (h : finite a b) : b ≠ 0 :=
let ⟨n, hn⟩ := h in λ hb, by simpa [hb] using hn

lemma pow_dvd_of_le_padic_val {a b : α}
  {k : ℕ} : (k : enat) ≤ padic_val a b → a ^ k ∣ b :=
nat.cases_on k (λ _, one_dvd _)
  (λ k ⟨h₁, h₂⟩, by_contradiction (λ hk, (nat.find_min _ (lt_of_succ_le (h₂ ⟨k, hk⟩)) hk)))

lemma spec {a b : α} (h : finite a b) : a ^ get (padic_val a b) h ∣ b :=
pow_dvd_of_le_padic_val (by rw enat.coe_get)

lemma is_greatest {a b : α} {m : ℕ} (hm : padic_val a b < m) : ¬a ^ m ∣ b :=
λ h, have finite a b, from enat.dom_of_le_some (le_of_lt hm),
by rw [← enat.coe_get this, enat.coe_lt_coe] at hm;
  exact nat.find_spec this (dvd.trans (pow_dvd_pow _ hm) h)

lemma is_greatest' {a b : α} {m : ℕ} (h : finite a b) (hm : get (padic_val a b) h < m) :
  ¬a ^ m ∣ b :=
is_greatest (by rwa [← enat.coe_lt_coe, enat.coe_get] at hm)

lemma unique {a b : α} {k : ℕ} (hk : a ^ k ∣ b) (hsucc : ¬a ^ (k + 1) ∣ b) :
  (k : enat) = padic_val a b :=
le_antisymm (le_of_not_gt (λ hk', is_greatest hk' hk)) $
  have finite a b, from ⟨k, hsucc⟩,
  by rw [← enat.coe_get this, enat.coe_le_coe];
    exact nat.find_min' _ hsucc

lemma unique' {a b : α} {k : ℕ} (hk : a ^ k ∣ b) (hsucc : ¬ a ^ (k + 1) ∣ b) :
  k = get (padic_val a b) ⟨k, hsucc⟩ :=
by rw [← enat.coe_inj, enat.coe_get, unique hk hsucc]

lemma le_padic_val_of_pow_dvd {a b : α}
  {k : ℕ} (hk : a ^ k ∣ b) : (k : enat) ≤ padic_val a b :=
le_of_not_gt $ λ hk', is_greatest hk' hk

lemma pow_dvd_iff_le_padic_val {a b : α}
  {k : ℕ} : a ^ k ∣ b ↔ (k : enat) ≤ padic_val a b :=
⟨le_padic_val_of_pow_dvd, pow_dvd_of_le_padic_val⟩

lemma eq_some_iff {a b : α} {n : ℕ} :
  padic_val a b = (n : enat) ↔ a ^ n ∣ b ∧ ¬a ^ (n + 1) ∣ b :=
⟨λ h, let ⟨h₁, h₂⟩ := eq_some_iff.1 h in
    h₂ ▸ ⟨spec _, is_greatest
      (by conv_lhs {rw ← enat.coe_get h₁ }; rw [enat.coe_lt_coe]; exact lt_succ_self _)⟩,
  λ h, eq_some_iff.2 ⟨⟨n, h.2⟩, eq.symm $ unique' h.1 h.2⟩⟩

lemma eq_top_iff {a b : α} :
  padic_val a b = ⊤ ↔ ∀ n : ℕ, a ^ n ∣ b :=
⟨λ h n, nat.cases_on n (one_dvd _)
  (λ n, by_contradiction (not_exists.1 (eq_none_iff'.1 h) n : _)),
   λ h, eq_none_iff.2 (λ n ⟨⟨_, h₁⟩, _⟩, h₁ (h _))⟩

@[simp] protected lemma zero (a : α) : padic_val a 0 = ⊤ :=
roption.eq_none_iff.2 (λ n ⟨⟨k, hk⟩, _⟩, hk (dvd_zero _))

lemma one_right {a : α} (ha : ¬is_unit a) : padic_val a 1 = 0 :=
eq_some_iff.2 ⟨dvd_refl _, mt is_unit_iff_dvd_one.2 $ by simpa⟩

@[simp] lemma get_one_right {a : α} (ha : finite a 1) : get (padic_val a 1) ha = 0 :=
get_eq_iff_eq_some.2 (eq_some_iff.2 ⟨dvd_refl _,
  by simpa [is_unit_iff_dvd_one.symm] using not_unit_of_finite ha⟩)

@[simp] lemma one_left (b : α) : padic_val 1 b = ⊤ := by simp [eq_top_iff]

@[simp] lemma padic_val_unit {a : α} (b : α) (ha : is_unit a) : padic_val a b = ⊤ :=
eq_top_iff.2 (λ _, is_unit_iff_forall_dvd.1 (is_unit_pow _ ha) _)

lemma padic_val_eq_zero_of_not_dvd {a b : α} (ha : ¬a ∣ b) : padic_val a b = 0 :=
eq_some_iff.2 (by simpa)

-- lemma padic_val_eq_zero_of_not_dvd' {p : ℕ} {n : ℕ} (hnd : ¬ p ∣ n) : padic_val p n = 0 :=
-- by apply padic_val_eq_zero_of_not_dvd; simpa [int.coe_nat_dvd] using hnd

lemma finite_of_finite_mul_left {a b c : α} : finite a (b * c) → finite a c :=
λ ⟨n, hn⟩, ⟨n, λ h, hn (dvd.trans h (by simp [_root_.mul_pow]))⟩

lemma finite_of_finite_mul_right {a b c : α} : finite a (b * c) → finite a b :=
by rw mul_comm; exact finite_of_finite_mul_left

lemma eq_top_iff_not_finite {a b : α} : padic_val a b = ⊤ ↔ ¬ finite a b :=
roption.eq_none_iff'

local attribute [instance, priority 0] classical.prop_decidable

lemma padic_val_le_padic_val_iff {a b c d : α} : padic_val a b ≤ padic_val c d ↔
  (∀ n : ℕ, a ^ n ∣ b → c ^ n ∣ d) :=
⟨λ h n hab, (pow_dvd_of_le_padic_val (le_trans (le_padic_val_of_pow_dvd hab) h)),
  λ h, if hab : finite a b
    then by rw [← enat.coe_get hab]; exact le_padic_val_of_pow_dvd (h _ (spec _))
    else
    have ∀ n : ℕ, c ^ n ∣ d, from λ n, h n (not_finite_iff_forall.1 hab _),
    by rw [eq_top_iff_not_finite.2 hab, eq_top_iff_not_finite.2
      (not_finite_iff_forall.2 this)]⟩

lemma min_le_padic_val_add {p a b : α} :
  min (padic_val p a) (padic_val p b) ≤ padic_val p (a + b) :=
(le_total (padic_val p a) (padic_val p b)).elim
  (λ h, by rw [min_eq_left h, padic_val_le_padic_val_iff];
    exact λ n hn, dvd_add hn (padic_val_le_padic_val_iff.1 h n hn))
  (λ h, by rw [min_eq_right h, padic_val_le_padic_val_iff];
    exact λ n hn, dvd_add (padic_val_le_padic_val_iff.1 h n hn) hn)

lemma dvd_of_padic_val_pos {a b : α} (h : (0 : enat) < padic_val a b) : a ∣ b :=
by rw [← _root_.pow_one a]; exact pow_dvd_of_le_padic_val (enat.pos_iff_one_le.1 h)

lemma finite_nat_iff {a b : ℕ} : finite a b ↔ (a ≠ 1 ∧ 0 < b) :=
begin
  rw [← not_iff_not, not_finite_iff_forall, not_and_distrib, ne.def,
    not_not, not_lt, nat.le_zero_iff],
  exact ⟨λ h, or_iff_not_imp_right.2 (λ hb,
    have ha : a ≠ 0, from λ ha, by simpa [ha] using h 1,
    by_contradiction (λ ha1 : a ≠ 1,
      have ha_gt_one : 1 < a, from
        have ∀ a : ℕ, a ≤ 1 → a ≠ 0 → a ≠ 1 → false, from dec_trivial,
        lt_of_not_ge (λ ha', this a ha' ha ha1),
      not_lt_of_ge (le_of_dvd (nat.pos_of_ne_zero hb) (h b))
          (by simp only [nat.pow_eq_pow]; exact lt_pow_self ha_gt_one b))),
    λ h, by cases h; simp *⟩
end

lemma finite_int_iff_nat_abs_finite {a b : ℤ} : finite a b ↔ finite a.nat_abs b.nat_abs :=
begin
  rw [finite_def, finite_def],
  conv in (a ^ _ ∣ b)
    { rw [← int.nat_abs_dvd_abs_iff, int.nat_abs_pow, ← pow_eq_pow] }
end

lemma finite_int_iff {a b : ℤ} : finite a b ↔ (a.nat_abs ≠ 1 ∧ b ≠ 0) :=
begin
  have := int.nat_abs_eq a,
  have := @int.nat_abs_ne_zero_of_ne_zero b,
  rw [finite_int_iff_nat_abs_finite, finite_nat_iff, nat.pos_iff_ne_zero'],
  split; finish
end

instance decidable_nat : decidable_rel (λ a b : ℕ, (padic_val a b).dom) :=
λ a b, decidable_of_iff _ finite_nat_iff.symm

instance decidable_int : decidable_rel (λ a b : ℤ, (padic_val a b).dom) :=
λ a b, decidable_of_iff _ finite_int_iff.symm

end comm_semiring

section comm_ring

variables [comm_ring α] [decidable_rel ((∣) : α → α → Prop)]

local attribute [instance, priority 0] classical.prop_decidable

@[simp] protected lemma neg (a b : α) : padic_val a (-b) = padic_val a b :=
roption.ext' (by simp only [padic_val]; conv in (_ ∣ - _) {rw dvd_neg})
  (λ h₁ h₂, enat.coe_inj.1 (by rw [enat.coe_get]; exact
    eq.symm (unique ((dvd_neg _ _).2 (spec _))
      (mt (dvd_neg _ _).1 (is_greatest' _ (lt_succ_self _))))))

end comm_ring

section integral_domain

variables [integral_domain α] [decidable_rel ((∣) : α → α → Prop)]

@[simp] lemma padic_val_self {a : α} (ha : ¬is_unit a) (ha0 : a ≠ 0) :
  padic_val a a = 1 :=
eq_some_iff.2 ⟨by simp, λ ⟨b, hb⟩, ha (is_unit_iff_dvd_one.2
  ⟨b, (domain.mul_left_inj ha0).1 $ by clear _fun_match;
    simpa [_root_.pow_succ, mul_assoc] using hb⟩)⟩

@[simp] lemma get_padic_val_self {a : α} (ha : finite a a) :
  get (padic_val a a) ha = 1 :=
roption.get_eq_iff_eq_some.2 (eq_some_iff.2
  ⟨by simp, λ ⟨b, hb⟩,
    by rw [← mul_one a, _root_.pow_add, _root_.pow_one, mul_assoc, mul_assoc,
        domain.mul_left_inj (ne_zero_of_finite ha)] at hb;
      exact mt is_unit_iff_dvd_one.2 (not_unit_of_finite ha)
        ⟨b, by clear _fun_match; simp * at *⟩⟩)

lemma finite_mul_aux {p : α} (hp : prime p) : ∀ {n m : ℕ} {a b : α},
  ¬p ^ (n + 1) ∣ a → ¬p ^ (m + 1) ∣ b → ¬p ^ (n + m + 1) ∣ a * b
| n m := λ a b ha hb ⟨s, hs⟩,
  have p ∣ a * b, from ⟨p ^ (n + m) * s,
    by simp [hs, _root_.pow_add, mul_comm, mul_assoc, mul_left_comm]⟩,
  (hp.2.2 a b this).elim
    (λ ⟨x, hx⟩, have hn0 : 0 < n,
        from nat.pos_of_ne_zero (λ hn0, by clear _fun_match _fun_match; simpa [hx, hn0] using ha),
      have wf : (n - 1) < n, from nat.sub_lt_self hn0 dec_trivial,
      have hpx : ¬ p ^ (n - 1 + 1) ∣ x,
        from λ ⟨y, hy⟩, ha (hx.symm ▸ ⟨y, (domain.mul_left_inj hp.1).1
          $ by rw [nat.sub_add_cancel hn0] at hy;
            simp [hy, _root_.pow_add, mul_comm, mul_assoc, mul_left_comm]⟩),
      have 1 ≤ n + m, from le_trans hn0 (le_add_right n m),
      finite_mul_aux hpx hb ⟨s, (domain.mul_left_inj hp.1).1 begin
          rw [← nat.sub_add_comm hn0, nat.sub_add_cancel this],
          clear _fun_match _fun_match finite_mul_aux,
          simp [*, mul_comm, mul_assoc, mul_left_comm, _root_.pow_add] at *
        end⟩)
    (λ ⟨x, hx⟩, have hm0 : 0 < m,
        from nat.pos_of_ne_zero (λ hm0, by clear _fun_match _fun_match; simpa [hx, hm0] using hb),
      have wf : (m - 1) < m, from nat.sub_lt_self hm0 dec_trivial,
      have hpx : ¬ p ^ (m - 1 + 1) ∣ x,
        from λ ⟨y, hy⟩, hb (hx.symm ▸ ⟨y, (domain.mul_left_inj hp.1).1
          $ by rw [nat.sub_add_cancel hm0] at hy;
            simp [hy, _root_.pow_add, mul_comm, mul_assoc, mul_left_comm]⟩),
      finite_mul_aux ha hpx ⟨s, (domain.mul_left_inj hp.1).1 begin
          rw [add_assoc, nat.sub_add_cancel hm0],
          clear _fun_match _fun_match finite_mul_aux,
          simp [*, mul_comm, mul_assoc, mul_left_comm, _root_.pow_add] at *
        end⟩)

lemma finite_mul {p a b : α} (hp : prime p) : finite p a → finite p b → finite p (a * b) :=
λ ⟨n, hn⟩ ⟨m, hm⟩, ⟨n + m, finite_mul_aux hp hn hm⟩

lemma finite_mul_iff {p a b : α} (hp : prime p) : finite p (a * b) ↔ finite p a ∧ finite p b :=
⟨λ h, ⟨finite_of_finite_mul_right h, finite_of_finite_mul_left h⟩,
  λ h, finite_mul hp h.1 h.2⟩

lemma finite_pow {p a : α} (hp : prime p) : Π {k : ℕ} (ha : finite p a), finite p (a ^ k)
| 0     ha := ⟨0, by simp [mt is_unit_iff_dvd_one.2 hp.2.1]⟩
| (k+1) ha := by rw [_root_.pow_succ]; exact finite_mul hp ha (finite_pow ha)

protected lemma mul' {p a b : α} (hp : prime p)
  (h : finite p (a * b)) :
  get (padic_val p (a * b)) h =
  get (padic_val p a) ((finite_mul_iff hp).1 h).1 +
  get (padic_val p b) ((finite_mul_iff hp).1 h).2 :=
have hdiva : p ^ get (padic_val p a) ((finite_mul_iff hp).1 h).1 ∣ a, from spec _,
have hdivb : p ^ get (padic_val p b) ((finite_mul_iff hp).1 h).2 ∣ b, from spec _,
have hpoweq : p ^ (get (padic_val p a) ((finite_mul_iff hp).1 h).1 +
    get (padic_val p b) ((finite_mul_iff hp).1 h).2) =
    p ^ get (padic_val p a) ((finite_mul_iff hp).1 h).1 *
    p ^ get (padic_val p b) ((finite_mul_iff hp).1 h).2,
  by simp [_root_.pow_add],
have hdiv : p ^ (get (padic_val p a) ((finite_mul_iff hp).1 h).1 +
    get (padic_val p b) ((finite_mul_iff hp).1 h).2) ∣ a * b,
  by rw [hpoweq]; apply mul_dvd_mul; assumption,
have hsucc : ¬p ^ ((get (padic_val p a) ((finite_mul_iff hp).1 h).1 +
    get (padic_val p b) ((finite_mul_iff hp).1 h).2) + 1) ∣ a * b,
  from λ h, not_or (is_greatest' _ (lt_succ_self _)) (is_greatest' _ (lt_succ_self _))
    (succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul hp (by convert hdiva)
      (by convert hdivb) h),
by rw [← enat.coe_inj, enat.coe_get, eq_some_iff];
  exact ⟨hdiv, hsucc⟩

local attribute [instance, priority 0] classical.prop_decidable

protected lemma mul {p a b : α} (hp : prime p) :
  padic_val p (a * b) = padic_val p a + padic_val p b :=
if h : finite p a ∧ finite p b then
by rw [← enat.coe_get h.1, ← enat.coe_get h.2, ← enat.coe_get (finite_mul hp h.1 h.2),
    ← enat.coe_add, enat.coe_inj, padic_val.mul' hp]
else begin
  rw [eq_top_iff_not_finite.2 (mt (finite_mul_iff hp).1 h)],
  cases not_and_distrib.1 h with h h;
    simp [eq_top_iff_not_finite.2 h]
end

protected lemma pow' {p a : α} (hp : prime p) (ha : finite p a) : ∀ {k : ℕ},
  get (padic_val p (a ^ k)) (finite_pow hp ha) = k * get (padic_val p a) ha
| 0     := by dsimp [_root_.pow_zero]; simp [one_right hp.2.1]; refl
| (k+1) := by dsimp only [_root_.pow_succ];
  erw [padic_val.mul' hp, pow', add_mul, one_mul, add_comm]

lemma pow {p a : α} (hp : prime p) : ∀ {k : ℕ},
  padic_val p (a ^ k) = add_monoid.smul k (padic_val p a)
| 0        := by simp [one_right hp.2.1]
| (succ k) := by simp [_root_.pow_succ, succ_smul, pow, padic_val.mul hp]

end integral_domain

variables [integral_domain α] [unique_factorization_domain α]
variables [decidable_rel ((∣) : α → α → Prop)]
open associates

local attribute [instance, priority 0] classical.prop_decidable

lemma finite_of_is_not_unit {a b : α} (ha : ¬is_unit a) (hb0 : b ≠ 0) : finite a b :=
if ha0 : a = 0 then ⟨0, by simp *⟩
else
  have has : option.is_some (factors (associates.mk a)),
    from is_some_factors_iff.2 (mt mk_eq_zero_iff_eq_zero.1 ha0),
  have hbs : option.is_some (factors (associates.mk b)),
    from is_some_factors_iff.2 (mt mk_eq_zero_iff_eq_zero.1 hb0),
  ⟨(option.get hbs).card,
    λ hn, lt_irrefl (option.get hbs).card
    (calc (option.get hbs).card
          < (option.get hbs).card + 1 : lt_succ_self _
      ... ≤ (multiset.card (option.get hbs) + 1) * multiset.card (option.get has) :
        le_mul_of_ge_one_right' (nat.zero_le _)
          (multiset.card_pos.2
            (mt (congr_arg (λ s, factor_set.prod (option.some s)))
              (by rw [option.some_get, factors_prod];
                exact mt (is_unit_iff_eq_one _).2
                  (mt is_unit_mk.1 ha))))
      ... ≤ (option.get hbs).card : begin
        rw [← multiset.card_smul],
        refine multiset.card_le_of_le (with_top.coe_le_coe.1 _),
        rw [factor_set.coe_smul, factor_set.coe_get,
          factor_set.coe_get, ← factors_pow, ← associates.mk_pow],
        exact factors_mono (mk_le_mk_of_dvd hn)
      end)⟩

lemma finite_of_prime {p a : α} (hp : prime p) (ha0 : a ≠ 0) : finite p a :=
finite_of_is_not_unit hp.2.1 ha0

end padic_val

section nat
open padic_val

lemma padic_val_eq_zero_of_coprime {p a b : ℕ} (hp : p ≠ 1)
  (hle : padic_val p a ≤ padic_val p b)
  (hab : nat.coprime a b) : padic_val p a = 0 :=
begin
  rw [padic_val_le_padic_val_iff] at hle,
  rw [← le_zero_iff_eq, ← not_lt, enat.pos_iff_one_le, ← enat.coe_one,
    ← pow_dvd_iff_le_padic_val],
  assume h,
  have := nat.dvd_gcd h (hle _ h),
  rw [coprime.gcd_eq_one hab, nat.dvd_one, _root_.pow_one] at this,
  exact hp this
end

end nat

local infix `/.`:70 := rat.mk

open padic_val

def padic_val_rat (p : ℕ) (q : ℚ) : ℤ :=
if h : q ≠ 0 ∧ p ≠ 1
then (padic_val (p : ℤ) q.num).get
    (padic_val.finite_int_iff.2 ⟨h.2, rat.num_ne_zero_of_ne_zero h.1⟩) -
  (padic_val (p : ℤ) q.denom).get
    (padic_val.finite_int_iff.2 ⟨h.2, ne.symm $ ne_of_lt (int.coe_nat_pos.2 q.3)⟩)
else 0

namespace padic_val_rat
open padic_val
section padic_val_rat
variables {p : ℕ}

@[simp] protected lemma neg (q : ℚ) : padic_val_rat p (-q) = padic_val_rat p q :=
begin
  unfold padic_val_rat,
  split_ifs,
  { simp [-add_comm] },
  { exfalso, simp * at * },
  { exfalso, simp * at * },
  { refl }
end

@[simp] protected lemma one : padic_val_rat p 1 = 0 :=
by unfold padic_val_rat; split_ifs; simp *

@[simp] lemma padic_val_rat_self (hp : 1 < p) : padic_val_rat p p = 1 :=
by unfold padic_val_rat; split_ifs; simp [*, nat.one_lt_iff_ne_zero_and_ne_one] at *

lemma padic_val_rat_of_int (z : ℤ) (hp : p ≠ 1) (hz : z ≠ 0) :
  padic_val_rat p (z : ℚ) = (padic_val (p : ℤ) z).get
    (finite_int_iff.2 ⟨hp, hz⟩) :=
by rw [padic_val_rat, dif_pos]; simp *

end padic_val_rat

section padic_val_rat
open padic_val
variables (p : ℕ) [p_prime : nat.prime p]
include p_prime

lemma padic_val_rat_def {q : ℚ} (hq : q ≠ 0) : padic_val_rat p q =
(padic_val (p : ℤ) q.num).get (finite_int_iff.2 ⟨p_prime.ne_one, rat.num_ne_zero_of_ne_zero hq⟩) -
(padic_val (p : ℤ) q.denom).get (finite_int_iff.2 ⟨p_prime.ne_one, rat.num_ne_zero_of_ne_zero hq⟩)

lemma prime_int_of_nat_prime : _root_.prime (p : ℤ) :=
⟨int.coe_nat_ne_zero_iff_pos.2 p_prime.pos,
  mt is_unit_iff_dvd_one.1 (mt int.coe_nat_dvd.1 p_prime.not_dvd_one),
  (λ a b ha, begin
    have : p ∣ a.nat_abs * b.nat_abs,
    { rwa [← int.nat_abs_mul, ← int.coe_nat_dvd, int.dvd_nat_abs] },
    cases p_prime.dvd_mul.1 this;
    rw [← int.coe_nat_dvd, int.dvd_nat_abs] at h; simp [h]
  end)⟩

lemma finite_int_prime_iff {p : ℕ} [p_prime : p.prime] {a : ℤ} : finite (p : ℤ) a ↔ a ≠ 0 :=
by simp [finite_int_iff, ne.symm (ne_of_lt (p_prime.gt_one))]

protected lemma defn {q : ℚ} {n d : ℤ} (hqz : q ≠ 0) (qdf : q = n /. d) :
  padic_val_rat p q = (padic_val (p : ℤ) n).get (finite_int_iff.2
    ⟨ne.symm $ ne_of_lt p_prime.gt_one, λ hn, by simp * at *⟩) -
  (padic_val (p : ℤ) d).get (finite_int_iff.2 ⟨ne.symm $ ne_of_lt p_prime.gt_one,
    λ hd, by simp * at *⟩) :=
have hn : n ≠ 0, from rat.mk_num_ne_zero_of_ne_zero hqz qdf,
have hd : d ≠ 0, from rat.mk_denom_ne_zero_of_ne_zero hqz qdf,
let ⟨c, hc1, hc2⟩ := rat.num_denom_mk hn hd qdf in
by rw [padic_val_rat, dif_pos];
  simp [hc1, hc2, padic_val.mul' (prime_int_of_nat_prime p),
    (ne.symm (ne_of_lt p_prime.gt_one)), hqz]

-- #print padic_val_mul'

protected lemma mul {q r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) :
  padic_val_rat p (q * r) = padic_val_rat p q + padic_val_rat p r :=
have q*r = (q.num * r.num) /. (↑q.denom * ↑r.denom), by simp [rat.mul_num_denom],
have hq' : q.num /. q.denom ≠ 0, by simpa [(rat.num_denom _).symm],
have hr' : r.num /. r.denom ≠ 0, by simpa [(rat.num_denom _).symm],
have hp' : prime (p : ℤ), from prime_int_of_nat_prime p,
begin
  rw [padic_val_rat.defn p (mul_ne_zero hq hr) this],
  conv_rhs { rw [rat.num_denom q, padic_val_rat.defn p hq',
    rat.num_denom r, padic_val_rat.defn p hr'] },
  rw [padic_val.mul', padic_val.mul']; simp *
end

protected lemma pow {q : ℚ} (hq : q ≠ 0) {k : ℕ} :
    padic_val_rat p (q ^ k) = k * padic_val_rat p q :=
by induction k; simp [*, padic_val_rat.mul _ hq (pow_ne_zero _ hq),
  _root_.pow_succ, add_mul]

protected lemma inv {q : ℚ} (hq : q ≠ 0) :
  padic_val_rat p (q⁻¹) = -padic_val_rat p q :=
by rw [eq_neg_iff_add_eq_zero, ← padic_val_rat.mul p (inv_ne_zero hq) hq,
    inv_mul_cancel hq, padic_val_rat.one]

protected lemma div {q r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) :
  padic_val_rat p (q / r) = padic_val_rat p q - padic_val_rat p r :=
by rw [div_eq_mul_inv, padic_val_rat.mul p hq (inv_ne_zero hr),
    padic_val_rat.inv p hr, sub_eq_add_neg]

lemma padic_val_rat_le_padic_val_rat_iff {n₁ n₂ d₁ d₂ : ℤ}
  (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0) (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) :
  padic_val_rat p (n₁ /. d₁) ≤ padic_val_rat p (n₂ /. d₂) ↔
  ∀ (n : ℕ), ↑p ^ n ∣ n₁ * d₂ → ↑p ^ n ∣ n₂ * d₁ :=
have hf1 : finite (p : ℤ) (n₁ * d₂),
  from finite_int_prime_iff.2 (mul_ne_zero hn₁ hd₂),
have hf2 : finite (p : ℤ) (n₂ * d₁),
  from finite_int_prime_iff.2 (mul_ne_zero hn₂ hd₁),
by conv {to_lhs, rw [padic_val_rat.defn p (rat.mk_ne_zero_of_ne_zero hn₁ hd₁) rfl,
    padic_val_rat.defn p (rat.mk_ne_zero_of_ne_zero hn₂ hd₂) rfl,
    sub_le_iff_le_add', ← add_sub_assoc, le_sub_iff_add_le,
    ← int.coe_nat_add, ← int.coe_nat_add, int.coe_nat_le,
    ← padic_val.mul' (prime_int_of_nat_prime p) hf1, add_comm,
    ← padic_val.mul' (prime_int_of_nat_prime p) hf2,
    enat.get_le_get, padic_val_le_padic_val_iff] }

theorem le_padic_val_rat_add_of_le {q r : ℚ}
  (hq : q ≠ 0) (hr : r ≠ 0) (hqr : q + r ≠ 0)
  (h : padic_val_rat p q ≤ padic_val_rat p r) :
  padic_val_rat p q ≤ padic_val_rat p (q + r) :=
have hqn : q.num ≠ 0, from rat.num_ne_zero_of_ne_zero hq,
have hqd : (q.denom : ℤ) ≠ 0, from int.coe_nat_ne_zero.2 $ rat.denom_ne_zero _,
have hrn : r.num ≠ 0, from rat.num_ne_zero_of_ne_zero hr,
have hrd : (r.denom : ℤ) ≠ 0, from int.coe_nat_ne_zero.2 $ rat.denom_ne_zero _,
have hqdv : q.num /. q.denom ≠ 0, from rat.mk_ne_zero_of_ne_zero hqn hqd,
have hrdv : r.num /. r.denom ≠ 0, from rat.mk_ne_zero_of_ne_zero hrn hrd,
have hqreq : q + r = (((q.num * r.denom + q.denom * r.num : ℤ)) /. (↑q.denom * ↑r.denom : ℤ)),
  from rat.add_num_denom _ _,
have hqrd : q.num * ↑(r.denom) + ↑(q.denom) * r.num ≠ 0,
  from rat.mk_num_ne_zero_of_ne_zero hqr hqreq,
begin
  conv_lhs { rw rat.num_denom q },
  rw [hqreq, padic_val_rat_le_padic_val_rat_iff p hqn hqrd hqd (mul_ne_zero hqd hrd),
    ← padic_val_le_padic_val_iff, mul_left_comm, padic_val.mul (prime_int_of_nat_prime p),
    add_mul],
  rw [rat.num_denom q, rat.num_denom r, padic_val_rat_le_padic_val_rat_iff p hqn hrn hqd hrd,
    ← padic_val_le_padic_val_iff] at h,
  calc _ ≤ min (padic_val ↑p (q.num * ↑(r.denom) * ↑(q.denom)))
    (padic_val ↑p (↑(q.denom) * r.num * ↑(q.denom))) : (le_min
    (by rw [@padic_val.mul _ _ _ _ (_ * _) _ (prime_int_of_nat_prime p), add_comm])
    (by rw [mul_assoc, @padic_val.mul _ _ _ _ (q.denom : ℤ)
        (_ * _) (prime_int_of_nat_prime p)];
      exact add_le_add_left' h))
    ... ≤ _ : min_le_padic_val_add
end

theorem min_le_padic_val_rat_add {q r : ℚ}
  (hq : q ≠ 0) (hr : r ≠ 0) (hqr : q + r ≠ 0) :
  min (padic_val_rat p q) (padic_val_rat p r) ≤ padic_val_rat p (q + r) :=
(le_total (padic_val_rat p q) (padic_val_rat p r)).elim
  (λ h, by rw [min_eq_left h]; exact le_padic_val_rat_add_of_le _ hq hr hqr h)
  (λ h, by rw [min_eq_right h, add_comm]; exact le_padic_val_rat_add_of_le _ hr hq
    (by rwa add_comm) h)

end padic_val_rat
end padic_val_rat

def padic_norm (p : ℕ) (q : ℚ) : ℚ :=
if q = 0 then 0 else fpow (↑p : ℚ) (-(padic_val_rat p q))

namespace padic_norm

section padic_norm
open padic_val_rat
variables (p : ℕ) [hp : p.prime]
include hp

@[simp] protected lemma zero : padic_norm p 0 = 0 := by simp [padic_norm]

@[simp] protected lemma one : padic_norm p 1 = 1 := by simp [padic_norm]

@[simp] protected lemma eq_fpow_of_nonzero {q : ℚ} (hq : q ≠ 0) :
  padic_norm p q = fpow p (-(padic_val_rat p q)) :=
by simp [hq, padic_norm]

protected lemma nonzero {q : ℚ} (hq : q ≠ 0) : padic_norm p q ≠ 0 :=
begin
  rw padic_norm.eq_fpow_of_nonzero p hq,
  apply fpow_ne_zero_of_ne_zero, simp,
  apply ne_of_gt,
  simpa using hp.pos
end

@[simp] protected lemma neg (q : ℚ) : padic_norm p (-q) = padic_norm p q :=
if hq : q = 0 then by simp [hq]
else by simp [padic_norm, hq, hp.gt_one]

lemma zero_of_padic_norm_eq_zero {q : ℚ} (h : padic_norm p q = 0) : q = 0 :=
by_contradiction $
  assume hq : q ≠ 0,
  have padic_norm p q = fpow p (-(padic_val_rat p q)), by simp [hq],
  fpow_ne_zero_of_ne_zero
    (show (↑p : ℚ) ≠ 0, by simp [prime.ne_zero hp])
    (-(padic_val_rat p q)) (by rw [←this, h])

protected lemma nonneg (q : ℚ) : padic_norm p q ≥ 0 :=
if hq : q = 0 then by simp [hq]
else
  begin
    unfold padic_norm; split_ifs,
    apply fpow_nonneg_of_nonneg,
    apply nat.cast_nonneg
  end

@[simp] protected theorem mul (q r : ℚ) : padic_norm p (q*r) = padic_norm p q * padic_norm p r :=
if hq : q = 0 then
  by simp [hq]
else if hr : r = 0 then
  by simp [hr]
else
  have q*r ≠ 0, from mul_ne_zero hq hr,
  have (↑p : ℚ) ≠ 0, by simp [prime.ne_zero hp],
  by simp [padic_norm, *, padic_val_rat.mul, fpow_add this]

@[simp] protected theorem div (q r : ℚ) : padic_norm p (q / r) = padic_norm p q / padic_norm p r :=
if hr : r = 0 then by simp [hr] else
eq_div_of_mul_eq _ _ (padic_norm.nonzero _ hr) (by rw [←padic_norm.mul, div_mul_cancel _ hr])

protected theorem of_int (z : ℤ) : padic_norm p ↑z ≤ 1 :=
if hz : z = 0 then by simp [hz] else
begin
  unfold padic_norm,
  rw [if_neg ((@int.cast_ne_zero ℚ _ _ _ _).2 hz)],
  refine fpow_le_one_of_nonpos
    (by rw [← nat.cast_one]; exact nat.cast_le.2 (le_of_lt hp.gt_one)) _,
  rw [padic_val_rat_of_int _ hp.ne_one hz, neg_nonpos],
  exact int.coe_nat_nonneg _
end

--TODO: p implicit
private lemma nonarchimedean_aux {q r : ℚ} (h : padic_val_rat p q ≤ padic_val_rat p r) :
  padic_norm p (q + r) ≤ max (padic_norm p q) (padic_norm p r) :=
have hnqp : padic_norm p q ≥ 0, from padic_norm.nonneg _ _,
have hnrp : padic_norm p r ≥ 0, from padic_norm.nonneg _ _,
if hq : q = 0 then
  by simp [hq, max_eq_right hnrp, le_max_right]
else if hr : r = 0 then
  by simp [hr, max_eq_left hnqp, le_max_left]
else if hqr : q + r = 0 then
  le_trans (by simpa [hqr] using padic_norm.nonneg) (le_max_left _ _)
else
  begin
    unfold padic_norm, split_ifs,
    apply le_max_iff.2,
    left,
    have hpge1 : (↑p : ℚ) ≥ ↑(1 : ℕ), from (nat.cast_le.2 $ le_of_lt $ prime.gt_one hp),
    apply fpow_le_of_le hpge1,
    apply neg_le_neg,
    have : padic_val_rat p q =
            min (padic_val_rat p q) (padic_val_rat p r),
      from (min_eq_left h).symm,
    rw this,
    apply min_le_padic_val_rat_add; assumption
  end

protected theorem nonarchimedean {q r : ℚ} :
  padic_norm p (q + r) ≤ max (padic_norm p q) (padic_norm p r) :=
begin
    wlog hle := le_total (padic_val_rat p q) (padic_val_rat p r) using [q r],
    exact nonarchimedean_aux p hle
end

theorem triangle_ineq (q r : ℚ) : padic_norm p (q + r) ≤ padic_norm p q + padic_norm p r :=
calc padic_norm p (q + r) ≤ max (padic_norm p q) (padic_norm p r) : padic_norm.nonarchimedean p
                       ... ≤ padic_norm p q + padic_norm p r :
                         max_le_add_of_nonneg (padic_norm.nonneg p _) (padic_norm.nonneg p _)

protected theorem sub {q r : ℚ} : padic_norm p (q - r) ≤ max (padic_norm p q) (padic_norm p r) :=
by rw [sub_eq_add_neg, ←padic_norm.neg p r]; apply padic_norm.nonarchimedean

lemma add_eq_max_of_ne {q r : ℚ} (hne : padic_norm p q ≠ padic_norm p r) :
  padic_norm p (q + r) = max (padic_norm p q) (padic_norm p r) :=
begin
  wlog hle := le_total (padic_norm p r) (padic_norm p q) using [q r],
  have hlt : padic_norm p r < padic_norm p q, from lt_of_le_of_ne hle hne.symm,
  have : padic_norm p q ≤ max (padic_norm p (q + r)) (padic_norm p r), from calc
   padic_norm p q = padic_norm p (q + r - r) : by congr; ring
               ... ≤ max (padic_norm p (q + r)) (padic_norm p (-r)) : padic_norm.nonarchimedean p
               ... = max (padic_norm p (q + r)) (padic_norm p r) : by simp,
  have hnge : padic_norm p r ≤ padic_norm p (q + r),
  { apply le_of_not_gt,
    intro hgt,
    rw max_eq_right_of_lt hgt at this,
    apply not_lt_of_ge this,
    assumption },
  have : padic_norm p q ≤ padic_norm p (q + r), by rwa [max_eq_left hnge] at this,
  apply _root_.le_antisymm,
  { apply padic_norm.nonarchimedean p },
  { rw max_eq_left_of_lt hlt,
    assumption }
end

protected theorem image {q : ℚ} (hq : q ≠ 0) : ∃ n : ℤ, padic_norm p q = fpow p (-n) :=
⟨ (padic_val_rat p q), by simp [padic_norm, hq] ⟩

instance : is_absolute_value (padic_norm p) :=
{ abv_nonneg := padic_norm.nonneg p,
  abv_eq_zero :=
    begin
      intros,
      constructor; intro,
      { apply zero_of_padic_norm_eq_zero p, assumption },
      { simp [*] }
    end,
  abv_add := padic_norm.triangle_ineq p,
  abv_mul := padic_norm.mul p }

lemma le_of_dvd {n : ℕ} {z : ℤ} (hd : ↑(p^n) ∣ z) : padic_norm p z ≤ fpow ↑p (-n) :=
have hp' : (↑p : ℚ) ≥ 1, from show ↑p ≥ ↑(1 : ℕ), from cast_le.2 (le_of_lt hp.gt_one),
have hpn : (↑p : ℚ) ≥ 0, from le_trans zero_le_one hp',
begin
  unfold padic_norm, split_ifs with hz hz,
  { simpa [padic_norm, hz] using fpow_nonneg_of_nonneg hpn _ },
  { apply fpow_le_of_le hp',
    apply neg_le_neg,
    rw padic_val_rat_of_int _ hp.ne_one (int.cast_ne_zero.1 hz),
    apply int.coe_nat_le.2,
    rw [← enat.coe_le_coe, enat.coe_get],
    apply padic_val.le_padic_val_of_pow_dvd,
    { simpa using hd } }
end

end padic_norm
end padic_norm