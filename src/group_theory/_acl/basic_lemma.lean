import tactic

import data.nat.parity
import data.multiset.basic

lemma all_cycle_types_le_5 {m : multiset ℕ} (hm : ∀ {n : ℕ}, n ∈ m → 2 ≤ n)
  (hs : m.sum ≤ 5) (hm0 : m ≠ 0) :
  m = {5} ∨ m = {4} ∨ m = {3} ∨ m = {2} ∨ m = {3,2} ∨ m = {2,2} :=
begin
  -- a is the smallest member of m
  let Hm := multiset.exists_mem_of_ne_zero hm0,
  let a := nat.find Hm,
  let a_in_m := nat.find_spec Hm,
  have a_is_inf_m : ∀ {n : ℕ} (h : n ∈ m), a ≤ n := λ n h, nat.find_min' Hm h,
  have a_ge_2 : 2 ≤ a := hm a_in_m,

  -- nat.find_spec _ a : a ∈ m
  -- nat.find_min _ : b < a → b ∉ m

  let m' := m.erase a,
  have hm_cons : a ::ₘ (m.erase a) = m := multiset.cons_erase a_in_m,
  cases dec_em (m.erase a = 0) with hm'0 hm'0,
  { -- m = {a} : prove a = 2, 3, 4, 5

    have m_is_a : m = {a},
    { rw [← hm_cons, hm'0],  exact rfl, },
    rw [m_is_a, multiset.sum_singleton] at hs,

    have eq_or_le_pred : ∀ {a n : ℕ} (h : a ≤ n), a = n ∨ a ≤ n.pred,
    { intros a n h,
      cases nat.lt_or_ge n a.succ with h1 h2,
      exact or.intro_left _ (nat.eq_of_le_of_lt_succ h h1).symm,
      apply or.intro_right, rw ← nat.pred_succ a, exact nat.pred_le_pred h2 },

    iterate {
      cases eq_or_le_pred hs with h hs,
      { apply or.intro_left, rw [m_is_a, h], },
      apply or.intro_right, rw nat.pred_succ at hs, },
    exfalso, refine nat.not_succ_le_self _ (le_trans a_ge_2 hs), },

  { -- m = {a, … }
    apply or.intro_right _, apply or.intro_right, apply or.intro_right, apply or.intro_right,

    let Hm' := multiset.exists_mem_of_ne_zero hm'0,
    let b := nat.find Hm',
    let b_in_m' : b ∈ m.erase a := nat.find_spec Hm',
    let b_in_m : b ∈ m := multiset.mem_of_mem_erase b_in_m',
    let b_is_inf_m' : ∀ {n : ℕ} (h: n ∈ m'), b ≤ n := λ n h, nat.find_min' Hm' h,
    let b_ge_2 : 2 ≤ b := hm b_in_m,
    have hm'cons : b ::ₘ ((m.erase a).erase b) = m.erase a := multiset.cons_erase b_in_m',

    have : m = {b,a},
    { change m = b ::ₘ a ::ₘ 0,
      rw multiset.cons_swap ,
      rw ← hm_cons, rw ← hm'cons,
      apply (multiset.cons_inj_right  _).mpr,
      apply (multiset.cons_inj_right  _).mpr,
      by_contradiction hm''0,
      obtain ⟨c, hc''⟩ := multiset.exists_mem_of_ne_zero hm''0,
      obtain ⟨m₃ , h₃⟩ := multiset.exists_cons_of_mem hc'',
      let c_ge_2 : 2 ≤ c := hm (multiset.mem_of_mem_erase (multiset.mem_of_mem_erase hc'')),
      apply nat.not_succ_le_self 5,
      apply le_trans _ hs,
      rw [← hm_cons, multiset.sum_cons],
      rw [← multiset.cons_erase b_in_m', multiset.sum_cons],
      rw [← multiset.cons_erase hc'', multiset.sum_cons],
      simp only [← add_assoc],
      refine le_trans _ (nat.le_add_right _ _),

      refine le_trans _ (add_le_add_left c_ge_2 _),
      rw add_comm, rw ← add_assoc,
      refine le_trans _ (add_le_add_left b_ge_2 _),
      rw add_comm, rw ← add_assoc,
      refine le_trans _ (add_le_add_left a_ge_2 _),
      by norm_num, },

  rw [this,multiset.insert_eq_cons, multiset.sum_cons, multiset.sum_singleton] at hs,
  rw this,

  have ha : a = 2,
  { refine le_antisymm _ a_ge_2,
    apply nat.lt_succ_iff.mp,
    refine not_le.mp _, intro ha',
    apply nat.not_succ_le_self 5,
    refine le_trans _ hs,
    refine le_trans _ (nat.add_le_add (le_trans ha' (a_is_inf_m b_in_m)) ha'),
    by norm_num },
  rw ha,

  cases nat.lt_or_ge b 3 with h h',
    apply or.intro_right _, rw nat.eq_of_le_of_lt_succ b_ge_2 h,
    apply or.intro_left _, rw nat.le_antisymm _ h',
      apply  nat.le_of_add_le_add_right, refine le_trans hs _, rw ha }
end

def cycle_type_of_even' (m : multiset ℕ) :=
  (multiset.map (λ (n : ℕ), -(-1 : units ℤ) ^ n) m).prod = 1

def cycle_type_of_even (m : multiset ℕ) :=
  even(m.sum + m.card)

/- lemma all_cycle_types_le_5 {m : multiset ℕ} (hm : ∀ {n : ℕ}, n ∈ m → 2 ≤ n)
  (hs : m.sum ≤ 5) (hm0 : m ≠ 0) :
  m = {5} ∨ m = {4} ∨ m = {3} ∨ m = {2} ∨ m = {3,2} ∨ m = {2,2} :=
-/
lemma basic_22 {m : multiset ℕ}
  (hm : ∀ (i : ℕ), i ∈ m → i ≥ 2) (hm0 : m ≠ 0) (hmsum4: 4 ≤ m.sum) (hmsum5 : m.sum ≤ 5)
    (hmsup : m.sup < 4) (hmeven : cycle_type_of_even m) :
  m = {2, 2} :=
begin
  cases all_cycle_types_le_5  hm hmsum5 hm0 with hz hz,
  { exfalso, rw hz at hmsup, simpa using hmsup, } ,
  cases hz with hz hz,
  { exfalso, rw hz at hmsup, simpa using hmsup, } ,
  cases hz with hz hz,
  { exfalso, rw hz at hmsum4,
    simp only [multiset.sum_singleton, nat.bit0_le_bit1_iff] at hmsum4,
    exact nat.not_succ_le_self _ hmsum4 },
  cases hz with hz hz,
  { exfalso,
  unfold cycle_type_of_even at hmeven,
  apply nat.even_iff_not_odd.mp hmeven,
  rw hz,
  simp, by norm_num },
  cases hz with hz hz,
  { exfalso,
    unfold cycle_type_of_even at hmeven,
    apply nat.even_iff_not_odd.mp hmeven,
    rw hz,
    simp, by norm_num },
  assumption,
end

lemma basic_5 {m : multiset ℕ}
  (hm : ∀ (i : ℕ), i ∈ m → i ≥ 2) (hm0 : m ≠ 0) (hmsum5 : m.sum ≤ 5) (hmsup : m.sup ≥ 4)
    (hmeven : cycle_type_of_even m) :
    m = {5} :=
begin
  cases all_cycle_types_le_5  hm hmsum5 hm0 with hz hz,
  assumption,
  cases hz with hz hz,
  { exfalso,
  unfold cycle_type_of_even at hmeven,
  apply nat.even_iff_not_odd.mp hmeven,
  rw hz,
  simp, by norm_num },
  cases hz with hz hz,
  { exfalso, rw hz at hmsup, simp at hmsup,
    apply nat.not_succ_le_self _ hmsup, },
  cases hz with hz hz,
  { exfalso,
  unfold cycle_type_of_even at hmeven,
  apply nat.even_iff_not_odd.mp hmeven,
  rw hz,
  simp, by norm_num },
  cases hz with hz hz,
  { exfalso,
    unfold cycle_type_of_even at hmeven,
    apply nat.even_iff_not_odd.mp hmeven,
    rw hz,
    simp, by norm_num },
  exfalso, rw hz at hmsup, simp at hmsup,
  apply nat.not_succ_le_self _ hmsup,
end
