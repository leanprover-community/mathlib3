

import tactic

import group_theory.solvable
import data.equiv.transfer_instance
import data.list.defs
import data.list.cycle
import data.multiset.basic

import group_theory.perm.list
import group_theory.perm.cycles
import group_theory.perm.concrete_cycle
import group_theory.perm.cycle_type

import group_theory.subgroup.basic
import group_theory.specific_groups.alternating
import group_theory.group_action.basic
import group_theory.group_action.conj_act


variables {α : Type*} [decidable_eq α] [fintype α]

open subgroup equiv.perm equiv alternating_group

lemma list.sum_le_mul_length {s : list ℕ} (a : ℕ) (h : ∀ (n : ℕ), n ∈ s → n ≤ a) :
  s.sum ≤ a * s.length :=
begin
  induction s with hd tl ih,
  { simp , },
  rw [list.sum_cons, add_comm],
  rw [list.length_cons, mul_add, mul_one],
  refine nat.add_le_add (ih _) (h _ _),
  { intros n hn, refine h n _,  --
    apply list.mem_cons_of_mem, exact hn, } ,
  { apply list.mem_cons_self, }
end

lemma list.mul_length_le_sum {s : list ℕ} (a : ℕ) (h : ∀ (n : ℕ), n ∈ s → a ≤ n) :
  a * s.length ≤ s.sum :=
begin
  induction s with hd tl ih,
  { simp , },
  rw [list.sum_cons, add_comm],
  rw [list.length_cons, mul_add, mul_one],
  refine nat.add_le_add (ih _) (h _ _),
  { intros n hn, refine h n _,  --
    apply list.mem_cons_of_mem, exact hn, } ,
  { apply list.mem_cons_self, }
end

lemma list.sum_eq_mul_length {s : list ℕ} (a : ℕ) (h : ∀ (n : ℕ), n ∈ s → n = a) :
  s.sum = a * s.length :=
begin
  apply le_antisymm,
  have h' : ∀ (n : ℕ), n ∈ s → n ≤ a, { intros n hn, rw h n hn, },
  exact list.sum_le_mul_length a h',
  have h'' : ∀ (n : ℕ), n ∈ s → a ≤ n, { intros n hn, rw h n hn, },
  exact list.mul_length_le_sum a h'',
end

lemma multiset.sum_le_sup_mul_card {m : multiset ℕ} :
  m.sum ≤ m.sup * m.card :=
quotient.induction_on m
  (λ l, by simpa using list.sum_le_mul_length (l : multiset ℕ).sup
  (λ n hn, begin apply multiset.sup_le.mp le_rfl, exact hn end))
/- begin
  apply quotient.induction_on m,
  intro l,
  simp only [multiset.quot_mk_to_coe, multiset.coe_sum, multiset.coe_card],
  refine list.sum_le_mul_length (l : multiset ℕ).sup _,
  intros n hn, apply multiset.sup_le.mp le_rfl,  exact hn,
end -/

/- lemma multiset.sum_le_mul_card {m : multiset ℕ} : ∀ {a : ℕ} (h : ∀ (n : ℕ), n ∈ m → n ≤ a),
  m.sum ≤ a * m.card :=
quotient.induction_on m (λ l a h, by simpa using list.sum_le_mul_length a h) -/

lemma multiset.inf_mul_length_le_card {m : multiset ℕ} : ∀ {a : ℕ} (h : ∀ (n : ℕ), n ∈ m → a ≤ n),
  a * m.card ≤ m.sum :=
quotient.induction_on m (λ l a h, by simpa using list.mul_length_le_sum a h)

lemma multiset.sum_eq_const_mul_card {m : multiset ℕ} : ∀ {a : ℕ} (h : ∀ (n : ℕ), n ∈ m → n = a),
  m.sum = a * m.card :=
quotient.induction_on m (λ l a h, by simpa using list.sum_eq_mul_length a h)

example (m n : ℕ) : (m ⊔ n = m ∨ m ⊔ n = n) :=
begin
  simp only [sup_eq_left, sup_eq_right],
end

example (m n: ℕ) (h : m ≥ n) (h' : m ≠ n) : m ≥ n.succ :=
begin
  by_contradiction h1,
  simp only [not_le] at h1,
  exact h' (le_antisymm  (nat.lt_succ_iff.mp h1) h),
  /-
  change n.succ ≤ m,
  refine or.resolve_left (m.lt_or_ge n.succ) _,
  intro h1, apply h', -/

  /-
  cases m.lt_or_ge n.succ with h1 h2,
  { exfalso,
    exact h' (le_antisymm (nat.lt_succ_iff.mp h1) h), },
  assumption,-/

end

lemma multiset.sup_mem_of {m : multiset ℕ} (hm : m ≠ 0) : m.sup ∈ m :=
begin
  revert hm,
  refine multiset.induction_on m _ _,
  { intro h0, exfalso, exact h0 rfl, },
  { intros a m' ih _,
    rw multiset.sup_cons,
    cases le_total a m'.sup,
    { rw sup_eq_right.mpr h,
      cases dec_em (m' = 0) with h1 h2,
      { rw [h1, multiset.sup_zero, bot_eq_zero, le_zero_iff] at h,
        rw [h, h1, multiset.sup_zero, bot_eq_zero],
        apply multiset.mem_cons_self 0 _, },
      apply multiset.mem_cons_of_mem,
      exact ih h2, },
    { rw ← left_eq_sup.mpr h,
      exact multiset.mem_cons_self a m' } }
end

lemma multiset.sup_le_sum (m : multiset ℕ) : m.sup ≤ m.sum :=
begin
  cases dec_em (m = 0) with H H,
  { rw H, simp only [multiset.sup_zero, bot_eq_zero, multiset.sum_zero], },
  { let m' := m.erase m.sup,
    let hm_cons := multiset.cons_erase (multiset.sup_mem_of H),
    rw [← hm_cons, multiset.sum_cons, hm_cons],
    refine nat.le_add_right _ _ }
end


lemma ineq_solve (a b m: ℕ) (hm : 1 ≤ m) (hb : 2 ≤ b) (ha : b < a) (h : m * a + b ≤ 5) :
  (a = 3 ∧ b = 2 ∧ m = 1) :=
begin
--  obtain ⟨m', rfl⟩ := le_iff_exists_add.mp hm,
--  obtain ⟨b', rfl⟩ := le_iff_exists_add.mp hb,
--  obtain ⟨a', rfl⟩ := le_iff_exists_add.mp (nat.lt_iff_add_one_le.mp ha),
--   rw [add_comm 2 b', ← add_assoc] at h,

  have h' : m * a ≤ 3,
  { refine nat.le_of_add_le_add_right _,
    apply b, apply le_trans h,
    refine le_trans _ (nat.add_le_add_left hb 3), by norm_num, },
  have ha' : a = 3,
  { apply le_antisymm,
    { -- a ≤ 3
      rw ← one_mul a,
      refine le_trans _ h',
      refine nat.mul_le_mul_right _ hm, },
    exact le_trans (nat.succ_le_succ hb) (nat.succ_le_iff.mp ha), },
  split, exact ha',
  rw ha' at ha h' h,
  split,
  exact nat.eq_of_le_of_lt_succ hb ha,
  refine le_antisymm _ hm,
  rw mul_comm at h',
  refine nat.le_of_mul_le_mul_left (le_trans h' _) _,
  dec_trivial, dec_trivial,
end

/-- Get an element distinct from those of a given list -/
lemma out_of_list {s : finset α} {l : list α} (h : l.length < s.card ) :
  ∃ (a : α), a ∈ s ∧ a ∉ l :=
begin
  let t := list.to_finset l,
  have : (s \ t).card > 0,
  { apply nat.lt_of_add_lt_add_right,
    rw [finset.card_sdiff_add_card  , zero_add],
    refine lt_of_lt_of_le
      (lt_of_le_of_lt (list.to_finset_card_le l) h)
      (finset.card_le_of_subset (finset.subset_union_left s t)),
  },
  obtain ⟨a : α, ha : a ∈ s \ t⟩ := finset.card_pos.mp this,
  use a,
  apply and.intro,
  exact (finset.mem_sdiff.mp ha).left,
  intro ha', apply (finset.mem_sdiff.mp ha).right,
  exact list.mem_to_finset.mpr ha'
end

lemma multiset_is_5_or_32 (m : multiset ℕ) (hm : ∀ (n : ℕ), n ∈ m → 2 ≤ n) (hs : m.sum = 5) :
  m = {5} ∨ m = {3,2} :=
begin
  have m_nonzero : m ≠ 0,
  { intro hm0, simpa only [hm0, multiset.sum_zero] using hs,  },

  have msup_ge_2 : 2 ≤ m.sup,
  { obtain ⟨a, ha⟩ := multiset.exists_mem_of_ne_zero m_nonzero,
    exact le_trans (hm a ha) (multiset.le_sup ha), },

  have : ∃ (m' : multiset ℕ), m =  (multiset.repeat m.sup (multiset.count m.sup m)) + m',
  { apply multiset.le_iff_exists_add.mp,
    refine multiset.le_count_iff_repeat_le.mp le_rfl, },
  obtain ⟨m', hm'_cons⟩ := this,
  rw [hm'_cons, multiset.sum_add, multiset.sum_repeat, algebra.id.smul_eq_mul] at hs,
  have h_msup_not_mem_m': m.sup ∉ m',
  { refine multiset.count_eq_zero.mp _,
    refine add_left_cancel _,
    exact multiset.count m.sup (multiset.repeat m.sup (multiset.count m.sup m)),
    rw [add_zero, ← multiset.count_add, ← hm'_cons, multiset.count_repeat_self] , },
  have h_cnt_msup : 1 ≤ multiset.count m.sup m :=
    multiset.count_pos.mpr (multiset.sup_mem_of m_nonzero),

  cases dec_em (m' = 0) with Hm' Hm',
  { -- m' = 0 : prove m = {5}
    apply or.intro_left,
    rw [Hm', multiset.sum_zero, add_zero] at hs,
    rw [Hm', add_zero] at hm'_cons,
    rw ←  multiset.repeat_one,
    rw hm'_cons,
    have hmsup_eq_5 : m.sup = 5,
    { -- m.sup = 5
      apply (nat.dvd_prime_two_le _ msup_ge_2).mp,
      rw ← hs,
      rw mul_comm,
      refine nat.dvd_mul_right _ _,
      by norm_num, },
    apply congr_arg2 _ hmsup_eq_5,
    rw hmsup_eq_5 at hs ⊢,
    refine mul_right_cancel₀ _ hs,
    by norm_num },

  -- m' ≠ 0 : prove m = {3,2}
  apply or.intro_right,
  have m'sup_mem_m : m'.sup ∈ m,
  { rw hm'_cons, refine multiset.mem_add.mpr (or.intro_right _ (multiset.sup_mem_of Hm')) , },

--   have m'sup_in_m' := multiset.sup_mem_of Hm',
  have m'sup_lt_msup : m'.sup < m.sup,
  { refine or.resolve_right (nat.lt_or_ge m'.sup m.sup) _,
    intro h,
    apply h_msup_not_mem_m',
    rw le_antisymm  h (multiset.le_sup m'sup_mem_m),
    exact multiset.sup_mem_of Hm', },

  let ineq := ineq_solve m.sup m'.sup (multiset.count m.sup m) h_cnt_msup _ _ _,
  let ineq1 := ineq.left,
  let ineq2 := ineq.right.left,
  let ineq3 := ineq.right.right,
  rw [ineq3, ineq1] at  hm'_cons hs,

  have : m'.sum = 2,
  { refine add_left_cancel _, apply 3, simp at hs, rw hs, },

  let hm''_cons  := multiset.cons_erase (multiset.sup_mem_of Hm'),
  rw ineq2 at hm''_cons,
  have hm'' : ∀ (n : ℕ), n ∈ m'.erase 2 → 2 ≤ n,
  { intros n hn, apply hm n _,
    rw hm'_cons, refine multiset.mem_cons_of_mem _,
    rw ← hm''_cons, exact multiset.mem_cons_of_mem hn },

  suffices : m'.erase 2 = 0,
  { rw [← hm''_cons, this] at hm'_cons, exact hm'_cons },

  apply multiset.card_eq_zero.mp,
  apply nat.eq_zero_of_le_zero,
  refine nat.le_of_mul_le_mul_left _ _, apply 2, rw mul_zero,
  refine le_trans (multiset.inf_mul_length_le_card hm'') _,

  suffices : (m'.erase 2).sum = 0,  rw this,
  refine add_left_cancel _, apply 2,
  rw [← multiset.sum_cons,  hm''_cons],
  rw this,

  -- 0 < 2
  by norm_num,

  -- 2 ≤ m'.sup
  { apply hm, exact m'sup_mem_m },

  exact m'sup_lt_msup,

  rw ← hs,
  refine  nat.add_le_add_left  _ _,
  apply multiset.sup_le_sum
end


example (p : perm α) (hp : p.support.card = 5) (hp' : p.sign = 1) : is_cycle p :=
begin
  refine equiv.perm.card_cycle_type_eq_one.mp _,
  cases nat.eq_zero_or_pos (multiset.card p.cycle_type) with h h',
  { rw equiv.perm.card_cycle_type_eq_zero at h,
    rw [h, equiv.perm.support_one, finset.card_empty] at hp,
    simp only [nat.zero_ne_bit1] at hp,
    exfalso, assumption, },

  cases nat.lt_or_ge (multiset.card p.cycle_type) 2 with h h,
  { exact nat.eq_of_le_of_lt_succ h' h, },

  -- a + b + … = 5, a ≥ 2, b ≥ 2 => [3,2] et contradiction
  rw ← equiv.perm.sum_cycle_type  at hp,

  have h2n : ∀ (n : ℕ), n ∈ p.cycle_type → 2 ≤ n,
  { intros n hn, refine equiv.perm.two_le_of_mem_cycle_type hn, },

  generalize hs : p.cycle_type = s,
  rw hs at h h2n hp,

  cases dec_em (∀ (n : ℕ), n ∈ s → n = 2) with h2n h2n',
  { rw multiset.sum_eq_const_mul_card 2 h2n at hp,
    rw two_mul at hp,
    exfalso,
    apply nat.bit0_ne_bit1 s.card 2,
    rw ← hp, refl, },

  simp at h2n',
  obtain ⟨x, ⟨hxn, hx3'⟩⟩ := h2n',
  have hx3 : x ≥ 3,
  { by_contradiction,
    simp only [not_le] at h,
    exact hx3' (le_antisymm  (nat.lt_succ_iff.mp h) (h2n x hxn)), },

  let s' := multiset.erase s x,
  rw ← multiset.cons_erase hxn at hp h,
  rw multiset.sum_cons at hp,
  rw [multiset.card_cons, nat.succ_le_succ_iff] at h,

  have hp' : s'.sum ≤ 2,
  { apply nat.le_of_add_le_add_left ,
    rw hp,
    apply nat.add_le_add_right hx3 2, },

  have H : s'.sum = 2,
  { apply le_antisymm hp',
    refine le_trans (nat.mul_le_mul_left 2 h) _,
    refine multiset.inf_mul_length_le_card 2 _,
    { intros n hypn, refine h2n n (multiset.mem_of_mem_erase hypn), }, },
  rw H at hp,
  have hp' : x = 3 := nat.add_right_cancel hp,

  obtain ⟨y, hys'⟩ := multiset.card_pos_iff_exists_mem.mp h,

  sorry,
end

lemma getof5 {m : multiset ℕ} (hm : ∀ {n : ℕ}, n ∈ m → 2 ≤ n) (hm0 : m ≠ 0) (hs : m.sum ≤ 5) :
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

def P5 := λ (m : multiset ℕ), (∀ (n : ℕ), n ∈ m → n ≥ 2) ∧ (m ≠ 0) ∧ (m.sum ≤ 5)


def types_of_5 := set_of P5

example : types_of_5 = { {5}, {4}, {3}, {2}, {3,2}, {2,2} } :=
begin
  ext m, unfold types_of_5, -- unfold P5,
  simp only [set.mem_insert_iff, set.mem_singleton_iff],

  split,

  intro hm,
  simp only [set.mem_set_of_eq] at hm,
  unfold P5 at hm,
  apply getof5,
  exact hm.left,
  exact hm.right.left,
  exact hm.right.right,

  intro hm, unfold P5, rw set.mem_set_of_eq,
  iterate { cases hm with hm hm, rw hm, dec_trivial, },
end


example : ∀ (h : 2 ≤ 1),  false := λ h, nat.not_succ_le_self 1 h

example {a b c : ℕ} (h : c * a < c * b.succ) (hc : 0 < c) :
a ≤ b

example (n : ℕ) : n ≤ 2 ∨ n ≥ 3 := by library_search
example (m n : ℕ) : m ≤ n ↔ m < n.succ := nat.lt_succ_iff.symm
example (m : ℕ) (h : 2 ≤ m + 1) : 1 ≤ m := nat.succ_le_succ_iff.mp h
example (a b c : ℕ) (h : b ≤ c) : a + b ≤ a + c := add_le_add_left h a


def is_partition_of_with_higher (a n : ℕ) (m : multiset ℕ) :=
  (∀ (n : ℕ), n ∈ m → a ≤ n) ∧ (m.sum = n)

def is_partition_of := is_partition_of_with_higher 1

lemma reduce_partition (a n : ℕ) (m : multiset ℕ) [ha : a ≥ 1]:
  is_partition_of_with_higher a n m ↔
  ite (n < a)
    (n = 0 ∧ m = 0)
    (∃ (k n' : ℕ) (m' : multiset ℕ),
      (k * a + n' = n) ∧
      (is_partition_of_with_higher (a+1) n' m') ∧ m = multiset.repeat k a + m') :=
begin
  split,
  { intro P,
    by_cases (n<a),
    rw ite_eq_left_iff.mpr _, swap, intro h', exfalso, exact h' h,
    have : m = 0,
    { by_contradiction hm,
      obtain ⟨a, ha⟩ := multiset.exists_mem_of_ne_zero hm,

      sorry,
      },
    rw this at P ⊢,
    split, rw ← P.right, rw multiset.sum_zero, refl, },
    { apply or.intro_left _,
    sorry, },
sorry,

end

#exit
      let hn := nat.eq_of_le_of_lt_succ (nat.zero_le n) hn,
      rw hn at P,
      split, exact hn,
      apply multiset.zero_eq_
      let w := P.right,
        sorry, },
    sorry,
  intro P,
  sorry,
end




def is_partition_of' (n : ℕ) (l : list ℕ) := (∀ (n : ℕ), n ∈ l → 1 ≤ n) ∧ (l.sum = n)

lemma partition_length_le_sum' {l : list ℕ} (h : ∀ (n : ℕ), n ∈ l → 1 ≤ n) :
  l.length ≤ l.sum :=
begin
  rw ← nat.one_mul l.length,
  exact list.inf_mul_length_le_sum 1 h,
end

lemma partition_length_le_sum {n : ℕ} {l : list ℕ} (h : is_partition_of n l) :
  l.length ≤ n :=
begin
  rw ← h.right,
  exact partition_length_le_sum' h.left,
end


lemma is_partition_of_zero (l : list ℕ) : is_partition_of 0 l ↔ l = list.nil :=
begin
  split,
  { intro h,
    apply list.eq_nil_of_length_eq_zero,
    apply nat.eq_zero_of_le_zero ,
    exact partition_length_le_sum h, },
  { intro h, rw h, unfold is_partition_of,
    split,
    { intros n hn, exfalso, exact list.not_mem_nil n hn },
    exact list.sum_nil },
end

lemma nil_is_partition_of (n : ℕ) : is_partition_of n list.nil ↔ n = 0 :=
begin
  split,
  { intro h, rw ← h.right, rw list.sum_nil, },
  { intro h, rw h, exact (is_partition_of_zero _).mpr rfl,   }
end

lemma reduce_partition_of {n : ℕ} {l : list ℕ} : is_partition_of n l
  → (n = 0 ∧ l = list.nil) ∨ (n ≥ 1 ∧ (∃ (a : ℕ) (l' : list ℕ), l = a :: l' ∧ a ≥ 1 ∧ n ≥ a  ∧
    is_partition_of (n-a) l')) :=
begin
  induction l with a l' hrec,
  { intro h,
    apply or.intro_left,
    split,
    rw ← h.right, simp, },
  { intro h,
    apply or.intro_right,
    split,
    swap,
    use a, use l', split, refl, split,
    apply h.left a (list.mem_cons_self a l'),
    have hs' : a + l'.sum = n,
    { rw ← list.sum_cons, exact h.right, },
    have ha_le_n : a ≤ n,
    { rw ← hs', apply nat.le_add_right, },
    split,
    exact ha_le_n,
    have hs'' : 0 ≤ l'.sum := zero_le l'.sum,
    unfold is_partition_of,
    split,
    { intros n hn, apply h.left n (list.mem_cons_of_mem a hn) },
    apply nat.add_left_cancel,
    rw nat.add_sub_of_le ha_le_n,
    exact hs',
    apply nat.pos_of_ne_zero,
    intro hn0,
    rw hn0 at h,
    apply list.cons_ne_nil a l',
    apply (is_partition_of_zero (a :: l')).mp h  }
end
