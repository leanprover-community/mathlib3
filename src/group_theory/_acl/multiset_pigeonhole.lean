
import tactic

-- import data.equiv.transfer_instance
import data.list.defs
import data.list.cycle
import data.multiset.basic
import data.nat.basic

/- import group_theory.perm.list
import group_theory.perm.cycles
import group_theory.perm.concrete_cycle
import group_theory.perm.cycle_type

import group_theory.subgroup.basic
import group_theory.specific_groups.alternating
import group_theory.group_action.basic
import group_theory.group_action.conj_act
-/

-- variables {α : Type*} [decidable_eq α] [fintype α]

-- open subgroup equiv.perm equiv alternating_group

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
      { rw [h1, multiset.sup_zero, bot_eq_zero, nat.le_zero_iff] at h,
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
