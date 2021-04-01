import group_theory.perm.cycles

namespace equiv.perm
open equiv

variables {α : Type*} [fintype α] [decidable_eq α]

def count_cycles (l : list (perm α)) (n : ℕ) :=
multiset.count n (l.map (finset.card ∘ support))

lemma lem3 (l : list (perm α)) (σ : perm α) (n : ℕ) :
  count_cycles (σ :: l) n = (ite (n = σ.support.card) 1 0) + count_cycles l n :=
eq.trans (multiset.count_cons n σ.support.card (l.map (finset.card ∘ support))) (add_comm _ _)

noncomputable def count_cycle_elements (σ : perm α) (n : ℕ) :=
(finset.univ.filter (λ a, (σ.cycle_of a).support.card = n)).card

lemma lem5 (n : ℕ) : count_cycle_elements (1 : perm α) n = 0 :=
begin
  simp_rw [count_cycle_elements, cycle_of_one],
  --simp_rw [support_one, finset.card_empty],
  sorry
end

lemma lem4 (σ : perm α) (hσ : is_cycle σ) (n : ℕ) :
  count_cycle_elements σ n = ite (n = σ.support.card) n 0 :=
begin
  rw [count_cycle_elements],
  simp_rw [hσ.cycle_of, apply_ite support, apply_ite finset.card],
  by_cases h : n = σ.support.card,
  { rw [if_pos h],
    sorry },
  { rw [if_neg h, finset.card_eq_zero],
    apply finset.filter_false_of_mem,
    intros x hx,
    sorry },
end

lemma lem2 (σ τ : perm α) (h : disjoint σ τ) (n : ℕ) :
  count_cycle_elements (σ * τ) n = count_cycle_elements σ n + count_cycle_elements τ n :=
begin
  rw [count_cycle_elements, count_cycle_elements, count_cycle_elements,
      ←finset.card_disjoint_union, ←finset.filter_or],
  { congr,
    ext a,
    sorry },
  { rw [disjoint_iff, finset.inf_eq_inter, ←finset.filter_and],
    sorry },
end

lemma lem1 (n : ℕ) (l : list (perm α)) (h1 : ∀ σ : perm α, σ ∈ l → σ.is_cycle)
  (h2 : l.pairwise disjoint) : n * count_cycles l n = count_cycle_elements l.prod n :=
begin
  revert h1 h2,
  induction l with σ l ih,
  { exact λ _ _, (lem5 n).symm },
  { intros h1 h2,
    rw [lem3, mul_add, mul_ite, mul_one, mul_zero, list.prod_cons, lem2],
    apply congr_arg2 has_add.add,
    { exact (lem4 σ (h1 σ (list.mem_cons_self σ l)) n).symm },
    { refine ih (λ τ hτ, h1 τ (list.mem_cons_of_mem σ hτ)) (list.pairwise_of_pairwise_cons h2) },
    { -- lemma from PR
      sorry } }
end

noncomputable def cycle_type (σ : perm α) : multiset ℕ :=
σ.trunc_cycle_factors.lift (λ l, l.1.map (finset.card ∘ support)) (λ l₁ l₂,
begin
  ext n,
  let s := {l : list (perm α) // l.prod = σ ∧ (∀ τ : perm α, τ ∈ l → τ.is_cycle) ∧
    l.pairwise disjoint},
  by_cases hn : n ≤ 1,
  { suffices : ∀ l : s, count_cycles l.1 n = 0,
    { rw [←count_cycles, ←count_cycles, this, this] },
    refine λ l, multiset.count_eq_zero_of_not_mem (λ h0, _),
    obtain ⟨τ, h1, h2⟩ := list.mem_map.mp h0,
    -- use stuff from PR to finish off (τ is a cycle with τ.support.card ≤ 1)
    sorry },
  { rw not_le at hn,
    suffices : ∀ l : s, n * count_cycles l.1 n = count_cycle_elements σ n,
    { exact (nat.mul_right_inj (zero_lt_one.trans hn)).mp ((this l₁).trans (this l₂).symm) },
    intro l,
    simp_rw ← l.2.1,
    exact lem1 n l.1 l.2.2.1 l.2.2.2 },
end)

end equiv.perm
