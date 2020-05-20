import data.nat.prime
import data.nat.choose
import data.nat.multiplicity
import ring_theory.multiplicity
import tactic

open_locale big_operators

def α (n : nat) (pos : 0 < n) (p : nat) (is_prime : nat.prime p) : nat :=
  (multiplicity p (nat.choose (2 * n) n)).get $
  begin
    have not_one : p ≠ 1 := nat.prime.ne_one is_prime,
    have pos : 0 < nat.choose (2 * n) n := nat.choose_pos (by linarith),
    have fin : multiplicity.finite p (nat.choose (2 * n) n) :=
      (@multiplicity.finite_nat_iff p (nat.choose (2 * n) n)).2 ⟨not_one, pos⟩,
    exact (multiplicity.finite_iff_dom.1 fin),
  end

lemma claim_1
  (p : nat)
  (is_prime : nat.prime p)
  (n : nat)
  (n_big : 3 < n)
  : pow p (α n (by linarith) p is_prime) ≤ 2 * n
  :=
begin
unfold α,
simp only [@nat.prime.multiplicity_choose p (2 * n) n _ is_prime (by linarith) (le_refl (2 * n))],
have r : 2 * n - n = n, by
  calc 2 * n - n = n + n - n: by rw two_mul n
  ... = n: nat.add_sub_cancel n n,
simp [r],

end

lemma add_two_not_le_one (x : nat) (pr : x.succ.succ ≤ 1) : false :=
  nat.not_succ_le_zero x (nat.lt_succ_iff.mp pr)

lemma filter_Ico_bot (m n : nat) (size : m < n) : finset.filter (λ x, x ≤ m) (finset.Ico m n) = {m} :=
begin
  ext,
  split,
  { intros hyp,
    simp only [finset.Ico.mem, finset.mem_filter] at hyp,
    simp only [finset.mem_singleton],
    linarith, },
  { intros singleton,
    rw finset.mem_singleton at singleton,
    subst singleton,
    simp,
    exact ⟨ ⟨ le_refl a, size ⟩, le_refl a ⟩ }
end

lemma card_singleton_inter {A : Type*} [d : decidable_eq A] {x : A} {s : finset A} : finset.card ({x} ∩ s) ≤ 1 :=
begin
  cases (finset.decidable_mem x s),
  { rw finset.singleton_inter_of_not_mem h,
    simp, },
  { rw finset.singleton_inter_of_mem h,
    simp, }
end

lemma claim_2
  (p : nat)
  (is_prime : nat.prime p)
  (n : nat)
  (n_big : 3 < n)
  (smallish : (2 * n) < p ^ 2)
  : (α n (by linarith) p is_prime) ≤ 1
  :=
begin
  unfold α,
  simp only [@nat.prime.multiplicity_choose p (2 * n) n _ is_prime (by linarith) (le_refl (2 * n))],
  have r : 2 * n - n = n, by
    calc 2 * n - n = n + n - n: by rw two_mul n
    ... = n: nat.add_sub_cancel n n,
  simp [r],
  have s : ∀ i, p ^ i ≤ n % p ^ i + n % p ^ i → i ≤ 1, by
    { intros i pr,
      cases le_or_lt i 1, {exact h,},
      { exfalso,
        have u : 2 * n < 2 * (n % p ^ i), by
          calc 2 * n < p ^ 2 : smallish
          ... ≤ p ^ i : nat.pow_le_pow_of_le_right (nat.prime.pos is_prime) h
          ... ≤ n % p ^ i + n % p ^ i : pr
          ... = 2 * (n % p ^ i) : (two_mul _).symm,
        have v : n < n % p ^ i, by linarith,
        have w : n % p ^ i ≤ n, exact (nat.mod_le _ _),
        linarith, }, },
  have t : ∀ x ∈ finset.Ico 1 (2 * n), p ^ x ≤ n % p ^ x + n % p ^ x ↔ (x ≤ 1 ∧ p ^ x ≤ n % p ^ x + n % p ^ x), by
    {
      intros x size,
      split,
      { intros bound, split, exact s x bound, exact bound, },
      { intros size2,
        cases x,
        { simp at size, trivial, },
        { cases x,
          { exact size2.right, },
          { exfalso, exact add_two_not_le_one _ (size2.left), }, }, },
    },
  simp only [finset.filter_congr t],
  simp only [finset.filter_and],
  simp only [filter_Ico_bot 1 (2 * n) (by linarith)],
  exact card_singleton_inter,
end

lemma claim_3
  (p : nat)
  (is_prime : nat.prime p)
  (n : nat)
  (n_big : 3 < n)
  (biggish : 2 * n < 3 * p)
  : α n (by linarith) p is_prime = 1
  :=
begin
-- Have p appearing twice in the factorisation of (2n)!
-- but only once in n!
-- and hence no times in 2n!/n!n!
sorry
end

lemma bertrand_eventually (n : nat) (n_big : 750 ≤ n) : ∃ p, nat.prime p ∧ n < p ∧ p ≤ 2 * n :=
begin
sorry
end

theorem bertrand (n : nat) (n_pos : 0 < n) : ∃ p, nat.prime p ∧ n < p ∧ p ≤ 2 * n :=
begin
cases le_or_lt 750 n,
{exact bertrand_eventually n h},
cases le_or_lt 376 n,
{ use 751, norm_num, split, linarith, linarith, },
clear h,
cases le_or_lt 274 n,
{ use 547, norm_num, split, linarith, linarith, },
clear h_1,
cases le_or_lt 139 n,
{ use 277, norm_num, split, linarith, linarith, },
clear h,
cases le_or_lt 70 n,
{ use 139, norm_num, split, linarith, linarith, },
clear h_1,
cases le_or_lt 37 n,
{ use 73, norm_num, split, linarith, linarith, },
clear h,
cases le_or_lt 19 n,
{ use 37, norm_num, split, linarith, linarith, },
clear h_1,
cases le_or_lt 11 n,
{ use 19, norm_num, split, linarith, linarith, },
clear h,
cases le_or_lt 6 n,
{ use 11, norm_num, split, linarith, linarith, },
clear h_1,
cases le_or_lt 4 n,
{ use 7, norm_num, split, linarith, linarith, },
clear h,
interval_cases n,
{ use 2, norm_num },
{ use 3, norm_num },
{ use 5, norm_num },
end


-/
