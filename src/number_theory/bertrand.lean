import data.nat.prime
import data.finset.intervals
import data.nat.multiplicity
import data.nat.choose.sum
import data.padics.padic_norm
import tactic
import ring_theory.multiplicity
import algebra.module
import number_theory.primorial

open_locale big_operators

/-- The multiplicity of p in the nth central binomial coefficient-/
private def α (n : nat) (p : nat) [hp : fact p.prime] : nat :=
padic_val_nat p (nat.choose (2 * n) n)

/-
def primes_le (n : nat) : finset {m : nat // m ≤ n ∧ nat.prime m} :=
begin
  have r : finset {m : nat // m ≤ n ∧ nat.prime m} = finset {m : nat // m < n + 1 ∧ nat.prime m},
  { congr, ext,
    split,
    { rintros ⟨x_le_n, x_prime⟩,
      exact ⟨nat.lt_succ_iff.mpr x_le_n, x_prime⟩, },
    { rintros ⟨x_lt_sn, x_prime⟩,
      exact ⟨nat.lt_succ_iff.mp x_lt_sn, x_prime ⟩, }, },
  simpa only [r, finset.mem_filter, finset.mem_range] using (finset.filter nat.prime (finset.range (n + 1))).attach,
end

lemma alpha_eq (n : nat) (n_pos : 0 < n) :
  nat.choose (2 * n) n = ∏ p in primes_le n, p.val ^ (α n n_pos p p.property.2) :=
begin
sorry
end
-/

lemma central_binom_nonzero (n : ℕ) : nat.choose (2 * n) n ≠ 0 :=
ne_of_gt (nat.choose_pos (by linarith))

lemma foo (p n : ℕ) : nat.log p (2 * n) < nat.log p (2 * n) + 1 :=
begin
  exact lt_add_one (nat.log p (2 * n))
end

lemma foo3 {p : ℕ} : p ≤ 2 * p :=
begin
  omega,
end

lemma claim_1
  (p : nat)
  [hp : fact p.prime]
  (n : nat)
  (n_big : 3 ≤ n)
  : p ^ (α n p) ≤ 2 * n
  :=
begin
  unfold α,
  rw @padic_val_nat_def p hp (nat.choose (2 * n) n) (central_binom_nonzero n),
  simp only [@nat.prime.multiplicity_choose p (2 * n) n (nat.log p (2 * n) + 1)
                        (hp.out) (by linarith) (foo p n)],
  have r : 2 * n - n = n, by
    calc 2 * n - n = n + n - n: by rw two_mul n
    ... = n: nat.add_sub_cancel n n,
  simp [r, ←two_mul],
  have bar : (finset.filter (λ (i : ℕ), p ^ i ≤ 2 * (n % p ^ i)) (finset.Ico 1 (nat.log p (2 * n) + 1))).card ≤ nat.log p (2 * n),
    calc (finset.filter (λ (i : ℕ), p ^ i ≤ 2 * (n % p ^ i)) (finset.Ico 1 (nat.log p (2 * n) + 1))).card ≤ (finset.Ico 1 (nat.log p (2 * n) + 1)).card : by apply finset.card_filter_le
    ... = (nat.log p (2 * n) + 1) - 1 : by simp,
  have baz : p ^ (nat.log p (2 * n)) ≤ 2 * n,
    apply nat.pow_log_le_self,
    apply hp.out.one_lt,
    calc 1 ≤ 3 : dec_trivial
    ...    ≤ n : n_big
    ...    ≤ 2 * n : foo3,
  -- have djf : 1 ≤ p,
  --   calc
  apply trans (pow_le_pow (trans one_le_two hp.out.two_le) bar) baz,
  -- apply trans (@foo2 p _ _ bar) baz,
end

lemma add_two_not_le_one (x : nat) (pr : x.succ.succ ≤ 1) : false :=
  nat.not_succ_le_zero x (nat.lt_succ_iff.mp pr)

lemma claim_2
  (p : nat)
  [hp : fact p.prime]
  (n : nat)
  (n_big : 3 ≤ n)
  (smallish : (2 * n) < p ^ 2)
  : (α n p) ≤ 1
  :=
begin
  have h1 : p ^ α n p < p ^ 2,
    calc p ^ α n p ≤ 2 * n : claim_1 p n n_big
    ...            < p ^ 2 : smallish,

  let h2 := (pow_lt_pow_iff hp.out.one_lt).1 h1,
  omega,
  -- -- pow_lt_pow_iff
  -- unfold α,
  -- rw @padic_val_nat_def p hp (nat.choose (2 * n) n) (central_binom_nonzero n),
  -- simp only [@nat.prime.multiplicity_choose p (2 * n) n _ hp.out (by linarith) (le_refl (2 * n))],
  -- have r : 2 * n - n = n, by
  --   calc 2 * n - n = n + n - n: by rw two_mul n
  --   ... = n: nat.add_sub_cancel n n,
  -- simp only [r, finset.filter_congr_decidable],
  -- have s : ∀ i, p ^ i ≤ n % p ^ i + n % p ^ i → i ≤ 1, by
  --   { intros i pr,
  --     cases le_or_lt i 1, {exact h,},
  --     { exfalso,
  --       have u : 2 * n < 2 * (n % p ^ i), by
  --         calc 2 * n < p ^ 2 : smallish
  --         ... ≤ p ^ i : nat.pow_le_pow_of_le_right (nat.prime.pos is_prime) h
  --         ... ≤ n % p ^ i + n % p ^ i : pr
  --         ... = 2 * (n % p ^ i) : (two_mul _).symm,
  --       have v : n < n % p ^ i, by linarith,
  --       have w : n % p ^ i ≤ n, exact (nat.mod_le _ _),
  --       linarith, }, },
  -- have t : ∀ x ∈ finset.Ico 1 (2 * n), p ^ x ≤ n % p ^ x + n % p ^ x ↔ (x ≤ 1 ∧ p ^ x ≤ n % p ^ x + n % p ^ x), by
  --   {
  --     intros x size,
  --     split,
  --     { intros bound, split, exact s x bound, exact bound, },
  --     { intros size2,
  --       cases x,
  --       { simp at size, trivial, },
  --       { cases x,
  --         { exact size2.right, },
  --         { exfalso, exact nat.not_succ_le_zero _ (nat.lt_succ_iff.mp (size2.left)), }, }, },
  --   },
  -- simp only [finset.filter_congr t],
  -- simp only [finset.filter_and],
  -- simp only [@finset.Ico.filter_Ico_bot 1 (2 * n) (by linarith)],
  -- exact finset.card_singleton_inter,
end

lemma move_mul (m p i : nat) (b : m < i * p) : m / p < i :=
begin
  cases lt_or_le (m / p) i,
  { exact h },
  exfalso,
  have u : i * p ≤ m, by exact le_trans (nat.mul_le_mul_right p h) (nat.div_mul_le_self m p),
  linarith,
end

private lemma collapse_enat (n : enat) (s : 2 = n + 1 + 1) : n = 0 :=
begin
  have u : 0 + 1 = n + 1, by simpa using (enat.add_right_cancel_iff (enat.coe_ne_top 1)).1 s,
  have v : 0 = n, by exact (enat.add_right_cancel_iff (enat.coe_ne_top 1)).1 u,
  exact v.symm
end

lemma twice_nat_small : ∀ (n : nat) (h : 2 * n < 2), n = 0
| 0 := λ _, rfl
| (n + 1) := λ pr, by linarith

lemma pow_big : ∀ (i p : nat) (p_pos : 0 < p) (i_big : 1 < i), p * p ≤ p ^ i
| 0 := λ _ _ pr, by linarith
| 1 := λ _ _ pr, by linarith
| (i + 2) := λ p p_pos i_big, by {
  calc p * p = p ^ 2 : by ring_exp
  ... ≤ p ^ (i + 2) : nat.pow_le_pow_of_le_right p_pos i_big,
}

lemma sasad (a b c : ℕ): a ≤ b -> c * a ≤ c * b :=
begin
  exact nat.mul_le_mul_left c
end

lemma claim_3
  (p : nat)
  [hp : fact p.prime]
  (n : nat)
  (n_big : 6 < n)
  (small : p ≤ n)
  (big : 2 * n < 3 * p)
  : α n p = 0
  :=
begin
  unfold α,
  rw @padic_val_nat_def p hp (nat.choose (2 * n) n) (central_binom_nonzero n),
  simp only [@nat.prime.multiplicity_choose p (2 * n) n (nat.log p (2 * n) + 1)
                        (hp.out) (by linarith) (foo p n)],
  have r : 2 * n - n = n, by
    calc 2 * n - n = n + n - n: by rw two_mul n
    ... = n: nat.add_sub_cancel n n,
  simp [r, ←two_mul],
  clear r,
  have sakdj : ∀ i : ℕ, i > 0 -> ¬ p ^ i ≤ 2 * (n % p ^ i),
    intros i hi,
    simp only [not_le],

  have p_pos : 0 < p,
    exact trans zero_lt_one hp.out.one_lt,

  have n_pos : 0 < n,
    exact pos_of_gt n_big,

  by_cases i = 1,
    {rw h,
    rw pow_one,
    have h4 : p * (n / p) + n % p = n ,
      rw nat.div_add_mod n p,
    suffices h23 : 2 * (p * (n / p)) + 2 * (n % p) < 2 * (p * (n / p)) + p,
    exact (add_lt_add_iff_left (2 * (p * (n / p)))).mp h23,

    rw ←mul_add,
    rw nat.div_add_mod,
    -- rw add_comm at h4,
    -- simp at h4,
    have hn : 0 < n,
      exact pos_of_gt n_big,


    have h345 : 1 ≤ (n / p),
      apply (nat.le_div_iff_mul_le' p_pos).2,
      simp,
      exact small,

    have h5 : p * 1 ≤ p * (n / p),
      -- apply (nat.le_div_iff_mul_le' p_pos).2,
      apply nat.mul_le_mul_left p h345,

    linarith,



    -- rw nat.add_mod
    },
    {
      -- have hTODO231afd : 2 ≤ i,
      --   omega,
      have hTODO231 : 2 * n < p ^ i,
        suffices htodo3214 : 2 * n < p ^ 2,
        have htodo3214431 : p ^ 2 ≤ p ^ i,
          apply nat.pow_le_pow_of_le_right,
          exact p_pos,
          omega,
          omega,
          have todo2sda131 : 3 * p ≤ p ^ 2,
            rw pow_two,
            -- rw ←mul_assoc,
            suffices todoskdajfh : 3 < p,
              rw (mul_le_mul_right p_pos),
              exact le_of_lt todoskdajfh,

            omega,

          calc 2 * n < 3 * p : big
          ...        ≤ p ^ 2 : todo2sda131,

        have todoasdkj : n % p ^ i = n,
          apply nat.mod_eq_of_lt,
          rw two_mul at hTODO231,
          omega,
        rw todoasdkj,
        exact hTODO231,
      },
    apply finset.filter_false_of_mem,
    intro,
    intro,
    apply sakdj,
    rw finset.Ico.mem at H,
    apply H.left,

end


lemma claim_4
  (p : nat)
  [hp : fact p.prime]
  -- (hp : p.prime)
  (n : nat)
  (multiplicity_pos : α n p > 0)
  : p ≤ 2 * n
  :=
begin
  unfold α at multiplicity_pos,
  rw @padic_val_nat_def p hp (nat.choose (2 * n) n) (central_binom_nonzero n) at multiplicity_pos,
  simp only [@nat.prime.multiplicity_choose p (2 * n) n (nat.log p (2 * n) + 1)
                        (hp.out) (by linarith) (foo p n)] at multiplicity_pos,
  have r : 2 * n - n = n, by
    calc 2 * n - n = n + n - n: by rw two_mul n
    ... = n: nat.add_sub_cancel n n,
  simp [r, ←two_mul] at multiplicity_pos,
  clear r,
  rw finset.card_pos at multiplicity_pos,
  cases multiplicity_pos with m hm,
  simp at *,
  calc p = p ^ 1 : by simp
  ...    ≤ p ^ m : begin
                      apply nat.pow_le_pow_of_le_right,
                      linarith [hp.out.one_lt],
                      exact hm.left.left
                    end
  ...    ≤ 2 * (n % p ^ m) : hm.right
  ...    ≤ 2 * n : begin
                     apply nat.mul_le_mul_left,
                     apply nat.mod_le,
                   end,
end

/--
"The mean of a bounded list is less than or equal to the bound".
-/
-- lemma mean_le_biggest {A B : Type*} [decidable_eq A] [ordered_semiring B]
--   (f : A → B) {m : B} (s : finset A) (bound : ∀ x ∈ s, f x ≤ m) : ∑ i in s, f i ≤ s.card * m :=
-- begin
--   rw ← @smul_eq_mul B _ s.card m,
--   rw ← @finset.sum_const _ _ s _ m,
--   apply finset.sum_le_sum bound,
-- end

-- lemma choose_le_middle_2 (r n : ℕ) : nat.choose (2 * n) r ≤ nat.choose (2 * n) n :=
-- begin
--   have s : (2 * n) / 2 = n, by exact nat.mul_div_cancel_left n (by linarith),
--   simpa [] using (@choose_le_middle r (2 * n)),
-- end

/-

/-
Then:
4^n ≤ 2nCn * (2 * n + 1) (by choose_halfway_is_big)
= prod (primes <= 2n) p^(α n p) * (2n+1) ---- need to prove this
= prod (primes <= n) p^(α n p) * prod (primes n < p <= 2n) p^α * (2n+1)
= prod (primes <= 2n/3) p^α * prod (primes 2n/3 to n) p^α * prod (primes n < p ≤ 2n) p^α * (2n+1)
= prod (primes <= 2n/3) p^α * prod (primes 2n/3 to n) 1 * prod (primes n < p ≤ 2n) p^α * (2n+1) -- by claim 3
= prod (primes <= 2n/3) p^α * prod (primes n < p ≤ 2n) p^α * (2n+1)
= prod (primes <= sqrt(2n)) p^α * prod(primes sqrt(2n) to 2n/3) p^α * prod (primes n < p ≤ 2n) p^α * (2n+1)
≤ prod (primes <= sqrt(2n)) p^α * prod(primes sqrt(2n) to 2n/3) p * prod (primes n < p ≤ 2n) p^α * (2n+1) -- by claim 2
≤ prod (primes <= sqrt(2n)) p^α * 4 ^ (2n / 3) * prod (primes n < p ≤ 2n) p^α * (2n+1) -- by primorial bound, proved in different PR
≤ prod (primes <= sqrt(2n)) (2n) * 4 ^ (2n / 3) * prod (primes n < p ≤ 2n) p^α * (2n+1) -- by claim 1
= (2n)^π (sqrt 2n) * 4 ^ (2n/3) * prod (primes n < p ≤ 2n) p^α * (2n+1)
≤ (2n)^(sqrt 2n) * 4 ^ (2n/3) * prod (primes n < p ≤ 2n) p^α * (2n+1) -- by "prime count of x is less than x", need to prove

For sufficiently large n, that last product term is > 1.
Indeed, suppose for contradiction it's equal to 1.
Then 4^n ≤ (2n)^(sqrt 2n) * 4^(2n/3) * (2n+1)
so 4^(n/3) ≤ (2n)^(sqrt 2n) (2n+1)
and this is Clearly False for sufficiently large n.
-/

-/

lemma two_n_div_3_le_two_mul_n_choose_n (n : ℕ) : 2 * n / 3 < (2 * n).choose n :=
begin
  sorry
end

lemma not_pos_iff_zero (n : ℕ) : ¬ 0 < n ↔ n = 0 :=
begin
  omega
end

lemma alskjhads (n x : ℕ): 2 * n / 3 + 1 ≤ x -> 2 * n < 3 * x :=
begin
  intro h,
  rw nat.add_one_le_iff at h,
  sorry
end

lemma central_binom_factorization (n : ℕ) :
      ∏ p in finset.filter nat.prime (finset.range ((2 * n).choose n + 1)),
        p ^ (padic_val_nat p ((2 * n).choose n))
      = (2 * n).choose n :=
begin
  apply prod_pow_prime_padic_val_nat,
  exact central_binom_nonzero n,
  exact lt_add_one ((2 * n).choose n),
end

lemma assafwge (a b c : ℕ) : b ≤ c -> a * b ≤ a * c :=
begin
  exact sasad b c a
end

def central_binom_lower_bound := nat.four_pow_le_two_mul_add_one_mul_central_binom

lemma bertrand_eventually (n : nat) (n_big : 750 ≤ n) : ∃ p, nat.prime p ∧ n < p ∧ p ≤ 2 * n :=
begin
  by_contradiction no_prime,

  have central_binom_factorization_small :
      ∏ p in finset.filter nat.prime (finset.range (2 * n / 3 + 1)),
        p ^ (padic_val_nat p ((2 * n).choose n))
      =
      ∏ p in finset.filter nat.prime (finset.range (((2 * n).choose n + 1))),
        p ^ (padic_val_nat p ((2 * n).choose n)) ,
    apply finset.prod_subset,
    apply finset.subset_iff.2,
    intro x,
    rw finset.mem_filter,
    rw finset.mem_filter,
    rw finset.mem_range,
    rw finset.mem_range,
    intro hx,
    split,
    linarith [(hx.left), (two_n_div_3_le_two_mul_n_choose_n n)],
    exact hx.right,
    intro x,
    rw finset.mem_filter,
    rw finset.mem_filter,
    rw finset.mem_range,
    rw finset.mem_range,
    intro hx,
    intro h2x,
    simp [hx.right] at h2x,
    by_contradiction,
    have x_le_two_mul_n : x ≤ 2 * n,
      apply (@claim_4 x ⟨hx.right⟩ n),
      unfold α,
      simp,
      by_contradiction h1,
      rw not_pos_iff_zero at h1,
      rw h1 at h,
      rw pow_zero at h,
      simp at h,
      exact h,
    apply no_prime,
    use x,
    split,
    exact hx.right,
    split,
    by_contradiction adskjf,
    simp at adskjf,
    have sadjkl := @claim_3 x ⟨hx.right⟩ n (by linarith) (by linarith) (alskjhads n x h2x),
    unfold α at sadjkl,
    rw sadjkl at h,
    rw pow_zero at h,
    simp at h,
    exact h,
    exact x_le_two_mul_n,

    have binom_inequality : (2 * n).choose n ≤ (2 * n) ^ (nat.sqrt (2 * n)) * 4 ^ (2 * n / 3 + 1),
    calc (2 * n).choose n
              = (∏ p in finset.filter nat.prime (finset.range ((2 * n).choose n + 1)),
                   p ^ (padic_val_nat p ((2 * n).choose n)))
                      : (central_binom_factorization n).symm
    ...       = (∏ p in finset.filter nat.prime (finset.range (2 * n / 3 + 1)),
                   p ^ (padic_val_nat p ((2 * n).choose n)))
                      : central_binom_factorization_small.symm
    ...       = (∏ p in finset.filter nat.prime
                          (finset.filter (λ p, p ≤ nat.sqrt (2 * n))
                            (finset.range (2 * n / 3 + 1))),
                   p ^ (padic_val_nat p ((2 * n).choose n)))
                 *
                (∏ p in finset.filter nat.prime
                          (finset.filter (λ p, p ≤ nat.sqrt (2 * n))
                            (finset.range (2 * n / 3 + 1))),
                   p ^ (padic_val_nat p ((2 * n).choose n)))
                     : sorry
    ...       ≤ (2 * n) ^ (nat.sqrt (2 * n))
                 *
                (∏ p in finset.filter nat.prime
                          (finset.filter (λ p, p ≤ nat.sqrt (2 * n))
                            (finset.range (2 * n / 3 + 1))),
                   p ^ (padic_val_nat p ((2 * n).choose n)))
                     : sorry
    ...       ≤ (2 * n) ^ (nat.sqrt (2 * n))
                 *
                (primorial (2 * n / 3 + 1))
                     : sorry
    ...       ≤ (2 * n) ^ (nat.sqrt (2 * n))
                 *
                4 ^ (2 * n / 3 + 1)
                     : nat.mul_le_mul_left _ (primorial_le_4_pow (2 * n / 3 + 1)),
    have faelfkj : 4 ^ n ≤ (2 * n + 1) * (2 * n) ^ (nat.sqrt (2 * n)) * 4 ^ (2 * n / 3 + 1),
    calc 4 ^ n ≤ (2 * n + 1) * (2 * n).choose n : central_binom_lower_bound n
    ...        ≤ (2 * n + 1) * ((2 * n) ^ (nat.sqrt (2 * n)) * 4 ^ (2 * n / 3 + 1))
                  : nat.mul_le_mul_left (2 * n + 1) binom_inequality
    ...        = (2 * n + 1) * (2 * n) ^ (nat.sqrt (2 * n)) * 4 ^ (2 * n / 3 + 1) : by ring,

    sorry

end

/-
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
