/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import algebra.squarefree
import data.nat.factorization.prime_pow
import data.nat.prime_norm_num
import ring_theory.int.basic

/-!
# Lemmas about squarefreeness of natural numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
A number is squarefree when it is not divisible by any squares except the squares of units.

## Main Results
 - `nat.squarefree_iff_nodup_factors`: A positive natural number `x` is squarefree iff
  the list `factors x` has no duplicate factors.

## Tags
squarefree, multiplicity

-/

namespace nat

lemma squarefree_iff_nodup_factors {n : ℕ} (h0 : n ≠ 0) :
  squarefree n ↔ n.factors.nodup :=
begin
  rw [unique_factorization_monoid.squarefree_iff_nodup_normalized_factors h0, nat.factors_eq],
  simp,
end

theorem squarefree_iff_prime_squarefree {n : ℕ} : squarefree n ↔ ∀ x, prime x → ¬ x * x ∣ n :=
squarefree_iff_irreducible_sq_not_dvd_of_exists_irreducible ⟨_, prime_two⟩

lemma squarefree.factorization_le_one {n : ℕ} (p : ℕ) (hn : squarefree n) :
  n.factorization p ≤ 1 :=
begin
  rcases eq_or_ne n 0 with rfl | hn',
  { simp },
  rw [multiplicity.squarefree_iff_multiplicity_le_one] at hn,
  by_cases hp : p.prime,
  { have := hn p,
    simp only [multiplicity_eq_factorization hp hn', nat.is_unit_iff, hp.ne_one, or_false] at this,
    exact_mod_cast this },
  { rw factorization_eq_zero_of_non_prime _ hp,
    exact zero_le_one }
end

lemma squarefree_of_factorization_le_one {n : ℕ} (hn : n ≠ 0) (hn' : ∀ p, n.factorization p ≤ 1) :
  squarefree n :=
begin
  rw [squarefree_iff_nodup_factors hn, list.nodup_iff_count_le_one],
  intro a,
  rw factors_count_eq,
  apply hn',
end

lemma squarefree_iff_factorization_le_one {n : ℕ} (hn : n ≠ 0) :
  squarefree n ↔ ∀ p, n.factorization p ≤ 1 :=
⟨λ p hn, squarefree.factorization_le_one hn p, squarefree_of_factorization_le_one hn⟩

lemma squarefree.ext_iff {n m : ℕ} (hn : squarefree n) (hm : squarefree m) :
  n = m ↔ ∀ p, prime p → (p ∣ n ↔ p ∣ m) :=
begin
  refine ⟨by { rintro rfl, simp }, λ h, eq_of_factorization_eq hn.ne_zero hm.ne_zero (λ p, _)⟩,
  by_cases hp : p.prime,
  { have h₁ := h _ hp,
    rw [←not_iff_not, hp.dvd_iff_one_le_factorization hn.ne_zero, not_le, lt_one_iff,
      hp.dvd_iff_one_le_factorization hm.ne_zero, not_le, lt_one_iff] at h₁,
    have h₂ := squarefree.factorization_le_one p hn,
    have h₃ := squarefree.factorization_le_one p hm,
    rw [nat.le_add_one_iff, le_zero_iff] at h₂ h₃,
    cases h₂,
    { rwa [h₂, eq_comm, ←h₁] },
    { rw [h₂, h₃.resolve_left],
      rw [←h₁, h₂],
      simp only [nat.one_ne_zero, not_false_iff] } },
  rw [factorization_eq_zero_of_non_prime _ hp, factorization_eq_zero_of_non_prime _ hp],
end

lemma squarefree_pow_iff {n k : ℕ} (hn : n ≠ 1) (hk : k ≠ 0) :
  squarefree (n ^ k) ↔ squarefree n ∧ k = 1 :=
begin
  refine ⟨λ h, _, by { rintro ⟨hn, rfl⟩, simpa }⟩,
  rcases eq_or_ne n 0 with rfl | hn₀,
  { simpa [zero_pow hk.bot_lt] using h },
  refine ⟨h.squarefree_of_dvd (dvd_pow_self _ hk), by_contradiction $ λ h₁, _⟩,
  have : 2 ≤ k := k.two_le_iff.mpr ⟨hk, h₁⟩,
  apply hn (nat.is_unit_iff.1 (h _ _)),
  rw ←sq,
  exact pow_dvd_pow _ this
end

lemma squarefree_and_prime_pow_iff_prime {n : ℕ} :
  squarefree n ∧ is_prime_pow n ↔ prime n :=
begin
  refine iff.symm ⟨λ hn, ⟨hn.squarefree, hn.is_prime_pow⟩, _⟩,
  rw is_prime_pow_nat_iff,
  rintro ⟨h, p, k, hp, hk, rfl⟩,
  rw squarefree_pow_iff hp.ne_one hk.ne' at h,
  rwa [h.2, pow_one],
end

/-- Assuming that `n` has no factors less than `k`, returns the smallest prime `p` such that
  `p^2 ∣ n`. -/
def min_sq_fac_aux : ℕ → ℕ → option ℕ
| n k :=
  if h : n < k * k then none else
  have nat.sqrt n + 2 - (k + 2) < nat.sqrt n + 2 - k,
    by { rw nat.add_sub_add_right, exact nat.min_fac_lemma n k h },
  if k ∣ n then
    let n' := n / k in
    have nat.sqrt n' + 2 - (k + 2) < nat.sqrt n + 2 - k, from
      lt_of_le_of_lt (nat.sub_le_sub_right
        (nat.add_le_add_right (nat.sqrt_le_sqrt $ nat.div_le_self _ _) _) _) this,
    if k ∣ n' then some k else min_sq_fac_aux n' (k + 2)
  else min_sq_fac_aux n (k + 2)
using_well_founded {rel_tac :=
  λ _ _, `[exact ⟨_, measure_wf (λ ⟨n, k⟩, nat.sqrt n + 2 - k)⟩]}

/-- Returns the smallest prime factor `p` of `n` such that `p^2 ∣ n`, or `none` if there is no
  such `p` (that is, `n` is squarefree). See also `squarefree_iff_min_sq_fac`. -/
def min_sq_fac (n : ℕ) : option ℕ :=
if 2 ∣ n then
  let n' := n / 2 in
  if 2 ∣ n' then some 2 else min_sq_fac_aux n' 3
else min_sq_fac_aux n 3

/-- The correctness property of the return value of `min_sq_fac`.
  * If `none`, then `n` is squarefree;
  * If `some d`, then `d` is a minimal square factor of `n` -/
def min_sq_fac_prop (n : ℕ) : option ℕ → Prop
| none := squarefree n
| (some d) := prime d ∧ d * d ∣ n ∧ ∀ p, prime p → p * p ∣ n → d ≤ p

theorem min_sq_fac_prop_div (n) {k} (pk : prime k) (dk : k ∣ n) (dkk : ¬ k * k ∣ n)
  {o} (H : min_sq_fac_prop (n / k) o) : min_sq_fac_prop n o :=
begin
  have : ∀ p, prime p → p*p ∣ n → k*(p*p) ∣ n := λ p pp dp,
    have _ := (coprime_primes pk pp).2 (λ e, by { subst e, contradiction }),
    (coprime_mul_iff_right.2 ⟨this, this⟩).mul_dvd_of_dvd_of_dvd dk dp,
  cases o with d,
  { rw [min_sq_fac_prop, squarefree_iff_prime_squarefree] at H ⊢,
    exact λ p pp dp, H p pp ((dvd_div_iff dk).2 (this _ pp dp)) },
  { obtain ⟨H1, H2, H3⟩ := H,
    simp only [dvd_div_iff dk] at H2 H3,
    exact ⟨H1, dvd_trans (dvd_mul_left _ _) H2, λ p pp dp, H3 _ pp (this _ pp dp)⟩ }
end

theorem min_sq_fac_aux_has_prop : ∀ {n : ℕ} k, 0 < n → ∀ i, k = 2*i+3 →
  (∀ m, prime m → m ∣ n → k ≤ m) → min_sq_fac_prop n (min_sq_fac_aux n k)
| n k := λ n0 i e ih, begin
  rw min_sq_fac_aux,
  by_cases h : n < k*k; simp [h],
  { refine squarefree_iff_prime_squarefree.2 (λ p pp d, _),
    have := ih p pp (dvd_trans ⟨_, rfl⟩ d),
    have := nat.mul_le_mul this this,
    exact not_le_of_lt h (le_trans this (le_of_dvd n0 d)) },
  have k2 : 2 ≤ k, { subst e, exact dec_trivial },
  have k0 : 0 < k := lt_of_lt_of_le dec_trivial k2,
  have IH : ∀ n', n' ∣ n → ¬ k ∣ n' → min_sq_fac_prop n' (n'.min_sq_fac_aux (k + 2)),
  { intros n' nd' nk,
    have hn' := le_of_dvd n0 nd',
    refine
      have nat.sqrt n' - k < nat.sqrt n + 2 - k, from
        lt_of_le_of_lt (nat.sub_le_sub_right (nat.sqrt_le_sqrt hn') _) (nat.min_fac_lemma n k h),
      @min_sq_fac_aux_has_prop n' (k+2) (pos_of_dvd_of_pos nd' n0)
        (i+1) (by simp [e, left_distrib]) (λ m m2 d, _),
    cases nat.eq_or_lt_of_le (ih m m2 (dvd_trans d nd')) with me ml,
    { subst me, contradiction },
    apply (nat.eq_or_lt_of_le ml).resolve_left, intro me,
    rw [← me, e] at d, change 2 * (i + 2) ∣ n' at d,
    have := ih _ prime_two (dvd_trans (dvd_of_mul_right_dvd d) nd'),
    rw e at this, exact absurd this dec_trivial },
  have pk : k ∣ n → prime k,
  { refine λ dk, prime_def_min_fac.2 ⟨k2, le_antisymm (min_fac_le k0) _⟩,
    exact ih _ (min_fac_prime (ne_of_gt k2)) (dvd_trans (min_fac_dvd _) dk) },
  split_ifs with dk dkk,
  { exact ⟨pk dk, (nat.dvd_div_iff dk).1 dkk, λ p pp d, ih p pp (dvd_trans ⟨_, rfl⟩ d)⟩ },
  { specialize IH (n/k) (div_dvd_of_dvd dk) dkk,
    exact min_sq_fac_prop_div _ (pk dk) dk (mt (nat.dvd_div_iff dk).2 dkk) IH },
  { exact IH n (dvd_refl _) dk }
end
using_well_founded {rel_tac :=
  λ _ _, `[exact ⟨_, measure_wf (λ ⟨n, k⟩, nat.sqrt n + 2 - k)⟩]}

theorem min_sq_fac_has_prop (n : ℕ) : min_sq_fac_prop n (min_sq_fac n) :=
begin
  dunfold min_sq_fac, split_ifs with d2 d4,
  { exact ⟨prime_two, (dvd_div_iff d2).1 d4, λ p pp _, pp.two_le⟩ },
  { cases nat.eq_zero_or_pos n with n0 n0, { subst n0, cases d4 dec_trivial },
    refine min_sq_fac_prop_div _ prime_two d2 (mt (dvd_div_iff d2).2 d4) _,
    refine min_sq_fac_aux_has_prop 3 (nat.div_pos (le_of_dvd n0 d2) dec_trivial) 0 rfl _,
    refine λ p pp dp, succ_le_of_lt (lt_of_le_of_ne pp.two_le _),
    rintro rfl, contradiction },
  { cases nat.eq_zero_or_pos n with n0 n0, { subst n0, cases d2 dec_trivial },
    refine min_sq_fac_aux_has_prop _ n0 0 rfl _,
    refine λ p pp dp, succ_le_of_lt (lt_of_le_of_ne pp.two_le _),
    rintro rfl, contradiction },
end

theorem min_sq_fac_prime {n d : ℕ} (h : n.min_sq_fac = some d) : prime d :=
by { have := min_sq_fac_has_prop n, rw h at this, exact this.1 }

theorem min_sq_fac_dvd {n d : ℕ} (h : n.min_sq_fac = some d) : d * d ∣ n :=
by { have := min_sq_fac_has_prop n, rw h at this, exact this.2.1 }

theorem min_sq_fac_le_of_dvd {n d : ℕ} (h : n.min_sq_fac = some d)
  {m} (m2 : 2 ≤ m) (md : m * m ∣ n) : d ≤ m :=
begin
  have := min_sq_fac_has_prop n, rw h at this,
  have fd := min_fac_dvd m,
  exact le_trans
    (this.2.2 _ (min_fac_prime $ ne_of_gt m2) (dvd_trans (mul_dvd_mul fd fd) md))
    (min_fac_le $ lt_of_lt_of_le dec_trivial m2),
end

lemma squarefree_iff_min_sq_fac {n : ℕ} :
  squarefree n ↔ n.min_sq_fac = none :=
begin
  have := min_sq_fac_has_prop n,
  split; intro H,
  { cases n.min_sq_fac with d, {refl},
    cases squarefree_iff_prime_squarefree.1 H _ this.1 this.2.1 },
  { rwa H at this }
end

instance : decidable_pred (squarefree : ℕ → Prop) :=
λ n, decidable_of_iff' _ squarefree_iff_min_sq_fac

theorem squarefree_two : squarefree 2 := by rw squarefree_iff_nodup_factors; norm_num

open unique_factorization_monoid

lemma divisors_filter_squarefree {n : ℕ} (h0 : n ≠ 0) :
  (n.divisors.filter squarefree).val =
    (unique_factorization_monoid.normalized_factors n).to_finset.powerset.val.map
      (λ x, x.val.prod) :=
begin
  rw (finset.nodup _).ext ((finset.nodup _).map_on _),
  { intro a,
    simp only [multiset.mem_filter, id.def, multiset.mem_map, finset.filter_val, ← finset.mem_def,
      mem_divisors],
    split,
    { rintro ⟨⟨an, h0⟩, hsq⟩,
      use (unique_factorization_monoid.normalized_factors a).to_finset,
      simp only [id.def, finset.mem_powerset],
      rcases an with ⟨b, rfl⟩,
      rw mul_ne_zero_iff at h0,
      rw unique_factorization_monoid.squarefree_iff_nodup_normalized_factors h0.1 at hsq,
      rw [multiset.to_finset_subset, multiset.to_finset_val, hsq.dedup, ← associated_iff_eq,
        normalized_factors_mul h0.1 h0.2],
      exact ⟨multiset.subset_of_le (multiset.le_add_right _ _), normalized_factors_prod h0.1⟩ },
    { rintro ⟨s, hs, rfl⟩,
      rw [finset.mem_powerset, ← finset.val_le_iff, multiset.to_finset_val] at hs,
      have hs0 : s.val.prod ≠ 0,
      { rw [ne.def, multiset.prod_eq_zero_iff],
        simp only [exists_prop, id.def, exists_eq_right],
        intro con,
        apply not_irreducible_zero (irreducible_of_normalized_factor 0
            (multiset.mem_dedup.1 (multiset.mem_of_le hs con))) },
      rw (normalized_factors_prod h0).symm.dvd_iff_dvd_right,
      refine ⟨⟨multiset.prod_dvd_prod_of_le (le_trans hs (multiset.dedup_le _)), h0⟩, _⟩,
      have h := unique_factorization_monoid.factors_unique irreducible_of_normalized_factor
        (λ x hx, irreducible_of_normalized_factor x (multiset.mem_of_le
          (le_trans hs (multiset.dedup_le _)) hx)) (normalized_factors_prod hs0),
      rw [associated_eq_eq, multiset.rel_eq] at h,
      rw [unique_factorization_monoid.squarefree_iff_nodup_normalized_factors hs0, h],
      apply s.nodup } },
  { intros x hx y hy h,
    rw [← finset.val_inj, ← multiset.rel_eq, ← associated_eq_eq],
    rw [← finset.mem_def, finset.mem_powerset] at hx hy,
    apply unique_factorization_monoid.factors_unique _ _ (associated_iff_eq.2 h),
    { intros z hz,
      apply irreducible_of_normalized_factor z,
      rw ← multiset.mem_to_finset,
      apply hx hz },
    { intros z hz,
      apply irreducible_of_normalized_factor z,
      rw ← multiset.mem_to_finset,
      apply hy hz } }
end

open_locale big_operators

lemma sum_divisors_filter_squarefree {n : ℕ} (h0 : n ≠ 0)
  {α : Type*} [add_comm_monoid α] {f : ℕ → α} :
  ∑ i in (n.divisors.filter squarefree), f i =
    ∑ i in (unique_factorization_monoid.normalized_factors n).to_finset.powerset, f (i.val.prod) :=
by rw [finset.sum_eq_multiset_sum, divisors_filter_squarefree h0, multiset.map_map,
    finset.sum_eq_multiset_sum]

lemma sq_mul_squarefree_of_pos {n : ℕ} (hn : 0 < n) :
  ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ b ^ 2 * a = n ∧ squarefree a :=
begin
  let S := {s ∈ finset.range (n + 1) | s ∣ n ∧ ∃ x, s = x ^ 2},
  have hSne : S.nonempty,
  { use 1,
    have h1 : 0 < n ∧ ∃ (x : ℕ), 1 = x ^ 2 := ⟨hn, ⟨1, (one_pow 2).symm⟩⟩,
    simpa [S] },
  let s := finset.max' S hSne,
  have hs : s ∈ S := finset.max'_mem S hSne,
  simp only [finset.sep_def, S, finset.mem_filter, finset.mem_range] at hs,
  obtain ⟨hsn1, ⟨a, hsa⟩, ⟨b, hsb⟩⟩ := hs,
  rw hsa at hn,
  obtain ⟨hlts, hlta⟩ := canonically_ordered_comm_semiring.mul_pos.mp hn,
  rw hsb at hsa hn hlts,
  refine ⟨a, b, hlta, (pow_pos_iff zero_lt_two).mp hlts, hsa.symm, _⟩,
  rintro x ⟨y, hy⟩,
  rw nat.is_unit_iff,
  by_contra hx,
  refine lt_le_antisymm _ (finset.le_max' S ((b * x) ^ 2) _),
  { simp_rw [S, hsa, finset.sep_def, finset.mem_filter, finset.mem_range],
    refine ⟨lt_succ_iff.mpr (le_of_dvd hn _), _, ⟨b * x, rfl⟩⟩; use y; rw hy; ring },
  { convert lt_mul_of_one_lt_right hlts
      (one_lt_pow 2 x zero_lt_two (one_lt_iff_ne_zero_and_ne_one.mpr ⟨λ h, by simp * at *, hx⟩)),
    rw mul_pow },
end

lemma sq_mul_squarefree_of_pos' {n : ℕ} (h : 0 < n) :
  ∃ a b : ℕ, (b + 1) ^ 2 * (a + 1) = n ∧ squarefree (a + 1) :=
begin
  obtain ⟨a₁, b₁, ha₁, hb₁, hab₁, hab₂⟩ := sq_mul_squarefree_of_pos h,
  refine ⟨a₁.pred, b₁.pred, _, _⟩;
  simpa only [add_one, succ_pred_eq_of_pos, ha₁, hb₁],
end

lemma sq_mul_squarefree (n : ℕ) : ∃ a b : ℕ, b ^ 2 * a = n ∧ squarefree a :=
begin
  cases n,
  { exact ⟨1, 0, (by simp), squarefree_one⟩ },
  { obtain ⟨a, b, -, -, h₁, h₂⟩ := sq_mul_squarefree_of_pos (succ_pos n),
    exact ⟨a, b, h₁, h₂⟩ },
end

/-- `squarefree` is multiplicative. Note that the → direction does not require `hmn`
and generalizes to arbitrary commutative monoids. See `squarefree.of_mul_left` and
`squarefree.of_mul_right` above for auxiliary lemmas. -/
lemma squarefree_mul {m n : ℕ} (hmn : m.coprime n) :
  squarefree (m * n) ↔ squarefree m ∧ squarefree n :=
begin
  simp only [squarefree_iff_prime_squarefree, ←sq, ←forall_and_distrib],
  refine ball_congr (λ p hp, _),
  simp only [hmn.is_prime_pow_dvd_mul (hp.is_prime_pow.pow two_ne_zero), not_or_distrib],
end

end nat

/-! ### Square-free prover -/

open norm_num

namespace tactic
namespace norm_num

/-- A predicate representing partial progress in a proof of `squarefree`. -/
def squarefree_helper (n k : ℕ) : Prop :=
0 < k → (∀ m, nat.prime m → m ∣ bit1 n → bit1 k ≤ m) → squarefree (bit1 n)

lemma squarefree_bit10 (n : ℕ) (h : squarefree_helper n 1) :
  squarefree (bit0 (bit1 n)) :=
begin
  refine @nat.min_sq_fac_prop_div _ _ nat.prime_two two_dvd_bit0 _ none _,
  { rw [bit0_eq_two_mul (bit1 n), mul_dvd_mul_iff_left (two_ne_zero' ℕ)],
    exact nat.not_two_dvd_bit1 _ },
  { rw [bit0_eq_two_mul, nat.mul_div_right _ (dec_trivial:0<2)],
    refine h dec_trivial (λ p pp dp, nat.succ_le_of_lt (lt_of_le_of_ne pp.two_le _)),
    rintro rfl, exact nat.not_two_dvd_bit1 _ dp }
end

lemma squarefree_bit1 (n : ℕ) (h : squarefree_helper n 1) :
  squarefree (bit1 n) :=
begin
  refine h dec_trivial (λ p pp dp, nat.succ_le_of_lt (lt_of_le_of_ne pp.two_le _)),
  rintro rfl, exact nat.not_two_dvd_bit1 _ dp
end

lemma squarefree_helper_0 {k} (k0 : 0 < k)
  {p : ℕ} (pp : nat.prime p) (h : bit1 k ≤ p) : bit1 (k + 1) ≤ p ∨ bit1 k = p :=
begin
  rcases lt_or_eq_of_le h with (hp:_+1≤_) | hp,
  { rw [bit1, bit0_eq_two_mul] at hp, change 2*(_+1) ≤ _ at hp,
    rw [bit1, bit0_eq_two_mul],
    refine or.inl (lt_of_le_of_ne hp _), unfreezingI { rintro rfl },
    exact nat.not_prime_mul dec_trivial (lt_add_of_pos_left _ k0) pp },
  { exact or.inr hp }
end

lemma squarefree_helper_1 (n k k' : ℕ) (e : k + 1 = k')
  (hk : nat.prime (bit1 k) → ¬ bit1 k ∣ bit1 n)
  (H : squarefree_helper n k') : squarefree_helper n k :=
λ k0 ih, begin
  subst e,
  refine H (nat.succ_pos _) (λ p pp dp, _),
  refine (squarefree_helper_0 k0 pp (ih p pp dp)).resolve_right (λ hp, _),
  subst hp, cases hk pp dp
end

lemma squarefree_helper_2 (n k k' c : ℕ) (e : k + 1 = k')
  (hc : bit1 n % bit1 k = c) (c0 : 0 < c)
  (h : squarefree_helper n k') : squarefree_helper n k :=
begin
  refine squarefree_helper_1 _ _ _ e (λ _, _) h,
  refine mt _ (ne_of_gt c0), intro e₁,
  rwa [← hc, ← nat.dvd_iff_mod_eq_zero],
end

lemma squarefree_helper_3 (n n' k k' c : ℕ) (e : k + 1 = k')
  (hn' : bit1 n' * bit1 k = bit1 n)
  (hc : bit1 n' % bit1 k = c) (c0 : 0 < c)
  (H : squarefree_helper n' k') : squarefree_helper n k :=
λ k0 ih, begin
  subst e,
  have k0' : 0 < bit1 k := bit1_pos (nat.zero_le _),
  have dn' : bit1 n' ∣ bit1 n := ⟨_, hn'.symm⟩,
  have dk : bit1 k ∣ bit1 n := ⟨_, ((mul_comm _ _).trans hn').symm⟩,
  have : bit1 n / bit1 k = bit1 n',
  { rw [← hn', nat.mul_div_cancel _ k0'] },
  have k2 : 2 ≤ bit1 k := nat.succ_le_succ (bit0_pos k0),
  have pk : (bit1 k).prime,
  { refine nat.prime_def_min_fac.2 ⟨k2, le_antisymm (nat.min_fac_le k0') _⟩,
    exact ih _ (nat.min_fac_prime (ne_of_gt k2)) (dvd_trans (nat.min_fac_dvd _) dk) },
  have dkk' : ¬ bit1 k ∣ bit1 n', {rw [nat.dvd_iff_mod_eq_zero, hc], exact ne_of_gt c0},
  have dkk : ¬ bit1 k * bit1 k ∣ bit1 n, {rwa [← nat.dvd_div_iff dk, this]},
  refine @nat.min_sq_fac_prop_div _ _ pk dk dkk none _,
  rw this, refine H (nat.succ_pos _) (λ p pp dp, _),
  refine (squarefree_helper_0 k0 pp (ih p pp $ dvd_trans dp dn')).resolve_right (λ e, _),
  subst e, contradiction
end

lemma squarefree_helper_4 (n k k' : ℕ) (e : bit1 k * bit1 k = k')
  (hd : bit1 n < k') : squarefree_helper n k :=
begin
  cases nat.eq_zero_or_pos n with h h,
  { subst n, exact λ _ _, squarefree_one },
  subst e,
  refine λ k0 ih, irreducible.squarefree (nat.prime_def_le_sqrt.2 ⟨bit1_lt_bit1.2 h, _⟩),
  intros m m2 hm md,
  obtain ⟨p, pp, hp⟩ := nat.exists_prime_and_dvd (ne_of_gt m2),
  have := (ih p pp (dvd_trans hp md)).trans
    (le_trans (nat.le_of_dvd (lt_of_lt_of_le dec_trivial m2) hp) hm),
  rw nat.le_sqrt at this,
  exact not_le_of_lt hd this
end

lemma not_squarefree_mul (a aa b n : ℕ) (ha : a * a = aa) (hb : aa * b = n)
  (h₁ : 1 < a) : ¬ squarefree n :=
by { rw [← hb, ← ha], exact λ H, ne_of_gt h₁ (nat.is_unit_iff.1 $ H _ ⟨_, rfl⟩) }

/-- Given `e` a natural numeral and `a : nat` with `a^2 ∣ n`, return `⊢ ¬ squarefree e`. -/
meta def prove_non_squarefree (e : expr) (n a : ℕ) : tactic expr := do
  let ea := reflect a,
  let eaa := reflect (a*a),
  c ← mk_instance_cache `(nat),
  (c, p₁) ← prove_lt_nat c `(1) ea,
  let b := n / (a*a), let eb := reflect b,
  (c, eaa, pa) ← prove_mul_nat c ea ea,
  (c, e', pb) ← prove_mul_nat c eaa eb,
  guard (e' =ₐ e),
  return $ `(@not_squarefree_mul).mk_app [ea, eaa, eb, e, pa, pb, p₁]

/-- Given `en`,`en1 := bit1 en`, `n1` the value of `en1`, `ek`,
  returns `⊢ squarefree_helper en ek`. -/
meta def prove_squarefree_aux : ∀ (ic : instance_cache) (en en1 : expr) (n1 : ℕ)
  (ek : expr) (k : ℕ), tactic expr
| ic en en1 n1 ek k := do
  let k1 := bit1 k,
  let ek1 := `(bit1:ℕ→ℕ).mk_app [ek],
  if n1 < k1*k1 then do
    (ic, ek', p₁) ← prove_mul_nat ic ek1 ek1,
    (ic, p₂) ← prove_lt_nat ic en1 ek',
    pure $ `(squarefree_helper_4).mk_app [en, ek, ek', p₁, p₂]
  else do
    let c := n1 % k1,
    let k' := k+1, let ek' := reflect k',
    (ic, p₁) ← prove_succ ic ek ek',
    if c = 0 then do
      let n1' := n1 / k1,
      let n' := n1' / 2, let en' := reflect n',
      let en1' := `(bit1:ℕ→ℕ).mk_app [en'],
      (ic, _, pn') ← prove_mul_nat ic en1' ek1,
      let c := n1' % k1,
      guard (c ≠ 0),
      (ic, ec, pc) ← prove_div_mod ic en1' ek1 tt,
      (ic, p₀) ← prove_pos ic ec,
      p₂ ← prove_squarefree_aux ic en' en1' n1' ek' k',
      pure $ `(squarefree_helper_3).mk_app [en, en', ek, ek', ec, p₁, pn', pc, p₀, p₂]
    else do
      (ic, ec, pc) ← prove_div_mod ic en1 ek1 tt,
      (ic, p₀) ← prove_pos ic ec,
      p₂ ← prove_squarefree_aux ic en en1 n1 ek' k',
      pure $ `(squarefree_helper_2).mk_app [en, ek, ek', ec, p₁, pc, p₀, p₂]

/-- Given `n > 0` a squarefree natural numeral, returns `⊢ squarefree n`. -/
meta def prove_squarefree (en : expr) (n : ℕ) : tactic expr :=
match match_numeral en with
| match_numeral_result.one := pure `(@squarefree_one ℕ _)
| match_numeral_result.bit0 en1 := match match_numeral en1 with
  | match_numeral_result.one := pure `(nat.squarefree_two)
  | match_numeral_result.bit1 en := do
    ic ← mk_instance_cache `(ℕ),
    p ← prove_squarefree_aux ic en en1 (n / 2) `(1:ℕ) 1,
    pure $ `(squarefree_bit10).mk_app [en, p]
  | _ := failed
  end
| match_numeral_result.bit1 en' := do
  ic ← mk_instance_cache `(ℕ),
  p ← prove_squarefree_aux ic en' en n `(1:ℕ) 1,
  pure $ `(squarefree_bit1).mk_app [en', p]
| _ := failed
end

/-- Evaluates the `squarefree` predicate on naturals. -/
@[norm_num] meta def eval_squarefree : expr → tactic (expr × expr)
| `(@squarefree ℕ %%inst %%e) := do
  is_def_eq inst `(nat.monoid),
  n ← e.to_nat,
  match n with
  | 0 := false_intro `(@not_squarefree_zero ℕ _ _)
  | 1 := true_intro `(@squarefree_one ℕ _)
  | _ := match n.min_sq_fac with
    | some d := prove_non_squarefree e n d >>= false_intro
    | none := prove_squarefree e n >>= true_intro
    end
  end
| _ := failed

end norm_num
end tactic
