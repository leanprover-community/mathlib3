
import data.list.sort
import data.nat.prime
import data.fintype
import data.nat.modeq
import data.nat.totient

import group_theory.order_of_element

local notation `φ` := nat.totient
local attribute [instance, priority 1] nat.has_pow

namespace zmod

lemma pow_totient {n : ℕ+} (x : units (zmod n)) : x ^ φ n = 1 :=
by rw [← card_units_eq_totient, pow_card_eq_one]

end zmod


namespace nat

open zmod
lemma pow_totient {x n : ℕ} (h : nat.coprime x n) : x ^ φ n ≡ 1 [MOD n] :=
begin
  rcases nat.eq_zero_or_pos n with rfl | h₁, {simp},
  let n' : ℕ+ := ⟨n, h₁⟩,
  let x' : units (zmod n') := zmod.unit_of_coprime _ h,
  have := pow_totient x',
  apply (zmod.eq_iff_modeq_nat' h₁).1,
  apply_fun (coe:units (zmod n') → zmod n') at this,
  simpa [show (x':zmod n') = x, from rfl],
end

def embedding.succ : ℕ ↪ ℕ :=
⟨ nat.succ, @nat.succ.inj ⟩

@[simp]
lemma embedding.succ_apply (x : ℕ) : embedding.succ x = x.succ := rfl

open finset
lemma totient_eq_of_prime {n : ℕ} (h : nat.prime n) : totient n = n-1 :=
begin
  suffices : finset.filter (nat.coprime n) (finset.range n) =
    (finset.range $ n - 1).map embedding.succ,
  { rw [totient,this,card_map,finset.card_range], },
  ext, simp, split; intro h₁,
  { have h' : 0 < a,
    { apply lt_of_not_ge, intro h, rw [(≥),nat.le_zero_iff] at h,
      subst a, rw [nat.coprime,nat.gcd_zero_right] at h₁,
      rw h₁.2 at h, apply nat.not_prime_one h },
    refine ⟨a-1,(nat.sub_lt_sub_right_iff h').2 h₁.1,_⟩,
    rw [← nat.succ_sub h',nat.succ_sub_succ,nat.sub_zero], },
  { rcases h₁ with ⟨a',h₀,h₁⟩,
    have h₂ : 0 < a, { rw ← h₁, apply nat.zero_lt_succ },
    have h₁ : a < n, { rw [← h₁], exact nat.lt_pred_iff.mp h₀, },
    existsi h₁,
    have h' := nat.coprime_or_dvd_of_prime h a,
    rw or_iff_not_imp_right at h', apply h', clear h',
    rintros ⟨b,h₄⟩,
    rw ← mul_zero n at h₂, rw ← mul_one n at h₁,
    subst h₄,
    replace h₂ := lt_of_mul_lt_mul_left h₂ (zero_le _),
    replace h₁ := lt_of_mul_lt_mul_left h₁ (zero_le _),
    exact not_le_of_lt h₁ h₂, },
end

lemma fermat_prime_test {a n : ℕ} (ha₂ : ¬ n ∣ a) (h : nat.prime n) : a^(n-1) ≡ 1 [MOD n] :=
begin
  have hh' : 0 < a % n,
  { apply lt_of_le_of_ne (nat.zero_le _), symmetry,
    intro h, rw [← dvd_iff_mod_eq_zero] at h,
    contradiction },
  have hn : 1 < n, from h.one_lt,
  have hn' : 0 < n, from lt_trans (by norm_num) hn,
  rw [← nat.totient_eq_of_prime h],
  apply nat.pow_totient,
  apply nat.coprime.symm,
  exact (prime.coprime_iff_not_dvd h).2 ha₂,
end

lemma fermat_prime_test' {a n : ℕ} (ha₀ : 0 < a) (ha₁ : a < n) (h : nat.prime n) : a^(n-1) ≡ 1 [MOD n] :=
begin
  have hh' : 0 < a % n,
  { rw nat.mod_eq_of_lt ha₁, exact ha₀ },
  apply fermat_prime_test _ h,
  intro hh, cases hh, subst a,
  rw nat.mul_mod_right at hh',
  exact nat.not_succ_le_zero 0 hh',
end

lemma succ_mod (x : ℕ) {n} (hn : n > 0) : succ (x % n) % n = succ x % n :=
begin
  induction x using nat.strong_induction_on with x ih,
  cases le_or_gt n x with h h,
  { rw [mod_eq_sub_mod h,ih,← succ_sub h,← mod_eq_sub_mod],
    apply le_trans h (le_succ _), apply nat.sub_lt (lt_of_lt_of_le hn h) hn },
  { rw mod_eq_of_lt h },
end

lemma mod_add_mod_left (x y : ℕ) {n} (hn : n > 0) : ((x % n) + y) % n = (x + y) % n :=
begin
  induction y; simp [add_zero,add_succ],
  rw [← succ_mod _ hn,y_ih,succ_mod _ hn],
end

lemma mod_add_mod_right (x y : ℕ) {n} (hn : n > 0) : (x + (y % n)) % n = (x + y) % n :=
by rw [add_comm,mod_add_mod_left _ _ hn,add_comm]

lemma mod_mul_mod_left (x y : ℕ) {n} (hn : n > 0) : (x % n) * y % n = x * y % n :=
begin
  induction y,
  simp [mul_zero,mul_succ],
  rw [mul_succ,← mod_add_mod_left _ _ hn,y_ih,mod_add_mod_left _ _ hn,mul_succ,mod_add_mod_right _ _ hn],
end

lemma mod_mul_mod_right (x y : ℕ) {n} (hn : n > 0) : x * (y % n) % n = x * y % n :=
by rw [mul_comm,mod_mul_mod_left _ _ hn,mul_comm]

lemma mod_pow_mod (e x : ℕ) {n} (hn : n > 0) : (e % n) ^ x % n = e ^ x % n :=
begin
  induction x with x x_ih; simp only [_root_.pow_zero,_root_.pow_succ],
  rw [← mod_mul_mod_right _ _ hn,x_ih,mod_mul_mod_left _ _ hn,mod_mul_mod_right _ _ hn],
end

open bounded_random

lemma succ_le_iff_le_pred {p q} (hq : 0 < q) : succ p ≤ q ↔ p ≤ pred q :=
begin
  cases q, cases hq,
  apply nat.succ_le_succ_iff
end

def modpow (n : ℕ) : ℕ → ℕ → ℕ
| x e :=
  if h : 0 < x then
    have x / 2 < x, from nat.div_lt_self h (by norm_num),
    if x % 2 = 1 then
      e * modpow (x / 2) (e * e % n) % n
    else
      modpow (x / 2) (e * e % n)
  else
    1

lemma modpow_eq (n e x : ℕ) (hn : n > 1) : modpow n x e = e^x % n :=
begin
  have hn' : n > 0, from nat.lt_trans (by norm_num) hn,
  induction x using nat.strong_induction_on
     with x ih generalizing e,
  rw modpow,
  have h₀ : e ^ (2 * (x / 2) + x % 2) % n = e ^ x % n,
  { rw [add_comm,nat.mod_add_div] },
  split_ifs with ha hb,
  all_goals
  { try { have h₁ : x / 2 < x, from nat.div_lt_self ha (by norm_num) } },
  { rwa [ih,mod_pow_mod _ _ hn',mod_mul_mod_right _ _ hn',← _root_.pow_two, ← _root_.pow_mul,
        ← _root_.pow_succ,← h₀,hb], },
  { replace hb : x % 2 = 0,
    { have := nat.mod_lt x (by norm_num : 0 < 2),
      clear_except hb this, omega },
    rwa [ih,mod_pow_mod,← _root_.pow_two, ← _root_.pow_mul,← h₀,hb, nat.add_zero];
      assumption },
  { replace ha : x = 0,
    { apply le_antisymm (le_of_not_lt ha) (zero_le _) },
    simp [*,nat.mod_eq_of_lt hn], }
end

def fermat_test' (n : ℕ) : ℕ → rand (decidable (nat.prime n))
| 0 := pure infer_instance
| (nat.succ k) :=
     if h : 2 ≤ n then
       have 1 ≤ n - 1, from nat.le_pred_of_lt h,
       have 0 < n, from nat.lt_of_succ_lt h,
       do ⟨a,ha,ha'⟩ ← bounded_random.random_r std_gen 1 (n - 1),
          have h_an : a < n, from (succ_le_iff_le_pred this).2 ha',
          if hh : nat.gcd a n = 1 then
            if hk : nat.modpow n (n-1) a = 1 then fermat_test' k
            else
              have hk' : ¬ (a^(n-1) % n) = 1 % n,
                by rwa [← nat.modpow_eq,nat.mod_eq_of_lt]; assumption,
              pure $ is_false $ λ h, hk' $ nat.fermat_prime_test' ha h_an h
          else
            have hh₃ : nat.gcd a n ≠ n,
              by { apply ne_of_lt, apply lt_of_le_of_lt (nat.gcd_le_left _ ha) h_an, },
            have han : nat.gcd a n ∣ n, from nat.gcd_dvd_right _ _,
            have h' : n ≠ 0, from ne_of_gt this,
            have hh' : ¬nat.gcd a n = 0,
              from λ h, h' $ nat.eq_zero_of_gcd_eq_zero_right h,
            have hgcd : 2 ≤ nat.gcd a n, by omega,
            pure $ is_false $ λ hh', hh₃ ((nat.dvd_prime_two_le hh' hgcd).1 han)
     else pure $ is_false $ λ h', h $ nat.prime.one_lt h'

def fermat_test (n : ℕ) : rand (decidable (nat.prime n)) :=
fermat_test' n 5

section mfind

parameter {p : ℕ → Prop}

private def lbp (m n : ℕ) : Prop := m = n + 1 ∧ ∀ k ≤ n, ¬p k

parameters {m : Type → Type*} [monad m]
parameters (pdec : ∀ x, m (decidable (p x))) (H : ∃n, p n)

private def wf_lbp : well_founded lbp :=
⟨let ⟨n, pn⟩ := H in
suffices ∀m k, n ≤ k + m → acc lbp k, from λa, this _ _ (nat.le_add_left _ _),
λm, nat.rec_on m
  (λk kn, ⟨_, λy r, match y, r with ._, ⟨rfl, a⟩ := absurd pn (a _ kn) end⟩)
  (λm IH k kn, ⟨_, λy r, match y, r with ._, ⟨rfl, a⟩ := IH _ (by rw nat.add_right_comm; exact kn) end⟩)⟩

/-- (adapted from core) find the first natural number that satisfies `p` using a monadic
decision procedure -/
protected def mfind : m {n // p n ∧ ∀m < n, ¬p m} :=
@well_founded.fix _ (λk, (∀n < k, ¬p n) → m {n // p n ∧ ∀m < n, ¬p m}) lbp wf_lbp
(λm IH al, do
    d ← pdec m,
    match d with
    | is_true pm := pure ⟨m, pm, al⟩
    | is_false pm :=
               have ∀ n ≤ m, ¬p n,
                 from λn h, or.elim (lt_or_eq_of_le h) (al n) (λe, by rw e; exact pm),
               IH _ ⟨rfl, this⟩ (λn h, this n $ nat.le_of_succ_le_succ h)
    end )
0 (λn h, absurd h (nat.not_lt_zero _))

end mfind

end nat


namespace list

variables {α : Type*} {R : α → α → Prop}

instance decidable_sorted [decidable_rel R] (l : list α) : decidable (sorted R l) :=
list.decidable_pairwise l

end list
