
-- set_option threa

-- #exit
import algebra.group_power
import data.nat.parity
import system.random.basic
import .nat

local attribute [instance, priority 1] nat.has_pow
local attribute [-simp] nat.pow_eq_pow

-- Input #1: n > 3, an odd integer to be tested for primality
-- Input #2: k, the number of rounds of testing to perform
-- Output: “composite” if n is found to be composite,
--   “probably prime” otherwise

-- write n as 2r·d + 1 with d odd (by factoring out powers of 2 from n − 1)
-- WitnessLoop: repeat k times:
--    pick a random integer a in the range [2, n − 2]
--    x ← ad mod n
--    if x = 1 or x = n − 1 then
--       continue WitnessLoop
--    repeat r − 1 times:
--       x ← x2 mod n
--       if x = n − 1 then
--          continue WitnessLoop
--    return “composite”
-- return “probably prime”

inductive half_decision (p : Prop) : Type
| is_true : p → half_decision
| unknown {} : half_decision

open nat
  (hiding pow_succ pow_two pow_zero pow_succ one_pow pow_le_pow_of_le_left
          pow_lt_iff_lt_left pow_one pow_le_iff_le_left zero_pow)

def get_roots_aux : ℕ → ℕ → ℕ × ℕ
| n acc :=
  if h : even n ∧ n > 0 then
    have n / 2 < n, from div_lt_self h.2 dec_trivial,
    get_roots_aux (n / 2) (acc + 1)
  else
    (acc, n)

-- #print get_roots_aux._main._pack

def get_roots : ℕ → ℕ × ℕ
| n := get_roots_aux n 0

lemma get_roots_def {n : ℕ} (hn : 0 < n) :
  (get_roots n).2 * 2 ^ (get_roots n).1 = n ∧ ¬ even (get_roots n).2 :=
begin
  rw get_roots, -- generalize : 0 = k,
  suffices : ∀ k,
           (get_roots_aux n k).snd * 2 ^ (get_roots_aux n k).fst = n * 2^k ∧
           ¬even (get_roots_aux n k).snd,
  { specialize this 0, simpa using this, },
  induction n using nat.strong_induction_on
    with n ih, intros k,
  rw get_roots_aux, split_ifs,
  { dsimp at ih,
    specialize ih (n / 2) _ _ (k + 1), cases ih with h₀ h₁,
    split,
    { rw [h₀,pow_succ],
      suffices : 2 ^ k * (2 * (n / 2)) = n * 2 ^ k, cc,
      rw nat.mul_div_cancel' h.1, simp [mul_comm] },
    { exact h₁ },
    { apply div_lt_self, exact h.2, exact dec_trivial },
    { change 1 ≤ n / 2, rw [@le_div_iff_mul_le' 1 _ 2 dec_trivial,mul_comm],
      rcases h with ⟨⟨i,h₀⟩,h₂⟩,
      subst n, clear ih, apply nat.mul_le_mul_left,
      linarith } },
  { rw not_and' at h,
    { exact ⟨rfl,h hn⟩ }, },
end

-- Input #1: n > 3, an odd integer to be tested for primality
-- Input #2: k, the number of rounds of testing to perform
-- Output: “composite” if n is found to be composite,
--   “probably prime” otherwise

-- write n as 2^r·d + 1 with d odd (by factoring out powers of 2 from n − 1)
-- WitnessLoop: repeat k times:
--    pick a random integer a in the range [2, n − 2]
--    x ← a^d mod n
--    if x = 1 or x = n − 1 then
--       continue WitnessLoop
--    repeat r − 1 times:
--       x ← x^2 mod n
--       if x = n − 1 then
--          continue WitnessLoop
--    return “composite”
-- return “probably prime”

lemma coprime_of_prime {p q} (h_prime : nat.prime q) (hp : 0 < p) (hq : p < q) : nat.coprime p q :=
begin
  apply coprime.symm,
  rw prime.coprime_iff_not_dvd h_prime,
  rintro ⟨a,h⟩, subst h,
  replace hq : q * a < q * 1, by rwa mul_one,
  replace hq := lt_of_mul_lt_mul_left hq (nat.zero_le _),
  replace hp : q * 0 < q * a, by rwa mul_zero,
  replace hp := lt_of_mul_lt_mul_left hp (nat.zero_le _),
  linarith,
end

lemma nat.mul_self_sub_mul_self {a b : ℕ} (h : b ≤ a) :
  (a + b) * (a - b) = a * a - b * b :=
begin
  rw [add_mul,nat.mul_sub_left_distrib,nat.mul_sub_left_distrib,mul_comm b a],
  rw [← sub_sub_assoc], congr, rw [sub_sub_assoc,nat.sub_self,zero_add],
  iterate 3 { mono; apply nat.zero_le },
  { rw ← nat.mul_sub_right_distrib, mono,
    apply nat.zero_le, apply nat.sub_le }
end

lemma mod_eq_mod_iff_mod_sub_eq_zero {p q n : ℕ} (hpq : q ≤ p) :
  p % n = q % n ↔ (p - q) % n = 0 :=
begin
  rw [← int.coe_nat_eq_coe_nat_iff,int.coe_nat_mod,int.coe_nat_mod],
  rw [int.mod_eq_mod_iff_mod_sub_eq_zero,← int.coe_nat_sub,← int.coe_nat_mod,← int.coe_nat_zero],
  rwa int.coe_nat_eq_coe_nat_iff,
end

lemma mod_eq_mod_iff_mod_add_eq_zero {p q n : ℕ} (hpq : q ≤ n) :
  p % n = (n - q) % n ↔ (p + q) % n = 0 :=
begin
  rw [← int.coe_nat_eq_coe_nat_iff,int.coe_nat_mod,int.coe_nat_mod],
  rw [eq_comm, int.mod_eq_mod_iff_mod_sub_eq_zero,int.coe_nat_sub,← sub_add_eq_sub_sub_swap],
  rw [sub_eq_add_neg,int.add_mod_self_left,← int.dvd_iff_mod_eq_zero,dvd_neg],
  erw [int.dvd_iff_mod_eq_zero,← int.coe_nat_add,← int.coe_nat_mod,int.coe_nat_eq_coe_nat_iff],
  assumption,
end

lemma two_sqrt {n} {a : ℕ} (h_prime : prime n) (h : a^2 % n = 1) :
  a % n = 1 ∨ a % n = n-1 :=
begin
  have hn : 1 < n := prime.one_lt h_prime,
  have hn₁ : 1 ≤ n := le_of_lt hn,
  have hn₀ : 0 < n := lt_trans dec_trivial hn,
  have hn_sub : n-1 < n,
    by rwa nat.sub_lt_right_iff_lt_add hn₁; apply le_refl (n+1),
  have ha' : 1 ≤ a % n,
  { by_contradiction h',
    replace h' := le_antisymm (le_of_succ_le_succ (lt_of_not_ge h')) (nat.zero_le _),
    rw [← mod_pow_mod _ _ hn₀,h'] at h, rw [zero_pow,mod_eq_of_lt] at h,
    contradiction, transitivity 1, exact dec_trivial, exact hn,
    exact dec_trivial, },
  by_cases hn₂ : n = 2,
  { left, subst n, have := mod_lt a (dec_trivial : 0 < 2),
    generalize_hyp : a % 2 = k at ha' this ⊢,
    clear_except ha' this, omega },
  replace hn₂ : 3 ≤ n, { clear_except hn₂ hn, omega },
  have hn' : 1 < (n : ℤ),
  { rwa [← int.coe_nat_one,int.coe_nat_lt], },
  have ha : 1 ≤ a,
  { by_cases a < n,
    { rwa mod_eq_of_lt h at ha', },
    { transitivity n,
      exact hn₁, apply le_of_not_lt h } },
  have ha₂ : 1 ≤ a * a,
  { rw ← pow_two,
    apply one_le_pow_of_one_le ha, },
  have : ((a+1)*(a-1) % n) = 0,
  { rwa [nat.mul_self_sub_mul_self,mul_one,← mod_eq_mod_iff_mod_sub_eq_zero,← pow_two,mod_eq_of_lt hn],
    all_goals { assumption } },
  rw ← dvd_iff_mod_eq_zero at this,
  by_cases a + 1 < n,
  { have Hpos : 0 < a + 1 := zero_lt_succ _,
    replace this := coprime.dvd_of_dvd_mul_left (coprime.symm $ coprime_of_prime h_prime Hpos h) this,
    rwa [dvd_iff_mod_eq_zero,← mod_eq_mod_iff_mod_sub_eq_zero ha,mod_eq_of_lt hn] at this,
    left, assumption },
  by_cases haₑ₁ : coprime n (a - 1),
  { replace h := le_of_not_lt h,
    have Ha_pos : 1 ≤ a - 1,
    { apply nat.le_sub_left_of_add_le,
      transitivity n - 1, apply nat.le_sub_left_of_add_le, exact hn₂,
      apply nat.sub_le_right_of_le_add h },
    replace this := coprime.dvd_of_dvd_mul_right haₑ₁ this,
    rwa [dvd_iff_mod_eq_zero,← mod_eq_mod_iff_mod_add_eq_zero hn₁,mod_eq_of_lt hn_sub] at this,
    { right, assumption },
     },
  { rw ← prime.dvd_iff_not_coprime h_prime at haₑ₁,
    rwa [dvd_iff_mod_eq_zero,← mod_eq_mod_iff_mod_sub_eq_zero ha,mod_eq_of_lt hn] at haₑ₁,
    left, assumption, }
end

lemma miller_rabin_prop {n} {a d r : ℕ}
  (ha : a > 1) (ha_n : a < n)
  (hdna : 2^r * d = n-1)
  (hn : nat.prime n) :
  a^d % n = 1 ∨ ∃ r' < r, a^(d * 2^r') % n = n-1 :=
begin
  have : a^(n-1) ≡ 1 [MOD n],
  { rwa [← totient_eq_of_prime hn],apply nat.pow_totient _,
    apply coprime_of_prime hn _ ha_n, apply lt_trans _ ha, exact dec_trivial },
  clear ha_n,
  have hn' : 1 < n, { apply prime.one_lt hn },
  rw ← hdna at this, clear hdna,
  induction r with r ih generalizing a,
  { rw [_root_.pow_zero,one_mul,modeq] at this,
    left, rwa [this,mod_eq_of_lt] },
  { rw [pow_succ,mul_assoc,pow_mul] at this,
    have ha₂ : a ^ 2 ≥ 2,
    { conv_rhs { rw [← pow_one 2] },
      transitivity 2^2,
      apply pow_le_pow_of_le_left (dec_trivial : 0 ≤ 2) ha,
      exact dec_trivial },
    specialize ih ha₂ this, cases ih,
    { rw [← pow_mul,mul_comm,pow_mul] at ih,
      have := two_sqrt hn ih, cases this,
      { left, assumption },
      { right, existsi [0,zero_lt_succ _],
        rwa [pow_zero,mul_one], } },
    { rcases ih with ⟨r',hr,h₀⟩, right,
      existsi [succ r',succ_lt_succ hr],
      rw ← h₀, rw [← pow_mul,pow_succ], ac_refl } },
end

def miller_rabin_aux {n : ℕ} (hn : 1 < n) (a rr d : ℕ) (ha : a > 1)
  (han : a < n)
  (hrd : 2 ^ rr * d = n-1)
  (hadn : a^d % n ≠ 1) :
  ∀ r₀ x r : ℕ,
    r₀ ≤ rr →
    r = rr - r₀ →
    x = a^(d * 2^r) % n →
    (∀ r' < r, a^(d * 2^r') % n ≠ n-1) →
    rand (half_decision (¬ nat.prime n))
| 0 x r h₀ h₁ h₂ h₃ := pure $ half_decision.is_true $
    λ h₄,
    -- let h := miller_rabin_prop ha _ hrd h₄ in
    -- let h := miller_rabin_prop ha hrd _ h₄  in
    absurd (miller_rabin_prop ha han hrd h₄)
      (not_or_distrib.2 ⟨hadn,not_exists_of_forall_not $ λ r', not_exists_of_forall_not $ λ hr, h₃ _ $ by rwa h₁ ⟩)
| (succ r₀) x r h₀ h₁ h₂ h₃ :=
  have hh₂ : 0 < n, from lt_trans dec_trivial hn,
  have hh₀ : r + 1 = rr - r₀, by rwa [h₁,← nat.sub_add_comm,succ_sub_succ],
    -- by rw [h₁,nat.sub_sub,nat.add_comm 1,← nat.sub_sub,nat.sub_add_cancel,nat.sub_sub,add_comm];
    --    apply nat.le_sub_left_of_add_le; exact h₀,
  have hh₁ : x * x % n = a ^ (d * 2 ^ (r + 1)) % n,
    by rw [← pow_two,h₂,mod_pow_mod _ _ hh₂,← pow_mul,pow_succ',mul_assoc],
  if hh₃ : x = n - 1 then
    pure half_decision.unknown
  else
    miller_rabin_aux r₀ (x*x % n) (r+1) (le_trans (le_succ _) h₀) hh₀ hh₁ $
      by { simp, introv h, rw lt_succ_iff_lt_or_eq at h,
           cases h, { exact h₃ _ h }, { rwa [h,← h₂] }, }

-- #exit

def miller_rabin' {n : ℕ} (hn : 3 < n) : ℕ → rand (half_decision (¬ nat.prime n))
| 0 := pure half_decision.unknown
| (succ k) :=
  match get_roots (n-1),rfl : ∀ x, get_roots (n-1) = x → _ with
  | ⟨r,d⟩, h :=
  -- let ⟨⟨r,s⟩,h⟩ := (⟨get_roots n,rfl⟩ : { k // k = get_roots n}) in do
    have hn₀ : n-1 > 0, by rw [(>)]; apply lt_of_succ_le;
      apply nat.le_sub_left_of_add_le;
      transitivity 4; [exact dec_trivial, assumption],
    have hn₁ : n > 1, from lt_trans dec_trivial hn,
    have hrs : d * 2 ^ r = n-1 ∧ ¬ even d,
      by convert get_roots_def hn₀; rw h,
    have h₀ : d * 2 ^ r = n-1, from hrs.1,
    have h₁ : ¬ even d, from hrs.2,
    have this : 2 ≤ n - 1, from nat.le_sub_left_of_add_le (le_of_lt hn),
    do ⟨a,ha₀,ha₁⟩ ← bounded_random.random_r _ 2 (n-1),
       let x := modpow n d a,
       have x = a^d % n, from modpow_eq n a d hn₁,
       if hx : x = 1 then miller_rabin' k
       else do
         have ha₂ : a + 1 ≤ n, from (nat.le_sub_right_iff_add_le (le_of_lt hn₁)).1 ha₁,
         have hrr : 0 = r - r, from (nat.sub_self r).symm,
         miller_rabin_aux hn₁ a r d ha₀ ha₂ (mul_comm d (2^r) ▸ h₀) (this ▸ hx) r x 0
           (le_refl _) hrr
           (by rw [pow_zero,mul_one]; exact this)
           (by simp)
  end

def miller_rabin (n : ℕ) : rand (half_decision (¬ nat.prime n)) :=
if h : 3 < n
  then miller_rabin' h 5
else if h' : n < 2
  then pure $ half_decision.is_true $ λ h'', not_le_of_gt h' $ prime.two_le h''
  else pure half_decision.unknown
