
import data.nat.prime
import data.nat.modeq
import data.nat.totient
import data.zmod.basic
import data.zmod.basic data.nat.totient group_theory.order_of_element
-- import data.int.modeq

local attribute [instance, priority 1] nat.has_pow
local prefix `φ `:65 := nat.totient
namespace zmod

open nat

-- Chris Hughes:
-- import data.zmod.basic data.nat.totient group_theory.order_of_element

local notation `φ` := nat.totient

open fintype finset (hiding card)

instance units_zmod.fintype {n : ℕ+} : fintype (units (zmod n)) :=
fintype.of_equiv _ zmod.units_equiv_coprime.symm

lemma card_units_eq_totient (n : ℕ+) :
  card (units (zmod n)) = φ n :=
calc card (units (zmod n)) = card {x : zmod n // x.1.coprime n} :
  fintype.card_congr zmod.units_equiv_coprime
... = φ n : finset.card_congr
  (λ a _, a.1.1)
  (λ a, by simp [a.1.2, a.2.symm] {contextual := tt})
  (λ _ _ h, by simp [subtype.val_injective.eq_iff, (fin.eq_iff_veq _ _).symm])
  (λ b hb, ⟨⟨⟨b, by finish⟩, nat.coprime.symm (by simp at hb; tauto)⟩, mem_univ _, rfl⟩)

lemma pow_totient {n : ℕ+} (x : units (zmod n)) : x ^ φ n = 1 :=
by rw [← card_units_eq_totient, pow_card_eq_one]

-- instance {n : ℕ+} : fintype (units (zmod n)) :=
-- fintype.of_equiv _ zmod.units_equiv_coprime.symm
-- Hmm, shouldn't there be an instance that says that units R is a fintype if R is?

def unit_of_coprime {n : ℕ+} (x : ℕ) (h : nat.coprime x n) : units (zmod n) :=
have (x * gcd_a x ↑n : zmod n) = 1,
  by rw [← int.cast_coe_nat, ← int.cast_one, ← int.cast_mul,
      zmod.eq_iff_modeq_int, ← int.coe_nat_one, ← (show nat.gcd _ _ = _, from h)];
    simpa using int.modeq.gcd_a_modeq x n,
⟨x, gcd_a x n, this, by simpa [mul_comm] using this⟩
end zmod

namespace nat

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

lemma mod_sub_mod_left (x y : ℕ) {n} (hn : n > 0) (hx : y ≤ x % n) :
  ((x % n) - y) % n = (x - y) % n :=
begin
  induction x using nat.strong_induction_on with x ih, dsimp at ih,
  by_cases x < n,
  { rw mod_eq_of_lt h },
  replace h := le_of_not_gt h,
  have hxn : x - n < x,
  { apply nat.sub_lt_self _ hn,
    apply lt_of_lt_of_le hn h, },
  have hx' : y ≤ (x - n) % n,
  { rwa ← nat.mod_eq_sub_mod h, },
  by_cases h' : n ≤ x - y,
  { rw [mod_eq_sub_mod h,ih _ hxn hx',nat.sub_sub,add_comm,← nat.sub_sub,← nat.mod_eq_sub_mod h'], },
  { replace h' := lt_of_not_ge h',
    have hh : y ≤ x := le_trans hx (mod_le _ _),
    rw [nat.sub_lt_left_iff_lt_add hh,← nat.sub_lt_right_iff_lt_add h] at h',
    have h₀ := lt_of_lt_of_le h' hx',
    have h₁ := not_lt_of_le (mod_le (x - n) n),
    contradiction },
end

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

@[simp] theorem totient_zero : φ 0 = 0 := rfl

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

lemma card_map {α β} (f : α ↪ β) (s : finset α) : (s.map f).card = s.card :=
begin
  cases s with s hs,
  simp [finset.card,finset.card,finset.map],
end

def embedding.succ : ℕ ↪ ℕ :=
⟨ nat.succ, @nat.succ.inj ⟩

@[simp]
lemma embedding.succ_apply (x : ℕ) : embedding.succ x = x.succ := rfl

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

def modpow_aux (n k e : ℕ) (hk : k > 1) (ar : array k ℕ) : ℕ → ℕ
| x :=
  if h : 0 < x then
    have x / k < x, from nat.div_lt_self h hk,
    have hk' : 0 < k, from nat.lt_trans (by norm_num) hk,
    ((modpow_aux (x / k)) ^ k % n) * ar.read ⟨x % k, nat.mod_lt _ hk'⟩ % n
  else 1

def modpow' (n k e x : ℕ) : ℕ :=
if hk : k > 1 then
  let ar : array k ℕ := ⟨ λ i, e ^ i.val % n ⟩ in
  modpow_aux n k e hk ar x
else 1
-- set_option pp.all true
open nat (mod_mul_mod_right mod_mul_mod_left modeq)

lemma modpow_eq' (n k e x : ℕ) (hk : k > 1) (hn : n > 1) : modpow' n k e x = e^x % n :=
begin
  rw [modpow',dif_pos hk],
  dsimp,
  generalize Har : (⟨ λ i, e ^ i.val % n ⟩ : array k ℕ) = ar,
  replace Har : ∀ i h, array.read ar ⟨i,h⟩ = e ^ i % n,
  { intros i h, rw ←  Har, refl },
  have hn' : n > 0, from nat.lt_trans (by norm_num) hn,
  induction x using nat.strong_induction_on
     with x ih,
  rw modpow_aux, dsimp at ih, split_ifs,
  { have : x / k < x, from nat.div_lt_self h hk,
    rw [Har,ih _ this,mod_pow_mod,mod_mul_mod_right,mod_mul_mod_left,← _root_.pow_mul,← _root_.pow_add, add_comm],
    rw [mul_comm, nat.mod_add_div,nat.pow_eq_pow],
    all_goals { assumption } },
  { replace h : x = 0,
    { apply le_antisymm (le_of_not_lt h) (zero_le _) },
    simp [*,nat.mod_eq_of_lt hn], }
end

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

end nat
