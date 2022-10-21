import number_theory.lucas_primality

namespace nat

def my_pow_mod (a b n : ℕ) : ℕ := a ^ b % n
def my_pow_mod_aux (a b c n : ℕ) : ℕ := (a ^ b * c) % n
  -- the tail recursive pow mod like on wikipedia

lemma my_pow_mod_aux_zero (a c c0 n : ℕ) (hc : c % n = c0) : my_pow_mod_aux a 0 c n = c0 :=
by rwa [my_pow_mod_aux, pow_zero, one_mul]

lemma my_pow_mod_aux_one (a c ac n m : ℕ) (hac : a * c = ac) (hm : ac % n = m) :
  my_pow_mod_aux a 1 c n = m :=
by rwa [my_pow_mod_aux, pow_one, hac]

lemma my_pow_mod_aux_bit0 (a b c n m a2 ra2 qa2 za2 : ℕ)
  (ha2 : a * a = a2) (hqa2 : n * qa2 = za2) (hra2 : ra2 + za2 = a2)
  (hm : my_pow_mod_aux ra2 b c n = m) :
  my_pow_mod_aux a (bit0 b) c n = m :=
begin
  substs za2 a2,
  rwa [my_pow_mod_aux, pow_bit0', mul_mod, pow_mod, ←hra2, add_mul_mod_self_left,
    ←pow_mod, ←mul_mod]
end

lemma my_pow_mod_aux_bit1 {a b c n m qa2 za2 ra2 a2 qac zac rac ac : ℕ}
  (ha2 : a * a = a2) (hqa2 : n * qa2 = za2) (hra2 : za2 + ra2 = a2)
  (hac : a * c = ac) (hqac : n * qac = zac) (hrac : zac + rac = ac)
  (hm : my_pow_mod_aux ra2 b rac n = m) :
  my_pow_mod_aux a (bit1 b) c n = m :=
begin
  substs a2 za2 ac zac,
  rwa [my_pow_mod_aux, pow_bit1', mul_assoc, ←hra2, ←hrac, mul_mod, pow_mod, add_mul_mod_self_left,
    add_comm, add_mul_mod_self_left, ←pow_mod, ←mul_mod],
end

lemma my_pow_mod_eq (a b n m : ℕ) (h : my_pow_mod_aux a b 1 n = m) :
  my_pow_mod a b n = m :=
by rwa [my_pow_mod_aux, mul_one] at h

section
open tactic
open norm_num

open norm_num.match_numeral_result

/-- Given `a b c n : nat`, returns `(m, ⊢ my_pow_mod_aux a b c n = m)`. -/
meta def prove_pow_mod_aux :
  instance_cache → expr → expr → expr → expr → tactic (instance_cache × expr × expr)
| ic a b c n :=
  match match_numeral b with
  | match_numeral_result.zero := do
      (ic, c0, p) ← prove_div_mod ic c n tt,
      q ← mk_app ``my_pow_mod_aux_zero [a, c, c0, n, p],
      return (ic, c0, q)
  | one := do
      (ic, ac, hac) ← prove_mul_nat ic a c,
      (ic, m, hm) ← prove_div_mod ic ac n tt,
      q ← mk_app ``my_pow_mod_aux_one [a, c, ac, n, m, hac, hm],
      return (ic, m, q)
  | bit0 b := do
      (ic, a2, ha2) ← prove_mul_nat ic a a,
      nn ← n.to_nat,
      na2 ← a2.to_nat,
      let nra2 := na2 % nn,
      let nqa2 := na2 / nn,
        -- instead of using `prove_div_mod`, mimic its proof since the prove_lt bit is unneeded
        -- should i use rats instead like that does?
      (ic, ra2) ← ic.of_nat nra2,
      (ic, qa2) ← ic.of_nat nqa2,
      (ic, za2, hqa2) ← prove_mul_nat ic n qa2,
      (ic, hra2) ← prove_add_nat ic ra2 za2 a2,
      (ic, m, hm) ← prove_pow_mod_aux ic ra2 b c n,
      q ← mk_app ``my_pow_mod_aux_bit0 [a, b, c, n, m, a2, ra2, qa2, za2, ha2, hqa2, hra2, hm],
      return (ic, m, q)
  | bit1 b := do
      (ic, a2, ha2) ← prove_mul_nat ic a a,
      (ic, ac, hac) ← prove_mul_nat ic a c,
      nn ← n.to_nat,
      na2 ← a2.to_nat,
      nac ← ac.to_nat,
      let nra2 := na2 % nn,
      let nqa2 := na2 / nn,
      let nrac := nac % nn,
      let nqac := nac / nn,
      (ic, ra2) ← ic.of_nat nra2,
      (ic, qa2) ← ic.of_nat nqa2,
      (ic, rac) ← ic.of_nat nrac,
      (ic, qac) ← ic.of_nat nqac,
      (ic, za2, hqa2) ← prove_mul_nat ic n qa2,
      (ic, zac, hqac) ← prove_mul_nat ic n qac,
      (ic, hra2) ← prove_add_nat ic ra2 za2 a2,
      (ic, hrac) ← prove_add_nat ic zac rac ac,
      (ic, m, hm) ← prove_pow_mod_aux ic ra2 b rac n,
      q ← mk_app ``my_pow_mod_aux_bit1 [a, b, c, n, m, qa2, za2, ra2, a2, qac, zac, rac, ac, ha2,
        hqa2, hra2, hac, hqac, hrac, hm],
      return (ic, m, q)
  | _ := failed
  end

@[norm_num] meta def eval_my_pow_mod : expr → tactic (expr × expr)
| `(my_pow_mod_aux %%a %%b %%c %%n) := do
    ic ← mk_instance_cache `(ℕ),
    prod.snd <$> prove_pow_mod_aux ic a b c n
| `(my_pow_mod %%a %%b %%n) := do
    ic ← mk_instance_cache `(ℕ),
    (ic, m, hm) ← prove_pow_mod_aux ic a b `(1) n,
    q ← mk_app ``my_pow_mod_eq [a, b, n, m, hm],
    return (m, q)
| e := failed

end

example : my_pow_mod 5 23509285402366 23509285402367 = 1 :=
by norm_num1

example : my_pow_mod 5 (11754642701183 - 1) 11754642701183 = 1 :=
by norm_num1

lemma x1 : my_pow_mod 5 23509285402366 23509285402367 = 1 ∧ my_pow_mod 5 (11754642701183 - 1) 11754642701183 = 1 :=
begin
  split,
  norm_num1,
  norm_num1,
end

def pratt_predicate (p a x : ℕ) : Prop := ∀ q ∈ x.factors, a ^ ((p - 1) / q) % p ≠ 1

lemma pratt_predicate_iff (p a x : ℕ) :
  pratt_predicate p a x ↔ ∀ q ∈ x.factors, my_pow_mod a ((p - 1) / q) p ≠ 1 :=
iff.rfl

def pratt_zero (p a : ℕ) : pratt_predicate p a 0 := by { rw [pratt_predicate], simp }
def pratt_axiom (p a : ℕ) : pratt_predicate p a 1 := by { rw [pratt_predicate], simp }

lemma pratt_rule_1 {p a x q : ℕ} (h : pratt_predicate p a x) (hq : prime q)
  (h' : a ^ ((p - 1) / q) % p ≠ 1) : pratt_predicate p a (q * x) :=
begin
  rcases eq_or_ne x 0 with rfl | hx,
  { rwa mul_zero },
  intros r hr,
  rw [mem_factors_mul hq.ne_zero hx, factors_prime hq, list.mem_singleton] at hr,
  rcases hr with rfl | hr,
  exacts [h', h r hr],
end

lemma pratt_rule_1' (q x : ℕ) {p a y : ℕ} (hq : prime q) (hy : q * x = y)
  (h' : my_pow_mod a ((p - 1) / q) p ≠ 1) (h : pratt_predicate p a x) : pratt_predicate p a y :=
by { rw [←hy], exact pratt_rule_1 h hq h' }

lemma pratt_rule_2 (a : ℕ) {p : ℕ} (hp : p ≠ 0) (h : pratt_predicate p a (p - 1))
  (h' : a ^ (p - 1) % p = 1) : prime p :=
begin
  rcases p with rfl | rfl | p,
  { cases hp rfl },
  { simpa using h' },
  rw [pratt_predicate, succ_sub_one] at h,
  rw [succ_sub_one] at h',
  simp only [mem_factors (succ_ne_zero _), and_assoc, ne.def, and_imp] at h,
  let a' : zmod (p + 2) := a,
  have := lucas_primality _ a',
  simp only [succ_sub_one, ←nat.cast_pow] at this,
  refine this _ (λ q hq hq', _),
  { rw [←zmod.nat_cast_mod, h', nat.cast_one] },
  rw [←zmod.nat_cast_mod, ←@nat.cast_one (zmod (p+2)), ne.def, zmod.eq_iff_modeq_nat,
    nat.modeq, mod_mod, one_mod],
  exact h _ hq hq',
end

lemma pratt_rule_2' (a : ℕ) {p : ℕ} (hp : p ≠ 0) (h' : my_pow_mod a (p - 1) p = 1)
  (h : pratt_predicate p a (p - 1)) : prime p :=
pratt_rule_2 a hp h h'


set_option profiler true
set_option profiler.threshold 0.1

lemma boltons_prime : prime (15 * 2^27 + 1) :=
begin
  have : ∀ x, x ∈ nat.factors (15 * 2^27 + 1 - 1) ↔ x = 2 ∨ x = 3 ∨ x = 5,
  { norm_num },
  refine pratt_rule_2' 31 (by norm_num) (by norm_num) _,
  simp only [pratt_predicate_iff, this, forall_eq_or_imp, forall_eq],
  norm_num,
end

lemma thing0 :
  ∀ x, x ∈ nat.factors (18446744069414584321 - 1) ↔
    x = 2 ∨ x = 3 ∨ x = 5 ∨ x = 17 ∨ x = 257 ∨ x = 65537 :=
by norm_num

lemma thing1 : 18446744069414584321 ≠ 0 := by norm_num
lemma thing2 : my_pow_mod 7 (18446744069414584321 - 1) 18446744069414584321 = 1 := by norm_num
lemma thing3 : my_pow_mod 7 ((18446744069414584321 - 1) / 2) 18446744069414584321 ≠ 1 := by norm_num
lemma thing4 : my_pow_mod 7 ((18446744069414584321 - 1) / 3) 18446744069414584321 ≠ 1 := by norm_num
lemma thing5 : my_pow_mod 7 ((18446744069414584321 - 1) / 5) 18446744069414584321 ≠ 1 := by norm_num
lemma thing6 : my_pow_mod 7 ((18446744069414584321 - 1) / 17) 18446744069414584321 ≠ 1 := by norm_num
lemma thing7 : my_pow_mod 7 ((18446744069414584321 - 1) / 257) 18446744069414584321 ≠ 1 := by norm_num
lemma thing8 : my_pow_mod 7 ((18446744069414584321 - 1) / 65537) 18446744069414584321 ≠ 1 := by norm_num

lemma goldilocks : prime 18446744069414584321 :=
begin
  refine pratt_rule_2' 7 thing1 thing2 _,
  simp only [pratt_predicate_iff, thing0, forall_eq_or_imp, forall_eq],
  simp [thing3, thing4, thing5, thing6, thing7, thing8]
end

lemma thing2' : my_pow_mod 7 18446744069414584320 18446744069414584321 = 1 := by norm_num

#exit










lemma thing : prime 1000000007 :=
begin
  refine pratt_rule_2' 5 (by norm_num) (by norm_num) _,
  refine pratt_rule_1' 2 500000003 prime_two (by norm_num) (by norm_num) _,
  refine pratt_rule_1' 500000003 1 _ (by norm_num) (by norm_num) (pratt_axiom _ _),
  refine pratt_rule_2' 2 (by norm_num) (by norm_num) _,
  refine pratt_rule_1' 2 250000001 prime_two (by norm_num) (by norm_num) _,
  refine pratt_rule_1' 41 6097561 (by norm_num) (by norm_num) (by norm_num) _,
  refine pratt_rule_1' 41 148721 (by norm_num) (by norm_num) (by norm_num) _,
  refine pratt_rule_1' 148721 1 (by norm_num) (by norm_num) (by norm_num) (pratt_axiom _ _),
    -- can quickly prove 148721 is prime by trial division
end

end arithmetic_function
end nat
