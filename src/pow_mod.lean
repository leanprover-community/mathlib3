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

lemma my_pow_mod_aux_bit0 (a b c n m a2 ra2 : ℕ)
  (ha2 : a * a = a2) (hra2 : a2 % n = ra2) (hm : my_pow_mod_aux ra2 b c n = m) :
  my_pow_mod_aux a (bit0 b) c n = m :=
by { substs ra2 a2, rwa [my_pow_mod_aux, pow_bit0', mul_mod, pow_mod, ←mul_mod] }

lemma my_pow_mod_aux_bit1 (a b c n m ra2 a2 rac ac : ℕ)
  (ha2 : a * a = a2) (hra2 : a2 % n = ra2)
  (hac : a * c = ac) (hrac : ac % n = rac)
  (hm : my_pow_mod_aux ra2 b rac n = m) :
  my_pow_mod_aux a (bit1 b) c n = m :=
begin
  substs ra2 a2 rac ac,
  rwa [my_pow_mod_aux, pow_bit1', mul_assoc, mul_mod, pow_mod, ←mod_mod (a * c), ←mul_mod]
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
      (ic, ra2, hra2) ← prove_div_mod ic a2 n tt,
      (ic, m, hm) ← prove_pow_mod_aux ic ra2 b c n,
      q ← mk_app ``my_pow_mod_aux_bit0 [a, b, c, n, m, a2, ra2, ha2, hra2, hm],
      return (ic, m, q)
  | bit1 b := do
      (ic, a2, ha2) ← prove_mul_nat ic a a,
      (ic, ac, hac) ← prove_mul_nat ic a c,
      (ic, ra2, hra2) ← prove_div_mod ic a2 n tt,
      (ic, rac, hrac) ← prove_div_mod ic ac n tt,
      (ic, m, hm) ← prove_pow_mod_aux ic ra2 b rac n,
      q ← mk_app ``my_pow_mod_aux_bit1 [a, b, c, n, m, ra2, a2, rac, ac, ha2, hra2, hac, hrac, hm],
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

def pratt_predicate (p a x : ℕ) : Prop := ∀ q ∈ x.factors, a ^ ((p - 1) / q) % p ≠ 1

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

-- these rules aren't great for integration with norm_num for now, but they're nice for testing

set_option profiler true

lemma small_test : prime 199999 :=
begin
  refine pratt_rule_2' 3 (by norm_num) (by norm_num) _,
  refine pratt_rule_1' 2 99999 prime_two (by norm_num) (by norm_num) _,
  refine pratt_rule_1' 3 33333 prime_three (by norm_num) (by norm_num) _,
  refine pratt_rule_1' 3 11111 prime_three (by norm_num) (by norm_num) _,
  refine pratt_rule_1' 41 271 (by norm_num) (by norm_num) (by norm_num) _,
  refine pratt_rule_1' 271 1 _ (by norm_num) (by norm_num) (pratt_axiom _ _),
  norm_num
end
#eval min_fac 271

-- lemma smallish_test : prime 1000000007 :=
-- begin
--   refine pratt_rule_2' 5 (by norm_num) (by norm_num) _,
--   refine pratt_rule_1' 2 500000003 prime_two (by norm_num) (by norm_num) _,
--   refine pratt_rule_1' 500000003 1 _ (by norm_num) (by norm_num) (pratt_axiom _ _),
--   refine pratt_rule_2' 2 (by norm_num) (by norm_num) _,
--   refine pratt_rule_1' 2 250000001 prime_two (by norm_num) (by norm_num) _,
--   refine pratt_rule_1' 41 6097561 (by norm_num) (by norm_num) (by norm_num) _,
--   refine pratt_rule_1' 41 148721 (by norm_num) (by norm_num) (by norm_num) _,
--   refine pratt_rule_1' 148721 1 (by norm_num) (by norm_num) (by norm_num) (pratt_axiom _ _),
--     -- can quickly prove 148721 is prime by trial division instead of using pratt again
-- end

-- lemma bigger_test : prime 23509285402367 :=
-- begin
--   refine pratt_rule_2' 5 (by norm_num1) (by norm_num1 /- goal 1 -/) _,
--   refine pratt_rule_1' 2 11754642701183 (by norm_num1) (by norm_num1) (by norm_num1) _,
--   refine pratt_rule_1' 11754642701183 1 _ (by norm_num1) (by norm_num1) (pratt_axiom _ _),
--   refine pratt_rule_2' 5 (by norm_num1) _ _,
--   -- { norm_num1 },
--   -- timesout if goal 1 and 2 are here
--   sorry,
-- end

-- example : my_pow_mod 5 23509285402366 23509285402367 = 1 :=
-- begin
--   norm_num1, -- succeeds
-- end

-- example : my_pow_mod 5 (11754642701183 - 1) 11754642701183 = 1 :=
-- begin
--   norm_num1, -- succeeds
-- end

-- lemma it :
--   my_pow_mod 5 (23509285402367 - 1) 23509285402367 = 1 ∧
--   my_pow_mod 5 ((23509285402367 - 1) / 2) 23509285402367 ≠ 1 ∧
--   my_pow_mod 5 ((23509285402367 - 1) / 11754642701183) 23509285402367 ≠ 1 ∧
--   my_pow_mod 5 (11754642701183 - 1) 11754642701183 = 1 ∧
--   true :=
-- begin
--   split,
--   { show_term {norm_num1} },
--   sorry,
--   -- split,
--   -- { norm_num1 },
--   -- split,
--   -- { norm_num },
--   -- split,
--   -- { show_term { norm_num } },
--   -- sorry, -- trivial,
--     -- last goal is `true`
--     -- but if I sorry this goal, the whole lemma says deterministic timeout
-- end

-- example : 7 ^ 1269505852555753484910 % 1269505852555753484911 = 1 :=
-- begin
--   norm_num,
-- end

-- lemma test : 7 ^ 1269505852555753484910 % 1269505852555753484911 = 1 :=
-- begin
--   refine my_pow_mod_eq _ _ _ _ _,
--   refine my_pow_mod_aux_bit0 _ _ _ _ _ 49 49 0 0 (by norm_num1) (by norm_num1) (by norm_num1) _,
--   refine my_pow_mod_aux_bit1 _ _ _ _ _ 0 0 2401 2401 0 0 49 49 (by norm_num1) (by norm_num1)
--     (by norm_num1) (by norm_num1) (by norm_num1) (by norm_num1) _,
--   refine my_pow_mod_aux_bit1 _ _ _ _ _ 0 0 5764801 5764801 0 0 117649 117649 (by norm_num1)
--     (by norm_num1) (by norm_num1) (by norm_num1) (by norm_num1) (by norm_num1) _,
--   refine my_pow_mod_aux_bit1 _ _ _ _ _ 0 0 33232930569601 33232930569601 0 0 678223072849
--     678223072849 (by norm_num1) (by norm_num1) (by norm_num1) (by norm_num1) (by norm_num1)
--     (by norm_num1) _,
--   refine my_pow_mod_aux_bit0 _ _ _ _ _ 1104427674243920646305299201 745719402010051216175 869966
--     1104426928524518636254083026 (by norm_num1) (by norm_num1) (by norm_num1) _,
--   refine my_pow_mod_aux_bit1 _ _ _ _ _ 438042428409998988884
--     556097426534228377830055119958269350729324 833361688327230901301
--     556097426534228377830888481646596581630625 398394464504 505764104313643389425349689099144
--     732293592728383033431 505764104314375683018078072132575 (by norm_num1) (by norm_num1)
--     (by norm_num1) (by norm_num1) (by norm_num1) (by norm_num1) _,
--   refine my_pow_mod_aux_bit1 _ _ _ _ _ 547056716732318032581
--     694491703571612736654661674958057989885291 343899984206813607310
--     694491703571612736655005574942264803492601 480710997557640317587
--     610265424787338902615536835216852052429757 537956025130491963974
--     610265424787338902616074791241982544393731 (by norm_num1) (by norm_num1) (by norm_num1)
--     (by norm_num1) (by norm_num1) (by norm_num1) _,
-- end


-- lemma thing : prime 23509285402469 :=
-- begin
--   refine pratt_rule_2' 2 (by norm_num1) (by norm_num1) _,
--   refine pratt_rule_1' 2 11754642701234 prime_two (by norm_num1) (by norm_num1) _,
--   refine pratt_rule_1' 2 5877321350617 prime_two (by norm_num1) (by norm_num1) _,
--   refine pratt_rule_1' 127 46278120871 (by norm_num1) (by norm_num1) _ _,
--   -- { sorry },

-- end

-- #exit

-- end arithmetic_function
end nat
