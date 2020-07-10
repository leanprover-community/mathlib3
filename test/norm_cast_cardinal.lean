import tactic.norm_cast

constant cardinal : Type
@[instance] constant cardinal.has_zero : has_zero cardinal
@[instance] constant cardinal.has_one : has_one cardinal
@[instance] constant cardinal.has_add : has_add cardinal
constant cardinal.succ : cardinal → cardinal

@[instance] constant cardinal.has_coe_from_nat : has_coe ℕ cardinal

@[norm_cast] axiom coe_zero : ((0 : ℕ) : cardinal) = 0
@[norm_cast] axiom coe_one : ((1 : ℕ) : cardinal) = 1
@[norm_cast] axiom coe_add {a b : ℕ} : ((a + b : ℕ) : cardinal) = a + b
@[norm_cast] lemma coe_bit0 {a : ℕ} : ((bit0 a : ℕ) : cardinal) = bit0 a := coe_add
@[norm_cast] lemma coe_bit1 {a : ℕ} : ((bit1 a : ℕ) : cardinal) = bit1 a :=
by unfold bit1; norm_cast
@[norm_cast, priority 900] axiom coe_succ {n : ℕ} : (n.succ : cardinal) = cardinal.succ n

example : cardinal.succ 0 = 1 := by norm_cast
example : cardinal.succ 1 = 2 := by norm_cast
example : cardinal.succ 2 = 3 := by norm_cast
example : cardinal.succ 3 = 4 := by norm_cast
