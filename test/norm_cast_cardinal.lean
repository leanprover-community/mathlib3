import tactic.norm_cast

constant cardinal : Type
@[instance] constant cardinal.has_zero : has_zero cardinal
@[instance] constant cardinal.has_one : has_one cardinal
@[instance] constant cardinal.has_add : has_add cardinal
constant cardinal.succ : cardinal → cardinal

@[instance] constant cardinal.has_coe_from_nat : has_coe ℕ cardinal

@[norm_cast] axiom coe_zero : ((0 : ℕ) : cardinal) = 0
@[norm_cast] axiom coe_one : ((1 : ℕ) : cardinal) = 1
@[norm_cast] axiom coe_succ {n : ℕ} : (n.succ : cardinal) = cardinal.succ n

example : cardinal.succ 0 = 1 :=
by norm_cast
