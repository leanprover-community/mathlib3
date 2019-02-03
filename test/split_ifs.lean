import tactic.split_ifs

example (p : Prop) [decidable p] (h : (if p then 1 else 2) > 3) : false :=
by split_ifs at h; repeat {cases h with h h}

example (p : Prop) [decidable p] (x : ℕ) (h : (if p then 1 else 2) > x) :
    x < (if ¬p then 1 else 0) + 1 :=
by split_ifs at *; assumption

example (p : Prop) [decidable p] : if if ¬p then p else true then p else ¬p :=
by split_ifs; assumption

example (p q : Prop) [decidable p] [decidable q] :
    if if if p then ¬p else q then p else q then q else ¬p ∨ ¬q :=
by split_ifs; simp *

example : true :=
by success_if_fail { split_ifs }; trivial