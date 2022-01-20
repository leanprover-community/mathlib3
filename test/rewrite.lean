/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import tactic.rewrite
import data.nat.basic

open tactic
example : ∀ x y z a b c : ℕ, true :=
begin
 intros,
 have : x + (y + z) = 3 + y, admit,
 have : a + (b + x) + y + (z + b + c) ≤ 0,
 (do this ← get_local `this,
     tgt ← to_expr ```(a + (b + x) + y + (z + b + c)),
     assoc ← mk_mapp ``add_monoid.add_assoc [`(ℕ),none],
     (l,p) ← assoc_rewrite_intl assoc this tgt,
     note `h none p  ),
 erw h,
 guard_target a + b + 3 + y + b + c ≤ 0,
 admit,
 trivial
end

example : ∀ x y z a b c : ℕ, true :=
begin
 intros,
 have : ∀ y, x + (y + z) = 3 + y, admit,
 have : a + (b + x) + y + (z + b + c) ≤ 0,
 (do this ← get_local `this,
     tgt ← to_expr ```(a + (b + x) + y + (z + b + c)),
     assoc_rewrite_target this ),
 guard_target a + b + 3 + y + b + c ≤ 0,
 admit,
 trivial
end

variables x y z a b c : ℕ
variables h₀ : ∀ (y : ℕ), x + (y + z) = 3 + y
variables h₁ : a + (b + x) + y + (z + b + a) ≤ 0
variables h₂ : y + b + c = y + b + a
include h₀ h₁ h₂
example : a + (b + x) + y + (z + b + c) ≤ 0 :=
by { assoc_rw [h₀,h₂] at *,
     guard_hyp _inst : is_associative ℕ has_add.add,
       -- keep a local instance of is_associative to cache
       -- type class queries
     exact h₁ }
