/-
Copyright (c) 2019 Jesse Michael Han. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Jesse Michael Han

Tests for `finish using [...]`
-/

import tactic.finish
import algebra.order.ring

section list_rev
open list
variable {α : Type*}

def append1 (a : α) : list α → list α
| nil      := [a]
| (b :: l) := b :: (append1 l)

def rev : list α → list α
| nil := nil
| (a :: l) := append1 a (rev l)

lemma hd_rev (a : α) (l : list α) :
  a :: rev l =  rev (append1 a l) :=
begin
  induction l with l_hd l_tl ih, refl,
  -- finish -- fails
  -- finish[rev, append1] -- fails
  -- finish[rev, append1, ih] -- fails
  -- finish[rev, append1, ih.symm] -- times out
  finish using [rev, append1]
end

end list_rev

section barber
variables (man : Type) (barber : man)
variable  (shaves : man → man → Prop)

example (h : ∀ x : man, shaves barber x ↔ ¬ shaves x x) : false :=
by finish using [h barber]

end barber

constant real : Type
@[instance] constant orreal : ordered_ring real

-- TODO(Mario): suspicious fix
@[irreducible] noncomputable instance : has_lt real := by apply_instance
constants (log exp : real → real)
constant  log_exp_eq : ∀ x, log (exp x) = x
constant  exp_log_eq : ∀ {x}, x > 0 → exp (log x) = x
constant  exp_pos    : ∀ x, exp x > 0
constant  exp_add    : ∀ x y, exp (x + y) = exp x * exp y

theorem log_mul' {x y : real} (hx : x > 0) (hy : y > 0) :
  log (x * y) = log x + log y :=
by finish using [log_exp_eq, exp_log_eq, exp_add]
