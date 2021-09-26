/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/

import data.nat.upto
import data.stream.basic
import data.pfun

/-!
# Fixed point

This module defines a generic `fix` operator for defining recursive
computations that are not necessarily well-founded or productive.
An instance is defined for `part`.

## Main definition

 * class `has_fix`
 * `part.fix`
-/

universes u v

open_locale classical
variables {α : Type*} {β : α → Type*}

/-- `has_fix α` gives us a way to calculate the fixed point
of function of type `α → α`. -/
class has_fix (α : Type*) :=
(fix : (α → α) → α)

namespace part

open part nat nat.upto

section basic

variables (f : (Π a, part $ β a) → (Π a, part $ β a))

/-- A series of successive, finite approximation of the fixed point of `f`, defined by
`approx f n = f^[n] ⊥`. The limit of this chain is the fixed point of `f`. -/
def fix.approx : stream $ Π a, part $ β a
| 0 := ⊥
| (nat.succ i) := f (fix.approx i)

/-- loop body for finding the fixed point of `f` -/
def fix_aux {p : ℕ → Prop} (i : nat.upto p)
  (g : Π j : nat.upto p, i < j → Π a, part $ β a) : Π a, part $ β a :=
f $ λ x : α,
assert (¬p (i.val)) $ λ h : ¬ p (i.val),
g (i.succ h) (nat.lt_succ_self _) x

/-- The least fixed point of `f`.

If `f` is a continuous function (according to complete partial orders),
it satisfies the equations:

  1. `fix f = f (fix f)`          (is a fixed point)
  2. `∀ X, f X ≤ X → fix f ≤ X`   (least fixed point)
-/
protected def fix (x : α) : part $ β x :=
part.assert (∃ i, (fix.approx f i x).dom) $ λ h,
well_founded.fix.{1} (nat.upto.wf h) (fix_aux f) nat.upto.zero x

protected lemma fix_def {x : α} (h' : ∃ i, (fix.approx f i x).dom) :
  part.fix f x = fix.approx f (nat.succ $ nat.find h') x :=
begin
  let p := λ (i : ℕ), (fix.approx f i x).dom,
  have : p (nat.find h') := nat.find_spec h',
  generalize hk : nat.find h' = k,
  replace hk : nat.find h' = k + (@upto.zero p).val := hk,
  rw hk at this,
  revert hk,
  dsimp [part.fix], rw assert_pos h', revert this,
  generalize : upto.zero = z, intros,
  suffices : ∀ x',
    well_founded.fix (fix._proof_1 f x h') (fix_aux f) z x' = fix.approx f (succ k) x',
    from this _,
  induction k generalizing z; intro,
  { rw [fix.approx,well_founded.fix_eq,fix_aux],
    congr, ext : 1, rw assert_neg, refl,
    rw nat.zero_add at this,
    simpa only [not_not, subtype.val_eq_coe] },
  { rw [fix.approx,well_founded.fix_eq,fix_aux],
    congr, ext : 1,
    have hh : ¬(fix.approx f (z.val) x).dom,
    { apply nat.find_min h',
      rw [hk,nat.succ_add,← nat.add_succ],
      apply nat.lt_of_succ_le,
      apply nat.le_add_left },
    rw succ_add_eq_succ_add at this hk,
    rw [assert_pos hh, k_ih (upto.succ z hh) this hk] }
end

lemma fix_def' {x : α} (h' : ¬ ∃ i, (fix.approx f i x).dom) :
  part.fix f x = none :=
by dsimp [part.fix]; rw assert_neg h'

end basic

end part

namespace part

instance : has_fix (part α) :=
⟨λ f, part.fix (λ x u, f (x u)) ()⟩

end part

open sigma

namespace pi

instance part.has_fix {β} : has_fix (α → part β) := ⟨part.fix⟩

end pi
