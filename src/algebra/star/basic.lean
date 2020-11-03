/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison.
-/
import tactic.apply_fun
import algebra.ordered_ring
import algebra.big_operators.basic

/-!
# star_monoid, star_ring

We introduce the basic algebraic notions of star monoids, and star rings.
Star algebras are introduced in `algebra.algebra.star`.

These are implemented as "mixin" typeclasses, so to summon a star ring (for example)
one needs to write `(R : Type) [ring R] [star_ring R]`.
This avoids difficulties with diamond inheritance.

For now we simply do not introduce notations,
as different users are expected to feel strongly about the relative merits of
`r^*`, `r†`, `rᘁ`, and so on.

Our star rings are actually star semirings, but of course we can prove
`star_neg : star (-r) = - star r` when the underlying semiring is a ring.
-/


universes u v

/--
Notation typeclass (with no default notation!) for an algebraic structure with a star operation.
-/
class has_star (R : Type u) :=
(star : R → R)

variables {R : Type u}

/--
A star operation (e.g. complex conjugate).
-/
def star [has_star R] (r : R) : R := has_star.star r

/--
Typeclass for a star operation with is involutive.
-/
class star_involutive (R : Type u) extends has_star R :=
(star_star : ∀ r : R, star (star r) = r)

@[simp] lemma star_star [star_involutive R] (r : R) : star (star r) = r :=
star_involutive.star_star _

lemma star_injective [star_involutive R] : function.injective (star : R → R) :=
begin
  intros x y h,
  apply_fun star at h,
  simpa using h,
end

/--
A *-monoid is a monoid `R` with an involutive operations `star`
so `star (r * s) = star s * star r`.
-/
class star_monoid (R : Type u) [monoid R] extends star_involutive R :=
(star_mul : ∀ r s : R, star (r * s) = star s * star r)

@[simp] lemma star_mul [monoid R] [star_monoid R] (r s : R) : star (r * s) = star s * star r :=
star_monoid.star_mul r s

@[simp] lemma star_one [monoid R] [star_monoid R] : star (1 : R) = 1 :=
begin
  have w : ∀ r, (star 1 : R) * r = r,
  { intro r, apply star_injective, simp, },
  simpa using w 1,
end

/--
A *-ring `R` is a (semi)ring with an involutive `star` operation which is additive
which makes `R` with its multiplicative structure into a *-monoid
(i.e. `star (r * s) = star s * star r`).
-/
class star_ring (R : Type u) [semiring R] extends star_monoid R :=
(star_zero : star 0 = 0)
(star_add : ∀ r s : R, star (r + s) = star r + star s)

@[simp] lemma star_zero [semiring R] [star_ring R] : star (0 : R) = 0 :=
star_ring.star_zero

@[simp] lemma star_add [semiring R] [star_ring R] (r s : R) : star (r + s) = star r + star s :=
star_ring.star_add r s

section
open_locale big_operators

@[simp] lemma star_sum [semiring R] [star_ring R] {α : Type*} [decidable_eq α]
  (s : finset α) (f : α → R):
  star (∑ x in s, f x) = ∑ x in s, star (f x) :=
begin
  apply finset.induction_on s,
  { simp, },
  { intros a s nm w,
    rw [finset.sum_insert nm, finset.sum_insert nm],
    simp [w], }
end

end

@[simp] lemma star_neg [ring R] [star_ring R] (r : R) : star (-r) = - star r :=
begin
  apply (add_left_inj (star r)).1,
  apply star_injective,
  simp,
end

@[simp] lemma star_sub [ring R] [star_ring R] (r s : R) : star (r - s) = star r - star s :=
by simp [sub_eq_add_neg]

@[simp] lemma star_bit0 [ring R] [star_ring R] (r : R) : star (bit0 r) = bit0 (star r) :=
by simp [bit0]

@[simp] lemma star_bit1 [ring R] [star_ring R] (r : R) : star (bit1 r) = bit1 (star r) :=
by simp [bit1]

/--
Any commutative semiring admits the trivial *-structure.
-/
def star_ring_of_comm {R : Type*} [comm_semiring R] : star_ring R :=
{ star := id,
  star_star := by simp,
  star_mul := by simp [mul_comm],
  star_zero := by simp,
  star_add := by simp, }

section
local attribute [instance] star_ring_of_comm

@[simp] lemma star_id_of_comm {R : Type*} [comm_semiring R] {x : R} : star x = x := rfl

end

