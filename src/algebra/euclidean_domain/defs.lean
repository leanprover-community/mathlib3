/-
Copyright (c) 2018 Louis Carlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis Carlin, Mario Carneiro
-/
import logic.nontrivial
import algebra.divisibility.basic
import algebra.group.basic
import algebra.ring.defs

/-!
# Euclidean domains

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file introduces Euclidean domains and provides the extended Euclidean algorithm. To be precise,
a slightly more general version is provided which is sometimes called a transfinite Euclidean domain
and differs in the fact that the degree function need not take values in `ℕ` but can take values in
any well-ordered set. Transfinite Euclidean domains were introduced by Motzkin and examples which
don't satisfy the classical notion were provided independently by Hiblot and Nagata.

## Main definitions

* `euclidean_domain`: Defines Euclidean domain with functions `quotient` and `remainder`. Instances
  of `has_div` and `has_mod` are provided, so that one can write `a = b * (a / b) + a % b`.
* `gcd`: defines the greatest common divisors of two elements of a Euclidean domain.
* `xgcd`: given two elements `a b : R`, `xgcd a b` defines the pair `(x, y)` such that
  `x * a + y * b = gcd a b`.
* `lcm`: defines the lowest common multiple of two elements `a` and `b` of a Euclidean domain as
  `a * b / (gcd a b)`

## Main statements

See `algebra.euclidean_domain.basic` for most of the theorems about Eucliean domains,
including Bézout's lemma.

See `algebra.euclidean_domain.instances` for that facts that `ℤ` is a Euclidean domain,
as is any field.

## Notation

`≺` denotes the well founded relation on the Euclidean domain, e.g. in the example of the polynomial
ring over a field, `p ≺ q` for polynomials `p` and `q` if and only if the degree of `p` is less than
the degree of `q`.

## Implementation details

Instead of working with a valuation, `euclidean_domain` is implemented with the existence of a well
founded relation `r` on the integral domain `R`, which in the example of `ℤ` would correspond to
setting `i ≺ j` for integers `i` and `j` if the absolute value of `i` is smaller than the absolute
value of `j`.

## References

* [Th. Motzkin, *The Euclidean algorithm*][MR32592]
* [J.-J. Hiblot, *Des anneaux euclidiens dont le plus petit algorithme n'est pas à valeurs finies*]
  [MR399081]
* [M. Nagata, *On Euclid algorithm*][MR541021]


## Tags

Euclidean domain, transfinite Euclidean domain, Bézout's lemma
-/

universe u

/-- A `euclidean_domain` is an non-trivial commutative ring with a division and a remainder,
  satisfying `b * (a / b) + a % b = a`.
  The definition of a euclidean domain usually includes a valuation function `R → ℕ`.
  This definition is slightly generalised to include a well founded relation
  `r` with the property that `r (a % b) b`, instead of a valuation.  -/
@[protect_proj without mul_left_not_lt r_well_founded]
class euclidean_domain (R : Type u) extends comm_ring R, nontrivial R :=
(quotient : R → R → R)
(quotient_zero : ∀ a, quotient a 0 = 0)
(remainder : R → R → R)
(quotient_mul_add_remainder_eq : ∀ a b, b * quotient a b + remainder a b = a)
(r : R → R → Prop)
(r_well_founded : well_founded r)
(remainder_lt : ∀ a {b}, b ≠ 0 → r (remainder a b) b)
(mul_left_not_lt : ∀ a {b}, b ≠ 0 → ¬r (a * b) a)

namespace euclidean_domain
variable {R : Type u}
variables [euclidean_domain R]

local infix ` ≺ `:50 := euclidean_domain.r

@[priority 70] -- see Note [lower instance priority]
instance : has_div R := ⟨euclidean_domain.quotient⟩

@[priority 70] -- see Note [lower instance priority]
instance : has_mod R := ⟨euclidean_domain.remainder⟩

theorem div_add_mod (a b : R) : b * (a / b) + a % b = a :=
euclidean_domain.quotient_mul_add_remainder_eq _ _

lemma mod_add_div (a b : R) : a % b + b * (a / b) = a :=
(add_comm _ _).trans (div_add_mod _ _)

lemma mod_add_div' (m k : R) : m % k + (m / k) * k = m :=
by { rw mul_comm, exact mod_add_div _ _ }

lemma div_add_mod' (m k : R) : (m / k) * k + m % k = m :=
by { rw mul_comm, exact div_add_mod _ _ }

lemma mod_eq_sub_mul_div {R : Type*} [euclidean_domain R] (a b : R) :
  a % b = a - b * (a / b) :=
calc a % b = b * (a / b) + a % b - b * (a / b) : (add_sub_cancel' _ _).symm
... = a - b * (a / b) : by rw div_add_mod

theorem mod_lt : ∀ a {b : R}, b ≠ 0 → (a % b) ≺ b :=
euclidean_domain.remainder_lt

theorem mul_right_not_lt {a : R} (b) (h : a ≠ 0) : ¬(a * b) ≺ b :=
by { rw mul_comm, exact mul_left_not_lt b h }

@[simp] lemma mod_zero (a : R) : a % 0 = a :=
by simpa only [zero_mul, zero_add] using div_add_mod a 0

lemma lt_one (a : R) : a ≺ (1:R) → a = 0 :=
by { haveI := classical.dec, exact
  not_imp_not.1 (λ h, by simpa only [one_mul] using mul_left_not_lt 1 h) }

lemma val_dvd_le : ∀ a b : R, b ∣ a → a ≠ 0 → ¬a ≺ b
| _ b ⟨d, rfl⟩ ha := mul_left_not_lt b (mt (by { rintro rfl, exact mul_zero _ }) ha)

@[simp, priority 900] lemma div_zero (a : R) : a / 0 = 0 :=
euclidean_domain.quotient_zero a

section
open_locale classical

@[elab_as_eliminator]
theorem gcd.induction {P : R → R → Prop} : ∀ a b : R,
  (∀ x, P 0 x) →
  (∀ a b, a ≠ 0 → P (b % a) a → P a b) →
  P a b
| a := λ b H0 H1, if a0 : a = 0 then a0.symm ▸ H0 _ else
  have h:_ := mod_lt b a0,
  H1 _ _ a0 (gcd.induction (b%a) a H0 H1)
using_well_founded {dec_tac := tactic.assumption,
  rel_tac := λ _ _, `[exact ⟨_, r_well_founded⟩]}

end

section gcd
variable [decidable_eq R]

/-- `gcd a b` is a (non-unique) element such that `gcd a b ∣ a` `gcd a b ∣ b`, and for
  any element `c` such that `c ∣ a` and `c ∣ b`, then `c ∣ gcd a b` -/
def gcd : R → R → R
| a := λ b, if a0 : a = 0 then b else
  have h:_ := mod_lt b a0,
  gcd (b%a) a
using_well_founded {dec_tac := tactic.assumption,
  rel_tac := λ _ _, `[exact ⟨_, r_well_founded⟩]}

@[simp] theorem gcd_zero_left (a : R) : gcd 0 a = a :=
by { rw gcd, exact if_pos rfl }

/--
An implementation of the extended GCD algorithm.
At each step we are computing a triple `(r, s, t)`, where `r` is the next value of the GCD
algorithm, to compute the greatest common divisor of the input (say `x` and `y`), and `s` and `t`
are the coefficients in front of `x` and `y` to obtain `r` (i.e. `r = s * x + t * y`).
The function `xgcd_aux` takes in two triples, and from these recursively computes the next triple:
```
xgcd_aux (r, s, t) (r', s', t') = xgcd_aux (r' % r, s' - (r' / r) * s, t' - (r' / r) * t) (r, s, t)
```
-/
def xgcd_aux : R → R → R → R → R → R → R × R × R
| r := λ s t r' s' t',
if hr : r = 0 then (r', s', t')
  else
  have r' % r ≺ r, from mod_lt _ hr,
  let q := r' / r in xgcd_aux (r' % r) (s' - q * s) (t' - q * t) r s t
using_well_founded {dec_tac := tactic.assumption,
  rel_tac := λ _ _, `[exact ⟨_, r_well_founded⟩]}

@[simp] theorem xgcd_zero_left {s t r' s' t' : R} : xgcd_aux 0 s t r' s' t' = (r', s', t') :=
by { unfold xgcd_aux, exact if_pos rfl }

theorem xgcd_aux_rec {r s t r' s' t' : R} (h : r ≠ 0) :
  xgcd_aux r s t r' s' t' = xgcd_aux (r' % r) (s' - (r' / r) * s) (t' - (r' / r) * t) r s t :=
by { conv {to_lhs, rw [xgcd_aux]}, exact if_neg h}

/-- Use the extended GCD algorithm to generate the `a` and `b` values
  satisfying `gcd x y = x * a + y * b`. -/
def xgcd (x y : R) : R × R := (xgcd_aux x 1 0 y 0 1).2

/-- The extended GCD `a` value in the equation `gcd x y = x * a + y * b`. -/
def gcd_a (x y : R) : R := (xgcd x y).1

/-- The extended GCD `b` value in the equation `gcd x y = x * a + y * b`. -/
def gcd_b (x y : R) : R := (xgcd x y).2

@[simp] theorem gcd_a_zero_left {s : R} : gcd_a 0 s = 0 :=
by { unfold gcd_a, rw [xgcd, xgcd_zero_left] }

@[simp] theorem gcd_b_zero_left {s : R} : gcd_b 0 s = 1 :=
by { unfold gcd_b, rw [xgcd, xgcd_zero_left] }

theorem xgcd_val (x y : R) : xgcd x y = (gcd_a x y, gcd_b x y) :=
prod.mk.eta.symm

end gcd

section lcm
variables [decidable_eq R]

/-- `lcm a b` is a (non-unique) element such that `a ∣ lcm a b` `b ∣ lcm a b`, and for
  any element `c` such that `a ∣ c` and `b ∣ c`, then `lcm a b ∣ c` -/
def lcm (x y : R) : R :=
x * y / gcd x y

end lcm

end euclidean_domain
