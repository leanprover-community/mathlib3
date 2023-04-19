/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
import data.rat.init
import algebra.ring.defs

/-!
# Division (semi)rings and (semi)fields

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file introduces fields and division rings (also known as skewfields) and proves some basic
statements about them. For a more extensive theory of fields, see the `field_theory` folder.

## Main definitions

* `division_semiring`: Nontrivial semiring with multiplicative inverses for nonzero elements.
* `division_ring`: : Nontrivial ring with multiplicative inverses for nonzero elements.
* `semifield`: Commutative division semiring.
* `field`: Commutative division ring.
* `is_field`: Predicate on a (semi)ring that it is a (semi)field, i.e. that the multiplication is
  commutative, that it has more than one element and that all non-zero elements have a
  multiplicative inverse. In contrast to `field`, which contains the data of a function associating
  to an element of the field its multiplicative inverse, this predicate only assumes the existence
  and can therefore more easily be used to e.g. transfer along ring isomorphisms.

## Implementation details

By convention `0⁻¹ = 0` in a field or division ring. This is due to the fact that working with total
functions has the advantage of not constantly having to check that `x ≠ 0` when writing `x⁻¹`. With
this convention in place, some statements like `(a + b) * c⁻¹ = a * c⁻¹ + b * c⁻¹` still remain
true, while others like the defining property `a * a⁻¹ = 1` need the assumption `a ≠ 0`. If you are
a beginner in using Lean and are confused by that, you can read more about why this convention is
taken in Kevin Buzzard's
[blogpost](https://xenaproject.wordpress.com/2020/07/05/division-by-zero-in-type-theory-a-faq/)

A division ring or field is an example of a `group_with_zero`. If you cannot find
a division ring / field lemma that does not involve `+`, you can try looking for
a `group_with_zero` lemma instead.

## Tags

field, division ring, skew field, skew-field, skewfield
-/

open function set

set_option old_structure_cmd true

universe u
variables {α β K : Type*}

/-- The default definition of the coercion `(↑(a : ℚ) : K)` for a division ring `K`
is defined as `(a / b : K) = (a : K) * (b : K)⁻¹`.
Use `coe` instead of `rat.cast_rec` for better definitional behaviour.
-/
def rat.cast_rec [has_lift_t ℕ K] [has_lift_t ℤ K] [has_mul K] [has_inv K] : ℚ → K
| ⟨a, b, _, _⟩ := ↑a * (↑b)⁻¹

/--
Type class for the canonical homomorphism `ℚ → K`.
-/
@[protect_proj]
class has_rat_cast (K : Type u) :=
(rat_cast : ℚ → K)

/-- The default definition of the scalar multiplication `(a : ℚ) • (x : K)` for a division ring `K`
is given by `a • x = (↑ a) * x`.
Use `(a : ℚ) • (x : K)` instead of `qsmul_rec` for better definitional behaviour.
-/
def qsmul_rec (coe : ℚ → K) [has_mul K] (a : ℚ) (x : K) : K :=
coe a * x

/-- A `division_semiring` is a `semiring` with multiplicative inverses for nonzero elements. -/
@[protect_proj, ancestor semiring group_with_zero]
class division_semiring (α : Type*) extends semiring α, group_with_zero α

/-- A `division_ring` is a `ring` with multiplicative inverses for nonzero elements.

An instance of `division_ring K` includes maps `rat_cast : ℚ → K` and `qsmul : ℚ → K → K`.
If the division ring has positive characteristic p, we define `rat_cast (1 / p) = 1 / 0 = 0`
for consistency with our division by zero convention.
The fields `rat_cast` and `qsmul` are needed to implement the
`algebra_rat [division_ring K] : algebra ℚ K` instance, since we need to control the specific
definitions for some special cases of `K` (in particular `K = ℚ` itself).
See also Note [forgetful inheritance].
-/
@[protect_proj, ancestor ring div_inv_monoid nontrivial]
class division_ring (K : Type u) extends ring K, div_inv_monoid K, nontrivial K, has_rat_cast K :=
(mul_inv_cancel : ∀ {a : K}, a ≠ 0 → a * a⁻¹ = 1)
(inv_zero : (0 : K)⁻¹ = 0)
(rat_cast := rat.cast_rec)
(rat_cast_mk : ∀ (a : ℤ) (b : ℕ) h1 h2, rat_cast ⟨a, b, h1, h2⟩ = a * b⁻¹ . try_refl_tac)
(qsmul : ℚ → K → K := qsmul_rec rat_cast)
(qsmul_eq_mul' : ∀ (a : ℚ) (x : K), qsmul a x = rat_cast a * x . try_refl_tac)

@[priority 100] -- see Note [lower instance priority]
instance division_ring.to_division_semiring [division_ring α] : division_semiring α :=
{ ..‹division_ring α›, ..(infer_instance : semiring α) }

/-- A `semifield` is a `comm_semiring` with multiplicative inverses for nonzero elements. -/
@[protect_proj, ancestor comm_semiring division_semiring comm_group_with_zero]
class semifield (α : Type*) extends comm_semiring α, division_semiring α, comm_group_with_zero α

/-- A `field` is a `comm_ring` with multiplicative inverses for nonzero elements.

An instance of `field K` includes maps `of_rat : ℚ → K` and `qsmul : ℚ → K → K`.
If the field has positive characteristic p, we define `of_rat (1 / p) = 1 / 0 = 0`
for consistency with our division by zero convention.
The fields `of_rat` and `qsmul are needed to implement the
`algebra_rat [division_ring K] : algebra ℚ K` instance, since we need to control the specific
definitions for some special cases of `K` (in particular `K = ℚ` itself).
See also Note [forgetful inheritance].
-/
@[protect_proj, ancestor comm_ring div_inv_monoid nontrivial]
class field (K : Type u) extends comm_ring K, division_ring K

section division_ring
variables [division_ring K] {a b : K}

namespace rat

/-- Construct the canonical injection from `ℚ` into an arbitrary
  division ring. If the field has positive characteristic `p`,
  we define `1 / p = 1 / 0 = 0` for consistency with our
  division by zero convention. -/
-- see Note [coercion into rings]
@[priority 900] instance cast_coe {K : Type*} [has_rat_cast K] : has_coe_t ℚ K :=
⟨has_rat_cast.rat_cast⟩

theorem cast_mk' (a b h1 h2) : ((⟨a, b, h1, h2⟩ : ℚ) : K) = a * b⁻¹ :=
division_ring.rat_cast_mk _ _ _ _

theorem cast_def : ∀ (r : ℚ), (r : K) = r.num / r.denom
| ⟨a, b, h1, h2⟩ := (cast_mk' _ _ _ _).trans (div_eq_mul_inv _ _).symm

@[priority 100]
instance smul_division_ring : has_smul ℚ K :=
⟨division_ring.qsmul⟩

lemma smul_def (a : ℚ) (x : K) : a • x = ↑a * x := division_ring.qsmul_eq_mul' a x

end rat

end division_ring

section field

variable [field K]

@[priority 100] -- see Note [lower instance priority]
instance field.to_semifield : semifield K :=
{ .. ‹field K›, .. (infer_instance : semiring K) }

end field

section is_field

/-- A predicate to express that a (semi)ring is a (semi)field.

This is mainly useful because such a predicate does not contain data,
and can therefore be easily transported along ring isomorphisms.
Additionaly, this is useful when trying to prove that
a particular ring structure extends to a (semi)field. -/
structure is_field (R : Type u) [semiring R] : Prop :=
(exists_pair_ne : ∃ (x y : R), x ≠ y)
(mul_comm : ∀ (x y : R), x * y = y * x)
(mul_inv_cancel : ∀ {a : R}, a ≠ 0 → ∃ b, a * b = 1)

/-- Transferring from `semifield` to `is_field`. -/
lemma semifield.to_is_field (R : Type u) [semifield R] : is_field R :=
{ mul_inv_cancel := λ a ha, ⟨a⁻¹, mul_inv_cancel ha⟩,
  ..‹semifield R› }

/-- Transferring from `field` to `is_field`. -/
lemma field.to_is_field (R : Type u) [field R] : is_field R := semifield.to_is_field _

@[simp] lemma is_field.nontrivial {R : Type u} [semiring R] (h : is_field R) : nontrivial R :=
⟨h.exists_pair_ne⟩

@[simp] lemma not_is_field_of_subsingleton (R : Type u) [semiring R] [subsingleton R] :
  ¬is_field R :=
λ h, let ⟨x, y, h⟩ := h.exists_pair_ne in h (subsingleton.elim _ _)

open_locale classical

/-- Transferring from `is_field` to `semifield`. -/
noncomputable def is_field.to_semifield {R : Type u} [semiring R] (h : is_field R) : semifield R :=
{ inv := λ a, if ha : a = 0 then 0 else classical.some (is_field.mul_inv_cancel h ha),
  inv_zero := dif_pos rfl,
  mul_inv_cancel := λ a ha,
    begin
      convert classical.some_spec (is_field.mul_inv_cancel h ha),
      exact dif_neg ha
    end,
  .. ‹semiring R›, ..h }

/-- Transferring from `is_field` to `field`. -/
noncomputable def is_field.to_field {R : Type u} [ring R] (h : is_field R) : field R :=
{ .. ‹ring R›, ..is_field.to_semifield h }

/-- For each field, and for each nonzero element of said field, there is a unique inverse.
Since `is_field` doesn't remember the data of an `inv` function and as such,
a lemma that there is a unique inverse could be useful.
-/
lemma uniq_inv_of_is_field (R : Type u) [ring R] (hf : is_field R) :
  ∀ (x : R), x ≠ 0 → ∃! (y : R), x * y = 1 :=
begin
  intros x hx,
  apply exists_unique_of_exists_of_unique,
  { exact hf.mul_inv_cancel hx },
  { intros y z hxy hxz,
    calc y = y * (x * z) : by rw [hxz, mul_one]
       ... = (x * y) * z : by rw [← mul_assoc, hf.mul_comm y x]
       ... = z           : by rw [hxy, one_mul] }
end

end is_field
