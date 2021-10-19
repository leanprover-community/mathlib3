/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import algebra.group_power.order
import algebra.smul_with_zero

/-!

# Tropical algebraic structures

This file defines algebraic structures of the (min-)tropical numbers, up to the tropical semiring.
Some basic lemmas about conversion from the base type `R` to `tropical R` are provided, as
well as the expected implementations of tropical addition and tropical multiplication.

## Main declarations

* `tropical R`: The type synonym of the tropical interpretation of `R`.
    If `[linear_order R]`, then addition on `R` is via `min`.
* `semiring (tropical R)`: A `linear_ordered_add_comm_monoid_with_top R`
    induces a `semiring (tropical R)`. If one solely has `[linear_ordered_add_comm_monoid R]`,
    then the "tropicalization of `R`" would be `tropical (with_top R)`.

## Implementation notes

The tropical structure relies on `has_top` and `min`. For the max-tropical numbers, use
`order_dual R`.

Inspiration was drawn from the implementation of `additive`/`multiplicative`/`opposite`,
where a type synonym is created with some barebones API, and quickly made irreducible.

Algebraic structures are provided with as few typeclass assumptions as possible, even though
most references rely on `semiring (tropical R)` for building up the whole theory.

## References followed

* https://arxiv.org/pdf/math/0408099.pdf
* https://www.mathenjeans.fr/sites/default/files/sujets/tropical_geometry_-_casagrande.pdf

-/

universes u v
variables (R : Type u)

/-- The tropicalization of a type `R`. -/
def tropical : Type u := R

variables {R}

namespace tropical

/-- Reinterpret `x : R` as an element of `tropical R`.
See `tropical.trop_equiv` for the equivalence.
-/
@[pp_nodot]
def trop : R → tropical R := id
/-- Reinterpret `x : tropical R` as an element of `R`.
See `tropical.trop_equiv` for the equivalence. -/
@[pp_nodot]
def untrop : tropical R → R := id

lemma trop_injective : function.injective (trop : R → tropical R) := λ _ _, id
lemma untrop_injective : function.injective (untrop : tropical R → R) := λ _ _, id

@[simp] lemma trop_inj_iff (x y : R) : trop x = trop y ↔ x = y := iff.rfl
@[simp] lemma untrop_inj_iff (x y : tropical R) : untrop x = untrop y ↔ x = y := iff.rfl

@[simp] lemma trop_untrop (x : tropical R) : trop (untrop x) = x := rfl
@[simp] lemma untrop_trop (x : R) : untrop (trop x) = x := rfl

lemma left_inverse_trop : function.left_inverse (trop : R → tropical R) untrop := trop_untrop
lemma right_inverse_trop : function.right_inverse (trop : R → tropical R) untrop := trop_untrop

attribute [irreducible] tropical

/-- Reinterpret `x : R` as an element of `tropical R`.
See `tropical.trop_order_iso` for the order-preserving equivalence. -/
def trop_equiv : R ≃ tropical R :=
{ to_fun := trop,
  inv_fun := untrop,
  left_inv := untrop_trop,
  right_inv := trop_untrop }

@[simp]
lemma trop_equiv_coe_fn : (trop_equiv : R → tropical R) = trop := rfl
@[simp]
lemma trop_equiv_symm_coe_fn : (trop_equiv.symm : tropical R → R) = untrop := rfl

lemma trop_eq_iff_eq_untrop {x : R} {y} : trop x = y ↔ x = untrop y :=
trop_equiv.apply_eq_iff_eq_symm_apply

lemma untrop_eq_iff_eq_trop {x} {y : R} : untrop x = y ↔ x = trop y :=
trop_equiv.symm.apply_eq_iff_eq_symm_apply

lemma injective_trop : function.injective (trop : R → tropical R) := trop_equiv.injective
lemma injective_untrop : function.injective (untrop : tropical R → R) := trop_equiv.symm.injective
lemma surjective_trop : function.surjective (trop : R → tropical R) := trop_equiv.surjective
lemma surjective_untrop : function.surjective (untrop : tropical R → R) :=
trop_equiv.symm.surjective

instance [inhabited R] : inhabited (tropical R) := ⟨trop (default _)⟩

/-- Recursing on a `x' : tropical R` is the same as recursing on an `x : R` reinterpreted
as a term of `tropical R` via `trop x`. -/
@[simp]
def trop_rec {F : Π (X : tropical R), Sort v} (h : Π X, F (trop X)) : Π X, F X :=
λ X, h (untrop X)

section order

instance [preorder R] : preorder (tropical R) :=
{ le := λ x y, untrop x ≤ untrop y,
  le_refl := λ _, le_refl _,
  le_trans := λ _ _ _ h h', le_trans h h', }

@[simp] lemma untrop_le_iff [preorder R] {x y : tropical R} :
  untrop x ≤ untrop y ↔ x ≤ y := iff.rfl

/-- Reinterpret `x : R` as an element of `tropical R`, preserving the order. -/
def trop_order_iso [preorder R] : R ≃o tropical R :=
{ map_rel_iff' := λ _ _, untrop_le_iff,
  ..trop_equiv }

@[simp]
lemma trop_order_iso_coe_fn [preorder R] : (trop_order_iso : R → tropical R) = trop := rfl
@[simp]
lemma trop_order_iso_symm_coe_fn [preorder R] : (trop_order_iso.symm : tropical R → R) = untrop :=
rfl

instance [partial_order R] : partial_order (tropical R) :=
{ le_antisymm := λ _ _ h h', untrop_injective (le_antisymm h h'),
  ..tropical.preorder }

instance [has_top R] : has_zero (tropical R) := ⟨trop ⊤⟩
instance [has_top R] : has_top (tropical R) := ⟨0⟩

@[simp] lemma untrop_zero [has_top R] : untrop (0 : tropical R) = ⊤ := rfl
@[simp] lemma trop_top [has_top R] : trop (⊤ : R) = 0 := rfl

@[simp] lemma trop_coe_ne_zero (x : R) : trop (x : with_top R) ≠ 0 .
@[simp] lemma zero_ne_trop_coe (x : R) : (0 : tropical (with_top R)) ≠ trop x .

@[simp] lemma le_zero [order_top R] (x : tropical R) : x ≤ 0 := le_top

instance [partial_order R] : order_top (tropical (with_top R)) :=
{ le_top := λ a a' h, option.no_confusion h,
  ..tropical.partial_order,
  ..tropical.has_top }

variable [linear_order R]

/-- Tropical addition is the minimum of two underlying elements of `R`. -/
protected def add (x y : tropical R) : tropical R :=
trop (min (untrop x) (untrop y))

instance : add_comm_semigroup (tropical R) :=
{ add := tropical.add,
  add_assoc := λ _ _ _, untrop_injective (min_assoc _ _ _),
  add_comm := λ _ _, untrop_injective (min_comm _ _) }

instance : linear_order (tropical R) :=
{ le_total := λ a b, le_total (untrop a) (untrop b),
  decidable_le := λ x y, if h : (untrop x) ≤ (untrop y) then is_true h else is_false h,
  ..tropical.partial_order }

@[simp] lemma untrop_add (x y : tropical R) : untrop (x + y) = min (untrop x) (untrop y) := rfl

lemma trop_add_def (x y : tropical R) : x + y = trop (min (untrop x) (untrop y)) := rfl

@[simp] lemma add_eq_left ⦃x y : tropical R⦄ (h : x ≤ y) :
  x + y = x := untrop_injective (by simpa using h)

@[simp] lemma add_eq_right ⦃x y : tropical R⦄ (h : y ≤ x) :
  x + y = y := untrop_injective (by simpa using h)

@[simp] lemma add_self (x : tropical R) : x + x = x := untrop_injective (min_eq_right le_rfl)

@[simp] lemma bit0 (x : tropical R) : bit0 x = x := add_self x

lemma add_eq_iff {x y z : tropical R} :
  x + y = z ↔ x = z ∧ x ≤ y ∨ y = z ∧ y ≤ x :=
by simp [trop_add_def, trop_eq_iff_eq_untrop, min_eq_iff]

@[simp] lemma add_eq_zero_iff {a b : tropical (with_top R)} :
  a + b = 0 ↔ a = 0 ∧ b = 0 :=
begin
  rw add_eq_iff,
  split,
  { rintro (⟨rfl, h⟩|⟨rfl, h⟩),
    { exact ⟨rfl, le_antisymm (le_zero _) h⟩ },
    { exact ⟨le_antisymm (le_zero _) h, rfl⟩ } },
  { rintro ⟨rfl, rfl⟩,
    simp }
end

-- We cannot define `add_comm_monoid` here because there is no class that is solely
-- `[linear_order R] [order_top R]`

end order

section monoid

/-- Tropical multiplication is the addition in the underlying `R`. -/
protected def mul [has_add R] (x y : tropical R) : tropical R := trop (untrop x + untrop y)

instance [has_add R] : has_mul (tropical R) := ⟨tropical.mul⟩

@[simp] lemma untrop_mul [has_add R] (x y : tropical R) :
  untrop (x * y) = untrop x + untrop y := rfl

lemma trop_mul_def [has_add R] (x y : tropical R) :
  x * y = trop (untrop x + untrop y) := rfl

instance [has_zero R] : has_one (tropical R) := ⟨trop 0⟩
instance [has_zero R] : nontrivial (tropical (with_top R)) :=
⟨⟨0, 1, trop_injective.ne with_top.top_ne_coe⟩⟩

instance [has_neg R] : has_inv (tropical R) := ⟨λ x, trop (- untrop x)⟩

@[simp] lemma untrop_inv [has_neg R] (x : tropical R) : untrop x⁻¹ = - untrop x := rfl

instance [has_sub R] : has_div (tropical R) := ⟨λ x y, trop (untrop x - untrop y)⟩

@[simp] lemma untrop_div [has_sub R] (x y : tropical R) :
  untrop (x / y) = untrop x - untrop y := rfl

instance [add_semigroup R] : semigroup (tropical R) :=
{ mul := tropical.mul,
  mul_assoc := λ _ _ _, untrop_injective (add_assoc _ _ _) }

instance [add_comm_semigroup R] : comm_semigroup (tropical R) :=
{ mul_comm := λ _ _, untrop_injective (add_comm _ _),
  ..tropical.semigroup }

instance [add_monoid R] : monoid (tropical R) :=
{ one := trop 0,
  one_mul := λ _, untrop_injective (zero_add _),
  mul_one := λ _, untrop_injective (add_zero _),
  ..tropical.semigroup }

@[simp] lemma untrop_one [add_monoid R] : untrop (1 : tropical R) = 0 := rfl

@[simp] lemma untrop_pow [add_monoid R] (x : tropical R) (n : ℕ) :
  untrop (x ^ n) = n • untrop x :=
begin
  induction n with n IH,
  { simp, },
  { rw [pow_succ, untrop_mul, IH, succ_nsmul] }
end

@[simp] lemma trop_nsmul [add_monoid R] (x : R) (n : ℕ) :
  trop (n • x) = trop x ^ n :=
by simp [trop_eq_iff_eq_untrop]

instance [add_comm_monoid R] : comm_monoid (tropical R) :=
{ ..tropical.monoid, ..tropical.comm_semigroup }

instance [add_group R] : group (tropical R) :=
{ inv := λ x, trop (- untrop x),
  mul_left_inv := λ _, untrop_injective (add_left_neg _),
  ..tropical.monoid }

instance [add_comm_group R] : comm_group (tropical R) :=
{ mul_comm := λ _ _, untrop_injective (add_comm _ _),
  ..tropical.group }

end monoid

section distrib

instance covariant_mul [preorder R] [has_add R] [covariant_class R R (+) (≤)] :
  covariant_class (tropical R) (tropical R) (*) (≤) :=
⟨λ x y z h, add_le_add_left h _⟩

instance covariant_swap_mul [preorder R] [has_add R] [covariant_class R R (function.swap (+)) (≤)] :
  covariant_class (tropical R) (tropical R) (function.swap (*)) (≤) :=
⟨λ x y z h, add_le_add_right h _⟩

instance [linear_order R] [has_add R]
  [covariant_class R R (+) (≤)] [covariant_class R R (function.swap (+)) (≤)] :
  distrib (tropical R) :=
{ mul := tropical.mul,
  add := tropical.add,
  left_distrib := λ _ _ _, untrop_injective (min_add_add_left _ _ _).symm,
  right_distrib := λ _ _ _, untrop_injective (min_add_add_right _ _ _).symm }

@[simp] lemma add_pow [linear_order R] [add_monoid R]
  [covariant_class R R (+) (≤)] [covariant_class R R (function.swap (+)) (≤)]
  (x y : tropical R) (n : ℕ) :
  (x + y) ^ n = x ^ n + y ^ n :=
begin
  cases le_total x y with h h,
  { rw [add_eq_left h, add_eq_left (pow_le_pow_of_le_left' h _)] },
  { rw [add_eq_right h, add_eq_right (pow_le_pow_of_le_left' h _)] }
end

end distrib

section semiring

variable [linear_ordered_add_comm_monoid_with_top R]

instance : comm_semiring (tropical R) :=
{ zero_add := λ _, untrop_injective (min_top_left _),
  add_zero := λ _, untrop_injective (min_top_right _),
  zero_mul := λ _, untrop_injective (top_add _),
  mul_zero := λ _, untrop_injective (add_top _),
  ..tropical.has_zero,
  ..tropical.distrib,
  ..tropical.add_comm_semigroup,
  ..tropical.comm_monoid  }

-- This could be stated on something like `linear_order_with_top α` if that existed
@[simp] lemma succ_nsmul (x : tropical R) (n : ℕ) :
  (n + 1) • x = x :=
begin
  induction n with n IH,
  { simp },
  { rw [add_nsmul, IH, one_nsmul, add_self] }
end

-- TODO: find/create the right classes to make this hold (for enat, ennreal, etc)
-- Requires `zero_eq_bot` to be true
-- lemma add_eq_zero_iff {a b : tropical R} :
--   a + b = 1 ↔ a = 1 ∨ b = 1 := sorry

@[simp] lemma mul_eq_zero_iff {R : Type*} [linear_ordered_add_comm_monoid R]
  {a b : tropical (with_top R)} :
  a * b = 0 ↔ a = 0 ∨ b = 0 :=
by simp [←untrop_inj_iff, with_top.add_eq_top]

instance {R : Type*} [linear_ordered_add_comm_monoid R] :
  no_zero_divisors (tropical (with_top R)) :=
⟨λ _ _, mul_eq_zero_iff.mp⟩

end semiring

end tropical
