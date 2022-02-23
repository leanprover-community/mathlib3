/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import tactic.apply_fun
import algebra.field.opposite
import algebra.field_power
import data.equiv.ring_aut
import group_theory.group_action.units
import group_theory.group_action.opposite
import algebra.ring.comp_typeclasses

/-!
# Star monoids, rings, and modules

We introduce the basic algebraic notions of star monoids, star rings, and star modules.
A star algebra is simply a star ring that is also a star module.

These are implemented as "mixin" typeclasses, so to summon a star ring (for example)
one needs to write `(R : Type) [ring R] [star_ring R]`.
This avoids difficulties with diamond inheritance.

We also define the class `star_ordered_ring R`, which says that the order on `R` respects the
star operation, i.e. an element `r` is nonnegative iff there exists an `s` such that
`r = star s * s`.

For now we simply do not introduce notations,
as different users are expected to feel strongly about the relative merits of
`r^*`, `r†`, `rᘁ`, and so on.

Our star rings are actually star semirings, but of course we can prove
`star_neg : star (-r) = - star r` when the underlying semiring is a ring.

## TODO

* In a Banach star algebra without a well-defined square root, the natural ordering is given by the
positive cone which is the closure of the sums of elements `star r * r`. A weaker version of
`star_ordered_ring` could be defined for this case. Note that the current definition has the
advantage of not requiring a topology.
-/


universes u v

open mul_opposite

/--
Notation typeclass (with no default notation!) for an algebraic structure with a star operation.
-/
class has_star (R : Type u) :=
(star : R → R)

variables {R : Type u}

export has_star (star)

/--
A star operation (e.g. complex conjugate).
-/
add_decl_doc star


/--
Typeclass for a star operation with is involutive.
-/
class has_involutive_star (R : Type u) extends has_star R :=
(star_involutive : function.involutive star)

export has_involutive_star (star_involutive)

@[simp] lemma star_star [has_involutive_star R] (r : R) : star (star r) = r :=
star_involutive _

lemma star_injective [has_involutive_star R] : function.injective (star : R → R) :=
star_involutive.injective

/--
Typeclass for a trivial star operation. This is mostly meant for `ℝ`.
-/
class has_trivial_star (R : Type u) [has_star R] : Prop :=
(star_trivial : ∀ (r : R), star r = r)

export has_trivial_star (star_trivial)
attribute [simp] star_trivial

/--
A `*`-monoid is a monoid `R` with an involutive operations `star`
so `star (r * s) = star s * star r`.
-/
class star_monoid (R : Type u) [monoid R] extends has_involutive_star R :=
(star_mul : ∀ r s : R, star (r * s) = star s * star r)

export star_monoid (star_mul)
attribute [simp] star_mul

/-- In a commutative ring, make `simp` prefer leaving the order unchanged. -/
@[simp] lemma star_mul' [comm_monoid R] [star_monoid R] (x y : R) :
  star (x * y) = star x * star y :=
(star_mul x y).trans (mul_comm _ _)

/-- `star` as an `mul_equiv` from `R` to `Rᵐᵒᵖ` -/
@[simps apply]
def star_mul_equiv [monoid R] [star_monoid R] : R ≃* Rᵐᵒᵖ :=
{ to_fun := λ x, mul_opposite.op (star x),
  map_mul' := λ x y, (star_mul x y).symm ▸ (mul_opposite.op_mul _ _),
  ..(has_involutive_star.star_involutive.to_equiv star).trans op_equiv}

/-- `star` as a `mul_aut` for commutative `R`. -/
@[simps apply]
def star_mul_aut [comm_monoid R] [star_monoid R] : mul_aut R :=
{ to_fun := star,
  map_mul' := star_mul',
  ..(has_involutive_star.star_involutive.to_equiv star) }

variables (R)

@[simp] lemma star_one [monoid R] [star_monoid R] : star (1 : R) = 1 :=
op_injective $ (star_mul_equiv : R ≃* Rᵐᵒᵖ).map_one.trans (op_one _).symm

variables {R}

@[simp] lemma star_pow [monoid R] [star_monoid R] (x : R) (n : ℕ) : star (x ^ n) = star x ^ n :=
op_injective $
  ((star_mul_equiv : R ≃* Rᵐᵒᵖ).to_monoid_hom.map_pow x n).trans (op_pow (star x) n).symm

@[simp] lemma star_inv [group R] [star_monoid R] (x : R) : star (x⁻¹) = (star x)⁻¹ :=
op_injective $
  ((star_mul_equiv : R ≃* Rᵐᵒᵖ).to_monoid_hom.map_inv x).trans (op_inv (star x)).symm

@[simp] lemma star_zpow [group R] [star_monoid R] (x : R) (z : ℤ) : star (x ^ z) = star x ^ z :=
op_injective $
  ((star_mul_equiv : R ≃* Rᵐᵒᵖ).to_monoid_hom.map_zpow x z).trans (op_zpow (star x) z).symm

/-- When multiplication is commutative, `star` preserves division. -/
@[simp] lemma star_div [comm_group R] [star_monoid R] (x y : R) : star (x / y) = star x / star y :=
(star_mul_aut : R ≃* R).to_monoid_hom.map_div _ _

section
open_locale big_operators

@[simp] lemma star_prod [comm_monoid R] [star_monoid R] {α : Type*}
  (s : finset α) (f : α → R):
  star (∏ x in s, f x) = ∏ x in s, star (f x) :=
(star_mul_aut : R ≃* R).map_prod _ _

end

/--
Any commutative monoid admits the trivial `*`-structure.

See note [reducible non-instances].
-/
@[reducible]
def star_monoid_of_comm {R : Type*} [comm_monoid R] : star_monoid R :=
{ star := id,
  star_involutive := λ x, rfl,
  star_mul := mul_comm }

section
local attribute [instance] star_monoid_of_comm

/-- Note that since `star_monoid_of_comm` is reducible, `simp` can already prove this. --/
lemma star_id_of_comm {R : Type*} [comm_semiring R] {x : R} : star x = x := rfl

end

/--
A `*`-additive monoid `R` is an additive monoid with an involutive `star` operation which
preserves addition.
-/
class star_add_monoid (R : Type u) [add_monoid R] extends has_involutive_star R :=
(star_add : ∀ r s : R, star (r + s) = star r + star s)

export star_add_monoid (star_add)
attribute [simp] star_add

/-- `star` as an `add_equiv` -/
@[simps apply]
def star_add_equiv [add_monoid R] [star_add_monoid R] : R ≃+ R :=
{ to_fun := star,
  map_add' := star_add,
  ..(has_involutive_star.star_involutive.to_equiv star)}

variables (R)

@[simp] lemma star_zero [add_monoid R] [star_add_monoid R] : star (0 : R) = 0 :=
(star_add_equiv : R ≃+ R).map_zero

variables {R}

@[simp] lemma star_neg [add_group R] [star_add_monoid R] (r : R) : star (-r) = - star r :=
(star_add_equiv : R ≃+ R).map_neg _

@[simp] lemma star_sub [add_group R] [star_add_monoid R] (r s : R) :
  star (r - s) = star r - star s :=
(star_add_equiv : R ≃+ R).map_sub _ _

@[simp] lemma star_nsmul [add_comm_monoid R] [star_add_monoid R] (x : R) (n : ℕ) :
  star (n • x) = n • star x :=
(star_add_equiv : R ≃+ R).to_add_monoid_hom.map_nsmul _ _

@[simp] lemma star_zsmul [add_comm_group R] [star_add_monoid R] (x : R) (n : ℤ) :
  star (n • x) = n • star x :=
(star_add_equiv : R ≃+ R).to_add_monoid_hom.map_zsmul _ _

section
open_locale big_operators

@[simp] lemma star_sum [add_comm_monoid R] [star_add_monoid R] {α : Type*}
  (s : finset α) (f : α → R):
  star (∑ x in s, f x) = ∑ x in s, star (f x) :=
(star_add_equiv : R ≃+ R).map_sum _ _

end

/--
A `*`-ring `R` is a (semi)ring with an involutive `star` operation which is additive
which makes `R` with its multiplicative structure into a `*`-monoid
(i.e. `star (r * s) = star s * star r`).
-/
class star_ring (R : Type u) [semiring R] extends star_monoid R :=
(star_add : ∀ r s : R, star (r + s) = star r + star s)

@[priority 100]
instance star_ring.to_star_add_monoid [semiring R] [star_ring R] : star_add_monoid R :=
{ star_add := star_ring.star_add }

/-- `star` as an `ring_equiv` from `R` to `Rᵐᵒᵖ` -/
@[simps apply]
def star_ring_equiv [semiring R] [star_ring R] : R ≃+* Rᵐᵒᵖ :=
{ to_fun := λ x, mul_opposite.op (star x),
  ..star_add_equiv.trans (mul_opposite.op_add_equiv : R ≃+ Rᵐᵒᵖ),
  ..star_mul_equiv }

/-- `star` as a ring automorphism, for commutative `R`. -/
@[simps apply]
def star_ring_aut [comm_semiring R] [star_ring R] : ring_aut R :=
{ to_fun := star,
  ..star_add_equiv,
  ..star_mul_aut }

variables (R)
/-- `star` as a ring endomorphism, for commutative `R`. This is used to denote complex
conjugation, and is available under the notation `conj` in the locale `complex_conjugate`.

Note that this is the preferred form (over `star_ring_aut`, available under the same hypotheses)
because the notation `E →ₗ⋆[R] F` for an `R`-conjugate-linear map (short for
`E →ₛₗ[star_ring_end R] F`) does not pretty-print if there is a coercion involved, as would be the
case for `(↑star_ring_aut : R →* R)`. -/
def star_ring_end [comm_semiring R] [star_ring R] : R →+* R := @star_ring_aut R _ _
variables {R}

localized "notation `conj` := star_ring_end _" in complex_conjugate

/-- This is not a simp lemma, since we usually want simp to keep `star_ring_end` bundled.
 For example, for complex conjugation, we don't want simp to turn `conj x`
 into the bare function `star x` automatically since most lemmas are about `conj x`. -/
lemma star_ring_end_apply [comm_semiring R] [star_ring R] {x : R} :
  star_ring_end R x = star x := rfl

@[simp] lemma star_ring_end_self_apply [comm_semiring R] [star_ring R] (x : R) :
  star_ring_end R (star_ring_end R x) = x := star_star x

-- A more convenient name for complex conjugation
alias star_ring_end_self_apply ← complex.conj_conj
alias star_ring_end_self_apply ← is_R_or_C.conj_conj

@[simp] lemma star_inv' [division_ring R] [star_ring R] (x : R) : star (x⁻¹) = (star x)⁻¹ :=
op_injective $
  ((star_ring_equiv : R ≃+* Rᵐᵒᵖ).to_ring_hom.map_inv x).trans (op_inv (star x)).symm

@[simp] lemma star_zpow₀ [division_ring R] [star_ring R] (x : R) (z : ℤ) :
  star (x ^ z) = star x ^ z :=
op_injective $
  ((star_ring_equiv : R ≃+* Rᵐᵒᵖ).to_ring_hom.map_zpow x z).trans (op_zpow (star x) z).symm

/-- When multiplication is commutative, `star` preserves division. -/
@[simp] lemma star_div' [field R] [star_ring R] (x y : R) : star (x / y) = star x / star y :=
(star_ring_end R).map_div _ _

@[simp] lemma star_bit0 [add_monoid R] [star_add_monoid R] (r : R) :
  star (bit0 r) = bit0 (star r) :=
by simp [bit0]

@[simp] lemma star_bit1 [semiring R] [star_ring R] (r : R) : star (bit1 r) = bit1 (star r) :=
by simp [bit1]

/--
Any commutative semiring admits the trivial `*`-structure.

See note [reducible non-instances].
-/
@[reducible]
def star_ring_of_comm {R : Type*} [comm_semiring R] : star_ring R :=
{ star := id,
  star_add := λ x y, rfl,
  ..star_monoid_of_comm }

/--
An ordered `*`-ring is a ring which is both an `ordered_add_comm_group` and a `*`-ring,
and `0 ≤ r ↔ ∃ s, r = star s * s`.
-/
class star_ordered_ring (R : Type u) [ring R] [partial_order R] extends star_ring R :=
(add_le_add_left       : ∀ a b : R, a ≤ b → ∀ c : R, c + a ≤ c + b)
(nonneg_iff            : ∀ r : R, 0 ≤ r ↔ ∃ s, r = star s * s)

namespace star_ordered_ring

variables [ring R] [partial_order R] [star_ordered_ring R]

@[priority 100] -- see note [lower instance priority]
instance : ordered_add_comm_group R :=
{ ..show ring R, by apply_instance,
  ..show partial_order R, by apply_instance,
  ..show star_ordered_ring R, by apply_instance }

end star_ordered_ring

lemma star_mul_self_nonneg [ring R] [partial_order R] [star_ordered_ring R] {r : R} :
  0 ≤ star r * r :=
(star_ordered_ring.nonneg_iff _).mpr ⟨r, rfl⟩

lemma star_mul_self_nonneg' [ring R] [partial_order R] [star_ordered_ring R] {r : R} :
  0 ≤ r * star r :=
by { nth_rewrite_rhs 0 [←star_star r], exact star_mul_self_nonneg }

/--
A star module `A` over a star ring `R` is a module which is a star add monoid,
and the two star structures are compatible in the sense
`star (r • a) = star r • star a`.

Note that it is up to the user of this typeclass to enforce
`[semiring R] [star_ring R] [add_comm_monoid A] [star_add_monoid A] [module R A]`, and that
the statement only requires `[has_star R] [has_star A] [has_scalar R A]`.

If used as `[comm_ring R] [star_ring R] [semiring A] [star_ring A] [algebra R A]`, this represents a
star algebra.
-/
class star_module (R : Type u) (A : Type v) [has_star R] [has_star A] [has_scalar R A] : Prop :=
(star_smul : ∀ (r : R) (a : A), star (r • a) = star r • star a)

export star_module (star_smul)
attribute [simp] star_smul

/-- A commutative star monoid is a star module over itself via `monoid.to_mul_action`. -/
instance star_monoid.to_star_module [comm_monoid R] [star_monoid R] : star_module R R :=
⟨star_mul'⟩

namespace ring_hom_inv_pair

/-- Instance needed to define star-linear maps over a commutative star ring
(ex: conjugate-linear maps when R = ℂ).  -/
instance [comm_semiring R] [star_ring R] :
  ring_hom_inv_pair (star_ring_end R) (star_ring_end R) :=
⟨ring_hom.ext star_star, ring_hom.ext star_star⟩

end ring_hom_inv_pair

/-! ### Instances -/

namespace units

variables [monoid R] [star_monoid R]

instance : star_monoid Rˣ :=
{ star := λ u,
  { val := star u,
    inv := star ↑u⁻¹,
    val_inv := (star_mul _ _).symm.trans $ (congr_arg star u.inv_val).trans $ star_one _,
    inv_val := (star_mul _ _).symm.trans $ (congr_arg star u.val_inv).trans $ star_one _ },
  star_involutive := λ u, units.ext (star_involutive _),
  star_mul := λ u v, units.ext (star_mul _ _) }

@[simp] lemma coe_star (u : Rˣ) : ↑(star u) = (star ↑u : R) := rfl
@[simp] lemma coe_star_inv (u : Rˣ) : ↑(star u)⁻¹ = (star ↑u⁻¹ : R) := rfl

instance {A : Type*} [has_star A] [has_scalar R A] [star_module R A] : star_module Rˣ A :=
⟨λ u a, (star_smul ↑u a : _)⟩

end units

lemma is_unit.star [monoid R] [star_monoid R] {a : R} : is_unit a → is_unit (star a)
| ⟨u, hu⟩ := ⟨star u, hu ▸ rfl⟩

@[simp] lemma is_unit_star [monoid R] [star_monoid R] {a : R} : is_unit (star a) ↔ is_unit a :=
⟨λ h, star_star a ▸ h.star, is_unit.star⟩

lemma ring.inverse_star [semiring R] [star_ring R] (a : R) :
  ring.inverse (star a) = star (ring.inverse a) :=
begin
  by_cases ha : is_unit a,
  { obtain ⟨u, rfl⟩ := ha,
    rw [ring.inverse_unit, ←units.coe_star, ring.inverse_unit, ←units.coe_star_inv], },
  rw [ring.inverse_non_unit _ ha, ring.inverse_non_unit _ (mt is_unit_star.mp ha), star_zero],
end

instance invertible.star {R : Type*} [monoid R] [star_monoid R] (r : R) [invertible r] :
  invertible (star r) :=
{ inv_of := star (⅟r),
  inv_of_mul_self := by rw [←star_mul, mul_inv_of_self, star_one],
  mul_inv_of_self := by rw [←star_mul, inv_of_mul_self, star_one] }

lemma star_inv_of {R : Type*} [monoid R] [star_monoid R] (r : R)
  [invertible r] [invertible (star r)] :
  star (⅟r) = ⅟(star r) :=
by { letI := invertible.star r, convert (rfl : star (⅟r) = _) }

namespace mul_opposite

/-- The opposite type carries the same star operation. -/
instance [has_star R] : has_star (Rᵐᵒᵖ) :=
{ star := λ r, op (star (r.unop)) }

@[simp] lemma unop_star [has_star R] (r : Rᵐᵒᵖ) : unop (star r) = star (unop r) := rfl
@[simp] lemma op_star [has_star R] (r : R) : op (star r) = star (op r) := rfl

instance [has_involutive_star R] : has_involutive_star (Rᵐᵒᵖ) :=
{ star_involutive := λ r, unop_injective (star_star r.unop) }

instance [monoid R] [star_monoid R] : star_monoid (Rᵐᵒᵖ) :=
{ star_mul := λ x y, unop_injective (star_mul y.unop x.unop) }

instance [add_monoid R] [star_add_monoid R] : star_add_monoid (Rᵐᵒᵖ) :=
{ star_add := λ x y, unop_injective (star_add x.unop y.unop) }

instance [semiring R] [star_ring R] : star_ring (Rᵐᵒᵖ) :=
{ .. mul_opposite.star_add_monoid }

end mul_opposite

/-- A commutative star monoid is a star module over its opposite via
`monoid.to_opposite_mul_action`. -/
instance star_monoid.to_opposite_star_module [comm_monoid R] [star_monoid R] : star_module Rᵐᵒᵖ R :=
⟨λ r s, star_mul' s r.unop⟩
