/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import tactic.apply_fun
import algebra.order.ring
import algebra.opposites
import algebra.big_operators.basic
import data.equiv.ring_aut
import data.equiv.mul_add_aut

/-!
# Star monoids, rings, and modules

We introduce the basic algebraic notions of star monoids, star rings, and star modules.
A star algebra is simply a star ring that is also a star module.

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

open opposite

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

/-- The opposite type carries the same star operation. -/
instance [has_star R] : has_star (Rᵒᵖ) :=
{ star := λ r, op (star (r.unop)) }

@[simp] lemma unop_star [has_star R] (r : Rᵒᵖ) : unop (star r) = star (unop r) := rfl
@[simp] lemma op_star [has_star R] (r : R) : op (star r) = star (op r) := rfl

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

instance [has_involutive_star R] : has_involutive_star (Rᵒᵖ) :=
{ star_involutive := λ r, unop_injective (star_star r.unop) }

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

/-- `star` as an `mul_equiv` from `R` to `Rᵒᵖ` -/
@[simps apply]
def star_mul_equiv [monoid R] [star_monoid R] : R ≃* Rᵒᵖ :=
{ to_fun := λ x, opposite.op (star x),
  map_mul' := λ x y, (star_mul x y).symm ▸ (opposite.op_mul _ _),
  ..(has_involutive_star.star_involutive.to_equiv star).trans opposite.equiv_to_opposite}

/-- `star` as a `mul_aut` for commutative `R`. -/
@[simps apply]
def star_mul_aut [comm_monoid R] [star_monoid R] : mul_aut R :=
{ to_fun := star,
  map_mul' := star_mul',
  ..(has_involutive_star.star_involutive.to_equiv star) }

variables (R)

@[simp] lemma star_one [monoid R] [star_monoid R] : star (1 : R) = 1 :=
op_injective $ (star_mul_equiv : R ≃* Rᵒᵖ).map_one.trans (op_one _).symm

variables {R}

@[simp] lemma star_pow [monoid R] [star_monoid R] (x : R) (n : ℕ) : star (x ^ n) = star x ^ n :=
op_injective $
  ((star_mul_equiv : R ≃* Rᵒᵖ).to_monoid_hom.map_pow x n).trans (op_pow (star x) n).symm

@[simp] lemma star_inv [group R] [star_monoid R] (x : R) : star (x⁻¹) = (star x)⁻¹ :=
op_injective $
  ((star_mul_equiv : R ≃* Rᵒᵖ).to_monoid_hom.map_inv x).trans (op_inv (star x)).symm

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

instance [monoid R] [star_monoid R] : star_monoid (Rᵒᵖ) :=
{ star_mul := λ x y, unop_injective (star_mul y.unop x.unop) }

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

instance [add_monoid R] [star_add_monoid R] : star_add_monoid (Rᵒᵖ) :=
{ star_add := λ x y, unop_injective (star_add x.unop y.unop) }

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

@[simp] lemma star_gsmul [add_comm_group R] [star_add_monoid R] (x : R) (n : ℤ) :
  star (n • x) = n • star x :=
(star_add_equiv : R ≃+ R).to_add_monoid_hom.map_gsmul _ _

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

instance [semiring R] [star_ring R] : star_ring (Rᵒᵖ) :=
{ .. opposite.star_add_monoid }

/-- `star` as an `ring_equiv` from `R` to `Rᵒᵖ` -/
@[simps apply]
def star_ring_equiv [semiring R] [star_ring R] : R ≃+* Rᵒᵖ :=
{ to_fun := λ x, opposite.op (star x),
  ..star_add_equiv.trans (opposite.op_add_equiv : R ≃+ Rᵒᵖ),
  ..star_mul_equiv}

/-- `star` as a `ring_aut` for commutative `R`. -/
@[simps apply]
def star_ring_aut [comm_semiring R] [star_ring R] : ring_aut R :=
{ to_fun := star,
  ..star_add_equiv,
  ..star_mul_aut }

@[simp] lemma star_inv' [division_ring R] [star_ring R] (x : R) : star (x⁻¹) = (star x)⁻¹ :=
op_injective $
  ((star_ring_equiv : R ≃+* Rᵒᵖ).to_ring_hom.map_inv x).trans (op_inv (star x)).symm

/-- When multiplication is commutative, `star` preserves division. -/
@[simp] lemma star_div' [field R] [star_ring R] (x y : R) : star (x / y) = star x / star y :=
(star_ring_aut : R ≃+* R).to_ring_hom.map_div _ _

@[simp] lemma star_bit0 [ring R] [star_ring R] (r : R) : star (bit0 r) = bit0 (star r) :=
by simp [bit0]

@[simp] lemma star_bit1 [ring R] [star_ring R] (r : R) : star (bit1 r) = bit1 (star r) :=
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
An ordered `*`-ring is a ring which is both an ordered ring and a `*`-ring,
and `0 ≤ star r * r` for every `r`.

(In a Banach algebra, the natural ordering is given by the positive cone
which is the closure of the sums of elements `star r * r`.
This ordering makes the Banach algebra an ordered `*`-ring.)
-/
class star_ordered_ring (R : Type u) [ordered_semiring R] extends star_ring R :=
(star_mul_self_nonneg : ∀ r : R, 0 ≤ star r * r)

lemma star_mul_self_nonneg [ordered_semiring R] [star_ordered_ring R] {r : R} : 0 ≤ star r * r :=
star_ordered_ring.star_mul_self_nonneg r

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
class star_module (R : Type u) (A : Type v) [has_star R] [has_star A] [has_scalar R A] :=
(star_smul : ∀ (r : R) (a : A), star (r • a) = star r • star a)

export star_module (star_smul)
attribute [simp] star_smul

/-- A commutative star monoid is a star module over itself via `monoid.to_mul_action`. -/
instance star_monoid.to_star_module [comm_monoid R] [star_monoid R] : star_module R R :=
⟨λ r s, (star_mul r s).trans (mul_comm _ _)⟩
