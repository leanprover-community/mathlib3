/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.ring.aut
import algebra.ring.comp_typeclasses
import data.rat.cast
import group_theory.group_action.opposite
import data.set_like.basic

/-!
# Star monoids, rings, and modules

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

assert_not_exists finset
assert_not_exists subgroup

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

/-- `star_mem_class S G` states `S` is a type of subsets `s ⊆ G` closed under star. -/
class star_mem_class (S R : Type*) [has_star R] [set_like S R] :=
(star_mem : ∀ {s : S} {r : R}, r ∈ s → star r ∈ s)

export star_mem_class (star_mem)

namespace star_mem_class

variables {S : Type u} [has_star R] [set_like S R] [hS : star_mem_class S R] (s : S)
include hS

instance : has_star s :=
{ star := λ r, ⟨star (r : R), star_mem r.prop⟩ }

end star_mem_class


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

/-- `star` as an equivalence when it is involutive. -/
protected def equiv.star [has_involutive_star R] : equiv.perm R :=
star_involutive.to_perm _

lemma eq_star_of_eq_star [has_involutive_star R] {r s : R} (h : r = star s) : s = star r :=
by simp [h]

lemma eq_star_iff_eq_star [has_involutive_star R] {r s : R} : r = star s ↔ s = star r :=
⟨eq_star_of_eq_star, eq_star_of_eq_star⟩

lemma star_eq_iff_star_eq [has_involutive_star R] {r s : R} : star r = s ↔ star s = r :=
eq_comm.trans $ eq_star_iff_eq_star.trans eq_comm

/--
Typeclass for a trivial star operation. This is mostly meant for `ℝ`.
-/
class has_trivial_star (R : Type u) [has_star R] : Prop :=
(star_trivial : ∀ (r : R), star r = r)

export has_trivial_star (star_trivial)
attribute [simp] star_trivial

/--
A `*`-semigroup is a semigroup `R` with an involutive operations `star`
so `star (r * s) = star s * star r`.
-/
class star_semigroup (R : Type u) [semigroup R] extends has_involutive_star R :=
(star_mul : ∀ r s : R, star (r * s) = star s * star r)

export star_semigroup (star_mul)
attribute [simp] star_mul

/-- In a commutative ring, make `simp` prefer leaving the order unchanged. -/
@[simp] lemma star_mul' [comm_semigroup R] [star_semigroup R] (x y : R) :
  star (x * y) = star x * star y :=
(star_mul x y).trans (mul_comm _ _)

/-- `star` as an `mul_equiv` from `R` to `Rᵐᵒᵖ` -/
@[simps apply]
def star_mul_equiv [semigroup R] [star_semigroup R] : R ≃* Rᵐᵒᵖ :=
{ to_fun := λ x, mul_opposite.op (star x),
  map_mul' := λ x y, (star_mul x y).symm ▸ (mul_opposite.op_mul _ _),
  ..(has_involutive_star.star_involutive.to_perm star).trans op_equiv}

/-- `star` as a `mul_aut` for commutative `R`. -/
@[simps apply]
def star_mul_aut [comm_semigroup R] [star_semigroup R] : mul_aut R :=
{ to_fun := star,
  map_mul' := star_mul',
  ..(has_involutive_star.star_involutive.to_perm star) }

variables (R)

@[simp] lemma star_one [monoid R] [star_semigroup R] : star (1 : R) = 1 :=
op_injective $ (star_mul_equiv : R ≃* Rᵐᵒᵖ).map_one.trans (op_one _).symm

variables {R}

@[simp] lemma star_pow [monoid R] [star_semigroup R] (x : R) (n : ℕ) : star (x ^ n) = star x ^ n :=
op_injective $
  ((star_mul_equiv : R ≃* Rᵐᵒᵖ).to_monoid_hom.map_pow x n).trans (op_pow (star x) n).symm

@[simp] lemma star_inv [group R] [star_semigroup R] (x : R) : star (x⁻¹) = (star x)⁻¹ :=
op_injective $
  ((star_mul_equiv : R ≃* Rᵐᵒᵖ).to_monoid_hom.map_inv x).trans (op_inv (star x)).symm

@[simp] lemma star_zpow [group R] [star_semigroup R] (x : R) (z : ℤ) : star (x ^ z) = star x ^ z :=
op_injective $
  ((star_mul_equiv : R ≃* Rᵐᵒᵖ).to_monoid_hom.map_zpow x z).trans (op_zpow (star x) z).symm

/-- When multiplication is commutative, `star` preserves division. -/
@[simp] lemma star_div [comm_group R] [star_semigroup R] (x y : R) :
  star (x / y) = star x / star y :=
map_div (star_mul_aut : R ≃* R) _ _

/--
Any commutative monoid admits the trivial `*`-structure.

See note [reducible non-instances].
-/
@[reducible]
def star_semigroup_of_comm {R : Type*} [comm_monoid R] : star_semigroup R :=
{ star := id,
  star_involutive := λ x, rfl,
  star_mul := mul_comm }

section
local attribute [instance] star_semigroup_of_comm

/-- Note that since `star_semigroup_of_comm` is reducible, `simp` can already prove this. -/
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
  ..(has_involutive_star.star_involutive.to_perm star)}

variables (R)

@[simp] lemma star_zero [add_monoid R] [star_add_monoid R] : star (0 : R) = 0 :=
(star_add_equiv : R ≃+ R).map_zero

variables {R}

@[simp]
lemma star_eq_zero [add_monoid R] [star_add_monoid R] {x : R} : star x = 0 ↔ x = 0 :=
star_add_equiv.map_eq_zero_iff

lemma star_ne_zero [add_monoid R] [star_add_monoid R] {x : R} : star x ≠ 0 ↔ x ≠ 0 :=
star_eq_zero.not

@[simp] lemma star_neg [add_group R] [star_add_monoid R] (r : R) : star (-r) = - star r :=
(star_add_equiv : R ≃+ R).map_neg _

@[simp] lemma star_sub [add_group R] [star_add_monoid R] (r s : R) :
  star (r - s) = star r - star s :=
(star_add_equiv : R ≃+ R).map_sub _ _

@[simp] lemma star_nsmul [add_monoid R] [star_add_monoid R] (x : R) (n : ℕ) :
  star (n • x) = n • star x :=
(star_add_equiv : R ≃+ R).to_add_monoid_hom.map_nsmul _ _

@[simp] lemma star_zsmul [add_group R] [star_add_monoid R] (x : R) (n : ℤ) :
  star (n • x) = n • star x :=
(star_add_equiv : R ≃+ R).to_add_monoid_hom.map_zsmul _ _

/--
A `*`-ring `R` is a (semi)ring with an involutive `star` operation which is additive
which makes `R` with its multiplicative structure into a `*`-semigroup
(i.e. `star (r * s) = star s * star r`).
-/
class star_ring (R : Type u) [non_unital_semiring R] extends star_semigroup R :=
(star_add : ∀ r s : R, star (r + s) = star r + star s)

@[priority 100]
instance star_ring.to_star_add_monoid [non_unital_semiring R] [star_ring R] : star_add_monoid R :=
{ star_add := star_ring.star_add }

/-- `star` as an `ring_equiv` from `R` to `Rᵐᵒᵖ` -/
@[simps apply]
def star_ring_equiv [non_unital_semiring R] [star_ring R] : R ≃+* Rᵐᵒᵖ :=
{ to_fun := λ x, mul_opposite.op (star x),
  ..star_add_equiv.trans (mul_opposite.op_add_equiv : R ≃+ Rᵐᵒᵖ),
  ..star_mul_equiv }

@[simp, norm_cast] lemma star_nat_cast [semiring R] [star_ring R] (n : ℕ) :
  star (n : R) = n :=
(congr_arg unop (map_nat_cast (star_ring_equiv : R ≃+* Rᵐᵒᵖ) n)).trans (unop_nat_cast _)

@[simp, norm_cast] lemma star_int_cast [ring R] [star_ring R] (z : ℤ) :
  star (z : R) = z :=
(congr_arg unop $ map_int_cast (star_ring_equiv : R ≃+* Rᵐᵒᵖ) z).trans (unop_int_cast _)

@[simp, norm_cast] lemma star_rat_cast [division_ring R] [star_ring R] (r : ℚ) :
  star (r : R) = r :=
(congr_arg unop $ map_rat_cast (star_ring_equiv : R ≃+* Rᵐᵒᵖ) r).trans (unop_rat_cast _)

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

localized "notation (name := star_ring_end) `conj` := star_ring_end hole!" in complex_conjugate

/-- This is not a simp lemma, since we usually want simp to keep `star_ring_end` bundled.
 For example, for complex conjugation, we don't want simp to turn `conj x`
 into the bare function `star x` automatically since most lemmas are about `conj x`. -/
lemma star_ring_end_apply [comm_semiring R] [star_ring R] {x : R} :
  star_ring_end R x = star x := rfl

@[simp] lemma star_ring_end_self_apply [comm_semiring R] [star_ring R] (x : R) :
  star_ring_end R (star_ring_end R x) = x := star_star x

instance ring_hom.has_involutive_star {S : Type*} [non_assoc_semiring S] [comm_semiring R]
  [star_ring R] : has_involutive_star (S →+* R) :=
{ to_has_star := { star := λ f, ring_hom.comp (star_ring_end R) f },
  star_involutive :=
    by { intro _, ext, simp only [ring_hom.coe_comp, function.comp_app, star_ring_end_self_apply] }}

lemma ring_hom.star_def {S : Type*} [non_assoc_semiring S] [comm_semiring R] [star_ring R]
  (f : S →+* R) : has_star.star f = ring_hom.comp (star_ring_end R) f := rfl

lemma ring_hom.star_apply {S : Type*} [non_assoc_semiring S] [comm_semiring R] [star_ring R]
  (f : S →+* R) (s : S) : star f s = star (f s) := rfl

-- A more convenient name for complex conjugation
alias star_ring_end_self_apply ← complex.conj_conj
alias star_ring_end_self_apply ← is_R_or_C.conj_conj

@[simp] lemma star_inv' [division_ring R] [star_ring R] (x : R) : star (x⁻¹) = (star x)⁻¹ :=
op_injective $ (map_inv₀ (star_ring_equiv : R ≃+* Rᵐᵒᵖ) x).trans (op_inv (star x)).symm

@[simp] lemma star_zpow₀ [division_ring R] [star_ring R] (x : R) (z : ℤ) :
  star (x ^ z) = star x ^ z :=
op_injective $ (map_zpow₀ (star_ring_equiv : R ≃+* Rᵐᵒᵖ) x z).trans (op_zpow (star x) z).symm

/-- When multiplication is commutative, `star` preserves division. -/
@[simp] lemma star_div' [field R] [star_ring R] (x y : R) : star (x / y) = star x / star y :=
map_div₀ (star_ring_end R) _ _

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
  ..star_semigroup_of_comm }

/--
An ordered `*`-ring is a ring which is both an `ordered_add_comm_group` and a `*`-ring,
and `0 ≤ r ↔ ∃ s, r = star s * s`.
-/
class star_ordered_ring (R : Type u) [non_unital_semiring R] [partial_order R]
  extends star_ring R :=
(add_le_add_left       : ∀ a b : R, a ≤ b → ∀ c : R, c + a ≤ c + b)
(nonneg_iff            : ∀ r : R, 0 ≤ r ↔ ∃ s, r = star s * s)

namespace star_ordered_ring

@[priority 100] -- see note [lower instance priority]
instance [non_unital_ring R] [partial_order R] [star_ordered_ring R] : ordered_add_comm_group R :=
{ ..show non_unital_ring R, by apply_instance,
  ..show partial_order R, by apply_instance,
  ..show star_ordered_ring R, by apply_instance }

end star_ordered_ring

section non_unital_semiring

variables [non_unital_semiring R] [partial_order R] [star_ordered_ring R]

lemma star_mul_self_nonneg {r : R} : 0 ≤ star r * r :=
(star_ordered_ring.nonneg_iff _).mpr ⟨r, rfl⟩

lemma star_mul_self_nonneg' {r : R} : 0 ≤ r * star r :=
by { nth_rewrite_rhs 0 [←star_star r], exact star_mul_self_nonneg }

lemma conjugate_nonneg {a : R} (ha : 0 ≤ a) (c : R) : 0 ≤ star c * a * c :=
begin
  obtain ⟨x, rfl⟩ := (star_ordered_ring.nonneg_iff _).1 ha,
  exact (star_ordered_ring.nonneg_iff _).2 ⟨x * c, by rw [star_mul, ←mul_assoc, mul_assoc _ _ c]⟩,
end

lemma conjugate_nonneg' {a : R} (ha : 0 ≤ a) (c : R) : 0 ≤ c * a * star c :=
by simpa only [star_star] using conjugate_nonneg ha (star c)

end non_unital_semiring

section non_unital_ring

variables [non_unital_ring R] [partial_order R] [star_ordered_ring R]

lemma conjugate_le_conjugate {a b : R} (hab : a ≤ b) (c : R) : star c * a * c ≤ star c * b * c :=
begin
  rw ←sub_nonneg at hab ⊢,
  convert conjugate_nonneg hab c,
  simp only [mul_sub, sub_mul],
end

lemma conjugate_le_conjugate' {a b : R} (hab : a ≤ b) (c : R) : c * a * star c ≤ c * b * star c :=
by simpa only [star_star] using conjugate_le_conjugate hab (star c)

end non_unital_ring

/--
A star module `A` over a star ring `R` is a module which is a star add monoid,
and the two star structures are compatible in the sense
`star (r • a) = star r • star a`.

Note that it is up to the user of this typeclass to enforce
`[semiring R] [star_ring R] [add_comm_monoid A] [star_add_monoid A] [module R A]`, and that
the statement only requires `[has_star R] [has_star A] [has_smul R A]`.

If used as `[comm_ring R] [star_ring R] [semiring A] [star_ring A] [algebra R A]`, this represents a
star algebra.
-/
class star_module (R : Type u) (A : Type v) [has_star R] [has_star A] [has_smul R A] : Prop :=
(star_smul : ∀ (r : R) (a : A), star (r • a) = star r • star a)

export star_module (star_smul)
attribute [simp] star_smul

/-- A commutative star monoid is a star module over itself via `monoid.to_mul_action`. -/
instance star_semigroup.to_star_module [comm_monoid R] [star_semigroup R] : star_module R R :=
⟨star_mul'⟩

namespace ring_hom_inv_pair

/-- Instance needed to define star-linear maps over a commutative star ring
(ex: conjugate-linear maps when R = ℂ).  -/
instance [comm_semiring R] [star_ring R] :
  ring_hom_inv_pair (star_ring_end R) (star_ring_end R) :=
⟨ring_hom.ext star_star, ring_hom.ext star_star⟩

end ring_hom_inv_pair

section
set_option old_structure_cmd true

/-- `star_hom_class F R S` states that `F` is a type of `star`-preserving maps from `R` to `S`. -/
class star_hom_class (F : Type*) (R S : out_param Type*) [has_star R] [has_star S]
  extends fun_like F R (λ _, S) :=
(map_star : ∀ (f : F) (r : R), f (star r) = star (f r))

export star_hom_class (map_star)

end

/-! ### Instances -/

namespace units

variables [monoid R] [star_semigroup R]

instance : star_semigroup Rˣ :=
{ star := λ u,
  { val := star u,
    inv := star ↑u⁻¹,
    val_inv := (star_mul _ _).symm.trans $ (congr_arg star u.inv_val).trans $ star_one _,
    inv_val := (star_mul _ _).symm.trans $ (congr_arg star u.val_inv).trans $ star_one _ },
  star_involutive := λ u, units.ext (star_involutive _),
  star_mul := λ u v, units.ext (star_mul _ _) }

@[simp] lemma coe_star (u : Rˣ) : ↑(star u) = (star ↑u : R) := rfl
@[simp] lemma coe_star_inv (u : Rˣ) : ↑(star u)⁻¹ = (star ↑u⁻¹ : R) := rfl

instance {A : Type*} [has_star A] [has_smul R A] [star_module R A] : star_module Rˣ A :=
⟨λ u a, (star_smul ↑u a : _)⟩

end units

lemma is_unit.star [monoid R] [star_semigroup R] {a : R} : is_unit a → is_unit (star a)
| ⟨u, hu⟩ := ⟨star u, hu ▸ rfl⟩

@[simp] lemma is_unit_star [monoid R] [star_semigroup R] {a : R} : is_unit (star a) ↔ is_unit a :=
⟨λ h, star_star a ▸ h.star, is_unit.star⟩

lemma ring.inverse_star [semiring R] [star_ring R] (a : R) :
  ring.inverse (star a) = star (ring.inverse a) :=
begin
  by_cases ha : is_unit a,
  { obtain ⟨u, rfl⟩ := ha,
    rw [ring.inverse_unit, ←units.coe_star, ring.inverse_unit, ←units.coe_star_inv], },
  rw [ring.inverse_non_unit _ ha, ring.inverse_non_unit _ (mt is_unit_star.mp ha), star_zero],
end

instance invertible.star {R : Type*} [monoid R] [star_semigroup R] (r : R) [invertible r] :
  invertible (star r) :=
{ inv_of := star (⅟r),
  inv_of_mul_self := by rw [←star_mul, mul_inv_of_self, star_one],
  mul_inv_of_self := by rw [←star_mul, inv_of_mul_self, star_one] }

lemma star_inv_of {R : Type*} [monoid R] [star_semigroup R] (r : R)
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

instance [monoid R] [star_semigroup R] : star_semigroup (Rᵐᵒᵖ) :=
{ star_mul := λ x y, unop_injective (star_mul y.unop x.unop) }

instance [add_monoid R] [star_add_monoid R] : star_add_monoid (Rᵐᵒᵖ) :=
{ star_add := λ x y, unop_injective (star_add x.unop y.unop) }

instance [semiring R] [star_ring R] : star_ring (Rᵐᵒᵖ) :=
{ .. mul_opposite.star_add_monoid }

end mul_opposite

/-- A commutative star monoid is a star module over its opposite via
`monoid.to_opposite_mul_action`. -/
instance star_semigroup.to_opposite_star_module [comm_monoid R] [star_semigroup R] :
  star_module Rᵐᵒᵖ R :=
⟨λ r s, star_mul' s r.unop⟩
