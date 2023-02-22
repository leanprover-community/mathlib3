/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import algebra.module.basic
import algebra.module.ulift
import algebra.ne_zero
import algebra.punit_instances
import algebra.ring.aut
import algebra.ring.ulift
import algebra.char_zero.lemmas
import linear_algebra.basic
import ring_theory.subring.basic
import tactic.abel

/-!
# Algebras over commutative semirings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define associative unital `algebra`s over commutative (semi)rings, algebra
homomorphisms `alg_hom`, and algebra equivalences `alg_equiv`.

`subalgebra`s are defined in `algebra.algebra.subalgebra`.

For the category of `R`-algebras, denoted `Algebra R`, see the file
`algebra/category/Algebra/basic.lean`.

See the implementation notes for remarks about non-associative and non-unital algebras.

## Main definitions:

* `algebra R A`: the algebra typeclass.
* `algebra_map R A : R →+* A`: the canonical map from `R` to `A`, as a `ring_hom`. This is the
  preferred spelling of this map, it is also available as:
  * `algebra.linear_map R A : R →ₗ[R] A`, a `linear_map`.
  * `algebra.of_id R A : R →ₐ[R] A`, an `alg_hom` (defined in a later file).
* Instances of `algebra` in this file:
  * `algebra.id`
  * `algebra_nat`
  * `algebra_int`
  * `algebra_rat`
  * `mul_opposite.algebra`
  * `module.End.algebra`

## Implementation notes

Given a commutative (semi)ring `R`, there are two ways to define an `R`-algebra structure on a
(possibly noncommutative) (semi)ring `A`:
* By endowing `A` with a morphism of rings `R →+* A` denoted `algebra_map R A` which lands in the
  center of `A`.
* By requiring `A` be an `R`-module such that the action associates and commutes with multiplication
  as `r • (a₁ * a₂) = (r • a₁) * a₂ = a₁ * (r • a₂)`.

We define `algebra R A` in a way that subsumes both definitions, by extending `has_smul R A` and
requiring that this scalar action `r • x` must agree with left multiplication by the image of the
structure morphism `algebra_map R A r * x`.

As a result, there are two ways to talk about an `R`-algebra `A` when `A` is a semiring:
1. ```lean
   variables [comm_semiring R] [semiring A]
   variables [algebra R A]
   ```
2. ```lean
   variables [comm_semiring R] [semiring A]
   variables [module R A] [smul_comm_class R A A] [is_scalar_tower R A A]
   ```

The first approach implies the second via typeclass search; so any lemma stated with the second set
of arguments will automatically apply to the first set. Typeclass search does not know that the
second approach implies the first, but this can be shown with:
```lean
example {R A : Type*} [comm_semiring R] [semiring A]
  [module R A] [smul_comm_class R A A] [is_scalar_tower R A A] : algebra R A :=
algebra.of_module smul_mul_assoc mul_smul_comm
```

The advantage of the first approach is that `algebra_map R A` is available, and `alg_hom R A B` and
`subalgebra R A` can be used. For concrete `R` and `A`, `algebra_map R A` is often definitionally
convenient.

The advantage of the second approach is that `comm_semiring R`, `semiring A`, and `module R A` can
all be relaxed independently; for instance, this allows us to:
* Replace `semiring A` with `non_unital_non_assoc_semiring A` in order to describe non-unital and/or
  non-associative algebras.
* Replace `comm_semiring R` and `module R A` with `comm_group R'` and `distrib_mul_action R' A`,
  which when `R' = Rˣ` lets us talk about the "algebra-like" action of `Rˣ` on an
  `R`-algebra `A`.

While `alg_hom R A B` cannot be used in the second approach, `non_unital_alg_hom R A B` still can.

You should always use the first approach when working with associative unital algebras, and mimic
the second approach only when you need to weaken a condition on either `R` or `A`.

-/

universes u v w u₁ v₁

open_locale big_operators

section prio
-- We set this priority to 0 later in this file
set_option extends_priority 200 /- control priority of
`instance [algebra R A] : has_smul R A` -/

/--
An associative unital `R`-algebra is a semiring `A` equipped with a map into its center `R → A`.

See the implementation notes in this file for discussion of the details of this definition.
-/
@[nolint has_nonempty_instance]
class algebra (R : Type u) (A : Type v) [comm_semiring R] [semiring A]
  extends has_smul R A, R →+* A :=
(commutes' : ∀ r x, to_fun r * x = x * to_fun r)
(smul_def' : ∀ r x, r • x = to_fun r * x)
end prio

/-- Embedding `R →+* A` given by `algebra` structure. -/
def algebra_map (R : Type u) (A : Type v) [comm_semiring R] [semiring A] [algebra R A] : R →+* A :=
algebra.to_ring_hom

namespace algebra_map

def has_lift_t (R A : Type*) [comm_semiring R] [semiring A] [algebra R A] :
  has_lift_t R A := ⟨λ r, algebra_map R A r⟩

attribute [instance, priority 900] algebra_map.has_lift_t

section comm_semiring_semiring

variables {R A : Type*} [comm_semiring R] [semiring A] [algebra R A]

@[simp, norm_cast] lemma coe_zero : (↑(0 : R) : A) = 0 := map_zero (algebra_map R A)
@[simp, norm_cast] lemma coe_one : (↑(1 : R) : A) = 1 := map_one (algebra_map R A)
@[norm_cast] lemma coe_add (a b : R) : (↑(a + b : R) : A) = ↑a + ↑b :=
map_add (algebra_map R A) a b
@[norm_cast] lemma coe_mul (a b : R) : (↑(a * b : R) : A) = ↑a * ↑b :=
map_mul (algebra_map R A) a b
@[norm_cast] lemma coe_pow (a : R) (n : ℕ) : (↑(a ^ n : R) : A) = ↑a ^ n :=
map_pow (algebra_map R A) _ _

end comm_semiring_semiring

section comm_ring_ring

variables {R A : Type*} [comm_ring R] [ring A] [algebra R A]

@[norm_cast] lemma coe_neg (x : R) : (↑(-x : R) : A) = -↑x :=
map_neg (algebra_map R A) x

end comm_ring_ring

section comm_semiring_comm_semiring

variables {R A : Type*} [comm_semiring R] [comm_semiring A] [algebra R A]

open_locale big_operators

-- direct to_additive fails because of some mix-up with polynomials
@[norm_cast] lemma coe_prod {ι : Type*} {s : finset ι} (a : ι → R) :
  (↑( ∏ (i : ι) in s, a i : R) : A) = ∏ (i : ι) in s, (↑(a i) : A) :=
map_prod (algebra_map R A) a s

-- to_additive fails for some reason
@[norm_cast] lemma coe_sum {ι : Type*} {s : finset ι} (a : ι → R) :
  ↑(( ∑ (i : ι) in s, a i)) = ∑ (i : ι) in s, (↑(a i) : A) :=
map_sum (algebra_map R A) a s

attribute [to_additive] coe_prod

end comm_semiring_comm_semiring

section field_nontrivial
variables {R A : Type*} [field R] [comm_semiring A] [nontrivial A] [algebra R A]

@[norm_cast, simp] lemma coe_inj {a b : R} : (↑a : A) = ↑b ↔ a = b :=
(algebra_map R A).injective.eq_iff

@[norm_cast, simp] lemma lift_map_eq_zero_iff (a : R) : (↑a : A) = 0 ↔ a = 0 :=
map_eq_zero_iff _ (algebra_map R A).injective

end field_nontrivial

section semifield_semidivision_ring
variables {R : Type*} (A : Type*) [semifield R] [division_semiring A] [algebra R A]

@[norm_cast] lemma coe_inv (r : R) : ↑(r⁻¹) = ((↑r)⁻¹ : A) :=
map_inv₀ (algebra_map R A) r

@[norm_cast] lemma coe_div (r s : R) : ↑(r / s) = (↑r / ↑s : A) :=
map_div₀ (algebra_map R A) r s

@[norm_cast] lemma coe_zpow (r : R) (z : ℤ) : ↑(r ^ z) = (↑r ^ z : A) :=
map_zpow₀ (algebra_map R A) r z

end semifield_semidivision_ring

section field_division_ring
variables (R A : Type*) [field R] [division_ring A] [algebra R A]

@[norm_cast] lemma coe_rat_cast (q : ℚ) : ↑(q : R) = (q : A) :=
map_rat_cast (algebra_map R A) q

end field_division_ring

end algebra_map

/-- Creating an algebra from a morphism to the center of a semiring. -/
def ring_hom.to_algebra' {R S} [comm_semiring R] [semiring S] (i : R →+* S)
  (h : ∀ c x, i c * x = x * i c) :
  algebra R S :=
{ smul := λ c x, i c * x,
  commutes' := h,
  smul_def' := λ c x, rfl,
  to_ring_hom := i}

/-- Creating an algebra from a morphism to a commutative semiring. -/
def ring_hom.to_algebra {R S} [comm_semiring R] [comm_semiring S] (i : R →+* S) :
  algebra R S :=
i.to_algebra' $ λ _, mul_comm _

lemma ring_hom.algebra_map_to_algebra {R S} [comm_semiring R] [comm_semiring S]
  (i : R →+* S) :
  @algebra_map R S _ _ i.to_algebra = i :=
rfl

namespace algebra

variables {R : Type u} {S : Type v} {A : Type w} {B : Type*}

/-- Let `R` be a commutative semiring, let `A` be a semiring with a `module R` structure.
If `(r • 1) * x = x * (r • 1) = r • x` for all `r : R` and `x : A`, then `A` is an `algebra`
over `R`.

See note [reducible non-instances]. -/
@[reducible]
def of_module' [comm_semiring R] [semiring A] [module R A]
  (h₁ : ∀ (r : R) (x : A), (r • 1) * x = r • x)
  (h₂ : ∀ (r : R) (x : A), x * (r • 1) = r • x) : algebra R A :=
{ to_fun := λ r, r • 1,
  map_one' := one_smul _ _,
  map_mul' := λ r₁ r₂, by rw [h₁, mul_smul],
  map_zero' := zero_smul _ _,
  map_add' := λ r₁ r₂, add_smul r₁ r₂ 1,
  commutes' := λ r x, by simp only [h₁, h₂],
  smul_def' := λ r x, by simp only [h₁] }

/-- Let `R` be a commutative semiring, let `A` be a semiring with a `module R` structure.
If `(r • x) * y = x * (r • y) = r • (x * y)` for all `r : R` and `x y : A`, then `A`
is an `algebra` over `R`.

See note [reducible non-instances]. -/
@[reducible]
def of_module [comm_semiring R] [semiring A] [module R A]
  (h₁ : ∀ (r : R) (x y : A), (r • x) * y = r • (x * y))
  (h₂ : ∀ (r : R) (x y : A), x * (r • y) = r • (x * y)) : algebra R A :=
of_module' (λ r x, by rw [h₁, one_mul]) (λ r x, by rw [h₂, mul_one])

section semiring

variables [comm_semiring R] [comm_semiring S]
variables [semiring A] [algebra R A] [semiring B] [algebra R B]

/-- We keep this lemma private because it picks up the `algebra.to_has_smul` instance
which we set to priority 0 shortly. See `smul_def` below for the public version. -/
private lemma smul_def'' (r : R) (x : A) : r • x = algebra_map R A r * x :=
algebra.smul_def' r x

/--
To prove two algebra structures on a fixed `[comm_semiring R] [semiring A]` agree,
it suffices to check the `algebra_map`s agree.
-/
-- We'll later use this to show `algebra ℤ M` is a subsingleton.
@[ext]
lemma algebra_ext {R : Type*} [comm_semiring R] {A : Type*} [semiring A] (P Q : algebra R A)
  (w : ∀ (r : R), by { haveI := P, exact algebra_map R A r } =
    by { haveI := Q, exact algebra_map R A r }) :
  P = Q :=
begin
  unfreezingI { rcases P with @⟨⟨P⟩⟩, rcases Q with @⟨⟨Q⟩⟩ },
  congr,
  { funext r a,
    replace w := congr_arg (λ s, s * a) (w r),
    simp only [←smul_def''] at w,
    apply w, },
  { ext r,
    exact w r, },
  { apply proof_irrel_heq, },
  { apply proof_irrel_heq, },
end

@[priority 200] -- see Note [lower instance priority]
instance to_module : module R A :=
{ one_smul := by simp [smul_def''],
  mul_smul := by simp [smul_def'', mul_assoc],
  smul_add := by simp [smul_def'', mul_add],
  smul_zero := by simp [smul_def''],
  add_smul := by simp [smul_def'', add_mul],
  zero_smul := by simp [smul_def''] }

-- From now on, we don't want to use the following instance anymore.
-- Unfortunately, leaving it in place causes deterministic timeouts later in mathlib.
attribute [instance, priority 0] algebra.to_has_smul

lemma smul_def (r : R) (x : A) : r • x = algebra_map R A r * x :=
algebra.smul_def' r x

lemma algebra_map_eq_smul_one (r : R) : algebra_map R A r = r • 1 :=
calc algebra_map R A r = algebra_map R A r * 1 : (mul_one _).symm
                   ... = r • 1                 : (algebra.smul_def r 1).symm

lemma algebra_map_eq_smul_one' : ⇑(algebra_map R A) = λ r, r • (1 : A) :=
funext algebra_map_eq_smul_one

/-- `mul_comm` for `algebra`s when one element is from the base ring. -/
theorem commutes (r : R) (x : A) : algebra_map R A r * x = x * algebra_map R A r :=
algebra.commutes' r x

/-- `mul_left_comm` for `algebra`s when one element is from the base ring. -/
theorem left_comm (x : A) (r : R) (y : A) :
  x * (algebra_map R A r * y) = algebra_map R A r * (x * y) :=
by rw [← mul_assoc, ← commutes, mul_assoc]

/-- `mul_right_comm` for `algebra`s when one element is from the base ring. -/
theorem right_comm (x : A) (r : R) (y : A) :
  (x * algebra_map R A r) * y = (x * y) * algebra_map R A r :=
by rw [mul_assoc, commutes, ←mul_assoc]

instance _root_.is_scalar_tower.right : is_scalar_tower R A A :=
⟨λ x y z, by rw [smul_eq_mul, smul_eq_mul, smul_def, smul_def, mul_assoc]⟩

/-- This is just a special case of the global `mul_smul_comm` lemma that requires less typeclass
search (and was here first). -/
@[simp] protected lemma mul_smul_comm (s : R) (x y : A) :
  x * (s • y) = s • (x * y) :=
-- TODO: set up `is_scalar_tower.smul_comm_class` earlier so that we can actually prove this using
-- `mul_smul_comm s x y`.
by rw [smul_def, smul_def, left_comm]

/-- This is just a special case of the global `smul_mul_assoc` lemma that requires less typeclass
search (and was here first). -/
@[simp] protected lemma smul_mul_assoc (r : R) (x y : A) :
  (r • x) * y = r • (x * y) :=
smul_mul_assoc r x y

@[simp]
lemma _root_.smul_algebra_map {α : Type*} [monoid α] [mul_distrib_mul_action α A]
  [smul_comm_class α R A] (a : α) (r : R) : a • algebra_map R A r = algebra_map R A r :=
by rw [algebra_map_eq_smul_one, smul_comm a r (1 : A), smul_one]

section
variables {r : R} {a : A}

@[simp] lemma bit0_smul_one : bit0 r • (1 : A) = bit0 (r • (1 : A)) :=
by simp [bit0, add_smul]
lemma bit0_smul_one' : bit0 r • (1 : A) = r • 2 :=
by simp [bit0, add_smul, smul_add]
@[simp] lemma bit0_smul_bit0 : bit0 r • bit0 a = r • (bit0 (bit0 a)) :=
by simp [bit0, add_smul, smul_add]
@[simp] lemma bit0_smul_bit1 : bit0 r • bit1 a = r • (bit0 (bit1 a)) :=
by simp [bit0, add_smul, smul_add]
@[simp] lemma bit1_smul_one : bit1 r • (1 : A) = bit1 (r • (1 : A)) :=
by simp [bit1, add_smul]
lemma bit1_smul_one' : bit1 r • (1 : A) = r • 2 + 1 :=
by simp [bit1, bit0, add_smul, smul_add]
@[simp] lemma bit1_smul_bit0 : bit1 r • bit0 a = r • (bit0 (bit0 a)) + bit0 a :=
by simp [bit1, add_smul, smul_add]
@[simp] lemma bit1_smul_bit1 : bit1 r • bit1 a = r • (bit0 (bit1 a)) + bit1 a :=
by { simp only [bit0, bit1, add_smul, smul_add, one_smul], abel }

end

variables (R A)

/--
The canonical ring homomorphism `algebra_map R A : R →* A` for any `R`-algebra `A`,
packaged as an `R`-linear map.
-/
protected def linear_map : R →ₗ[R] A :=
{ map_smul' := λ x y, by simp [algebra.smul_def],
  ..algebra_map R A }

@[simp]
lemma linear_map_apply (r : R) : algebra.linear_map R A r = algebra_map R A r := rfl

lemma coe_linear_map : ⇑(algebra.linear_map R A) = algebra_map R A := rfl

instance id : algebra R R := (ring_hom.id R).to_algebra

variables {R A}

namespace id

@[simp] lemma map_eq_id : algebra_map R R = ring_hom.id _ := rfl

lemma map_eq_self (x : R) : algebra_map R R x = x := rfl

@[simp] lemma smul_eq_mul (x y : R) : x • y = x * y := rfl

end id

section punit

instance _root_.punit.algebra : algebra R punit :=
{ to_fun := λ x, punit.star,
  map_one' := rfl,
  map_mul' := λ _ _, rfl,
  map_zero' := rfl,
  map_add' := λ _ _, rfl,
  commutes' := λ _ _, rfl,
  smul_def' := λ _ _, rfl }

@[simp] lemma algebra_map_punit (r : R) : algebra_map R punit r = punit.star := rfl

end punit

section ulift

instance _root_.ulift.algebra : algebra R (ulift A) :=
{ to_fun := λ r, ulift.up (algebra_map R A r),
  commutes' := λ r x, ulift.down_injective $ algebra.commutes r x.down,
  smul_def' := λ r x, ulift.down_injective $ algebra.smul_def' r x.down,
  .. ulift.module',
  .. (ulift.ring_equiv : ulift A ≃+* A).symm.to_ring_hom.comp (algebra_map R A) }

lemma _root_.ulift.algebra_map_eq (r : R) :
  algebra_map R (ulift A) r = ulift.up (algebra_map R A r) := rfl

@[simp] lemma _root_.ulift.down_algebra_map (r : R) :
  (algebra_map R (ulift A) r).down = algebra_map R A r := rfl

end ulift

/-- Algebra over a subsemiring. This builds upon `subsemiring.module`. -/
instance of_subsemiring (S : subsemiring R) : algebra S A :=
{ smul := (•),
  commutes' := λ r x, algebra.commutes r x,
  smul_def' := λ r x, algebra.smul_def r x,
  .. (algebra_map R A).comp S.subtype }

lemma algebra_map_of_subsemiring (S : subsemiring R) :
  (algebra_map S R : S →+* R) = subsemiring.subtype S := rfl

lemma coe_algebra_map_of_subsemiring (S : subsemiring R) :
  (algebra_map S R : S → R) = subtype.val := rfl

lemma algebra_map_of_subsemiring_apply (S : subsemiring R) (x : S) :
  algebra_map S R x = x := rfl

/-- Algebra over a subring. This builds upon `subring.module`. -/
instance of_subring {R A : Type*} [comm_ring R] [ring A] [algebra R A]
  (S : subring R) : algebra S A :=
{ smul := (•),
  .. algebra.of_subsemiring S.to_subsemiring,
  .. (algebra_map R A).comp S.subtype }

lemma algebra_map_of_subring {R : Type*} [comm_ring R] (S : subring R) :
  (algebra_map S R : S →+* R) = subring.subtype S := rfl

lemma coe_algebra_map_of_subring {R : Type*} [comm_ring R] (S : subring R) :
  (algebra_map S R : S → R) = subtype.val := rfl

lemma algebra_map_of_subring_apply {R : Type*} [comm_ring R] (S : subring R) (x : S) :
  algebra_map S R x = x := rfl

/-- Explicit characterization of the submonoid map in the case of an algebra.
`S` is made explicit to help with type inference -/
def algebra_map_submonoid (S : Type*) [semiring S] [algebra R S]
  (M : submonoid R) : submonoid S :=
M.map (algebra_map R S)

lemma mem_algebra_map_submonoid_of_mem {S : Type*} [semiring S] [algebra R S] {M : submonoid R}
  (x : M) : (algebra_map R S x) ∈ algebra_map_submonoid S M :=
set.mem_image_of_mem (algebra_map R S) x.2

end semiring

section comm_semiring

variables [comm_semiring R]

lemma mul_sub_algebra_map_commutes [ring A] [algebra R A] (x : A) (r : R) :
  x * (x - algebra_map R A r) = (x - algebra_map R A r) * x :=
by rw [mul_sub, ←commutes, sub_mul]

lemma mul_sub_algebra_map_pow_commutes [ring A] [algebra R A] (x : A) (r : R) (n : ℕ) :
  x * (x - algebra_map R A r) ^ n = (x - algebra_map R A r) ^ n * x :=
begin
  induction n with n ih,
  { simp },
  { rw [pow_succ, ←mul_assoc, mul_sub_algebra_map_commutes, mul_assoc, ih, ←mul_assoc] }
end

end comm_semiring

section ring
variables [comm_ring R]

variables (R)

/-- A `semiring` that is an `algebra` over a commutative ring carries a natural `ring` structure.
See note [reducible non-instances]. -/
@[reducible]
def semiring_to_ring [semiring A] [algebra R A] : ring A :=
{ ..module.add_comm_monoid_to_add_comm_group R,
  ..(infer_instance : semiring A) }

end ring

end algebra

namespace mul_opposite

variables {R A : Type*} [comm_semiring R] [semiring A] [algebra R A]

instance : algebra R Aᵐᵒᵖ :=
{ to_ring_hom := (algebra_map R A).to_opposite $ λ x y, algebra.commutes _ _,
  smul_def' := λ c x, unop_injective $
    by { dsimp, simp only [op_mul, algebra.smul_def, algebra.commutes, op_unop] },
  commutes' := λ r, mul_opposite.rec $ λ x, by dsimp; simp only [← op_mul, algebra.commutes],
  .. mul_opposite.has_smul A R }

@[simp] lemma algebra_map_apply (c : R) : algebra_map R Aᵐᵒᵖ c = op (algebra_map R A c) := rfl

end mul_opposite

namespace module
variables (R : Type u) (M : Type v) [comm_semiring R] [add_comm_monoid M] [module R M]

instance : algebra R (module.End R M) :=
algebra.of_module smul_mul_assoc (λ r f g, (smul_comm r f g).symm)

lemma algebra_map_End_eq_smul_id (a : R) :
  (algebra_map R (End R M)) a = a • linear_map.id := rfl

@[simp] lemma algebra_map_End_apply (a : R) (m : M) :
  (algebra_map R (End R M)) a m = a • m := rfl

@[simp] lemma ker_algebra_map_End (K : Type u) (V : Type v)
  [field K] [add_comm_group V] [module K V] (a : K) (ha : a ≠ 0) :
  ((algebra_map K (End K V)) a).ker = ⊥ :=
linear_map.ker_smul _ _ ha

section

variables {R M}

lemma End_is_unit_apply_inv_apply_of_is_unit {f : module.End R M} (h : is_unit f) (x : M) :
  f (h.unit.inv x) = x :=
show (f * h.unit.inv) x = x, by simp

lemma End_is_unit_inv_apply_apply_of_is_unit {f : module.End R M} (h : is_unit f) (x : M) :
  h.unit.inv (f x) = x :=
(by simp : (h.unit.inv * f) x = x)

lemma End_is_unit_iff (f : module.End R M) :
  is_unit f ↔ function.bijective f :=
⟨λ h, function.bijective_iff_has_inverse.mpr $
  ⟨h.unit.inv, ⟨End_is_unit_inv_apply_apply_of_is_unit h,
    End_is_unit_apply_inv_apply_of_is_unit h⟩⟩,
 λ H, let e : M ≃ₗ[R] M := { ..f, ..(equiv.of_bijective f H)} in
  ⟨⟨_, e.symm, linear_map.ext e.right_inv, linear_map.ext e.left_inv⟩, rfl⟩⟩

lemma End_algebra_map_is_unit_inv_apply_eq_iff
  {x : R} (h : is_unit (algebra_map R (module.End R M) x)) (m m' : M) :
  h.unit⁻¹ m = m' ↔ m = x • m' :=
{ mp := λ H, ((congr_arg h.unit H).symm.trans (End_is_unit_apply_inv_apply_of_is_unit h _)).symm,
  mpr := λ H, H.symm ▸
  begin
    apply_fun h.unit using ((module.End_is_unit_iff _).mp h).injective,
    erw [End_is_unit_apply_inv_apply_of_is_unit],
    refl,
  end }

lemma End_algebra_map_is_unit_inv_apply_eq_iff'
  {x : R} (h : is_unit (algebra_map R (module.End R M) x)) (m m' : M) :
  m' = h.unit⁻¹ m ↔ m = x • m' :=
{ mp := λ H, ((congr_arg h.unit H).trans (End_is_unit_apply_inv_apply_of_is_unit h _)).symm,
  mpr := λ H, H.symm ▸
  begin
    apply_fun h.unit using ((module.End_is_unit_iff _).mp h).injective,
    erw [End_is_unit_apply_inv_apply_of_is_unit],
    refl,
  end }

end

end module

namespace linear_map

variables {R : Type*} {A : Type*} {B : Type*} [comm_semiring R] [semiring A] [semiring B]
  [algebra R A] [algebra R B]

/-- An alternate statement of `linear_map.map_smul` for when `algebra_map` is more convenient to
work with than `•`. -/
lemma map_algebra_map_mul (f : A →ₗ[R] B) (a : A) (r : R) :
  f (algebra_map R A r * a) = algebra_map R B r * f a :=
by rw [←algebra.smul_def, ←algebra.smul_def, map_smul]

lemma map_mul_algebra_map (f : A →ₗ[R] B) (a : A) (r : R) :
  f (a * algebra_map R A r) = f a * algebra_map R B r :=
by rw [←algebra.commutes, ←algebra.commutes, map_algebra_map_mul]

end linear_map


@[simp] lemma rat.smul_one_eq_coe {A : Type*} [division_ring A] [algebra ℚ A] (m : ℚ) :
  @@has_smul.smul algebra.to_has_smul m (1 : A) = ↑m :=
by rw [algebra.smul_def, mul_one, eq_rat_cast]


section nat

variables {R : Type*} [semiring R]

-- Lower the priority so that `algebra.id` is picked most of the time when working with
-- `ℕ`-algebras. This is only an issue since `algebra.id` and `algebra_nat` are not yet defeq.
-- TODO: fix this by adding an `of_nat` field to semirings.
/-- Semiring ⥤ ℕ-Alg -/
@[priority 99] instance algebra_nat : algebra ℕ R :=
{ commutes' := nat.cast_commute,
  smul_def' := λ _ _, nsmul_eq_mul _ _,
  to_ring_hom := nat.cast_ring_hom R }

instance nat_algebra_subsingleton : subsingleton (algebra ℕ R) :=
⟨λ P Q, by { ext, simp, }⟩

end nat

namespace ring_hom

variables {R S : Type*}

-- note that `R`, `S` could be `semiring`s but this is useless mathematically speaking -
-- a ℚ-algebra is a ring. furthermore, this change probably slows down elaboration.
@[simp] lemma map_rat_algebra_map [ring R] [ring S] [algebra ℚ R] [algebra ℚ S]
  (f : R →+* S) (r : ℚ) : f (algebra_map ℚ R r) = algebra_map ℚ S r :=
ring_hom.ext_iff.1 (subsingleton.elim (f.comp (algebra_map ℚ R)) (algebra_map ℚ S)) r

end ring_hom

section rat

instance algebra_rat {α} [division_ring α] [char_zero α] : algebra ℚ α :=
{ smul := (•),
  smul_def' := division_ring.qsmul_eq_mul',
  to_ring_hom := rat.cast_hom α,
  commutes' := rat.cast_commute }

/-- The two `algebra ℚ ℚ` instances should coincide. -/
example : algebra_rat = algebra.id ℚ := rfl

@[simp] theorem algebra_map_rat_rat : algebra_map ℚ ℚ = ring_hom.id ℚ :=
subsingleton.elim _ _

instance algebra_rat_subsingleton {α} [semiring α] :
  subsingleton (algebra ℚ α) :=
⟨λ x y, algebra.algebra_ext x y $ ring_hom.congr_fun $ subsingleton.elim _ _⟩

end rat

section int

variables (R : Type*) [ring R]

-- Lower the priority so that `algebra.id` is picked most of the time when working with
-- `ℤ`-algebras. This is only an issue since `algebra.id ℤ` and `algebra_int ℤ` are not yet defeq.
-- TODO: fix this by adding an `of_int` field to rings.
/-- Ring ⥤ ℤ-Alg -/
@[priority 99] instance algebra_int : algebra ℤ R :=
{ commutes' := int.cast_commute,
  smul_def' := λ _ _, zsmul_eq_mul _ _,
  to_ring_hom := int.cast_ring_hom R }

/-- A special case of `eq_int_cast'` that happens to be true definitionally -/
@[simp] lemma algebra_map_int_eq : algebra_map ℤ R = int.cast_ring_hom R := rfl

variables {R}

instance int_algebra_subsingleton : subsingleton (algebra ℤ R) :=
⟨λ P Q, by { ext, simp, }⟩

end int

namespace no_zero_smul_divisors

variables {R A : Type*}

open algebra

/-- If `algebra_map R A` is injective and `A` has no zero divisors,
`R`-multiples in `A` are zero only if one of the factors is zero.

Cannot be an instance because there is no `injective (algebra_map R A)` typeclass.
-/
lemma of_algebra_map_injective
  [comm_semiring R] [semiring A] [algebra R A] [no_zero_divisors A]
  (h : function.injective (algebra_map R A)) : no_zero_smul_divisors R A :=
⟨λ c x hcx, (mul_eq_zero.mp ((smul_def c x).symm.trans hcx)).imp_left
  (map_eq_zero_iff (algebra_map R A) h).mp⟩

variables (R A)
lemma algebra_map_injective [comm_ring R] [ring A] [nontrivial A]
  [algebra R A] [no_zero_smul_divisors R A] :
  function.injective (algebra_map R A) :=
suffices function.injective (λ (c : R), c • (1 : A)),
by { convert this, ext, rw [algebra.smul_def, mul_one] },
smul_left_injective R one_ne_zero

lemma _root_.ne_zero.of_no_zero_smul_divisors (n : ℕ) [comm_ring R] [ne_zero (n : R)] [ring A]
  [nontrivial A] [algebra R A] [no_zero_smul_divisors R A] : ne_zero (n : A) :=
ne_zero.nat_of_injective $ no_zero_smul_divisors.algebra_map_injective R A

variables {R A}
lemma iff_algebra_map_injective [comm_ring R] [ring A] [is_domain A] [algebra R A] :
  no_zero_smul_divisors R A ↔ function.injective (algebra_map R A) :=
⟨@@no_zero_smul_divisors.algebra_map_injective R A _ _ _ _,
 no_zero_smul_divisors.of_algebra_map_injective⟩

@[priority 100] -- see note [lower instance priority]
instance char_zero.no_zero_smul_divisors_nat [semiring R] [no_zero_divisors R] [char_zero R] :
  no_zero_smul_divisors ℕ R :=
no_zero_smul_divisors.of_algebra_map_injective $ (algebra_map ℕ R).injective_nat

@[priority 100] -- see note [lower instance priority]
instance char_zero.no_zero_smul_divisors_int [ring R] [no_zero_divisors R] [char_zero R] :
  no_zero_smul_divisors ℤ R :=
no_zero_smul_divisors.of_algebra_map_injective $ (algebra_map ℤ R).injective_int

section field

variables [field R] [semiring A] [algebra R A]

@[priority 100] -- see note [lower instance priority]
instance algebra.no_zero_smul_divisors [nontrivial A] [no_zero_divisors A] :
  no_zero_smul_divisors R A :=
no_zero_smul_divisors.of_algebra_map_injective (algebra_map R A).injective

end field

end no_zero_smul_divisors

section is_scalar_tower

variables {R : Type*} [comm_semiring R]
variables (A : Type*) [semiring A] [algebra R A]
variables {M : Type*} [add_comm_monoid M] [module A M] [module R M] [is_scalar_tower R A M]
variables {N : Type*} [add_comm_monoid N] [module A N] [module R N] [is_scalar_tower R A N]

lemma algebra_compatible_smul (r : R) (m : M) : r • m = ((algebra_map R A) r) • m :=
by rw [←(one_smul A m), ←smul_assoc, algebra.smul_def, mul_one, one_smul]

@[simp] lemma algebra_map_smul (r : R) (m : M) : ((algebra_map R A) r) • m = r • m :=
(algebra_compatible_smul A r m).symm

lemma int_cast_smul {k V : Type*} [comm_ring k] [add_comm_group V] [module k V] (r : ℤ) (x : V) :
  (r : k) • x = r • x :=
algebra_map_smul k r x

lemma no_zero_smul_divisors.trans (R A M : Type*) [comm_ring R] [ring A] [is_domain A] [algebra R A]
  [add_comm_group M] [module R M] [module A M] [is_scalar_tower R A M] [no_zero_smul_divisors R A]
  [no_zero_smul_divisors A M] : no_zero_smul_divisors R M :=
begin
  refine ⟨λ r m h, _⟩,
  rw [algebra_compatible_smul A r m] at h,
  cases smul_eq_zero.1 h with H H,
  { have : function.injective (algebra_map R A) :=
      no_zero_smul_divisors.iff_algebra_map_injective.1 infer_instance,
    left,
    exact (injective_iff_map_eq_zero _).1 this _ H },
  { right,
    exact H }
end

variable {A}

@[priority 100] -- see Note [lower instance priority]
instance is_scalar_tower.to_smul_comm_class : smul_comm_class R A M :=
⟨λ r a m, by rw [algebra_compatible_smul A r (a • m), smul_smul, algebra.commutes, mul_smul,
  ←algebra_compatible_smul]⟩

@[priority 100] -- see Note [lower instance priority]
instance is_scalar_tower.to_smul_comm_class' : smul_comm_class A R M :=
smul_comm_class.symm _ _ _

lemma smul_algebra_smul_comm (r : R) (a : A) (m : M) : a • r • m = r • a • m :=
smul_comm _ _ _

namespace linear_map

instance coe_is_scalar_tower : has_coe (M →ₗ[A] N) (M →ₗ[R] N) :=
⟨restrict_scalars R⟩

variables (R) {A M N}

@[simp, norm_cast squash] lemma coe_restrict_scalars_eq_coe (f : M →ₗ[A] N) :
  (f.restrict_scalars R : M → N) = f := rfl

@[simp, norm_cast squash] lemma coe_coe_is_scalar_tower (f : M →ₗ[A] N) :
  ((f : M →ₗ[R] N) : M → N) = f := rfl

/-- `A`-linearly coerce a `R`-linear map from `M` to `A` to a function, given an algebra `A` over
a commutative semiring `R` and `M` a module over `R`. -/
def lto_fun (R : Type u) (M : Type v) (A : Type w)
  [comm_semiring R] [add_comm_monoid M] [module R M] [comm_ring A] [algebra R A] :
  (M →ₗ[R] A) →ₗ[A] (M → A) :=
{ to_fun := linear_map.to_fun,
  map_add' := λ f g, rfl,
  map_smul' := λ c f, rfl }

end linear_map

end is_scalar_tower

/-! TODO: The following lemmas no longer involve `algebra` at all, and could be moved closer
to `algebra/module/submodule.lean`. Currently this is tricky because `ker`, `range`, `⊤`, and `⊥`
are all defined in `linear_algebra/basic.lean`. -/
section module
open module

variables (R S M N : Type*) [semiring R] [semiring S] [has_smul R S]
variables [add_comm_monoid M] [module R M] [module S M] [is_scalar_tower R S M]
variables [add_comm_monoid N] [module R N] [module S N] [is_scalar_tower R S N]

variables {S M N}

@[simp]
lemma linear_map.ker_restrict_scalars (f : M →ₗ[S] N) :
  (f.restrict_scalars R).ker = f.ker.restrict_scalars R :=
rfl

end module

example {R A} [comm_semiring R] [semiring A]
  [module R A] [smul_comm_class R A A] [is_scalar_tower R A A] : algebra R A :=
algebra.of_module smul_mul_assoc mul_smul_comm
