/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.group.inj_surj
import algebra.group_power.basic
import data.set_like.basic
import data.sigma.basic
import group_theory.group_action.defs

/-!
# Additively-graded multiplicative structures

This module provides a set of heterogeneous typeclasses for defining a multiplicative structure
over the sigma type `graded_monoid A` such that `(*) : A i → A j → A (i + j)`; that is to say, `A`
forms an additively-graded monoid. The typeclasses are:

* `graded_monoid.ghas_one A`
* `graded_monoid.ghas_mul A`
* `graded_monoid.gmonoid A`
* `graded_monoid.gcomm_monoid A`

With the `sigma_graded` locale open, these respectively imbue:

* `has_one (graded_monoid A)`
* `has_mul (graded_monoid A)`
* `monoid (graded_monoid A)`
* `comm_monoid (graded_monoid A)`

the base type `A 0` with:

* `graded_monoid.grade_zero.has_one`
* `graded_monoid.grade_zero.has_mul`
* `graded_monoid.grade_zero.monoid`
* `graded_monoid.grade_zero.comm_monoid`

and the `i`th grade `A i` with `A 0`-actions (`•`) defined as left-multiplication:

* (nothing)
* `graded_monoid.grade_zero.has_scalar (A 0)`
* `graded_monoid.grade_zero.mul_action (A 0)`
* (nothing)

For now, these typeclasses are primarily used in the construction of `direct_sum.ring` and the rest
of that file.

## Indexed subobjects

Additionally, this module provides helper functions to construct `gmonoid` and `gcomm_monoid`
instances for collections of subobjects:

* `ghas_one.of_add_subobjects`
* `ghas_mul.of_add_subobjects`
* `gmonoid.of_add_subobjects`
* `gcomm_monoid.of_add_subobjects`

## tags

graded monoid
-/

set_option old_structure_cmd true

variables {ι : Type*}

/-- A type alias of sigma types for graded monoids. -/
def graded_monoid (A : ι → Type*) := sigma A

namespace graded_monoid

instance {A : ι → Type*} [inhabited ι] [inhabited (A (default ι))]: inhabited (graded_monoid A) :=
sigma.inhabited

/-- Construct an element of a graded monoid. -/
def mk {A : ι → Type*} : Π i, A i → graded_monoid A := sigma.mk

/-! ### Typeclasses -/
section defs

variables (A : ι → Type*)

/-- A graded version of `has_one`, which must be of grade 0. -/
class ghas_one [has_zero ι] :=
(one : A 0)

/-- `ghas_one` implies `has_one (graded_monoid A)` -/
instance ghas_one.to_has_one [has_zero ι] [ghas_one A] : has_one (graded_monoid A) :=
⟨⟨_, ghas_one.one⟩⟩

/-- A graded version of `has_mul`. Multiplication combines grades additively, like
`add_monoid_algebra`. -/
class ghas_mul [has_add ι] :=
(mul {i j} : A i → A j → A (i + j))

/-- `ghas_mul` implies `has_mul (graded_monoid A)`. -/
instance ghas_mul.to_has_mul [has_add ι] [ghas_mul A] :
  has_mul (graded_monoid A) :=
⟨λ (x y : graded_monoid A), ⟨_, ghas_mul.mul x.snd y.snd⟩⟩

lemma mk_mul_mk [has_add ι] [ghas_mul A] {i j} (a : A i) (b : A j) :
  mk i a * mk j b = mk (i + j) (ghas_mul.mul a b) :=
rfl

namespace gmonoid

variables {A} [add_monoid ι] [ghas_mul A] [ghas_one A]

/-- A default implementation of power on a graded monoid, like `npow_rec`.
`gmonoid.gnpow` should be used instead. -/
def gnpow_rec : Π (n : ℕ) {i}, A i → A (n • i)
| 0 i a := cast (congr_arg A (zero_nsmul i).symm) ghas_one.one
| (n + 1) i a := cast (congr_arg A (succ_nsmul i n).symm) (ghas_mul.mul a $ gnpow_rec _ a)

@[simp] lemma gnpow_rec_zero (a : graded_monoid A) : graded_monoid.mk _ (gnpow_rec 0 a.snd) = 1 :=
sigma.ext (zero_nsmul _) (heq_of_cast_eq _ rfl).symm

/-- Tactic used to autofill `graded_monoid.gmonoid.gnpow_zero'` when the default
`graded_monoid.gmonoid.gnpow_rec` is used. -/
meta def apply_gnpow_rec_zero_tac : tactic unit := `[apply direct_sum.gmonoid.gnpow_rec_zero]

@[simp] lemma gnpow_rec_succ (n : ℕ) (a : graded_monoid A) :
  (graded_monoid.mk _ $ gnpow_rec n.succ a.snd) = a * ⟨_, gnpow_rec n a.snd⟩ :=
sigma.ext (succ_nsmul _ _) (heq_of_cast_eq _ rfl).symm

/-- Tactic used to autofill `graded_monoid.gmonoid.gnpow_succ'` when the default
`graded_monoid.gmonoid.gnpow_rec` is used. -/
meta def apply_gnpow_rec_succ_tac : tactic unit := `[apply direct_sum.gmonoid.gnpow_rec_succ]

end gmonoid

/-- A graded version of `monoid`.

Like `monoid.npow`, this has an optional `gmonoid.gnpow` field to allow definitional control of
natural powers of a graded monoid. -/
class gmonoid [add_monoid ι]  extends ghas_mul A, ghas_one A :=
(one_mul (a : graded_monoid A) : 1 * a = a)
(mul_one (a : graded_monoid A) : a * 1 = a)
(mul_assoc (a b c : graded_monoid A) : a * b * c = a * (b * c))
(gnpow : Π (n : ℕ) {i}, A i → A (n • i) := gmonoid.gnpow_rec)
(gnpow_zero' : Π (a : graded_monoid A), graded_monoid.mk _ (gnpow 0 a.snd) = 1
  . gmonoid.apply_gnpow_rec_zero_tac)
(gnpow_succ' : Π (n : ℕ) (a : graded_monoid A),
  (graded_monoid.mk _ $ gnpow n.succ a.snd) = a * ⟨_, gnpow n a.snd⟩
  . gmonoid.apply_gnpow_rec_succ_tac)

/-- `gmonoid` implies a `monoid (graded_monoid A)`. -/
instance gmonoid.to_monoid [add_monoid ι] [gmonoid A] :
  monoid (graded_monoid A) :=
{ one := (1), mul := (*),
  npow := λ n a, graded_monoid.mk _ (gmonoid.gnpow n a.snd),
  npow_zero' := λ a, gmonoid.gnpow_zero' a,
  npow_succ' := λ n a, gmonoid.gnpow_succ' n a,
  one_mul := gmonoid.one_mul, mul_one := gmonoid.mul_one, mul_assoc := gmonoid.mul_assoc }

lemma mk_pow [add_monoid ι] [gmonoid A] {i} (a : A i) (n : ℕ) :
  mk i a ^ n = mk (n • i) (gmonoid.gnpow _ a) :=
begin
  induction n with n,
  { rw [pow_zero],
    exact (gmonoid.gnpow_zero' ⟨_, a⟩).symm, },
  { rw [pow_succ, n_ih, mk_mul_mk],
    exact (gmonoid.gnpow_succ' n ⟨_, a⟩).symm, },
end

/-- A graded version of `comm_monoid`. -/
class gcomm_monoid [add_comm_monoid ι] extends gmonoid A :=
(mul_comm (a : graded_monoid A) (b : graded_monoid A) : a * b = b * a)

/-- `gcomm_monoid` implies a `comm_monoid (graded_monoid A)`, although this is only used as an
instance locally to define notation in `gmonoid` and similar typeclasses. -/
instance gcomm_monoid.to_comm_monoid [add_comm_monoid ι] [gcomm_monoid A] :
  comm_monoid (graded_monoid A) :=
{ mul_comm := gcomm_monoid.mul_comm, ..gmonoid.to_monoid A }

end defs


/-! ### Instances for `A 0`

The various `g*` instances are enough to promote the `add_comm_monoid (A 0)` structure to various
types of multiplicative structure.
-/

section grade_zero

variables (A : ι → Type*)

section one
variables [has_zero ι] [ghas_one A]

/-- `1 : A 0` is the value provided in `ghas_one.one`. -/
@[nolint unused_arguments]
instance grade_zero.has_one : has_one (A 0) :=
⟨ghas_one.one⟩

end one

section mul
variables [add_monoid ι] [ghas_mul A]

/-- `(•) : A 0 → A i → A i` is the value provided in `direct_sum.ghas_mul.mul`, composed with
an `eq.rec` to turn `A (0 + i)` into `A i`.
-/
instance grade_zero.has_scalar (i : ι) : has_scalar (A 0) (A i) :=
{ smul := λ x y, (zero_add i).rec (ghas_mul.mul x y) }

/-- `(*) : A 0 → A 0 → A 0` is the value provided in `direct_sum.ghas_mul.mul`, composed with
an `eq.rec` to turn `A (0 + 0)` into `A 0`.
-/
instance grade_zero.has_mul : has_mul (A 0) :=
{ mul := (•) }

variables {A}

@[simp] lemma mk_zero_smul {i} (a : A 0) (b : A i) : mk _ (a • b) = mk _ a * mk _ b :=
sigma.ext (zero_add _).symm $ eq_rec_heq _ _

@[simp] lemma grade_zero.smul_eq_mul (a b : A 0) : a • b = a * b := rfl


end mul

section monoid
variables [add_monoid ι] [gmonoid A]

/-- The `monoid` structure derived from `gmonoid A`. -/
instance grade_zero.monoid : monoid (A 0) :=
function.injective.monoid (mk 0) sigma_mk_injective rfl mk_zero_smul

end monoid

section monoid
variables [add_comm_monoid ι] [gcomm_monoid A]

/-- The `comm_monoid` structure derived from `gcomm_monoid A`. -/
instance grade_zero.comm_monoid : comm_monoid (A 0) :=
function.injective.comm_monoid (mk 0) sigma_mk_injective rfl mk_zero_smul

end monoid

section mul_action
variables [add_monoid ι] [gmonoid A]

/-- `graded_monoid.mk 0` is a `monoid_hom`, using the `graded_monoid.grade_zero.monoid` structure.
-/
def mk_zero_monoid_hom : A 0 →* (graded_monoid A) :=
{ to_fun := mk 0, map_one' := rfl, map_mul' := mk_zero_smul }

/-- Each grade `A i` derives a `A 0`-action structure from `gmonoid A`. -/
instance grade_zero.mul_action {i} : mul_action (A 0) (A i) :=
begin
  letI := mul_action.comp_hom (graded_monoid A) (mk_zero_monoid_hom A),
  exact function.injective.mul_action (mk i) sigma_mk_injective mk_zero_smul,
end

end mul_action


end grade_zero

/-! ### Shorthands for creating instance of the above typeclasses for collections of subobjects -/

section subobjects

variables {R : Type*}

/-- Build a `ghas_one` instance for a collection of subobjects. -/
@[simps one]
def ghas_one.of_subobjects {S : Type*} [set_like S R] [has_one R] [has_zero ι]
  (carriers : ι → S)
  (one_mem : (1 : R) ∈ carriers 0) :
  ghas_one (λ i, carriers i) :=
{ one := ⟨1, one_mem⟩ }

/-- Build a `ghas_mul` instance for a collection of subobjects. -/
@[simps mul]
def ghas_mul.of_subobjects {S : Type*} [set_like S R] [has_mul R] [has_add ι]
  (carriers : ι → S)
  (mul_mem : ∀ ⦃i j⦄ (gi : carriers i) (gj : carriers j), (gi * gj : R) ∈ carriers (i + j)) :
  ghas_mul (λ i, carriers i) :=
{ mul := λ i j a b, ⟨(a * b : R), mul_mem a b⟩ }

/-- Build a `gmonoid` instance for a collection of subobjects.

See note [reducible non-instances]. -/
@[reducible]
def gmonoid.of_subobjects {S : Type*} [set_like S R] [monoid R] [add_monoid ι]
  (carriers : ι → S)
  (one_mem : (1 : R) ∈ carriers 0)
  (mul_mem : ∀ ⦃i j⦄ (gi : carriers i) (gj : carriers j), (gi * gj : R) ∈ carriers (i + j)) :
  gmonoid (λ i, carriers i) :=
{ one_mul := λ ⟨i, a, h⟩, sigma.subtype_ext (zero_add _) (one_mul _),
  mul_one := λ ⟨i, a, h⟩, sigma.subtype_ext (add_zero _) (mul_one _),
  mul_assoc := λ ⟨i, a, ha⟩ ⟨j, b, hb⟩ ⟨k, c, hc⟩,
    sigma.subtype_ext (add_assoc _ _ _) (mul_assoc _ _ _),
  gnpow := λ n i a, ⟨a ^ n, begin
    induction n,
    { rw [pow_zero, zero_nsmul], exact one_mem },
    { rw [pow_succ', succ_nsmul'], exact mul_mem ⟨_, n_ih⟩ a },
  end⟩,
  gnpow_zero' := λ n, sigma.subtype_ext (zero_nsmul _) (pow_zero _),
  gnpow_succ' := λ n a, sigma.subtype_ext (succ_nsmul _ _) (pow_succ _ _),
  ..ghas_one.of_subobjects carriers one_mem,
  ..ghas_mul.of_subobjects carriers mul_mem }

/-- Build a `gcomm_monoid` instance for a collection of subobjects.

See note [reducible non-instances]. -/
@[reducible]
def gcomm_monoid.of_subobjects {S : Type*} [set_like S R] [comm_monoid R] [add_comm_monoid ι]
  (carriers : ι → S)
  (one_mem : (1 : R) ∈ carriers 0)
  (mul_mem : ∀ ⦃i j⦄ (gi : carriers i) (gj : carriers j), (gi * gj : R) ∈ carriers (i + j)) :
  gcomm_monoid (λ i, carriers i) :=
{ mul_comm := λ ⟨i, a, ha⟩ ⟨j, b, hb⟩, sigma.subtype_ext (add_comm _ _) (mul_comm _ _),
  ..gmonoid.of_subobjects carriers one_mem mul_mem}

end subobjects

end graded_monoid

/-! ### Concrete instances -/
section

variables (ι) {R : Type*}

@[simps one]
instance has_one.ghas_one [has_zero ι] [has_one R] : graded_monoid.ghas_one (λ i : ι, R) :=
{ one := 1 }

@[simps mul]
instance has_mul.ghas_mul [has_add ι] [has_mul R] : graded_monoid.ghas_mul (λ i : ι, R) :=
{ mul := λ i j, (*) }

/-- If all grades are the same type and themselves form a monoid, then there is a trivial grading
structure. -/
@[simps gnpow]
instance monoid.gmonoid [add_monoid ι] [monoid R] : graded_monoid.gmonoid (λ i : ι, R) :=
{ one_mul := λ a, sigma.ext (zero_add _) (heq_of_eq (one_mul _)),
  mul_one := λ a, sigma.ext (add_zero _) (heq_of_eq (mul_one _)),
  mul_assoc := λ a b c, sigma.ext (add_assoc _ _ _) (heq_of_eq (mul_assoc _ _ _)),
  gnpow := λ n i a, a ^ n,
  gnpow_zero' := λ a, sigma.ext (zero_nsmul _) (heq_of_eq (monoid.npow_zero' _)),
  gnpow_succ' := λ n ⟨i, a⟩, sigma.ext (succ_nsmul _ _) (heq_of_eq (monoid.npow_succ' _ _)),
  ..has_one.ghas_one ι,
  ..has_mul.ghas_mul ι }

/-- If all grades are the same type and themselves form a commutative monoid, then there is a
trivial grading structure. -/
instance comm_monoid.gcomm_monoid [add_comm_monoid ι] [comm_monoid R] :
  graded_monoid.gcomm_monoid (λ i : ι, R) :=
{ mul_comm := λ a b, sigma.ext (add_comm _ _) (heq_of_eq (mul_comm _ _)),
  ..monoid.gmonoid ι }

end
