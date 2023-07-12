/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.group.inj_surj
import data.list.big_operators.basic
import data.list.fin_range
import group_theory.group_action.defs
import group_theory.submonoid.basic
import data.set_like.basic
import data.sigma.basic

/-!
# Additively-graded multiplicative structures

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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
* `graded_monoid.grade_zero.has_smul (A 0)`
* `graded_monoid.grade_zero.mul_action (A 0)`
* (nothing)

For now, these typeclasses are primarily used in the construction of `direct_sum.ring` and the rest
of that file.

## Dependent graded products

This also introduces `list.dprod`, which takes the (possibly non-commutative) product of a list
of graded elements of type `A i`. This definition primarily exist to allow `graded_monoid.mk`
and `direct_sum.of` to be pulled outside a product, such as in `graded_monoid.mk_list_dprod` and
`direct_sum.of_list_dprod`.

## Internally graded monoids

In addition to the above typeclasses, in the most frequent case when `A` is an indexed collection of
`set_like` subobjects (such as `add_submonoid`s, `add_subgroup`s, or `submodule`s), this file
provides the `Prop` typeclasses:

* `set_like.has_graded_one A` (which provides the obvious `graded_monoid.ghas_one A` instance)
* `set_like.has_graded_mul A` (which provides the obvious `graded_monoid.ghas_mul A` instance)
* `set_like.graded_monoid A` (which provides the obvious `graded_monoid.gmonoid A` and
  `graded_monoid.gcomm_monoid A` instances)

which respectively provide the API lemmas

* `set_like.one_mem_graded`
* `set_like.mul_mem_graded`
* `set_like.pow_mem_graded`, `set_like.list_prod_map_mem_graded`

Strictly this last class is unecessary as it has no fields not present in its parents, but it is
included for convenience. Note that there is no need for `set_like.graded_ring` or similar, as all
the information it would contain is already supplied by `graded_monoid` when `A` is a collection
of objects satisfying `add_submonoid_class` such as `submodule`s. These constructions are explored
in `algebra.direct_sum.internal`.

This file also defines:

* `set_like.is_homogeneous A` (which says that `a` is homogeneous iff `a ∈ A i` for some `i : ι`)
* `set_like.homogeneous_submonoid A`, which is, as the name suggests, the submonoid consisting of
  all the homogeneous elements.

## tags

graded monoid
-/

set_option old_structure_cmd true

variables {ι : Type*}

/-- A type alias of sigma types for graded monoids. -/
def graded_monoid (A : ι → Type*) := sigma A

namespace graded_monoid

instance {A : ι → Type*} [inhabited ι] [inhabited (A default)]: inhabited (graded_monoid A) :=
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
meta def apply_gnpow_rec_zero_tac : tactic unit := `[apply graded_monoid.gmonoid.gnpow_rec_zero]

@[simp] lemma gnpow_rec_succ (n : ℕ) (a : graded_monoid A) :
  (graded_monoid.mk _ $ gnpow_rec n.succ a.snd) = a * ⟨_, gnpow_rec n a.snd⟩ :=
sigma.ext (succ_nsmul _ _) (heq_of_cast_eq _ rfl).symm

/-- Tactic used to autofill `graded_monoid.gmonoid.gnpow_succ'` when the default
`graded_monoid.gmonoid.gnpow_rec` is used. -/
meta def apply_gnpow_rec_succ_tac : tactic unit := `[apply graded_monoid.gmonoid.gnpow_rec_succ]

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
variables [add_zero_class ι] [ghas_mul A]

/-- `(•) : A 0 → A i → A i` is the value provided in `graded_monoid.ghas_mul.mul`, composed with
an `eq.rec` to turn `A (0 + i)` into `A i`.
-/
instance grade_zero.has_smul (i : ι) : has_smul (A 0) (A i) :=
{ smul := λ x y, (zero_add i).rec (ghas_mul.mul x y) }

/-- `(*) : A 0 → A 0 → A 0` is the value provided in `graded_monoid.ghas_mul.mul`, composed with
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

instance : has_pow (A 0) ℕ :=
{ pow := λ x n, (nsmul_zero n).rec (gmonoid.gnpow n x : A (n • 0)) }

variables {A}

@[simp] lemma mk_zero_pow (a : A 0) (n : ℕ) : mk _ (a ^ n) = mk _ a ^ n :=
sigma.ext (nsmul_zero n).symm $ eq_rec_heq _ _

variables (A)

/-- The `monoid` structure derived from `gmonoid A`. -/
instance grade_zero.monoid : monoid (A 0) :=
function.injective.monoid (mk 0) sigma_mk_injective rfl mk_zero_smul mk_zero_pow

end monoid

section monoid
variables [add_comm_monoid ι] [gcomm_monoid A]

/-- The `comm_monoid` structure derived from `gcomm_monoid A`. -/
instance grade_zero.comm_monoid : comm_monoid (A 0) :=
function.injective.comm_monoid (mk 0) sigma_mk_injective rfl mk_zero_smul mk_zero_pow

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

end graded_monoid

/-! ### Dependent products of graded elements -/

section dprod

variables {α : Type*} {A : ι → Type*} [add_monoid ι] [graded_monoid.gmonoid A]

/-- The index used by `list.dprod`. Propositionally this is equal to `(l.map fι).sum`, but
definitionally it needs to have a different form to avoid introducing `eq.rec`s in `list.dprod`. -/
def list.dprod_index (l : list α) (fι : α → ι) : ι :=
l.foldr (λ i b, fι i + b) 0

@[simp] lemma list.dprod_index_nil (fι : α → ι) : ([] : list α).dprod_index fι = 0 := rfl
@[simp] lemma list.dprod_index_cons (a : α) (l : list α) (fι : α → ι) :
  (a :: l).dprod_index fι = fι a + l.dprod_index fι := rfl

lemma list.dprod_index_eq_map_sum (l : list α) (fι : α → ι) :
  l.dprod_index fι = (l.map fι).sum :=
begin
  dunfold list.dprod_index,
  induction l,
  { simp, },
  { simp [l_ih], },
end

/-- A dependent product for graded monoids represented by the indexed family of types `A i`.
This is a dependent version of `(l.map fA).prod`.

For a list `l : list α`, this computes the product of `fA a` over `a`, where each `fA` is of type
`A (fι a)`. -/
def list.dprod (l : list α) (fι : α → ι) (fA : Π a, A (fι a)) :
  A (l.dprod_index fι) :=
l.foldr_rec_on _ _ graded_monoid.ghas_one.one (λ i x a ha, graded_monoid.ghas_mul.mul (fA a) x)

@[simp] lemma list.dprod_nil (fι : α → ι) (fA : Π a, A (fι a)) :
  (list.nil : list α).dprod fι fA = graded_monoid.ghas_one.one := rfl

-- the `( : _)` in this lemma statement results in the type on the RHS not being unfolded, which
-- is nicer in the goal view.
@[simp] lemma list.dprod_cons (fι : α → ι) (fA : Π a, A (fι a)) (a : α) (l : list α) :
  (a :: l).dprod fι fA = (graded_monoid.ghas_mul.mul (fA a) (l.dprod fι fA) : _) := rfl

lemma graded_monoid.mk_list_dprod (l : list α) (fι : α → ι) (fA : Π a, A (fι a)) :
  graded_monoid.mk _ (l.dprod fι fA) = (l.map (λ a, graded_monoid.mk (fι a) (fA a))).prod :=
begin
  induction l,
  { simp, refl  },
  { simp [←l_ih, graded_monoid.mk_mul_mk, list.prod_cons],
    refl, },
end

/-- A variant of `graded_monoid.mk_list_dprod` for rewriting in the other direction. -/
lemma graded_monoid.list_prod_map_eq_dprod (l : list α) (f : α → graded_monoid A) :
  (l.map f).prod = graded_monoid.mk _ (l.dprod (λ i, (f i).1) (λ i, (f i).2)) :=
begin
  rw [graded_monoid.mk_list_dprod, graded_monoid.mk],
  simp_rw sigma.eta,
end

lemma graded_monoid.list_prod_of_fn_eq_dprod {n : ℕ} (f : fin n → graded_monoid A) :
  (list.of_fn f).prod =
    graded_monoid.mk _ ((list.fin_range n).dprod (λ i, (f i).1) (λ i, (f i).2)) :=
by rw [list.of_fn_eq_map, graded_monoid.list_prod_map_eq_dprod]

end dprod

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

/-- When all the indexed types are the same, the dependent product is just the regular product. -/
@[simp] lemma list.dprod_monoid {α} [add_monoid ι] [monoid R] (l : list α) (fι : α → ι)
  (fA : α → R) :
  (l.dprod fι fA : (λ i : ι, R) _) = ((l.map fA).prod : _) :=
begin
  induction l,
  { rw [list.dprod_nil, list.map_nil, list.prod_nil], refl },
  { rw [list.dprod_cons, list.map_cons, list.prod_cons, l_ih], refl },
end

end

/-! ### Shorthands for creating instance of the above typeclasses for collections of subobjects -/

section subobjects

variables {R : Type*}

/-- A version of `graded_monoid.ghas_one` for internally graded objects. -/
class set_like.has_graded_one {S : Type*} [set_like S R] [has_one R] [has_zero ι]
  (A : ι → S) : Prop :=
(one_mem : (1 : R) ∈ A 0)

lemma set_like.one_mem_graded {S : Type*} [set_like S R] [has_one R] [has_zero ι] (A : ι → S)
  [set_like.has_graded_one A] : (1 : R) ∈ A 0 := set_like.has_graded_one.one_mem

instance set_like.ghas_one {S : Type*} [set_like S R] [has_one R] [has_zero ι] (A : ι → S)
  [set_like.has_graded_one A] : graded_monoid.ghas_one (λ i, A i) :=
{ one := ⟨1, set_like.one_mem_graded _⟩ }

@[simp] lemma set_like.coe_ghas_one {S : Type*} [set_like S R] [has_one R] [has_zero ι] (A : ι → S)
  [set_like.has_graded_one A] : ↑(@graded_monoid.ghas_one.one _ (λ i, A i) _ _) = (1 : R) := rfl

/-- A version of `graded_monoid.ghas_one` for internally graded objects. -/
class set_like.has_graded_mul {S : Type*} [set_like S R] [has_mul R] [has_add ι]
  (A : ι → S) : Prop :=
(mul_mem : ∀ ⦃i j⦄ {gi gj}, gi ∈ A i → gj ∈ A j → gi * gj ∈ A (i + j))

lemma set_like.mul_mem_graded {S : Type*} [set_like S R] [has_mul R] [has_add ι] {A : ι → S}
  [set_like.has_graded_mul A] ⦃i j⦄ {gi gj} (hi : gi ∈ A i) (hj : gj ∈ A j) :
  gi * gj ∈ A (i + j) :=
set_like.has_graded_mul.mul_mem hi hj

instance set_like.ghas_mul {S : Type*} [set_like S R] [has_mul R] [has_add ι] (A : ι → S)
  [set_like.has_graded_mul A] :
  graded_monoid.ghas_mul (λ i, A i) :=
{ mul := λ i j a b, ⟨(a * b : R), set_like.mul_mem_graded a.prop b.prop⟩ }

@[simp] lemma set_like.coe_ghas_mul {S : Type*} [set_like S R] [has_mul R] [has_add ι] (A : ι → S)
  [set_like.has_graded_mul A] {i j : ι} (x : A i) (y : A j) :
    ↑(@graded_monoid.ghas_mul.mul _ (λ i, A i) _ _ _ _ x y) = (x * y : R) := rfl

/-- A version of `graded_monoid.gmonoid` for internally graded objects. -/
class set_like.graded_monoid {S : Type*} [set_like S R] [monoid R] [add_monoid ι]
  (A : ι → S) extends set_like.has_graded_one A, set_like.has_graded_mul A : Prop

namespace set_like
variables {S : Type*} [set_like S R] [monoid R] [add_monoid ι]
variables {A : ι → S} [set_like.graded_monoid A]

lemma pow_mem_graded (n : ℕ) {r : R} {i : ι} (h : r ∈ A i) : r ^ n ∈ A (n • i) :=
begin
  induction n,
  { rw [pow_zero, zero_nsmul], exact one_mem_graded _ },
  { rw [pow_succ', succ_nsmul'], exact mul_mem_graded n_ih h },
end

lemma list_prod_map_mem_graded {ι'} (l : list ι') (i : ι' → ι) (r : ι' → R)
  (h : ∀ j ∈ l, r j ∈ A (i j)) :
  (l.map r).prod ∈ A (l.map i).sum :=
begin
  induction l,
  { rw [list.map_nil, list.map_nil, list.prod_nil, list.sum_nil],
    exact one_mem_graded _ },
  { rw [list.map_cons, list.map_cons, list.prod_cons, list.sum_cons],
    exact mul_mem_graded
      (h _ $ list.mem_cons_self _ _) (l_ih $ λ j hj, h _ $ list.mem_cons_of_mem _ hj) },
end

lemma list_prod_of_fn_mem_graded {n} (i : fin n → ι) (r : fin n → R) (h : ∀ j, r j ∈ A (i j)) :
  (list.of_fn r).prod ∈ A (list.of_fn i).sum :=
begin
  rw [list.of_fn_eq_map, list.of_fn_eq_map],
  exact list_prod_map_mem_graded _ _ _ (λ _ _, h _),
end

end set_like

/-- Build a `gmonoid` instance for a collection of subobjects. -/
instance set_like.gmonoid {S : Type*} [set_like S R] [monoid R] [add_monoid ι] (A : ι → S)
  [set_like.graded_monoid A] :
  graded_monoid.gmonoid (λ i, A i) :=
{ one_mul := λ ⟨i, a, h⟩, sigma.subtype_ext (zero_add _) (one_mul _),
  mul_one := λ ⟨i, a, h⟩, sigma.subtype_ext (add_zero _) (mul_one _),
  mul_assoc := λ ⟨i, a, ha⟩ ⟨j, b, hb⟩ ⟨k, c, hc⟩,
    sigma.subtype_ext (add_assoc _ _ _) (mul_assoc _ _ _),
  gnpow := λ n i a, ⟨a ^ n, set_like.pow_mem_graded n a.prop⟩,
  gnpow_zero' := λ n, sigma.subtype_ext (zero_nsmul _) (pow_zero _),
  gnpow_succ' := λ n a, sigma.subtype_ext (succ_nsmul _ _) (pow_succ _ _),
  ..set_like.ghas_one A,
  ..set_like.ghas_mul A }

@[simp] lemma set_like.coe_gnpow {S : Type*} [set_like S R] [monoid R] [add_monoid ι] (A : ι → S)
  [set_like.graded_monoid A] {i : ι} (x : A i) (n : ℕ) :
    ↑(@graded_monoid.gmonoid.gnpow _ (λ i, A i) _ _ n _ x) = (x ^ n : R) := rfl

/-- Build a `gcomm_monoid` instance for a collection of subobjects. -/
instance set_like.gcomm_monoid {S : Type*} [set_like S R] [comm_monoid R] [add_comm_monoid ι]
  (A : ι → S) [set_like.graded_monoid A] :
  graded_monoid.gcomm_monoid (λ i, A i) :=
{ mul_comm := λ ⟨i, a, ha⟩ ⟨j, b, hb⟩, sigma.subtype_ext (add_comm _ _) (mul_comm _ _),
  ..set_like.gmonoid A}

section dprod
open set_like set_like.graded_monoid
variables {α S : Type*} [set_like S R] [monoid R] [add_monoid ι]

/-- Coercing a dependent product of subtypes is the same as taking the regular product of the
coercions. -/
@[simp] lemma set_like.coe_list_dprod (A : ι → S) [set_like.graded_monoid A]
  (fι : α → ι) (fA : Π a, A (fι a)) (l : list α) :
  ↑(l.dprod fι fA : (λ i, ↥(A i)) _) = (list.prod (l.map (λ a, fA a)) : R) :=
begin
  induction l,
  { rw [list.dprod_nil, coe_ghas_one, list.map_nil, list.prod_nil] },
  { rw [list.dprod_cons, coe_ghas_mul, list.map_cons, list.prod_cons, l_ih], },
end

include R

/-- A version of `list.coe_dprod_set_like` with `subtype.mk`. -/
lemma set_like.list_dprod_eq (A : ι → S) [set_like.graded_monoid A]
  (fι : α → ι) (fA : Π a, A (fι a)) (l : list α) :
  (l.dprod fι fA : (λ i, ↥(A i)) _) =
    ⟨list.prod (l.map (λ a, fA a)), (l.dprod_index_eq_map_sum fι).symm ▸
      list_prod_map_mem_graded l _ _ (λ i hi, (fA i).prop)⟩ :=
subtype.ext $ set_like.coe_list_dprod _ _ _ _

end dprod

end subobjects

section homogeneous_elements

variables {R S : Type*} [set_like S R]

/-- An element `a : R` is said to be homogeneous if there is some `i : ι` such that `a ∈ A i`. -/
def set_like.is_homogeneous (A : ι → S) (a : R) : Prop := ∃ i, a ∈ A i

@[simp] lemma set_like.is_homogeneous_coe {A : ι → S} {i} (x : A i) :
  set_like.is_homogeneous A (x : R) :=
⟨i, x.prop⟩

lemma set_like.is_homogeneous_one [has_zero ι] [has_one R]
  (A : ι → S) [set_like.has_graded_one A] : set_like.is_homogeneous A (1 : R) :=
⟨0, set_like.one_mem_graded _⟩

lemma set_like.is_homogeneous.mul [has_add ι] [has_mul R] {A : ι → S}
  [set_like.has_graded_mul A] {a b : R} :
  set_like.is_homogeneous A a → set_like.is_homogeneous A b → set_like.is_homogeneous A (a * b)
| ⟨i, hi⟩ ⟨j, hj⟩ := ⟨i + j, set_like.mul_mem_graded hi hj⟩

/-- When `A` is a `set_like.graded_monoid A`, then the homogeneous elements forms a submonoid. -/
def set_like.homogeneous_submonoid [add_monoid ι] [monoid R]
  (A : ι → S) [set_like.graded_monoid A] : submonoid R :=
{ carrier := { a | set_like.is_homogeneous A a },
  one_mem' := set_like.is_homogeneous_one A,
  mul_mem' := λ a b, set_like.is_homogeneous.mul }

end homogeneous_elements
