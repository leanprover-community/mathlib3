/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.algebra.basic
import algebra.algebra.operations
import algebra.direct_sum.basic
import group_theory.subgroup.basic
import algebra.graded_monoid

/-!
# Additively-graded multiplicative structures on `⨁ i, A i`

This module provides a set of heterogeneous typeclasses for defining a multiplicative structure
over `⨁ i, A i` such that `(*) : A i → A j → A (i + j)`; that is to say, `A` forms an
additively-graded ring. The typeclasses are:

* `direct_sum.gnon_unital_non_assoc_semiring A`
* `direct_sum.gsemiring A`
* `direct_sum.gcomm_semiring A`

Respectively, these imbue the direct sum `⨁ i, A i` with:

* `direct_sum.non_unital_non_assoc_semiring`
* `direct_sum.semiring`, `direct_sum.ring`
* `direct_sum.comm_semiring`, `direct_sum.comm_ring`

the base ring `A 0` with:

* `direct_sum.grade_zero.non_unital_non_assoc_semiring`
* `direct_sum.grade_zero.semiring`, `direct_sum.grade_zero.ring`
* `direct_sum.grade_zero.comm_semiring`, `direct_sum.grade_zero.comm_ring`

and the `i`th grade `A i` with `A 0`-actions (`•`) defined as left-multiplication:

* `direct_sum.grade_zero.has_scalar (A 0)`, `direct_sum.grade_zero.smul_with_zero (A 0)`
* `direct_sum.grade_zero.module (A 0)`
* (nothing)

Note that in the presence of these instances, `⨁ i, A i` itself inherits an `A 0`-action.

`direct_sum.of_zero_ring_hom : A 0 →+* ⨁ i, A i` provides `direct_sum.of A 0` as a ring
homomorphism.

`direct_sum.to_semiring` extends `direct_sum.to_add_monoid` to produce a `ring_hom`.

## Direct sums of subobjects

Additionally, this module provides helper functions to construct `gsemiring` and `gcomm_semiring`
instances for:

* `A : ι → submonoid S`:
  `direct_sum.gsemiring.of_add_submonoids`, `direct_sum.gcomm_semiring.of_add_submonoids`.
* `A : ι → subgroup S`:
  `direct_sum.gsemiring.of_add_subgroups`, `direct_sum.gcomm_semiring.of_add_subgroups`.
* `A : ι → submodule S`:
  `direct_sum.gsemiring.of_submodules`, `direct_sum.gcomm_semiring.of_submodules`.

If `complete_lattice.independent (set.range A)`, these provide a gradation of `⨆ i, A i`, and the
mapping `⨁ i, A i →+ ⨆ i, A i` can be obtained as
`direct_sum.to_monoid (λ i, add_submonoid.inclusion $ le_supr A i)`.

## tags

graded ring, filtered ring, direct sum, add_submonoid
-/

set_option old_structure_cmd true

variables {ι : Type*} [decidable_eq ι]

namespace direct_sum

open_locale direct_sum

/-! ### Typeclasses -/
section defs

variables (A : ι → Type*)

/-- A graded version of `non_unital_non_assoc_semiring`. -/
class gnon_unital_non_assoc_semiring [has_add ι] [Π i, add_comm_monoid (A i)] extends
  graded_monoid.ghas_mul A :=
(mul_zero : ∀ {i j} (a : A i), mul a (0 : A j) = 0)
(zero_mul : ∀ {i j} (b : A j), mul (0 : A i) b = 0)
(mul_add : ∀ {i j} (a : A i) (b c : A j), mul a (b + c) = mul a b + mul a c)
(add_mul : ∀ {i j} (a b : A i) (c : A j), mul (a + b) c = mul a c + mul b c)

end defs

section defs

variables (A : ι → Type*)

/-- A graded version of `semiring`. -/
class gsemiring [add_monoid ι] [Π i, add_comm_monoid (A i)] extends
  gnon_unital_non_assoc_semiring A, graded_monoid.gmonoid A

/-- A graded version of `comm_semiring`. -/
class gcomm_semiring [add_comm_monoid ι] [Π i, add_comm_monoid (A i)] extends
  gsemiring A, graded_monoid.gcomm_monoid A

end defs

/-! ### Shorthands for creating the above typeclasses -/

section shorthands

variables {R : Type*}

/-! #### From `add_submonoid`s -/

/-- Build a `gsemiring` instance for a collection of `add_submonoid`s.

See note [reducible non-instances]. -/
@[reducible]
def gsemiring.of_add_submonoids [semiring R] [add_monoid ι]
  (carriers : ι → add_submonoid R)
  (one_mem : (1 : R) ∈ carriers 0)
  (mul_mem : ∀ ⦃i j⦄ (gi : carriers i) (gj : carriers j), (gi * gj : R) ∈ carriers (i + j)) :
  gsemiring (λ i, carriers i) :=
{ mul_zero := λ i j _, subtype.ext (mul_zero _),
  zero_mul := λ i j _, subtype.ext (zero_mul _),
  mul_add := λ i j _ _ _, subtype.ext (mul_add _ _ _),
  add_mul := λ i j _ _ _, subtype.ext (add_mul _ _ _),
  ..graded_monoid.gmonoid.of_subobjects carriers one_mem mul_mem }

/-- Build a `gcomm_semiring` instance for a collection of `add_submonoid`s.

See note [reducible non-instances]. -/
@[reducible]
def gcomm_semiring.of_add_submonoids [comm_semiring R] [add_comm_monoid ι]
  (carriers : ι → add_submonoid R)
  (one_mem : (1 : R) ∈ carriers 0)
  (mul_mem : ∀ ⦃i j⦄ (gi : carriers i) (gj : carriers j), (gi * gj : R) ∈ carriers (i + j)) :
  gcomm_semiring (λ i, carriers i) :=
{ ..graded_monoid.gcomm_monoid.of_subobjects carriers one_mem mul_mem,
  ..gsemiring.of_add_submonoids carriers one_mem mul_mem}

/-! #### From `add_subgroup`s -/

/-- Build a `gsemiring` instance for a collection of `add_subgroup`s.

See note [reducible non-instances]. -/
@[reducible]
def gsemiring.of_add_subgroups [ring R] [add_monoid ι]
  (carriers : ι → add_subgroup R)
  (one_mem : (1 : R) ∈ carriers 0)
  (mul_mem : ∀ ⦃i j⦄ (gi : carriers i) (gj : carriers j), (gi * gj : R) ∈ carriers (i + j)) :
  gsemiring (λ i, carriers i) :=
gsemiring.of_add_submonoids (λ i, (carriers i).to_add_submonoid) one_mem mul_mem

/-- Build a `gcomm_semiring` instance for a collection of `add_subgroup`s.

See note [reducible non-instances]. -/
@[reducible]
def gcomm_semiring.of_add_subgroups [comm_ring R] [add_comm_monoid ι]
  (carriers : ι → add_subgroup R)
  (one_mem : (1 : R) ∈ carriers 0)
  (mul_mem : ∀ ⦃i j⦄ (gi : carriers i) (gj : carriers j), (gi * gj : R) ∈ carriers (i + j)) :
  gcomm_semiring (λ i, carriers i) :=
gcomm_semiring.of_add_submonoids (λ i, (carriers i).to_add_submonoid) one_mem mul_mem

/-! #### From `submodules`s -/

variables {A : Type*}

/-- Build a `gsemiring` instance for a collection of `submodules`s.

See note [reducible non-instances]. -/
@[reducible]
def gsemiring.of_submodules
  [comm_semiring R] [semiring A] [algebra R A] [add_monoid ι]
  (carriers : ι → submodule R A)
  (one_mem : (1 : A) ∈ carriers 0)
  (mul_mem : ∀ ⦃i j⦄ (gi : carriers i) (gj : carriers j), (gi * gj : A) ∈ carriers (i + j)) :
  gsemiring (λ i, carriers i) :=
gsemiring.of_add_submonoids (λ i, (carriers i).to_add_submonoid) one_mem mul_mem

/-- Build a `gcomm_semiring` instance for a collection of `submodules`s.

See note [reducible non-instances]. -/
@[reducible]
def gcomm_semiring.of_submodules
  [comm_semiring R] [comm_semiring A] [algebra R A] [add_comm_monoid ι]
  (carriers : ι → submodule R A)
  (one_mem : (1 : A) ∈ carriers 0)
  (mul_mem : ∀ ⦃i j⦄ (gi : carriers i) (gj : carriers j), (gi * gj : A) ∈ carriers (i + j)) :
  gcomm_semiring (λ i, carriers i) :=
gcomm_semiring.of_add_submonoids (λ i, (carriers i).to_add_submonoid) one_mem mul_mem

end shorthands

variables (A : ι → Type*)

/-! ### Instances for `⨁ i, A i` -/


section one
variables [has_zero ι] [graded_monoid.ghas_one A] [Π i, add_comm_monoid (A i)]

instance : has_one (⨁ i, A i) :=
{ one := direct_sum.of (λ i, A i) 0 graded_monoid.ghas_one.one}

end one

section mul
variables [has_add ι] [Π i, add_comm_monoid (A i)] [gnon_unital_non_assoc_semiring A]

open add_monoid_hom (map_zero map_add flip_apply coe_comp comp_hom_apply_apply)

/-- The piecewise multiplication from the `has_mul` instance, as a bundled homomorphism. -/
@[simps]
def gmul_hom {i j} : A i →+ A j →+ A (i + j) :=
{ to_fun := λ a,
  { to_fun := λ b, graded_monoid.ghas_mul.mul a b,
    map_zero' := gnon_unital_non_assoc_semiring.mul_zero _,
    map_add' := gnon_unital_non_assoc_semiring.mul_add _ },
  map_zero' := add_monoid_hom.ext $ λ a, gnon_unital_non_assoc_semiring.zero_mul a,
  map_add' := λ a₁ a₂, add_monoid_hom.ext $ λ b, gnon_unital_non_assoc_semiring.add_mul _ _ _}

/-- The multiplication from the `has_mul` instance, as a bundled homomorphism. -/
def mul_hom : (⨁ i, A i) →+ (⨁ i, A i) →+ ⨁ i, A i :=
direct_sum.to_add_monoid $ λ i,
  add_monoid_hom.flip $ direct_sum.to_add_monoid $ λ j, add_monoid_hom.flip $
    (direct_sum.of A _).comp_hom.comp $ gmul_hom A

instance : non_unital_non_assoc_semiring (⨁ i, A i) :=
{ mul := λ a b, mul_hom A a b,
  zero := 0,
  add := (+),
  zero_mul := λ a, by simp only [map_zero, add_monoid_hom.zero_apply],
  mul_zero := λ a, by simp only [map_zero],
  left_distrib := λ a b c, by simp only [map_add],
  right_distrib := λ a b c, by simp only [map_add, add_monoid_hom.add_apply],
  .. direct_sum.add_comm_monoid _ _}

variables {A}

lemma mul_hom_of_of {i j} (a : A i) (b : A j) :
  mul_hom A (of _ i a) (of _ j b) = of _ (i + j) (graded_monoid.ghas_mul.mul a b) :=
begin
  unfold mul_hom,
  rw [to_add_monoid_of, flip_apply, to_add_monoid_of, flip_apply, coe_comp, function.comp_app,
      comp_hom_apply_apply, coe_comp, function.comp_app, gmul_hom_apply_apply],
end

lemma of_mul_of {i j} (a : A i) (b : A j) :
  of _ i a * of _ j b = of _ (i + j) (graded_monoid.ghas_mul.mul a b) :=
mul_hom_of_of a b

end mul

section semiring
variables [Π i, add_comm_monoid (A i)] [add_monoid ι] [gsemiring A]

open add_monoid_hom (flip_hom coe_comp comp_hom_apply_apply flip_apply flip_hom_apply)

private lemma one_mul (x : ⨁ i, A i) : 1 * x = x :=
suffices mul_hom A 1 = add_monoid_hom.id (⨁ i, A i),
  from add_monoid_hom.congr_fun this x,
begin
  apply add_hom_ext, intros i xi,
  unfold has_one.one,
  rw mul_hom_of_of,
  exact dfinsupp.single_eq_of_sigma_eq (gsemiring.one_mul ⟨i, xi⟩),
end

private lemma mul_one (x : ⨁ i, A i) : x * 1 = x :=
suffices (mul_hom A).flip 1 = add_monoid_hom.id (⨁ i, A i),
  from add_monoid_hom.congr_fun this x,
begin
  apply add_hom_ext, intros i xi,
  unfold has_one.one,
  rw [flip_apply, mul_hom_of_of],
  exact dfinsupp.single_eq_of_sigma_eq (gsemiring.mul_one ⟨i, xi⟩),
end

private lemma mul_assoc (a b c : ⨁ i, A i) : a * b * c = a * (b * c) :=
suffices (mul_hom A).comp_hom.comp (mul_hom A)            -- `λ a b c, a * b * c` as a bundled hom
       = (add_monoid_hom.comp_hom flip_hom $              -- `λ a b c, a * (b * c)` as a bundled hom
             (mul_hom A).flip.comp_hom.comp (mul_hom A)).flip,
  from add_monoid_hom.congr_fun (add_monoid_hom.congr_fun (add_monoid_hom.congr_fun this a) b) c,
begin
  ext ai ax bi bx ci cx : 6,
  dsimp only [coe_comp, function.comp_app, comp_hom_apply_apply, flip_apply, flip_hom_apply],
  rw [mul_hom_of_of, mul_hom_of_of, mul_hom_of_of, mul_hom_of_of],
  exact dfinsupp.single_eq_of_sigma_eq (gsemiring.mul_assoc ⟨ai, ax⟩ ⟨bi, bx⟩ ⟨ci, cx⟩),
end

/-- The `semiring` structure derived from `gsemiring A`. -/
instance semiring : semiring (⨁ i, A i) := {
  one := 1,
  mul := (*),
  zero := 0,
  add := (+),
  one_mul := one_mul A,
  mul_one := mul_one A,
  mul_assoc := mul_assoc A,
  ..direct_sum.non_unital_non_assoc_semiring _, }

end semiring

section comm_semiring

variables [Π i, add_comm_monoid (A i)] [add_comm_monoid ι] [gcomm_semiring A]

private lemma mul_comm (a b : ⨁ i, A i) : a * b = b * a :=
suffices mul_hom A = (mul_hom A).flip,
  from add_monoid_hom.congr_fun (add_monoid_hom.congr_fun this a) b,
begin
  apply add_hom_ext, intros ai ax, apply add_hom_ext, intros bi bx,
  rw [add_monoid_hom.flip_apply, mul_hom_of_of, mul_hom_of_of],
  exact dfinsupp.single_eq_of_sigma_eq (gcomm_semiring.mul_comm ⟨ai, ax⟩ ⟨bi, bx⟩),
end

/-- The `comm_semiring` structure derived from `gcomm_semiring A`. -/
instance comm_semiring : comm_semiring (⨁ i, A i) := {
  one := 1,
  mul := (*),
  zero := 0,
  add := (+),
  mul_comm := mul_comm A,
  ..direct_sum.semiring _, }

end comm_semiring

section ring
variables [Π i, add_comm_group (A i)] [add_comm_monoid ι] [gsemiring A]

/-- The `ring` derived from `gsemiring A`. -/
instance ring : ring (⨁ i, A i) := {
  one := 1,
  mul := (*),
  zero := 0,
  add := (+),
  neg := has_neg.neg,
  ..(direct_sum.semiring _),
  ..(direct_sum.add_comm_group _), }


end ring

section comm_ring
variables [Π i, add_comm_group (A i)] [add_comm_monoid ι] [gcomm_semiring A]

/-- The `comm_ring` derived from `gcomm_semiring A`. -/
instance comm_ring : comm_ring (⨁ i, A i) := {
  one := 1,
  mul := (*),
  zero := 0,
  add := (+),
  neg := has_neg.neg,
  ..(direct_sum.ring _),
  ..(direct_sum.comm_semiring _), }

end comm_ring


/-! ### Instances for `A 0`

The various `g*` instances are enough to promote the `add_comm_monoid (A 0)` structure to various
types of multiplicative structure.
-/

section grade_zero

section one
variables [has_zero ι] [graded_monoid.ghas_one A] [Π i, add_comm_monoid (A i)]

@[simp] lemma of_zero_one : of _ 0 (1 : A 0) = 1 := rfl

end one

section mul
variables [add_monoid ι] [Π i, add_comm_monoid (A i)] [gnon_unital_non_assoc_semiring A]

@[simp] lemma of_zero_smul {i} (a : A 0) (b : A i) : of _ _ (a • b) = of _ _ a * of _ _ b :=
(dfinsupp.single_eq_of_sigma_eq (graded_monoid.mk_zero_smul a b)).trans (of_mul_of _ _).symm

@[simp] lemma of_zero_mul (a b : A 0) : of _ 0 (a * b) = of _ 0 a * of _ 0 b:=
of_zero_smul A a b

instance grade_zero.non_unital_non_assoc_semiring : non_unital_non_assoc_semiring (A 0) :=
function.injective.non_unital_non_assoc_semiring (of A 0) dfinsupp.single_injective
  (of A 0).map_zero (of A 0).map_add (of_zero_mul A)

instance grade_zero.smul_with_zero (i : ι) : smul_with_zero (A 0) (A i) :=
begin
  letI := smul_with_zero.comp_hom (⨁ i, A i) (of A 0).to_zero_hom,
  refine dfinsupp.single_injective.smul_with_zero (of A i).to_zero_hom (of_zero_smul A),
end

end mul

section semiring
variables [Π i, add_comm_monoid (A i)] [add_monoid ι] [gsemiring A]

/-- The `semiring` structure derived from `gsemiring A`. -/
instance grade_zero.semiring : semiring (A 0) :=
function.injective.semiring (of A 0) dfinsupp.single_injective
  (of A 0).map_zero (of_zero_one A) (of A 0).map_add (of_zero_mul A)

/-- `of A 0` is a `ring_hom`, using the `direct_sum.grade_zero.semiring` structure. -/
def of_zero_ring_hom : A 0 →+* (⨁ i, A i) :=
{ map_one' := of_zero_one A, map_mul' := of_zero_mul A, ..(of _ 0) }

/-- Each grade `A i` derives a `A 0`-module structure from `gsemiring A`. Note that this results
in an overall `module (A 0) (⨁ i, A i)` structure via `direct_sum.module`.
-/
instance grade_zero.module {i} : module (A 0) (A i) :=
begin
  letI := module.comp_hom (⨁ i, A i) (of_zero_ring_hom A),
  exact dfinsupp.single_injective.module (A 0) (of A i) (λ a, of_zero_smul A a),
end

end semiring

section comm_semiring

variables [Π i, add_comm_monoid (A i)] [add_comm_monoid ι] [gcomm_semiring A]

/-- The `comm_semiring` structure derived from `gcomm_semiring A`. -/
instance grade_zero.comm_semiring : comm_semiring (A 0) :=
function.injective.comm_semiring (of A 0) dfinsupp.single_injective
  (of A 0).map_zero (of_zero_one A) (of A 0).map_add (of_zero_mul A)

end comm_semiring

section ring
variables [Π i, add_comm_group (A i)] [add_comm_monoid ι] [gsemiring A]

/-- The `ring` derived from `gsemiring A`. -/
instance grade_zero.ring : ring (A 0) :=
function.injective.ring (of A 0) dfinsupp.single_injective
  (of A 0).map_zero (of_zero_one A) (of A 0).map_add (of_zero_mul A)
  (of A 0).map_neg (of A 0).map_sub

end ring

section comm_ring
variables [Π i, add_comm_group (A i)] [add_comm_monoid ι] [gcomm_semiring A]

/-- The `comm_ring` derived from `gcomm_semiring A`. -/
instance grade_zero.comm_ring : comm_ring (A 0) :=
function.injective.comm_ring (of A 0) dfinsupp.single_injective
  (of A 0).map_zero (of_zero_one A) (of A 0).map_add (of_zero_mul A)
  (of A 0).map_neg (of A 0).map_sub

end comm_ring

end grade_zero

section to_semiring

variables {R : Type*} [Π i, add_comm_monoid (A i)] [add_monoid ι] [gsemiring A] [semiring R]
variables {A}

/-- If two ring homomorphisms from `⨁ i, A i` are equal on each `of A i y`,
then they are equal.

See note [partially-applied ext lemmas]. -/
@[ext]
lemma ring_hom_ext' (F G : (⨁ i, A i) →+* R)
  (h : ∀ i, (F : (⨁ i, A i) →+ R).comp (of _ i) = (G : (⨁ i, A i) →+ R).comp (of _ i)) : F = G :=
ring_hom.coe_add_monoid_hom_injective $ direct_sum.add_hom_ext' h

/-- A family of `add_monoid_hom`s preserving `direct_sum.ghas_one.one` and `direct_sum.ghas_mul.mul`
describes a `ring_hom`s on `⨁ i, A i`. This is a stronger version of `direct_sum.to_monoid`.

Of particular interest is the case when `A i` are bundled subojects, `f` is the family of
coercions such as `add_submonoid.subtype (A i)`, and the `[gsemiring A]` structure originates from
`direct_sum.gsemiring.of_add_submonoids`, in which case the proofs about `ghas_one` and `ghas_mul`
can be discharged by `rfl`. -/
@[simps]
def to_semiring
  (f : Π i, A i →+ R) (hone : f _ (graded_monoid.ghas_one.one) = 1)
  (hmul : ∀ {i j} (ai : A i) (aj : A j), f _ (graded_monoid.ghas_mul.mul ai aj) = f _ ai * f _ aj) :
  (⨁ i, A i) →+* R :=
{ to_fun := to_add_monoid f,
  map_one' := begin
    change (to_add_monoid f) (of _ 0 _) = 1,
    rw to_add_monoid_of,
    exact hone
  end,
  map_mul' := begin
    rw (to_add_monoid f).map_mul_iff,
    ext xi xv yi yv : 4,
    show to_add_monoid f (of A xi xv * of A yi yv) =
         to_add_monoid f (of A xi xv) * to_add_monoid f (of A yi yv),
    rw [of_mul_of, to_add_monoid_of, to_add_monoid_of, to_add_monoid_of],
    exact hmul _ _,
  end,
  .. to_add_monoid f}

@[simp] lemma to_semiring_of (f : Π i, A i →+ R) (hone hmul) (i : ι) (x : A i) :
  to_semiring f hone hmul (of _ i x) = f _ x :=
to_add_monoid_of f i x

@[simp] lemma to_semiring_coe_add_monoid_hom (f : Π i, A i →+ R) (hone hmul):
  (to_semiring f hone hmul : (⨁ i, A i) →+ R) = to_add_monoid f := rfl

/-- Families of `add_monoid_hom`s preserving `direct_sum.ghas_one.one` and `direct_sum.ghas_mul.mul`
are isomorphic to `ring_hom`s on `⨁ i, A i`. This is a stronger version of `dfinsupp.lift_add_hom`.
-/
@[simps]
def lift_ring_hom :
  {f : Π {i}, A i →+ R //
    f (graded_monoid.ghas_one.one) = 1 ∧
    ∀ {i j} (ai : A i) (aj : A j), f (graded_monoid.ghas_mul.mul ai aj) = f ai * f aj} ≃
    ((⨁ i, A i) →+* R) :=
{ to_fun := λ f, to_semiring f.1 f.2.1 f.2.2,
  inv_fun := λ F,
    ⟨λ i, (F : (⨁ i, A i) →+ R).comp (of _ i), begin
      simp only [add_monoid_hom.comp_apply, ring_hom.coe_add_monoid_hom],
      rw ←F.map_one,
      refl
    end, λ i j ai aj, begin
      simp only [add_monoid_hom.comp_apply, ring_hom.coe_add_monoid_hom],
      rw [←F.map_mul, of_mul_of],
    end⟩,
  left_inv := λ f, begin
    ext xi xv,
    exact to_add_monoid_of f.1 xi xv,
  end,
  right_inv := λ F, begin
    apply ring_hom.coe_add_monoid_hom_injective,
    ext xi xv,
    simp only [ring_hom.coe_add_monoid_hom_mk,
      direct_sum.to_add_monoid_of,
      add_monoid_hom.mk_coe,
      add_monoid_hom.comp_apply, to_semiring_coe_add_monoid_hom],
  end}

/-- Two `ring_hom`s out of a direct sum are equal if they agree on the generators.

See note [partially-applied ext lemmas]. -/
@[ext]
lemma ring_hom_ext ⦃f g : (⨁ i, A i) →+* R⦄
  (h : ∀ i, (↑f : (⨁ i, A i) →+ R).comp (of A i) = (↑g : (⨁ i, A i) →+ R).comp (of A i)) :
  f = g :=
direct_sum.lift_ring_hom.symm.injective $ subtype.ext $ funext h

end to_semiring

end direct_sum

/-! ### Concrete instances -/

section uniform

variables (ι)

/-- A direct sum of copies of a `semiring` inherits the multiplication structure. -/
instance non_unital_non_assoc_semiring.direct_sum_gnon_unital_non_assoc_semiring
  {R : Type*} [add_monoid ι] [non_unital_non_assoc_semiring R] :
  direct_sum.gnon_unital_non_assoc_semiring (λ i : ι, R) :=
{ mul_zero := λ i j, mul_zero,
  zero_mul := λ i j, zero_mul,
  mul_add := λ i j, mul_add,
  add_mul := λ i j, add_mul,
  ..has_mul.ghas_mul ι }

/-- A direct sum of copies of a `semiring` inherits the multiplication structure. -/
instance semiring.direct_sum_gsemiring {R : Type*} [add_monoid ι] [semiring R] :
  direct_sum.gsemiring (λ i : ι, R) :=
{ ..non_unital_non_assoc_semiring.direct_sum_gnon_unital_non_assoc_semiring ι, ..monoid.gmonoid ι }

open_locale direct_sum

-- To check `has_mul.ghas_mul_mul` matches
example {R : Type*} [add_monoid ι] [semiring R] (i j : ι) (a b : R) :
  (direct_sum.of _ i a * direct_sum.of _ j b : ⨁ i, R) = direct_sum.of _ (i + j) (by exact a * b) :=
by rw [direct_sum.of_mul_of, has_mul.ghas_mul_mul]

/-- A direct sum of copies of a `comm_semiring` inherits the commutative multiplication structure.
-/
instance comm_semiring.direct_sum_gcomm_semiring {R : Type*} [add_comm_monoid ι] [comm_semiring R] :
  direct_sum.gcomm_semiring (λ i : ι, R) :=
{ ..comm_monoid.gcomm_monoid ι, ..semiring.direct_sum_gsemiring ι }

end uniform

namespace submodule

variables {R A : Type*} [comm_semiring R]

/-- A direct sum of powers of a submodule of an algebra has a multiplicative structure. -/
instance nat_power_direct_sum_gsemiring [semiring A] [algebra R A] (S : submodule R A) :
  direct_sum.gsemiring (λ i : ℕ, ↥(S ^ i)) :=
direct_sum.gsemiring.of_submodules _
  (by { rw [←one_le, pow_zero], exact le_rfl })
  (λ i j p q, by { rw pow_add, exact submodule.mul_mem_mul p.prop q.prop })

/-- A direct sum of powers of a submodule of a commutative algebra has a commutative multiplicative
structure. -/
instance nat_power_direct_sum_gcomm_semiring [comm_semiring A] [algebra R A] (S : submodule R A) :
  direct_sum.gcomm_semiring (λ i : ℕ, ↥(S ^ i)) :=
direct_sum.gcomm_semiring.of_submodules _
  (by { rw [←one_le, pow_zero], exact le_rfl })
  (λ i j p q, by { rw pow_add, exact submodule.mul_mem_mul p.prop q.prop })

end submodule
