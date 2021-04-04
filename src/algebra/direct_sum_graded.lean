/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.direct_sum
import algebra.algebra.basic
import algebra.algebra.operations
import group_theory.subgroup

/-!
# Additively-graded multiplicative structures on `⨁ i, A i`

This module provides a set of heterogeneous typeclasses for defining a multiplicative structure
over `⨁ i, A i` such that `(*) : A i → A j → A (i + j)`; that is to say, `A` forms an
additively-graded ring. The typeclasses are:

* `direct_sum.ghas_one A`
* `direct_sum.ghas_mul A`
* `direct_sum.gmonoid A`
* `direct_sum.gcomm_monoid A`

Respectively, these imbue the direct sum `⨁ i, A i` with:

* `has_one`
* `mul_zero_class`, `distrib`
* `semiring`, `ring`
* `comm_semiring`, `comm_ring`

Additionally, this module provides helper functions to construct `gmonoid` and `gcomm_monoid`
instances for:

* `A : ι → submonoid S`:
  `direct_sum.ghas_one.of_add_submonoids`, `direct_sum.ghas_mul.of_add_submonoids`,
  `direct_sum.gmonoid.of_add_submonoids`, `direct_sum.gcomm_monoid.of_add_submonoids`.
* `A : ι → subgroup S`:
  `direct_sum.ghas_one.of_add_subgroups`, `direct_sum.ghas_mul.of_add_subgroups`,
  `direct_sum.gmonoid.of_add_subgroups`, `direct_sum.gcomm_monoid.of_add_subgroups`.
* `A : ι → submodule S`:
  `direct_sum.ghas_one.of_submodules`, `direct_sum.ghas_mul.of_submodules`,
  `direct_sum.gmonoid.of_submodules`, `direct_sum.gcomm_monoid.of_submodules`.

If `complete_lattice.independent (set.range A)`, these provide a gradation of `⨆ i, A i`, and the
mapping `⨁ i, A i →+ ⨆ i, A i` can be obtained as
`direct_sum.to_monoid (λ i, add_submonoid.inclusion $ le_supr A i)`.

## tags

graded ring, filtered ring, direct sum, add_submonoid
-/
variables {ι : Type*} [decidable_eq ι]

namespace direct_sum

open_locale direct_sum

/-! ### Typeclasses -/
section defs

variables (A : ι → Type*)

/-- A graded version of `has_one`, which must be of grade 0. -/
class ghas_one [has_zero ι] :=
(one : A 0)

/-- A graded version of `has_mul` that also subsumes `distrib` and `mul_zero_class` by requiring
the multiplication be an `add_monoid_hom`. Multiplication combines grades additively, like
`add_monoid_algebra`. -/
class ghas_mul [has_add ι] [Π i, add_comm_monoid (A i)] :=
(mul {i j} : A i →+ A j →+ A (i + j))

variables {A}

/-- `direct_sum.ghas_one` implies a `has_one (Σ i, A i)`, although this is only used as an instance
locally to define notation in `direct_sum.gmonoid`. -/
def ghas_one.to_sigma_has_one [has_zero ι] [ghas_one A] : has_one (Σ i, A i) := ⟨⟨_, ghas_one.one⟩⟩

/-- `direct_sum.ghas_mul` implies a `has_mul (Σ i, A i)`, although this is only used as an instance
locally to define notation in `direct_sum.gmonoid`. -/
def ghas_mul.to_sigma_has_mul [has_add ι] [Π i, add_comm_monoid (A i)] [ghas_mul A] :
  has_mul (Σ i, A i) :=
⟨λ (x y : Σ i, A i), ⟨_, ghas_mul.mul x.snd y.snd⟩⟩

end defs

section defs

variables (A : ι → Type*)

local attribute [instance] ghas_one.to_sigma_has_one
local attribute [instance] ghas_mul.to_sigma_has_mul

/-- A graded version of `monoid`. -/
class gmonoid [add_monoid ι] [Π i, add_comm_monoid (A i)] extends ghas_mul A, ghas_one A :=
(one_mul (a : Σ i, A i) : 1 * a = a)
(mul_one (a : Σ i, A i) : a * 1 = a)
(mul_assoc (a : Σ i, A i) (b : Σ i, A i) (c : Σ i, A i) : a * b * c = a * (b * c))

/-- A graded version of `comm_monoid`. -/
class gcomm_monoid [add_comm_monoid ι] [Π i, add_comm_monoid (A i)] extends gmonoid A :=
(mul_comm (a : Σ i, A i) (b : Σ i, A i) : a * b = b * a)

end defs

/-! ### Shorthands for creating the above typeclasses -/

section shorthands

variables {R : Type*}

/-! #### From `add_submonoid`s -/

/-- Build a `ghas_one` instance for a collection of `add_submonoid`s. -/
@[simps one]
def ghas_one.of_add_submonoids [semiring R] [has_zero ι]
  (carriers : ι → add_submonoid R)
  (one_mem : (1 : R) ∈ carriers 0) :
  ghas_one (λ i, carriers i) :=
{ one := ⟨1, one_mem⟩ }

/-- Build a `ghas_mul` instance for a collection of `add_submonoids`. -/
@[simps mul]
def ghas_mul.of_add_submonoids [semiring R] [has_add ι]
  (carriers : ι → add_submonoid R)
  (mul_mem : ∀ ⦃i j⦄ (gi : carriers i) (gj : carriers j), (gi * gj : R) ∈ carriers (i + j)) :
  ghas_mul (λ i, carriers i) :=
{ mul := λ i j,
  { to_fun := λ a,
    { to_fun := λ b, ⟨(a * b : R), mul_mem a b⟩,
      map_add' := λ _ _, subtype.ext (mul_add _ _ _),
      map_zero' := subtype.ext (mul_zero _), },
    map_add' := λ _ _, add_monoid_hom.ext $ λ _, subtype.ext (add_mul _ _ _),
    map_zero' := add_monoid_hom.ext $ λ _, subtype.ext (zero_mul _) }, }

/-- Build a `gmonoid` instance for a collection of `add_submonoid`s. -/
@[simps to_ghas_one to_ghas_mul]
def gmonoid.of_add_submonoids [semiring R] [add_monoid ι]
  (carriers : ι → add_submonoid R)
  (one_mem : (1 : R) ∈ carriers 0)
  (mul_mem : ∀ ⦃i j⦄ (gi : carriers i) (gj : carriers j), (gi * gj : R) ∈ carriers (i + j)) :
  gmonoid (λ i, carriers i) :=
{ one_mul := λ ⟨i, a, h⟩, sigma.subtype_ext (zero_add _) (one_mul _),
  mul_one := λ ⟨i, a, h⟩, sigma.subtype_ext (add_zero _) (mul_one _),
  mul_assoc := λ ⟨i, a, ha⟩ ⟨j, b, hb⟩ ⟨k, c, hc⟩,
    sigma.subtype_ext (add_assoc _ _ _) (mul_assoc _ _ _),
  ..ghas_one.of_add_submonoids carriers one_mem,
  ..ghas_mul.of_add_submonoids carriers mul_mem }

/-- Build a `gcomm_monoid` instance for a collection of `add_submonoid`s. -/
@[simps to_gmonoid]
def gcomm_monoid.of_add_submonoids [comm_semiring R] [add_comm_monoid ι]
  (carriers : ι → add_submonoid R)
  (one_mem : (1 : R) ∈ carriers 0)
  (mul_mem : ∀ ⦃i j⦄ (gi : carriers i) (gj : carriers j), (gi * gj : R) ∈ carriers (i + j)) :
  gcomm_monoid (λ i, carriers i) :=
{ mul_comm := λ ⟨i, a, ha⟩ ⟨j, b, hb⟩, sigma.subtype_ext (add_comm _ _) (mul_comm _ _),
  ..gmonoid.of_add_submonoids carriers one_mem mul_mem}

/-! #### From `add_subgroup`s -/

/-- Build a `ghas_one` instance for a collection of `add_subgroup`s. -/
@[simps one]
def ghas_one.of_add_subgroups [ring R] [has_zero ι]
  (carriers : ι → add_subgroup R)
  (one_mem : (1 : R) ∈ carriers 0) :
  ghas_one (λ i, carriers i) :=
ghas_one.of_add_submonoids (λ i, (carriers i).to_add_submonoid) one_mem

/-- Build a `ghas_mul` instance for a collection of `add_subgroup`s. -/
@[simps mul]
def ghas_mul.of_add_subgroups [ring R] [has_add ι]
  (carriers : ι → add_subgroup R)
  (mul_mem : ∀ ⦃i j⦄ (gi : carriers i) (gj : carriers j), (gi * gj : R) ∈ carriers (i + j)) :
  ghas_mul (λ i, carriers i) :=
ghas_mul.of_add_submonoids (λ i, (carriers i).to_add_submonoid) mul_mem

/-- Build a `gmonoid` instance for a collection of `add_subgroup`s. -/
@[simps to_ghas_one to_ghas_mul]
def gmonoid.of_add_subgroups [ring R] [add_monoid ι]
  (carriers : ι → add_subgroup R)
  (one_mem : (1 : R) ∈ carriers 0)
  (mul_mem : ∀ ⦃i j⦄ (gi : carriers i) (gj : carriers j), (gi * gj : R) ∈ carriers (i + j)) :
  gmonoid (λ i, carriers i) :=
gmonoid.of_add_submonoids (λ i, (carriers i).to_add_submonoid) one_mem mul_mem

/-- Build a `gcomm_monoid` instance for a collection of `add_subgroup`s. -/
@[simps to_gmonoid]
def gcomm_monoid.of_add_subgroups [comm_ring R] [add_comm_monoid ι]
  (carriers : ι → add_subgroup R)
  (one_mem : (1 : R) ∈ carriers 0)
  (mul_mem : ∀ ⦃i j⦄ (gi : carriers i) (gj : carriers j), (gi * gj : R) ∈ carriers (i + j)) :
  gcomm_monoid (λ i, carriers i) :=
gcomm_monoid.of_add_submonoids (λ i, (carriers i).to_add_submonoid) one_mem mul_mem

/-! #### From `submodules`s -/

variables {A : Type*}

/-- Build a `ghas_one` instance for a collection of `submodule`s. -/
@[simps one]
def ghas_one.of_submodules
  [comm_semiring R] [semiring A] [algebra R A] [has_zero ι]
  (carriers : ι → submodule R A)
  (one_mem : (1 : A) ∈ carriers 0) :
  ghas_one (λ i, carriers i) :=
ghas_one.of_add_submonoids (λ i, (carriers i).to_add_submonoid) one_mem

/-- Build a `ghas_mul` instance for a collection of `submodule`s. -/
@[simps mul]
def ghas_mul.of_submodules
  [comm_semiring R] [semiring A] [algebra R A] [has_add ι]
  (carriers : ι → submodule R A)
  (mul_mem : ∀ ⦃i j⦄ (gi : carriers i) (gj : carriers j), (gi * gj : A) ∈ carriers (i + j)) :
  ghas_mul (λ i, carriers i) :=
ghas_mul.of_add_submonoids (λ i, (carriers i).to_add_submonoid) mul_mem

/-- Build a `gmonoid` instance for a collection of `submodules`s. -/
@[simps to_ghas_one to_ghas_mul]
def gmonoid.of_submodules
  [comm_semiring R] [semiring A] [algebra R A] [add_monoid ι]
  (carriers : ι → submodule R A)
  (one_mem : (1 : A) ∈ carriers 0)
  (mul_mem : ∀ ⦃i j⦄ (gi : carriers i) (gj : carriers j), (gi * gj : A) ∈ carriers (i + j)) :
  gmonoid (λ i, carriers i) :=
gmonoid.of_add_submonoids (λ i, (carriers i).to_add_submonoid) one_mem mul_mem

/-- Build a `gcomm_monoid` instance for a collection of `submodules`s. -/
@[simps to_gmonoid]
def gcomm_monoid.of_submodules
  [comm_semiring R] [comm_semiring A] [algebra R A] [add_comm_monoid ι]
  (carriers : ι → submodule R A)
  (one_mem : (1 : A) ∈ carriers 0)
  (mul_mem : ∀ ⦃i j⦄ (gi : carriers i) (gj : carriers j), (gi * gj : A) ∈ carriers (i + j)) :
  gcomm_monoid (λ i, carriers i) :=
gcomm_monoid.of_add_submonoids (λ i, (carriers i).to_add_submonoid) one_mem mul_mem

end shorthands

/-! ### Instances for `⨁ i, A i` -/

variables (A : ι → Type*)

section one
variables [has_zero ι] [ghas_one A] [Π i, add_comm_monoid (A i)]

instance : has_one (⨁ i, A i) :=
{ one := direct_sum.of (λ i, A i) 0 ghas_one.one}

end one

section mul
variables [has_add ι] [Π i, add_comm_monoid (A i)] [ghas_mul A]

open add_monoid_hom (map_zero map_add flip_apply coe_comp comp_hom_apply_apply)

/-- The multiplication from the `has_mul` instance, as a bundled homomorphism. -/
def mul_hom : (⨁ i, A i) →+ (⨁ i, A i) →+ ⨁ i, A i :=
direct_sum.to_add_monoid $ λ i,
  add_monoid_hom.flip $ direct_sum.to_add_monoid $ λ j, add_monoid_hom.flip $
    (direct_sum.of A _).comp_hom.comp ghas_mul.mul

instance : has_mul (⨁ i, A i) :=
{ mul := λ a b, mul_hom A a b }

instance : mul_zero_class (⨁ i, A i) :=
{ mul := (*),
  zero := 0,
  zero_mul := λ a, by { unfold has_mul.mul, simp only [map_zero, add_monoid_hom.zero_apply]},
  mul_zero := λ a, by { unfold has_mul.mul, simp only [map_zero] } }

instance : distrib (⨁ i, A i) :=
{ mul := (*),
  add := (+),
  left_distrib := λ a b c, by { unfold has_mul.mul, simp only [map_add]},
  right_distrib := λ a b c, by { unfold has_mul.mul, simp only [map_add, add_monoid_hom.add_apply]}}

variables {A}

lemma of_mul_of' {i j} (a : A i) (b : A j) :
  mul_hom A (of _ i a) (of _ j b) = of _ (i + j) (ghas_mul.mul a b) :=
begin
  unfold mul_hom,
  rw [to_add_monoid_of, flip_apply, to_add_monoid_of, flip_apply, coe_comp, function.comp_app,
      comp_hom_apply_apply, coe_comp, function.comp_app],
end

lemma of_mul_of {i j} (a : A i) (b : A j) :
  of _ i a * of _ j b = of _ (i + j) (ghas_mul.mul a b) :=
of_mul_of' a b

end mul

-- Like `add_monoid_hom.congr_fun`, but convenient for a simple argument and complicated equality.
-- A non-private version might be called `add_monoid_hom.congr_at`.
private abbreviation congr_at {M N : Type*} {mM : add_monoid M} {mN : add_monoid N}
 {f g : M →+ N} := λ x (h : f = g), add_monoid_hom.congr_fun h x

section semiring
variables [Π i, add_comm_monoid (A i)] [add_monoid ι] [gmonoid A]

open add_monoid_hom (flip_hom coe_comp comp_hom_apply_apply flip_apply flip_hom_apply)

private lemma one_mul (x : ⨁ i, A i) : 1 * x = x :=
congr_at x $ show mul_hom A 1 = add_monoid_hom.id (⨁ i, A i),
begin
  apply add_hom_ext, intros i xi,
  unfold has_one.one,
  rw of_mul_of',
  exact dfinsupp.single_eq_of_sigma_eq (gmonoid.one_mul ⟨i, xi⟩),
end

private lemma mul_one (x : ⨁ i, A i) : x * 1 = x :=
congr_at x $ show (mul_hom A).flip 1 = add_monoid_hom.id (⨁ i, A i),
begin
  apply add_hom_ext, intros i xi,
  unfold has_one.one,
  rw [flip_apply, of_mul_of'],
  exact dfinsupp.single_eq_of_sigma_eq (gmonoid.mul_one ⟨i, xi⟩),
end

private lemma mul_assoc (a b c : ⨁ i, A i) : a * b * c = a * (b * c) :=
congr_at c $ congr_at b $ congr_at a $
show (mul_hom A).comp_hom.comp (mul_hom A)               -- `λ a b c, a * b * c` as a bundled hom
   = (add_monoid_hom.comp_hom flip_hom $
       (mul_hom A).flip.comp_hom.comp (mul_hom A)).flip, -- `λ a b c, a * (b * c)` as a bundled hom
begin
  apply add_hom_ext, intros ai ax, apply add_hom_ext, intros bi bx, apply add_hom_ext, intros ci cx,
  -- simplify lhs
  rw [coe_comp, function.comp_app, comp_hom_apply_apply, coe_comp, function.comp_app],
  -- simplify rhs
  rw [flip_apply, comp_hom_apply_apply, coe_comp, function.comp_app, flip_hom_apply, coe_comp,
      function.comp_app, comp_hom_apply_apply, flip_apply, coe_comp, function.comp_app, flip_apply],
  rw [of_mul_of', of_mul_of', of_mul_of', of_mul_of'],
  exact dfinsupp.single_eq_of_sigma_eq (gmonoid.mul_assoc ⟨ai, ax⟩ ⟨bi, bx⟩ ⟨ci, cx⟩),
end

/-- The `semiring` structure derived from `gmonoid A`. -/
instance semiring : semiring (⨁ i, A i) := {
  one := 1,
  mul := (*),
  zero := 0,
  add := (+),
  one_mul := one_mul A,
  mul_one := mul_one A,
  mul_assoc := mul_assoc A,
  ..direct_sum.mul_zero_class A,
  ..direct_sum.distrib A,
  ..direct_sum.add_comm_monoid _ _, }

end semiring

section comm_semiring

variables [Π i, add_comm_monoid (A i)] [add_comm_monoid ι] [gcomm_monoid A]

private lemma mul_comm (a b : ⨁ i, A i) : a * b = b * a :=
congr_at b $ congr_at a $ show mul_hom A = (mul_hom A).flip,
begin
  apply add_hom_ext, intros ai ax, apply add_hom_ext, intros bi bx,
  rw [add_monoid_hom.flip_apply, of_mul_of', of_mul_of'],
  exact dfinsupp.single_eq_of_sigma_eq (gcomm_monoid.mul_comm ⟨ai, ax⟩ ⟨bi, bx⟩),
end

/-- The `comm_semiring` structure derived from `gcomm_monoid A`. -/
instance comm_semiring : comm_semiring (⨁ i, A i) := {
  one := 1,
  mul := (*),
  zero := 0,
  add := (+),
  mul_comm := mul_comm A,
  ..direct_sum.semiring _, }

end comm_semiring

section ring
variables [Π i, add_comm_group (A i)] [add_comm_monoid ι] [gmonoid A]

/-- The `ring` derived from `gmonoid A`. -/
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
variables [Π i, add_comm_group (A i)] [add_comm_monoid ι] [gcomm_monoid A]

/-- The `comm_ring` derived from `gcomm_monoid A`. -/
instance comm_ring : comm_ring (⨁ i, A i) := {
  one := 1,
  mul := (*),
  zero := 0,
  add := (+),
  neg := has_neg.neg,
  ..(direct_sum.ring _),
  ..(direct_sum.comm_semiring _), }

end comm_ring

end direct_sum

/-! ### Concrete instances -/

namespace submodule

variables {R A : Type*} [comm_semiring R]

/-- A direct sum of powers of a submodule of an algebra has a multiplicative structure. -/
instance nat_power_direct_sum_gmonoid [semiring A] [algebra R A] (S : submodule R A) :
  direct_sum.gmonoid (λ i : ℕ, ↥(S ^ i)) :=
direct_sum.gmonoid.of_submodules _
  (by { rw [←one_le, pow_zero], exact le_rfl })
  (λ i j p q, by { rw pow_add, exact submodule.mul_mem_mul p.prop q.prop })

/-- A direct sum of powers of a submodule of a commutative algebra has a commutative multiplicative
structure. -/
instance nat_power_direct_sum_gcomm_monoid [comm_semiring A] [algebra R A] (S : submodule R A) :
  direct_sum.gcomm_monoid (λ i : ℕ, ↥(S ^ i)) :=
direct_sum.gcomm_monoid.of_submodules _
  (by { rw [←one_le, pow_zero], exact le_rfl })
  (λ i j p q, by { rw pow_add, exact submodule.mul_mem_mul p.prop q.prop })

end submodule
