/-
Copyright (c) 2020 Zhangir Azerbayev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Wieser, Zhangir Azerbayev
-/

import linear_algebra.multilinear
import group_theory.perm.sign

/-!
# Alternating Maps

We construct the bundled function `alternating_map`, which extends `multilinear_map` with all the
arguments of the same type.

## Main definitions
* `alternating_map R M N ι` is the space of `R`-linear alternating maps from `ι → M` to `N`.
* `f.map_eq_args` expresses that `f` is zero when two inputs are equal.
* `f.map_swap` expresses that `f` is negated when two inputs are swapped.
* `f.map_perm` expresses how `f` varies by a sign change under a permutation of its inputs.
* An `add_comm_monoid`, `add_comm_group`, and `semimodule` structure over `alternating_map`s that
  matches the definitions over `multilinear_map`s.

## Implementation notes
`alternating_map` is defined in terms of `map_eq_args`, as this is easier to work with than
using `map_swap` as a definition, and does not require `has_neg N`.
-/

-- semiring / add_comm_monoid
variables {R : Type*} [semiring R]
variables {M : Type*} [add_comm_monoid M] [semimodule R M]
variables {N : Type*} [add_comm_monoid N] [semimodule R N]

-- semiring / add_comm_group
variables {L : Type*} [add_comm_group L] [semimodule R L]

-- ring / add_comm_group
variables {R' : Type*} [ring R']
variables {M' : Type*} [add_comm_group M'] [semimodule R' M']
variables {N' : Type*} [add_comm_group N'] [semimodule R' N']

variables {ι : Type*} [decidable_eq ι]

set_option old_structure_cmd true

section
variables (R M N ι)
/--
An alternating map is a multilinear map that vanishes when two of its arguments are equal.
-/
structure alternating_map extends multilinear_map R (λ i : ι, M) N :=
(map_eq_args' : ∀ (v : ι → M) (i j : ι) (h : v i = v j) (hij : i ≠ j), to_fun v = 0)
end

attribute [nolint doc_blame] alternating_map.to_multilinear_map

namespace alternating_map

variables (f f' : alternating_map R M N ι)
variables (g' : alternating_map R' M' N' ι)
variables (v : ι → M) (v' : ι → M')
open function

/-! Basic coercion simp lemmas, largely copied from `ring_hom` -/
section coercions

instance : has_coe_to_fun (alternating_map R M N ι) := ⟨_, λ x, x.to_fun⟩

initialize_simps_projections alternating_map (to_fun → apply)

@[simp] lemma to_fun_eq_coe : f.to_fun = f := rfl

@[simp] lemma coe_mk (f : (ι → M) → N) (h₁ h₂ h₃) : ⇑(⟨f, h₁, h₂, h₃⟩ :
  alternating_map R M N ι) = f := rfl

instance : has_coe (alternating_map R M N ι) (multilinear_map R (λ i : ι, M) N) :=
⟨λ x, x.to_multilinear_map⟩

@[simp, norm_cast] lemma coe_multilinear_map : ⇑(f : multilinear_map R (λ i : ι, M) N) = f := rfl

@[simp] lemma to_multilinear_map_eq_coe : f.to_multilinear_map = f := rfl

@[simp] lemma coe_multilinear_map_mk (f : (ι → M) → N) (h₁ h₂ h₃) :
  ((⟨f, h₁, h₂, h₃⟩ : alternating_map R M N ι) :  multilinear_map R (λ i : ι, M) N) = ⟨f, h₁, h₂⟩ :=
rfl

@[ext] theorem ext {f f' : alternating_map R M N ι} (H : ∀ x, f x = f' x) : f = f' :=
by cases f; cases f'; congr'; exact funext H

end coercions

@[simp] lemma map_add (i : ι) (x y : M) :
  f (update v i (x + y)) = f (update v i x) + f (update v i y) :=
f.to_multilinear_map.map_add' v i x y

@[simp] lemma map_sub (i : ι) (x y : M') :
  g' (update v' i (x - y)) = g' (update v' i x) - g' (update v' i y) :=
g'.to_multilinear_map.map_sub v' i x y

@[simp] lemma map_smul (i : ι) (r : R) (x : M) :
  f (update v i (r • x)) = r • f (update v i x) :=
f.to_multilinear_map.map_smul' v i r x

@[simp] lemma map_eq_args (v : ι → M) {i j : ι} (h : v i = v j) (hij : i ≠ j) :
  f v = 0 :=
f.map_eq_args' v i j h hij

/-!
### Algebraic structure inherited from `multilinear_map`

`alternating_map` carries the same `add_comm_monoid`, `add_comm_group`, and `semimodule` structure
as `multilinear_map`
-/

instance : has_add (alternating_map R M N ι) :=
⟨λ a b,
  { map_eq_args' := λ v i j h hij, by simp [a.map_eq_args v h hij, b.map_eq_args v h hij],
    ..(a + b : multilinear_map R (λ i : ι, M) N)}⟩

@[simp] lemma add_apply : (f + f') v = f v + f' v := rfl

instance : has_zero (alternating_map R M N ι) :=
⟨{map_eq_args' := λ v i j h hij, by simp,
  ..(0 : multilinear_map R (λ i : ι, M) N)}⟩

@[simp] lemma zero_apply : (0 : alternating_map R M N ι) v = 0 := rfl

instance : inhabited (alternating_map R M N ι) := ⟨0⟩

instance : add_comm_monoid (alternating_map R M N ι) :=
by refine {zero := 0, add := (+), ..};
   intros; ext; simp [add_comm, add_left_comm]

instance : has_neg (alternating_map R' M' N' ι) :=
⟨λ f, {
  map_eq_args' := λ v i j h hij, by simp [f.map_eq_args v h hij],
  ..(-(f : multilinear_map R' (λ i : ι, M') N')) }⟩

@[simp] lemma neg_apply (m : ι → M') : (-g') m = - (g' m) := rfl

instance : add_comm_group (alternating_map R' M' N' ι) :=
by refine {zero := 0, add := (+), neg := has_neg.neg, ..alternating_map.add_comm_monoid, ..};
   intros; ext; simp [add_comm, add_left_comm]

section semimodule

variables {S : Type*} [comm_semiring S] [algebra S R] [semimodule S N]
  [is_scalar_tower S R N]

instance : has_scalar S (alternating_map R M N ι) :=
⟨λ c f, {
  map_eq_args' := λ v i j h hij, by simp [f.map_eq_args v h hij],
  ..((c • f : multilinear_map R (λ i : ι, M) N)) }⟩

@[simp] lemma smul_apply (f : alternating_map R M N ι) (c : S) (m : ι → M) :
  (c • f) m = c • f m := rfl

/-- The space of multilinear maps over an algebra over `S` is a module over `S`, for the pointwise
addition and scalar multiplication. -/
instance : semimodule S (alternating_map R M N ι) :=
{ one_smul := λ f, ext $ λ x, one_smul _ _,
  mul_smul := λ c₁ c₂ f, ext $ λ x, mul_smul _ _ _,
  smul_zero := λ r, ext $ λ x, smul_zero _,
  smul_add := λ r f₁ f₂, ext $ λ x, smul_add _ _ _,
  add_smul := λ r₁ r₂ f, ext $ λ x, add_smul _ _ _,
  zero_smul := λ f, ext $ λ x, zero_smul _ _ }

end semimodule

/-!
### Theorems specific to alternating maps

Various properties of reordered and repeated inputs which follow from
`alternating_map.map_eq_args`.
-/

lemma map_update_self {i j : ι} (hij : i ≠ j) :
  f (function.update v i (v j)) = 0 :=
f.map_eq_args _ (by rw [function.update_same, function.update_noteq hij.symm]) hij

lemma map_update_update {i j : ι} (hij : i ≠ j) (m : M) :
  f (function.update (function.update v i m) j m) = 0 :=
f.map_eq_args _
  (by rw [function.update_same, function.update_noteq hij, function.update_same]) hij

lemma map_swap_add {i j : ι} (hij : i ≠ j) :
  f (v ∘ equiv.swap i j) + f v = 0 :=
begin
  rw equiv.comp_swap_eq_update,
  convert f.map_update_update v hij (v i + v j),
  simp [
    f.map_update_self _ hij,
    f.map_update_self _ hij.symm,
    function.update_comm hij (v i + v j) (v _) v,
    function.update_comm hij.symm (v i) (v i) v
  ],
end

lemma map_add_swap {i j : ι} (hij : i ≠ j) :
  f v + f (v ∘ equiv.swap i j) = 0 :=
by { rw add_comm, exact f.map_swap_add v hij }

variable (g : alternating_map R M L ι)

lemma map_swap {i j : ι} (hij : i ≠ j) :
  g (v ∘ equiv.swap i j) = - g v  :=
eq_neg_of_add_eq_zero (g.map_swap_add v hij)

lemma map_perm [fintype ι] (v : ι → M) (σ : equiv.perm ι) :
  g (v ∘ σ) = (equiv.perm.sign σ : ℤ) • g v :=
begin
  apply equiv.perm.swap_induction_on' σ,
  { simp },
  { intros s x y hxy hI,
    simpa [g.map_swap (v ∘ s) hxy, equiv.perm.sign_swap hxy] using hI, }
end

lemma map_congr_perm [fintype ι] (σ : equiv.perm ι) :
  g v = (equiv.perm.sign σ : ℤ) • g (v ∘ σ) :=
by { rw [g.map_perm, smul_smul], simp }

end alternating_map
