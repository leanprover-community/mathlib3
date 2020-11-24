/-
Copyright (c) 2020 Zhangir Azerbayev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Zhangir Azerbayev.
-/

import linear_algebra.multilinear
import group_theory.perm.sign

/-!
# Alternating Maps

We construct the bundled function `alternating_map`, which extends `multilinear_map` with all the
arguments of the same type.

## Notation
For `R`-semimodules `M` and `N` and an index set `ι`, the structure of alternating multilinear maps
from`ι → M` into `N` is denoted `alternating_map R M N ι`. For some results, we must work with
`L` an `R-semimodule` that is also an `add_comm_group` and the structure `alternating_map R M L ι`.

## Theorems
1. `map_perm` asserts that for a map `f : alternating_map R M N ι`, and a
permutation `sigma` of `ι`, we have that `f v = (sign σ) f (v ∘ σ)`.
-/

variables (R : Type*) [semiring R]
variables (M : Type*) [add_comm_monoid M] [semimodule R M]
variables (N : Type*) [add_comm_monoid N] [semimodule R N]
variables (L : Type*) [add_comm_group L] [semimodule R L]
variables (ι : Type*) [decidable_eq ι]

set_option old_structure_cmd true

/--
An alternating map is a multilinear map that vanishes when two of its arguments are equal.
-/
structure alternating_map extends multilinear_map R (λ i : ι, M) N :=
(map_eq_args' : ∀ (v : ι → M) (i j : ι) (h : v i = v j) (hij : i ≠ j), to_fun v = 0)

namespace alternating_map

variables (f f' : alternating_map R M N ι)
variable (v : ι → M)
variables {R M N L ι}
open function

/-! Basic coercion simp lemmas, largely copied from ring_hom -/
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

@[simp] lemma map_smul (i : ι) (r : R) (x : M) :
  f (update v i (r • x)) = r • f (update v i x) :=
f.to_multilinear_map.map_smul' v i r x

@[simp] lemma map_eq_args (v : ι → M) {i j : ι} (h : v i = v j) (hij : i ≠ j) :
  f v = 0 :=
f.map_eq_args' v i j h hij

/-! `alternating_map` carries the same `add_comm_monoid` structure as `multilinear_map` -/
section add_monoid

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

end add_monoid

lemma map_add_swap {i j : ι} (hij : i ≠ j) :
  f v + f (v ∘ equiv.swap i j) = 0 :=
begin
  have key : f (function.update (function.update v i (v i + v j)) j (v i + v j)) = 0 :=
    by rw f.map_eq_args (function.update (function.update v i (v i + v j)) j (v i + v j))
    (by rw [function.update_same, function.update_noteq hij, function.update_same]) hij,
  rw map_add at key,
  rw [function.update_comm hij (v i + v j) (v i) v, map_add] at key,
  rw f.map_eq_args (function.update (function.update v j (v i)) i (v i))
    (by rw [function.update_same, function.update_comm (ne_comm.mp hij) (v i) (v i) v,
    function.update_same]) hij at key,
  rw zero_add at key,
  rw [function.update_comm hij (v i + v j) (v j) v, map_add] at key,
  rw f.map_eq_args (function.update (function.update v j (v j)) i (v j))
  (by rw [function.update_same, function.update_comm (ne_comm.mp hij) (v j) (v j) v,
  function.update_same]) hij at key,
  rw [add_zero, add_comm] at key,
  convert key,
  { simp,  },
  { ext x,
    cases classical.em (x = i) with hx hx,
    --case x = i
    { rw hx,
      simp only [equiv.swap_apply_left, function.comp_app],
      rw function.update_same,  },
    --case x ≠ i
    { cases classical.em (x = j) with hx1 hx1,
      { rw hx1,
        simp only [equiv.swap_apply_left, function.comp_app],
        rw function.update_noteq (ne_comm.mp hij),
        simp, },
    --case x ≠ i, x ≠ j,
      { simp only [hx, hx1, function.comp_app, function.update_noteq, ne.def, not_false_iff],
        rw equiv.swap_apply_of_ne_of_ne hx hx1, }, }, },
end

variable (g : alternating_map R M L ι)

lemma map_swap {i j : ι} (hij : i ≠ j) :
  g (v ∘ equiv.swap i j) = - g v  :=
begin
  apply eq_neg_of_add_eq_zero,
  rw add_comm,
  exact g.map_add_swap v hij,
end

variable [fintype ι]

lemma map_perm (σ : equiv.perm ι) :
  g v = (equiv.perm.sign σ : ℤ) • g (v ∘ σ) :=
begin
  apply equiv.perm.swap_induction_on' σ,
  { rw equiv.perm.sign_one,
    simp only [units.coe_one, one_smul, coe_fn_coe_base],
    congr,  },
  { intros s x y hxy hI,
    have assoc : v ∘ (s * equiv.swap x y : equiv.perm ι) = (v ∘ s ∘ equiv.swap x y) := rfl,
    rw [assoc, g.map_swap (v ∘ s) hxy, ←neg_one_smul ℤ (g (v ∘ s))],
    have h1 : (-1 : ℤ) = equiv.perm.sign (equiv.swap x y) := by simp [hxy],
    rw [h1, smul_smul, ←units.coe_mul, ←equiv.perm.sign_mul, mul_assoc, equiv.swap_mul_self,
      mul_one],
    assumption, },
end

end alternating_map
