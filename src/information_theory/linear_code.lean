/-
Copyright (c) 2022 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
import information_theory.hamming
import linear_algebra.linear_independent
import linear_algebra.affine_space.affine_subspace
import linear_algebra.finite_dimensional
import data.set.basic

/-!
# Linear Codes

This file introduces Linear codes. A linear code is a type of error-correcting code defined as a
linear subspace of a finite-dimensional vector space.

## Main Definitions

* `linear_code 𝓓 F`: The type of linear codes with domain `𝓓` over field `F`
* `reed_solomon k D` : The code consisting of all polynomials of degree `≤ k` evaluated on a
subset `D` of the field
-/

/--
A linear error-correcting code, defined as a subspace of the vector space of functions from a
domain into a field.
-/
def linear_code (𝓓 F : Type) [fintype 𝓓] [field F] := submodule F ( 𝓓 -> F )

namespace linear_code

variables {𝓓 F : Type} [fintype 𝓓] [field F]

/-- The size of the domain of a code, i.e. the number of field elements transmitted -/
def length (C : linear_code 𝓓 F) : ℕ := fintype.card 𝓓

/-- The set of all valid codewords -/
def codewords (C : linear_code 𝓓 F) := C.carrier

/-- The dimension of the subspace of codewords -/
noncomputable def dimension (C : linear_code 𝓓 F) : ℕ := set.finrank F C.codewords

/--
The minimum hamming distance between any two elements of the code. Equivalently, the minimum
hamming distance of 0 from any nonzero element of the code.
-/
noncomputable def distance [decidable_eq F] (C : linear_code 𝓓 F) : ℕ :=
Inf (set.image (λ w : hamming (λ i : 𝓓, F), hamming_dist w 0) (C.codewords \ {0}))

/-- The proportion of the code dimension to the size of the code -/
noncomputable def rate (C : linear_code 𝓓 F) : ℚ := rat.mk C.dimension C.length

end linear_code

section reed_solomon

variables {F : Type} [field F]

/--
The linear code consisting of all polynomials of degree `≤ k` evaluated on a subset `D` of the
field.
-/
def reed_solomon (k : ℕ) (D : finset F) : linear_code D F :=
{ carrier := {w | ∃ p : polynomial F, p.nat_degree ≤ k ∧ w = (λ x, polynomial.eval x p)},
  add_mem' :=
    begin
      intros a b ha hb,
      rw set.mem_set_of at ha hb ⊢,
      rcases ha with ⟨pa, hap⟩,
      rcases hb with ⟨pb, hbp⟩,
      use pa + pb,
      split,
      { apply le_trans (polynomial.nat_degree_add_le _ _),
        simp only [max_le_iff],
        simp [hap.left, hbp.left], },
      { rw [hap.right, hbp.right],
        funext,
        simp, },
    end,
  zero_mem' :=
    begin
      rw set.mem_set_of,
      use 0,
      simp,
      funext,
      simp,
    end,
  smul_mem' :=
    begin
      intros c a ha,
      rw set.mem_set_of at ha ⊢,
      rcases ha with ⟨pa, hap⟩,
      use c • pa,
      split,
      { rw polynomial.smul_eq_C_mul,
        by_cases c = 0, simp [h],
        rw polynomial.nat_degree_C_mul h,
        simp [hap.left], },
      { rw [hap.right],
        funext,
        simp, },
    end }

end reed_solomon

section repetition

variables {𝓓 F : Type} [field F] [fintype 𝓓]

/-- The repetition code, where all symbols in each codeword are the same. This is equivalent to a
Reed-Solomon code with max degree 0 -/
def repetition : linear_code 𝓓 F :=
{ carrier :=  {w | ∃ f : F, w = (λ x, f)},
  add_mem' :=
    begin
      intros a b ha hb,
      rw set.mem_set_of at ha hb ⊢,
      rcases ha with ⟨pa, hap⟩,
      rcases hb with ⟨pb, hbp⟩,
      use pa + pb,
      funext,
      simp [hap, hbp],
    end,
  zero_mem' :=
    begin
      rw set.mem_set_of,
      use 0,
      funext,
      simp,
    end,
  smul_mem' :=
    begin
      intros c a ha,
      rw set.mem_set_of at ha ⊢,
      rcases ha with ⟨pa, hap⟩,
      use c • pa,
      funext,
      simp [hap],
    end }

instance : inhabited (linear_code 𝓓 F) := ⟨repetition⟩

end repetition
