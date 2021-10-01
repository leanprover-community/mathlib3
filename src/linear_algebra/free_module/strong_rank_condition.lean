/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

import linear_algebra.charpoly.basic
import linear_algebra.invariant_basis_number

/-!

# Strong rank condition for commutative rings

We prove that any nontrivial commutative ring satisfies `strong_rank_condition`.

## Main result

* `comm_ring_strong_rank_condition R` : `R` has the `strong_rank_condition`.

## References

We follow the proof given in https://mathoverflow.net/a/47846/7845.

-/

variables (R : Type*) [comm_ring R] [nontrivial R]

open polynomial function fin linear_map

instance comm_ring_strong_rank_condition : strong_rank_condition R :=
begin
  suffices : ∀ n, ∀ f : (fin (n + 1) → R) →ₗ[R] fin n → R, ¬injective f,
  { rwa strong_rank_condition_iff_succ R },
  intros n f, by_contradiction hf,

  letI := module.finite.of_basis (pi.basis_fun R (fin (n + 1))),

  let g : (fin (n + 1) → R) →ₗ[R] fin (n + 1) → R :=
    (extend_by_zero.linear_map R cast_succ).comp f,
  have hg : injective g := (extend_injective (rel_embedding.injective cast_succ) 0).comp hf,

  have hnex : ¬∃ i : fin n, cast_succ i = last n := λ ⟨i, hi⟩, ne_of_lt (cast_succ_lt_last i) hi,

  let a₀ := (minpoly R g).coeff 0,
  have : a₀ ≠ 0 := charpoly_coeff_zero_of_injective hg,
  have : a₀ = 0,
  { -- evaluate the minimal polynomial at the vector `(0,...,0,1)`
    have heval := linear_map.congr_fun (minpoly.aeval R g) (pi.single (fin.last n) 1),
    obtain ⟨P, hP⟩ := X_dvd_iff.2 (erase_same (minpoly R g) 0),
    rw [← monomial_add_erase (minpoly R g) 0, hP] at heval,
    replace heval := congr_fun heval (fin.last n),
    simpa [hnex] using heval },
  contradiction,
end
