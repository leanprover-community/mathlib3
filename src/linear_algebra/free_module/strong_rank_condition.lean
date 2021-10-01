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

open polynomial function fin nat linear_map

instance comm_ring_strong_rank_condition : strong_rank_condition R :=
begin
  suffices : ∀ n, ∀ f : (fin (n + 1) → R) →ₗ[R] fin n → R, ¬injective f,
  { rwa strong_rank_condition_iff_succ R },
  intros n f, by_contradiction hf,

  letI := module.finite.of_basis (pi.basis_fun R (fin (n + 1))),

  let g : (fin (n + 1) → R) →ₗ[R] fin (n + 1) → R :=
    (extend_by_zero.linear_map R cast_succ).comp f,
  have hg : injective g := (extend_injective (rel_embedding.injective cast_succ) 0).comp hf,

  have hnex : ¬∃ i : fin n, fin.cast_succ i = fin.last n :=
    λ ⟨i, hi⟩, ne_of_lt (fin.cast_succ_lt_last i) hi,

-- Since `g` is injective, its minimal polynomial `P` has nonzero constant term `a₀`, but evaluating
-- `P(g)` at the vector `(0,...,0,1)` gives `a₀ = 0`, a contradiction.
  let heval := minpoly.aeval R g,
  obtain ⟨P₁, hP₁⟩ := X_dvd_iff.2 (erase_same (minpoly R g) 0),
  rw [← monomial_add_erase (minpoly R g) 0, hP₁, linear_map.ext_iff] at heval,
  replace heval := congr_fun (heval (pi.single (fin.last n) 1)) (fin.last n),
  simpa [hnex, charpoly_coeff_zero_of_injective hg] using heval
end
