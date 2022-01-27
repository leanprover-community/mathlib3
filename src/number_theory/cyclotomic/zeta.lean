/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Best, Riccardo Brasca, Eric Rodriguez
-/

import number_theory.cyclotomic.basic
import ring_theory.adjoin.power_basis

/-!
# `ζ` elements in cyclotmic fields
If `is_cyclotomic_extension {n} A B`, we define an element `zeta n A B : B` that is (under certain
assumptions) a primitive `n`-root of unity in `B` and we study its properties.

## Main definitions
* `is_cyclotomic_extension.zeta n A B` : if `is_cyclotomic_extension {n} A B`, than `zeta n A B`
  is an element of `B` that plays the role of a primitive `n`-th root of unity.
* `is_cyclotomic_extension.zeta.power_basis` : if `K` and `L` are fields such that
  `is_cyclotomic_extension {n} K L` and `ne_zero ((n : ℕ) : K)`, then `zeta.power_basis` is the
  power basis given by `zeta n K L`.
* `is_cyclotomic_extension.zeta.embeddings_equiv_primitive_roots` : the equiv between `L →ₐ[K] A`
  and `primitive_roots n A` given by the choice of `zeta`.

## Main results
* `is_cyclotomic_extension.zeta_primitive_root` : if `is_domain B` and `ne_zero ((n : ℕ) : B)` then
  `zeta n A B` is a primitive `n`-th root of unity.

## Implementation details
`zeta n A B` is defined as any root of `cyclotomic n A` in `B`, that exists because of
`is_cyclotomic_extension {n} A B`. It is not true in general that it is a primitive `n`-th root of
unity, but this holds if `is_domain B` and `ne_zero ((n : ℕ) : B)`.

-/

noncomputable theory

open polynomial

universes u v w z

variables (n : ℕ+) (A : Type w) (B : Type z)
variables [comm_ring A] [comm_ring B] [algebra A B] [is_cyclotomic_extension {n} A B]

namespace is_cyclotomic_extension

/-- If `B` is a `n`-th cyclotomic extension of `A`, then `zeta n A B` is any root of
`cyclotomic n A` in L. -/
def zeta : B := (exists_root (set.mem_singleton n) : ∃ r : B, aeval r (cyclotomic n A) = 0).some

@[simp] lemma zeta_spec : aeval (zeta n A B) (cyclotomic n A) = 0 :=
classical.some_spec (exists_root (set.mem_singleton n) : ∃ r : B, aeval r (cyclotomic n A) = 0)

lemma zeta_spec' : is_root (cyclotomic n B) (zeta n A B) :=
by { convert zeta_spec n A B, rw [is_root.def, aeval_def, eval₂_eq_eval_map, map_cyclotomic] }

/-- If `is_domain B` and `ne_zero ((n : ℕ) : B)` then `zeta n A B` is a primitive `n`-th root of
unity. -/
lemma zeta_primitive_root [is_domain B] [ne_zero ((n : ℕ) : B)] :
  is_primitive_root (zeta n A B) n :=
by { rw ←is_root_cyclotomic_iff, exact zeta_spec' n A B }

section field

variables {K : Type u} (L : Type v) [field K] [field L] [algebra K L] [algebra K A]
variables [is_cyclotomic_extension {n} K L] [ne_zero ((n : ℕ) : K)]

/-- If `irreducible (cyclotomic n K)`, then the minimal polynomial of `zeta n K A` is
`cyclotomic n K`. -/
lemma zeta_minpoly {n : ℕ+} (hirr : irreducible (cyclotomic n K)) [is_cyclotomic_extension {n} K A]
  [nontrivial A] : minpoly K (zeta n K A) = cyclotomic n K :=
(minpoly.eq_of_irreducible_of_monic hirr (zeta_spec _ _ _) (cyclotomic.monic n K)).symm

include n

variable (K)

/-- The `power_basis` given by `zeta n K L`. -/
@[simps] def zeta.power_basis : power_basis K L :=
begin
  haveI : ne_zero ((n : ℕ) : L) := ne_zero.of_no_zero_smul_divisors K L,
  refine power_basis.map
  (algebra.adjoin.power_basis $ integral {n} K L $ zeta n K L) _,
  exact (subalgebra.equiv_of_eq _ _
      (is_cyclotomic_extension.adjoin_primitive_root_eq_top n _ $ zeta_primitive_root n K L)).trans
      algebra.top_equiv
end

variables {K} {n}

lemma zeta.power_basis_gen_minpoly (hirr : irreducible (cyclotomic n K)) :
  minpoly K (zeta.power_basis n K L).gen = cyclotomic n K :=
begin
  rw [zeta.power_basis_gen],
  exact zeta_minpoly L hirr
end

variables (K) (n)

/-- `zeta.embeddings_equiv_primitive_roots` is the equiv between `L →ₐ[K] A` and
  `primitive_roots n A` given by the choice of `zeta`. -/
@[simps]
def zeta.embeddings_equiv_primitive_roots [is_domain A] (hirr : irreducible (cyclotomic n K)) :
  (L →ₐ[K] A) ≃ primitive_roots n A :=
((zeta.power_basis n K L).lift_equiv).trans
{ to_fun    := λ x,
  begin
    haveI hn : ne_zero ((n : ℕ) : A) := ne_zero.of_no_zero_smul_divisors K A,
    refine ⟨x.1, _⟩,
    cases x,
    rwa [mem_primitive_roots n.pos, ←is_root_cyclotomic_iff, is_root.def,
      ← map_cyclotomic _ (algebra_map K A), ← zeta.power_basis_gen_minpoly L hirr,
      ← eval₂_eq_eval_map, ← aeval_def]
  end,
  inv_fun   := λ x,
  begin
    haveI hn : ne_zero ((n : ℕ) : A) := ne_zero.of_no_zero_smul_divisors K A,
    refine ⟨x.1, _⟩,
    cases x,
    rwa [aeval_def, eval₂_eq_eval_map, zeta.power_basis_gen_minpoly L hirr, map_cyclotomic,
      ← is_root.def, is_root_cyclotomic_iff, ← mem_primitive_roots n.pos],
  end,
  left_inv  := λ x, subtype.ext rfl,
  right_inv := λ x, subtype.ext rfl }

end field

end is_cyclotomic_extension
