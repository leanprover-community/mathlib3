/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Best, Riccardo Brasca, Eric Rodriguez
-/

import number_theory.cyclotomic.basic
import ring_theory.adjoin.power_basis
import ring_theory.norm

/-!
# Primitive roots in cyclotomic fields
If `is_cyclotomic_extension {n} A B`, we define an element `zeta n A B : B` that is (under certain
assumptions) a primitive `n`-root of unity in `B` and we study its properties. We also prove related
theorems under the more general assumption of just being a primitive root, for reasons described
in the implementation details section.

## Main definitions
* `is_cyclotomic_extension.zeta n A B`: if `is_cyclotomic_extension {n} A B`, than `zeta n A B`
  is an element of `B` that plays the role of a primitive `n`-th root of unity.
* `is_primitive_root.power_basis`: if `K` and `L` are fields such that
  `is_cyclotomic_extension {n} K L` and `ne_zero (↑n : K)`, then `is_primitive_root.power_basis`
  gives a K-power basis for L given a primitive root `ζ`.
* `is_primitive_root.embeddings_equiv_primitive_roots`: the equivalence between `L →ₐ[K] A`
  and `primitive_roots n A` given by the choice of `ζ`.

## Main results
* `is_cyclotomic_extension.zeta_primitive_root`: if `is_domain B` and `ne_zero (↑n : B)`, then
  `zeta n A B` is a primitive `n`-th root of unity.
* `is_cyclotomic_extension.finrank`: if `irreducible (cyclotomic n K)` (in particular for
  `K = ℚ`), then the `finrank` of a cyclotomic extension is `n.totient`.
* `is_primitive_root.norm_eq_one`: If `K` is linearly ordered (in particular for `K = ℚ`), the norm
  of a primitive root is `1` if `n` is odd.
* `is_primitive_root.sub_one_norm_eq_eval_cyclotomic`: If `irreducible (cyclotomic n K)`, then
  the norm of `ζ - 1` is `eval 1 (cyclotomic n ℤ)`.

## Implementation details
`zeta n A B` is defined as any root of `cyclotomic n A` in `B`, that exists because of
`is_cyclotomic_extension {n} A B`. It is not true in general that it is a primitive `n`-th root of
unity, but this holds if `is_domain B` and `ne_zero (↑n : B)`.

`zeta n A B` is defined using `exists.some`, which means we cannot control it.
For example, in normal mathematics, we can demand that `(zeta p ℤ ℤ[ζₚ] : ℚ(ζₚ))` is equal to
`zeta p ℚ ℚ(ζₚ)`, as we are just choosing "an arbitrary primitive root" and we can internally
specify that our choices agree. This is not the case here, and it is indeed impossible to prove that
these two are equal. Therefore, whenever possible, we prove our results for any primitive root,
and only at the "final step", when we need to provide an "explicit" primitive root, we use `zeta`.

-/

open polynomial algebra finset finite_dimensional is_cyclotomic_extension


universes u v w z

variables {n : ℕ+} (A : Type w) (B : Type z) (K : Type u) {L : Type v} (C : Type w)
variables [comm_ring A] [comm_ring B] [algebra A B] [is_cyclotomic_extension {n} A B]

section zeta

namespace is_cyclotomic_extension

variables (n)

/-- If `B` is a `n`-th cyclotomic extension of `A`, then `zeta n A B` is any root of
`cyclotomic n A` in L. -/
noncomputable def zeta : B :=
  (exists_root $ set.mem_singleton n : ∃ r : B, aeval r (cyclotomic n A) = 0).some

@[simp] lemma zeta_spec : aeval (zeta n A B) (cyclotomic n A) = 0 :=
classical.some_spec (exists_root (set.mem_singleton n) : ∃ r : B, aeval r (cyclotomic n A) = 0)

lemma zeta_spec' : is_root (cyclotomic n B) (zeta n A B) :=
by { convert zeta_spec n A B, rw [is_root.def, aeval_def, eval₂_eq_eval_map, map_cyclotomic] }

lemma zeta_pow : (zeta n A B) ^ (n : ℕ) = 1 :=
is_root_of_unity_of_root_cyclotomic (nat.mem_divisors_self _ n.pos.ne') (zeta_spec' _ _ _)

/-- If `is_domain B` and `ne_zero (↑n : B)` then `zeta n A B` is a primitive `n`-th root of
unity. -/
lemma zeta_primitive_root [is_domain B] [ne_zero ((n : ℕ) : B)] :
  is_primitive_root (zeta n A B) n :=
by { rw ←is_root_cyclotomic_iff, exact zeta_spec' n A B }

end is_cyclotomic_extension

end zeta

section no_order

variables [field K] [field L] [comm_ring C] [algebra K L] [algebra K C]
          [is_cyclotomic_extension {n} K L]
          {ζ : L} (hζ : is_primitive_root ζ n)

namespace is_primitive_root

/-- The `power_basis` given by a primitive root `ζ`. -/
@[simps] noncomputable def power_basis : power_basis K L :=
power_basis.map (algebra.adjoin.power_basis $ integral {n} K L ζ) $
(subalgebra.equiv_of_eq _ _ (is_cyclotomic_extension.adjoin_primitive_root_eq_top n _ hζ)).trans
top_equiv

variables {K}

/-- The equivalence between `L →ₐ[K] A` and `primitive_roots n A` given by a primitive root `ζ`. -/
@[simps] noncomputable def embeddings_equiv_primitive_roots [is_domain C] [ne_zero ((n : ℕ) : K)]
  (hirr : irreducible (cyclotomic n K)) : (L →ₐ[K] C) ≃ primitive_roots n C :=
((hζ.power_basis K).lift_equiv).trans
{ to_fun    := λ x,
  begin
    haveI hn := ne_zero.of_no_zero_smul_divisors K C n,
    refine ⟨x.1, _⟩,
    cases x,
    rwa [mem_primitive_roots n.pos, ←is_root_cyclotomic_iff, is_root.def,
         ←map_cyclotomic _ (algebra_map K C), hζ.minpoly_eq_cyclotomic_of_irreducible hirr,
         ←eval₂_eq_eval_map, ←aeval_def]
  end,
  inv_fun   := λ x,
  begin
    haveI hn := ne_zero.of_no_zero_smul_divisors K C n,
    refine ⟨x.1, _⟩,
    cases x,
    rwa [aeval_def, eval₂_eq_eval_map, hζ.power_basis_gen K,
         ←hζ.minpoly_eq_cyclotomic_of_irreducible hirr, map_cyclotomic, ←is_root.def,
         is_root_cyclotomic_iff, ← mem_primitive_roots n.pos]
  end,
  left_inv  := λ x, subtype.ext rfl,
  right_inv := λ x, subtype.ext rfl }

end is_primitive_root

namespace is_cyclotomic_extension

variables {K} (L)

/-- If `irreducible (cyclotomic n K)` (in particular for `K = ℚ`), then the `finrank` of a
cyclotomic extension is `n.totient`. -/
lemma finrank (hirr : irreducible (cyclotomic n K)) [ne_zero ((n : ℕ) : K)] :
  finrank K L = (n : ℕ).totient :=
begin
  haveI := ne_zero.of_no_zero_smul_divisors K L n,
  rw [((zeta_primitive_root n K L).power_basis K).finrank, is_primitive_root.power_basis_dim,
      ←(zeta_primitive_root n K L).minpoly_eq_cyclotomic_of_irreducible hirr, nat_degree_cyclotomic]
end

end is_cyclotomic_extension

end no_order

namespace is_primitive_root

section norm

variables [field L] {ζ : L} (hζ : is_primitive_root ζ n)

include hζ

/-- If `K` is linearly ordered (in particular for `K = ℚ`), the norm of a primitive root is `1`
if `n` is odd. -/
lemma norm_eq_one [linear_ordered_field K] [algebra K L] (hodd : odd (n : ℕ)) : norm K ζ = 1 :=
begin
  haveI := ne_zero.of_no_zero_smul_divisors K L n,
  have hz := congr_arg (norm K) ((is_primitive_root.iff_def _ n).1 hζ).1,
  rw [←(algebra_map K L).map_one , norm_algebra_map, one_pow, map_pow, ←one_pow ↑n] at hz,
  exact strict_mono.injective hodd.strict_mono_pow hz
end

variables {K}

/-- If `irreducible (cyclotomic n K)` (in particular for `K = ℚ`), then the norm of
`ζ - 1` is `eval 1 (cyclotomic n ℤ)`. -/
lemma sub_one_norm_eq_eval_cyclotomic [field K] [algebra K L] [is_cyclotomic_extension {n} K L]
  [ne_zero ((n : ℕ) : K)] (h : 2 < (n : ℕ)) (hirr : irreducible (cyclotomic n K)) :
  norm K (ζ - 1) = ↑(eval 1 (cyclotomic n ℤ)) :=
begin
  let E := algebraic_closure L,
  obtain ⟨z, hz⟩ := is_alg_closed.exists_root _ (degree_cyclotomic_pos n E n.pos).ne.symm,
  apply (algebra_map K E).injective,
  letI := finite_dimensional {n} K L,
  letI := is_galois n K L,
  rw [norm_eq_prod_embeddings],
  conv_lhs { congr, skip, funext,
    rw [← neg_sub, alg_hom.map_neg, alg_hom.map_sub, alg_hom.map_one, neg_eq_neg_one_mul] },
  rw [prod_mul_distrib, prod_const, card_univ, alg_hom.card, is_cyclotomic_extension.finrank L hirr,
      nat.neg_one_pow_of_even (nat.totient_even h), one_mul],
  have : univ.prod (λ (σ : L →ₐ[K] E), 1 - σ ζ) = eval 1 (cyclotomic' n E),
  { rw [cyclotomic', eval_prod, ← @finset.prod_attach E E, ← univ_eq_attach],
    refine fintype.prod_equiv (hζ.embeddings_equiv_primitive_roots E hirr) _ _ (λ σ, _),
    simp },
  haveI : ne_zero ((n : ℕ) : E) := (ne_zero.of_no_zero_smul_divisors K _ (n : ℕ)),
  rw [this, cyclotomic', ← cyclotomic_eq_prod_X_sub_primitive_roots (is_root_cyclotomic_iff.1 hz),
      ← map_cyclotomic_int, (algebra_map K E).map_int_cast, ←int.cast_one, eval_int_cast_map,
      ring_hom.eq_int_cast, int.cast_id]
end

end norm

end is_primitive_root
