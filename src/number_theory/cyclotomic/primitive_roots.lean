/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Best, Riccardo Brasca, Eric Rodriguez
-/

import data.pnat.prime
import algebra.is_prime_pow
import number_theory.cyclotomic.basic
import ring_theory.adjoin.power_basis
import ring_theory.polynomial.cyclotomic.eval
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
  `is_cyclotomic_extension {n} K L`, then `is_primitive_root.power_basis`
  gives a K-power basis for L given a primitive root `ζ`.
* `is_primitive_root.embeddings_equiv_primitive_roots`: the equivalence between `L →ₐ[K] A`
  and `primitive_roots n A` given by the choice of `ζ`.

## Main results
* `is_cyclotomic_extension.zeta_spec`: `zeta n A B` is a primitive `n`-th root of unity.
* `is_cyclotomic_extension.finrank`: if `irreducible (cyclotomic n K)` (in particular for
  `K = ℚ`), then the `finrank` of a cyclotomic extension is `n.totient`.
* `is_primitive_root.norm_eq_one`: if `irreducible (cyclotomic n K)` (in particular for `K = ℚ`),
  the norm of a primitive root is `1` if `n ≠ 2`.
* `is_primitive_root.sub_one_norm_eq_eval_cyclotomic`: if `irreducible (cyclotomic n K)`
  (in particular for `K = ℚ`), then the norm of `ζ - 1` is `eval 1 (cyclotomic n ℤ)`, for a
  primitive root ζ. We also prove the analogous of this result for `zeta`.
* `is_primitive_root.pow_sub_one_norm_prime_pow_ne_two` : if
  `irreducible (cyclotomic (p ^ (k + 1)) K)` (in particular for `K = ℚ`) and `p` is a prime,
  then the norm of `ζ ^ (p ^ s) - 1` is `p ^ (p ^ s)` `p ^ (k - s + 1) ≠ 2`. See the following
  lemmas for similar results. We also prove the analogous of this result for `zeta`.
* `is_primitive_root.sub_one_norm_prime_ne_two` : if `irreducible (cyclotomic (p ^ (k + 1)) K)`
  (in particular for `K = ℚ`) and `p` is an odd prime, then the norm of `ζ - 1` is `p`. We also
  prove the analogous of this result for `zeta`.
* `is_primitive_root.embeddings_equiv_primitive_roots`: the equivalence between `L →ₐ[K] A`
  and `primitive_roots n A` given by the choice of `ζ`.

## Implementation details
`zeta n A B` is defined as any primitive root of unity in `B`, that exists by definition. It is not
true in general that it is a root of `cyclotomic n B`, but this holds if `is_domain B` and
`ne_zero (↑n : B)`.

`zeta n A B` is defined using `exists.some`, which means we cannot control it.
For example, in normal mathematics, we can demand that `(zeta p ℤ ℤ[ζₚ] : ℚ(ζₚ))` is equal to
`zeta p ℚ ℚ(ζₚ)`, as we are just choosing "an arbitrary primitive root" and we can internally
specify that our choices agree. This is not the case here, and it is indeed impossible to prove that
these two are equal. Therefore, whenever possible, we prove our results for any primitive root,
and only at the "final step", when we need to provide an "explicit" primitive root, we use `zeta`.

-/

open polynomial algebra finset finite_dimensional is_cyclotomic_extension nat pnat set

universes u v w z

variables {p n : ℕ+} (A : Type w) (B : Type z) (K : Type u) {L : Type v} (C : Type w)
variables [comm_ring A] [comm_ring B] [algebra A B] [is_cyclotomic_extension {n} A B]

section zeta

namespace is_cyclotomic_extension

variables (n)

/-- If `B` is a `n`-th cyclotomic extension of `A`, then `zeta n A B` is a primitive root of
unity in `B`. -/
noncomputable def zeta : B :=
(exists_prim_root A $ set.mem_singleton n : ∃ r : B, is_primitive_root r n).some

/-- `zeta n A B` is a primitive `n`-th root of unity. -/
@[simp] lemma zeta_spec : is_primitive_root (zeta n A B) n :=
classical.some_spec (exists_prim_root A (set.mem_singleton n) : ∃ r : B, is_primitive_root r n)

lemma aeval_zeta [is_domain B] [ne_zero ((n : ℕ) : B)] :
  aeval (zeta n A B) (cyclotomic n A) = 0 :=
begin
  rw [aeval_def,  ← eval_map, ← is_root.def, map_cyclotomic, is_root_cyclotomic_iff],
  exact zeta_spec n A B
end

lemma zeta_is_root [is_domain B] [ne_zero ((n : ℕ) : B)] :
  is_root (cyclotomic n B) (zeta n A B) :=
by { convert aeval_zeta n A B, rw [is_root.def, aeval_def, eval₂_eq_eval_map, map_cyclotomic] }

lemma zeta_pow : (zeta n A B) ^ (n : ℕ) = 1 :=
(zeta_spec n A B).pow_eq_one

end is_cyclotomic_extension

end zeta

section no_order

variables [field K] [comm_ring L] [is_domain L] [algebra K L] [is_cyclotomic_extension {n} K L]
          {ζ : L} (hζ : is_primitive_root ζ n)

namespace is_primitive_root

variable {C}

/-- The `power_basis` given by a primitive root `η`. -/
@[simps] protected noncomputable def power_basis : power_basis K L :=
power_basis.map (algebra.adjoin.power_basis $ integral {n} K L ζ) $
  (subalgebra.equiv_of_eq _ _ (is_cyclotomic_extension.adjoin_primitive_root_eq_top hζ)).trans
  subalgebra.top_equiv

lemma power_basis_gen_mem_adjoin_zeta_sub_one :
  (hζ.power_basis K).gen ∈ adjoin K ({ζ - 1} : set L) :=
begin
  rw [power_basis_gen, adjoin_singleton_eq_range_aeval, alg_hom.mem_range],
  exact ⟨X + 1, by simp⟩
end

/-- The `power_basis` given by `η - 1`. -/
@[simps] noncomputable def sub_one_power_basis : power_basis K L :=
  (hζ.power_basis K).of_gen_mem_adjoin
    (is_integral_sub (is_cyclotomic_extension.integral {n} K L ζ) is_integral_one)
    (hζ.power_basis_gen_mem_adjoin_zeta_sub_one _)

variables {K} (C)

-- We are not using @[simps] to avoid a timeout.

/-- The equivalence between `L →ₐ[K] C` and `primitive_roots n C` given by a primitive root `ζ`. -/
noncomputable def embeddings_equiv_primitive_roots (C : Type*) [comm_ring C] [is_domain C]
  [algebra K C] (hirr : irreducible (cyclotomic n K)) : (L →ₐ[K] C) ≃ primitive_roots n C :=
((hζ.power_basis K).lift_equiv).trans
{ to_fun    := λ x,
  begin
    haveI := is_cyclotomic_extension.ne_zero' n K L,
    haveI hn := ne_zero.of_no_zero_smul_divisors K C n,
    refine ⟨x.1, _⟩,
    cases x,
    rwa [mem_primitive_roots n.pos, ←is_root_cyclotomic_iff, is_root.def,
         ←map_cyclotomic _ (algebra_map K C), hζ.minpoly_eq_cyclotomic_of_irreducible hirr,
         ←eval₂_eq_eval_map, ←aeval_def]
  end,
  inv_fun   := λ x,
  begin
    haveI := is_cyclotomic_extension.ne_zero' n K L,
    haveI hn := ne_zero.of_no_zero_smul_divisors K C n,
    refine ⟨x.1, _⟩,
    cases x,
    rwa [aeval_def, eval₂_eq_eval_map, hζ.power_basis_gen K,
         ←hζ.minpoly_eq_cyclotomic_of_irreducible hirr, map_cyclotomic, ←is_root.def,
         is_root_cyclotomic_iff, ← mem_primitive_roots n.pos]
  end,
  left_inv  := λ x, subtype.ext rfl,
  right_inv := λ x, subtype.ext rfl }

@[simp]
lemma embeddings_equiv_primitive_roots_apply_coe (C : Type*) [comm_ring C] [is_domain C]
  [algebra K C] (hirr : irreducible (cyclotomic n K)) (φ : L →ₐ[K] C) :
  (hζ.embeddings_equiv_primitive_roots C hirr φ : C) = φ ζ := rfl

end is_primitive_root

namespace is_cyclotomic_extension

variables {K} (L)

/-- If `irreducible (cyclotomic n K)` (in particular for `K = ℚ`), then the `finrank` of a
cyclotomic extension is `n.totient`. -/
lemma finrank (hirr : irreducible (cyclotomic n K)) :
  finrank K L = (n : ℕ).totient :=
begin
  haveI := is_cyclotomic_extension.ne_zero' n K L,
  rw [((zeta_spec n K L).power_basis K).finrank, is_primitive_root.power_basis_dim,
      ←(zeta_spec n K L).minpoly_eq_cyclotomic_of_irreducible hirr, nat_degree_cyclotomic]
end

end is_cyclotomic_extension

end no_order

section norm

namespace is_primitive_root

section comm_ring

variables [comm_ring L] {ζ : L} (hζ : is_primitive_root ζ n)
variables {K} [field K] [algebra K L]

/-- This mathematically trivial result is complementary to `norm_eq_one` below. -/
lemma norm_eq_neg_one_pow (hζ : is_primitive_root ζ 2) [is_domain L] :
  norm K ζ = (-1) ^ finrank K L :=
by rw [hζ.eq_neg_one_of_two_right, show -1 = algebra_map K L (-1), by simp,
       algebra.norm_algebra_map]

include hζ

/-- If `irreducible (cyclotomic n K)` (in particular for `K = ℚ`), the norm of a primitive root is
`1` if `n ≠ 2`. -/
lemma norm_eq_one [is_domain L] [is_cyclotomic_extension {n} K L] (hn : n ≠ 2)
  (hirr : irreducible (cyclotomic n K)) : norm K ζ = 1 :=
begin
  haveI := is_cyclotomic_extension.ne_zero' n K L,
  by_cases h1 : n = 1,
  { rw [h1, one_coe, one_right_iff] at hζ,
    rw [hζ, show 1 = algebra_map K L 1, by simp, algebra.norm_algebra_map, one_pow] },
  { replace h1 : 2 ≤ n,
    { by_contra' h,
      exact h1 (pnat.eq_one_of_lt_two h) },
    rw [← hζ.power_basis_gen K, power_basis.norm_gen_eq_coeff_zero_minpoly, hζ.power_basis_gen K,
      ← hζ.minpoly_eq_cyclotomic_of_irreducible hirr, cyclotomic_coeff_zero _ h1, mul_one,
      hζ.power_basis_dim K, ← hζ.minpoly_eq_cyclotomic_of_irreducible hirr, nat_degree_cyclotomic],
    exact (totient_even $ h1.lt_of_ne hn.symm).neg_one_pow }
end

/-- If `K` is linearly ordered, the norm of a primitive root is `1` if `n` is odd. -/
lemma norm_eq_one_of_linearly_ordered {K : Type*} [linear_ordered_field K] [algebra K L]
  (hodd : odd (n : ℕ)) : norm K ζ = 1 :=
begin
  have hz := congr_arg (norm K) ((is_primitive_root.iff_def _ n).1 hζ).1,
  rw [←(algebra_map K L).map_one , algebra.norm_algebra_map, one_pow, map_pow, ←one_pow ↑n] at hz,
  exact strict_mono.injective hodd.strict_mono_pow hz
end

lemma norm_of_cyclotomic_irreducible [is_domain L] [is_cyclotomic_extension {n} K L]
  (hirr : irreducible (cyclotomic n K)) : norm K ζ = ite (n = 2) (-1) 1 :=
begin
  split_ifs with hn,
  { unfreezingI {subst hn},
    convert norm_eq_neg_one_pow hζ,
    erw [is_cyclotomic_extension.finrank _ hirr, totient_two, pow_one],
    all_goals { apply_instance } },
  { exact hζ.norm_eq_one hn hirr }
end

end comm_ring

section field

variables [field L] {ζ : L} (hζ : is_primitive_root ζ n)
variables {K} [field K] [algebra K L]

include hζ

/-- If `irreducible (cyclotomic n K)` (in particular for `K = ℚ`), then the norm of
`ζ - 1` is `eval 1 (cyclotomic n ℤ)`. -/
lemma sub_one_norm_eq_eval_cyclotomic [is_cyclotomic_extension {n} K L]
  (h : 2 < (n : ℕ)) (hirr : irreducible (cyclotomic n K)) :
  norm K (ζ - 1) = ↑(eval 1 (cyclotomic n ℤ)) :=
begin
  haveI := is_cyclotomic_extension.ne_zero' n K L,
  let E := algebraic_closure L,
  obtain ⟨z, hz⟩ := is_alg_closed.exists_root _ (degree_cyclotomic_pos n E n.pos).ne.symm,
  apply (algebra_map K E).injective,
  letI := finite_dimensional {n} K L,
  letI := is_galois n K L,
  rw [norm_eq_prod_embeddings],
  conv_lhs { congr, skip, funext,
    rw [← neg_sub, alg_hom.map_neg, alg_hom.map_sub, alg_hom.map_one, neg_eq_neg_one_mul] },
  rw [prod_mul_distrib, prod_const, card_univ, alg_hom.card, is_cyclotomic_extension.finrank L hirr,
    (totient_even h).neg_one_pow, one_mul],
  have : finset.univ.prod (λ (σ : L →ₐ[K] E), 1 - σ ζ) = eval 1 (cyclotomic' n E),
  { rw [cyclotomic', eval_prod, ← @finset.prod_attach E E, ← univ_eq_attach],
    refine fintype.prod_equiv (hζ.embeddings_equiv_primitive_roots E hirr) _ _ (λ σ, _),
    simp },
  haveI : ne_zero ((n : ℕ) : E) := (ne_zero.of_no_zero_smul_divisors K _ (n : ℕ)),
  rw [this, cyclotomic', ← cyclotomic_eq_prod_X_sub_primitive_roots (is_root_cyclotomic_iff.1 hz),
    ← map_cyclotomic_int, _root_.map_int_cast, ←int.cast_one, eval_int_cast_map, eq_int_cast,
    int.cast_id]
end

/-- If `is_prime_pow (n : ℕ)`, `n ≠ 2` and `irreducible (cyclotomic n K)` (in particular for
`K = ℚ`), then the norm of `ζ - 1` is `(n : ℕ).min_fac`. -/
lemma sub_one_norm_is_prime_pow (hn : is_prime_pow (n : ℕ)) [is_cyclotomic_extension {n} K L]
  (hirr : irreducible (cyclotomic (n : ℕ) K)) (h : n ≠ 2) :
  norm K (ζ - 1) = (n : ℕ).min_fac :=
begin
  have := (coe_lt_coe 2 _).1 (lt_of_le_of_ne (succ_le_of_lt (is_prime_pow.one_lt hn))
    (function.injective.ne pnat.coe_injective h).symm),
  letI hprime : fact ((n : ℕ).min_fac.prime) := ⟨min_fac_prime (is_prime_pow.ne_one hn)⟩,
  rw [sub_one_norm_eq_eval_cyclotomic hζ this hirr],
  nth_rewrite 0 [← is_prime_pow.min_fac_pow_factorization_eq hn],
  obtain ⟨k, hk⟩ : ∃ k, ((n : ℕ).factorization) (n : ℕ).min_fac = k + 1 :=
    exists_eq_succ_of_ne_zero (((n : ℕ).factorization.mem_support_to_fun (n : ℕ).min_fac).1 $
      factor_iff_mem_factorization.2 $ (mem_factors (is_prime_pow.ne_zero hn)).2
        ⟨hprime.out, min_fac_dvd _⟩),
  simp [hk, sub_one_norm_eq_eval_cyclotomic hζ this hirr],
end

omit hζ

variable {A}

lemma minpoly_sub_one_eq_cyclotomic_comp [algebra K A] [is_domain A] {ζ : A}
  [is_cyclotomic_extension {n} K A] (hζ : is_primitive_root ζ n)
  (h : irreducible (polynomial.cyclotomic n K)) :
  minpoly K (ζ - 1) = (cyclotomic n K).comp (X + 1) :=
begin
  haveI := is_cyclotomic_extension.ne_zero' n K A,
  rw [show ζ - 1 = ζ + (algebra_map K A (-1)), by simp [sub_eq_add_neg], minpoly.add_algebra_map
    (is_cyclotomic_extension.integral {n} K A ζ), hζ.minpoly_eq_cyclotomic_of_irreducible h],
  simp
end

local attribute [instance] is_cyclotomic_extension.finite_dimensional
local attribute [instance] is_cyclotomic_extension.is_galois

/-- If `irreducible (cyclotomic (p ^ (k + 1)) K)` (in particular for `K = ℚ`) and `p` is a prime,
then the norm of `ζ ^ (p ^ s) - 1` is `p ^ (p ^ s)` if `p ^ (k - s + 1) ≠ 2`. See the next lemmas
for similar results. -/
lemma pow_sub_one_norm_prime_pow_ne_two {k s : ℕ} (hζ : is_primitive_root ζ ↑(p ^ (k + 1)))
  [hpri : fact (p : ℕ).prime] [is_cyclotomic_extension {p ^ (k + 1)} K L]
  (hirr : irreducible (cyclotomic (↑(p ^ (k + 1)) : ℕ) K)) (hs : s ≤ k)
  (htwo : p ^ (k - s + 1) ≠ 2) : norm K (ζ ^ ((p : ℕ) ^ s) - 1) = p ^ ((p : ℕ) ^ s) :=
begin
  have hirr₁ : irreducible (cyclotomic (p ^ (k - s + 1)) K) :=
  cyclotomic_irreducible_pow_of_irreducible_pow hpri.1 (by linarith) hirr,
  rw ←pnat.pow_coe at hirr₁,
  let η := ζ ^ ((p : ℕ) ^ s) - 1,
  let η₁ : K⟮η⟯ := intermediate_field.adjoin_simple.gen K η,
  have hη : is_primitive_root (η + 1) (p ^ (k + 1 - s)),
  { rw [sub_add_cancel],
    refine is_primitive_root.pow (p ^ (k + 1)).pos hζ _,
    rw [pnat.pow_coe, ← pow_add, add_comm s, nat.sub_add_cancel (le_trans hs (nat.le_succ k))] },
  haveI : is_cyclotomic_extension {p ^ (k - s + 1)} K K⟮η⟯,
  { suffices : is_cyclotomic_extension {p ^ (k - s + 1)} K K⟮η + 1⟯.to_subalgebra,
    { have H : K⟮η + 1⟯.to_subalgebra = K⟮η⟯.to_subalgebra,
      { simp only [intermediate_field.adjoin_simple_to_subalgebra_of_integral
          (is_cyclotomic_extension.integral {p ^ (k + 1)} K L _)],
        refine subalgebra.ext (λ x, ⟨λ hx, adjoin_le _ hx, λ hx, adjoin_le _ hx⟩),
        { simp only [set.singleton_subset_iff, set_like.mem_coe],
          exact subalgebra.add_mem _ (subset_adjoin (mem_singleton η)) (subalgebra.one_mem _) },
        { simp only [set.singleton_subset_iff, set_like.mem_coe],
          nth_rewrite 0 [← add_sub_cancel η 1],
          refine subalgebra.sub_mem _ (subset_adjoin (mem_singleton _)) (subalgebra.one_mem _) } },
      rw [H] at this,
      exact this },
    rw [intermediate_field.adjoin_simple_to_subalgebra_of_integral
      (is_cyclotomic_extension.integral {p ^ (k + 1)} K L _)],
    have hη' : is_primitive_root (η + 1) ↑(p ^ (k + 1 - s)) := by simpa using hη,
    convert hη'.adjoin_is_cyclotomic_extension K,
    rw [nat.sub_add_comm hs] },
  replace hη : is_primitive_root (η₁ + 1) ↑(p ^ (k - s + 1)),
  { apply coe_submonoid_class_iff.1,
    convert hη,
    rw [nat.sub_add_comm hs, pow_coe] },
  rw [norm_eq_norm_adjoin K],
  { have H := hη.sub_one_norm_is_prime_pow _ hirr₁ htwo,
    swap, { rw [pnat.pow_coe], exact hpri.1.is_prime_pow.pow (nat.succ_ne_zero _) },
    rw [add_sub_cancel] at H,
    rw [H, coe_coe],
    congr,
    { rw [pnat.pow_coe, nat.pow_min_fac, hpri.1.min_fac_eq], exact nat.succ_ne_zero _ },
    have := finite_dimensional.finrank_mul_finrank K K⟮η⟯ L,
    rw [is_cyclotomic_extension.finrank L hirr, is_cyclotomic_extension.finrank K⟮η⟯ hirr₁,
      pnat.pow_coe, pnat.pow_coe, nat.totient_prime_pow hpri.out (k - s).succ_pos,
      nat.totient_prime_pow hpri.out k.succ_pos, mul_comm _ (↑p - 1), mul_assoc,
      mul_comm (↑p ^ (k.succ - 1))] at this,
    replace this := mul_left_cancel₀ (tsub_pos_iff_lt.2 hpri.out.one_lt).ne' this,
    have Hex : k.succ - 1 = (k - s).succ - 1 + s,
    { simp only [nat.succ_sub_succ_eq_sub, tsub_zero],
      exact (nat.sub_add_cancel hs).symm },
    rw [Hex, pow_add] at this,
    exact mul_left_cancel₀ (pow_ne_zero _ hpri.out.ne_zero) this },
  all_goals { apply_instance }
end

/-- If `irreducible (cyclotomic (p ^ (k + 1)) K)` (in particular for `K = ℚ`) and `p` is a prime,
then the norm of `ζ ^ (p ^ s) - 1` is `p ^ (p ^ s)` if `p ≠ 2`. -/
lemma pow_sub_one_norm_prime_ne_two {k : ℕ} (hζ : is_primitive_root ζ ↑(p ^ (k + 1)))
  [hpri : fact (p : ℕ).prime] [is_cyclotomic_extension {p ^ (k + 1)} K L]
  (hirr : irreducible (cyclotomic (↑(p ^ (k + 1)) : ℕ) K)) {s : ℕ} (hs : s ≤ k)
  (hodd : p ≠ 2) : norm K (ζ ^ ((p : ℕ) ^ s) - 1) = p ^ ((p : ℕ) ^ s) :=
begin
  refine hζ.pow_sub_one_norm_prime_pow_ne_two hirr hs (λ h, _),
  rw [← pnat.coe_inj, pnat.coe_bit0, pnat.one_coe, pnat.pow_coe, ← pow_one 2] at h,
  replace h := eq_of_prime_pow_eq (prime_iff.1 hpri.out) (prime_iff.1 nat.prime_two)
    ((k - s).succ_pos) h,
  rw [← pnat.one_coe, ← pnat.coe_bit0, pnat.coe_inj] at h,
  exact hodd h
end

/-- If `irreducible (cyclotomic (p ^ (k + 1)) K)` (in particular for `K = ℚ`) and `p` is an odd
prime, then the norm of `ζ - 1` is `p`. -/
lemma sub_one_norm_prime_ne_two {k : ℕ} (hζ : is_primitive_root ζ ↑(p ^ (k + 1)))
  [hpri : fact (p : ℕ).prime] [is_cyclotomic_extension {p ^ (k + 1)} K L]
  (hirr : irreducible (cyclotomic (↑(p ^ (k + 1)) : ℕ) K)) (h : p ≠ 2) :
  norm K (ζ - 1) = p :=
by simpa using hζ.pow_sub_one_norm_prime_ne_two hirr k.zero_le h

/-- If `irreducible (cyclotomic p K)` (in particular for `K = ℚ`) and `p` is an odd prime,
then the norm of `ζ - 1` is `p`. -/
lemma sub_one_norm_prime [hpri : fact (p : ℕ).prime] [hcyc : is_cyclotomic_extension {p} K L]
  (hζ: is_primitive_root ζ p) (hirr : irreducible (cyclotomic p K)) (h : p ≠ 2) :
  norm K (ζ - 1) = p :=
begin
  replace hirr : irreducible (cyclotomic (↑(p ^ (0 + 1)) : ℕ) K) := by simp [hirr],
  replace hζ : is_primitive_root ζ (↑(p ^ (0 + 1)) : ℕ) := by simp [hζ],
  haveI : is_cyclotomic_extension {p ^ (0 + 1)} K L := by simp [hcyc],
  simpa using sub_one_norm_prime_ne_two hζ hirr h
end

/-- If `irreducible (cyclotomic (2 ^ (k + 1)) K)` (in particular for `K = ℚ`), then the norm of
`ζ ^ (2 ^ k) - 1` is `(-2) ^ (2 ^ k)`. -/
lemma pow_sub_one_norm_two {k : ℕ} (hζ : is_primitive_root ζ (2 ^ (k + 1)))
  [is_cyclotomic_extension {2 ^ (k + 1)} K L]
  (hirr : irreducible (cyclotomic (2 ^ (k + 1)) K)) :
  norm K (ζ ^ (2 ^ k) - 1) = (-2) ^ (2 ^ k) :=
begin
  have := hζ.pow_of_dvd (λ h, two_ne_zero (pow_eq_zero h)) (pow_dvd_pow 2 (le_succ k)),
  rw [nat.pow_div (le_succ k) zero_lt_two, nat.succ_sub (le_refl k), nat.sub_self, pow_one] at this,
  have H : (-1 : L) - (1 : L) = algebra_map K L (-2),
  { simp only [_root_.map_neg, map_bit0, _root_.map_one],
    ring },
  replace hirr : irreducible (cyclotomic (2 ^ (k + 1) : ℕ+) K) := by simp [hirr],
  rw [this.eq_neg_one_of_two_right, H, algebra.norm_algebra_map,
    is_cyclotomic_extension.finrank L hirr,
    pow_coe, pnat.coe_bit0, one_coe, totient_prime_pow nat.prime_two (zero_lt_succ k),
    succ_sub_succ_eq_sub, tsub_zero, mul_one]
end

/-- If `irreducible (cyclotomic (2 ^ k) K)` (in particular for `K = ℚ`) and `k` is at least `2`,
then the norm of `ζ - 1` is `2`. -/
lemma sub_one_norm_two {k : ℕ} (hζ : is_primitive_root ζ (2 ^ k)) (hk : 2 ≤ k)
  [H : is_cyclotomic_extension {2 ^ k} K L] (hirr : irreducible (cyclotomic (2 ^ k) K)) :
  norm K (ζ - 1) = 2 :=
begin
  have : 2 < (2 ^ k : ℕ+),
  { simp only [← coe_lt_coe, pnat.coe_bit0, one_coe, pow_coe],
    nth_rewrite 0 [← pow_one 2],
    exact pow_lt_pow one_lt_two (lt_of_lt_of_le one_lt_two hk) },
  replace hirr : irreducible (cyclotomic (2 ^ k : ℕ+) K) := by simp [hirr],
  replace hζ : is_primitive_root ζ (2 ^ k : ℕ+) := by simp [hζ],
  obtain ⟨k₁, hk₁⟩ := exists_eq_succ_of_ne_zero ((lt_of_lt_of_le zero_lt_two hk).ne.symm),
  simpa [hk₁] using sub_one_norm_eq_eval_cyclotomic hζ this hirr,
end

/-- If `irreducible (cyclotomic (p ^ (k + 1)) K)` (in particular for `K = ℚ`) and `p` is a prime,
then the norm of `ζ ^ (p ^ s) - 1` is `p ^ (p ^ s)` if `k ≠ 0` and `s ≤ k`. -/
lemma pow_sub_one_norm_prime_pow_of_ne_zero {k s : ℕ} (hζ : is_primitive_root ζ ↑(p ^ (k + 1)))
  [hpri : fact (p : ℕ).prime] [hcycl : is_cyclotomic_extension {p ^ (k + 1)} K L]
  (hirr : irreducible (cyclotomic (↑(p ^ (k + 1)) : ℕ) K)) (hs : s ≤ k)
  (hk : k ≠ 0) : norm K (ζ ^ ((p : ℕ) ^ s) - 1) = p ^ ((p : ℕ) ^ s) :=
begin
  by_cases htwo : p ^ (k - s + 1) = 2,
  { have hp : p = 2,
    { rw [← pnat.coe_inj, pnat.coe_bit0, pnat.one_coe, pnat.pow_coe, ← pow_one 2] at htwo,
      replace htwo := eq_of_prime_pow_eq (prime_iff.1 hpri.out) (prime_iff.1 nat.prime_two)
        (succ_pos _) htwo,
      rwa [show 2 = ((2 : ℕ+) : ℕ), by simp, pnat.coe_inj] at htwo },
    replace hs : s = k,
    { rw [hp, ← pnat.coe_inj, pnat.pow_coe, pnat.coe_bit0, pnat.one_coe] at htwo,
      nth_rewrite 1 [← pow_one 2] at htwo,
      replace htwo := nat.pow_right_injective rfl.le htwo,
      rw [add_left_eq_self, nat.sub_eq_zero_iff_le] at htwo,
      refine le_antisymm hs htwo },
    simp only [hs, hp, pnat.coe_bit0, one_coe, coe_coe, cast_bit0, cast_one,
      pow_coe] at ⊢ hζ hirr hcycl,
    haveI := hcycl,
    obtain ⟨k₁, hk₁⟩ := nat.exists_eq_succ_of_ne_zero hk,
    rw [hζ.pow_sub_one_norm_two hirr],
    rw [hk₁, pow_succ, pow_mul, neg_eq_neg_one_mul, mul_pow, neg_one_sq, one_mul, ← pow_mul,
      ← pow_succ] },
  { exact hζ.pow_sub_one_norm_prime_pow_ne_two hirr hs htwo }
end

end field

end is_primitive_root

namespace is_cyclotomic_extension

open is_primitive_root

variables {K} (L) [field K] [field L] [algebra K L]
/-- If `irreducible (cyclotomic n K)` (in particular for `K = ℚ`), the norm of `zeta n K L` is `1`
if `n` is odd. -/
lemma norm_zeta_eq_one [is_cyclotomic_extension {n} K L] (hn : n ≠ 2)
  (hirr : irreducible (cyclotomic n K)) : norm K (zeta n K L) = 1 :=
(zeta_spec n K L).norm_eq_one hn hirr

/-- If `is_prime_pow (n : ℕ)`, `n ≠ 2` and `irreducible (cyclotomic n K)` (in particular for
`K = ℚ`), then the norm of `zeta n K L - 1` is `(n : ℕ).min_fac`. -/
lemma is_prime_pow_norm_zeta_sub_one (hn : is_prime_pow (n : ℕ))
  [is_cyclotomic_extension {n} K L]
  (hirr : irreducible (cyclotomic (n : ℕ) K)) (h : n ≠ 2) :
  norm K (zeta n K L - 1) = (n : ℕ).min_fac :=
(zeta_spec n K L).sub_one_norm_is_prime_pow hn hirr h

/-- If `irreducible (cyclotomic (p ^ (k + 1)) K)` (in particular for `K = ℚ`) and `p` is a prime,
then the norm of `(zeta (p ^ (k + 1)) K L) ^ (p ^ s) - 1` is `p ^ (p ^ s)`
if `p ^ (k - s + 1) ≠ 2`. -/
lemma prime_ne_two_pow_norm_zeta_pow_sub_one {k : ℕ} [hpri : fact (p : ℕ).prime]
  [is_cyclotomic_extension {p ^ (k + 1)} K L]
  (hirr : irreducible (cyclotomic (↑(p ^ (k + 1)) : ℕ) K))  {s : ℕ} (hs : s ≤ k)
  (htwo : p ^ (k - s + 1) ≠ 2) :
  norm K ((zeta (p ^ (k + 1)) K L) ^ ((p : ℕ) ^ s) - 1) = p ^ ((p : ℕ) ^ s) :=
(zeta_spec _ K L).pow_sub_one_norm_prime_pow_ne_two hirr hs htwo

/-- If `irreducible (cyclotomic (p ^ (k + 1)) K)` (in particular for `K = ℚ`) and `p` is an odd
prime, then the norm of `zeta (p ^ (k + 1)) K L - 1` is `p`. -/
lemma prime_ne_two_pow_norm_zeta_sub_one {k : ℕ} [hpri : fact (p : ℕ).prime]
  [is_cyclotomic_extension {p ^ (k + 1)} K L]
  (hirr : irreducible (cyclotomic (↑(p ^ (k + 1)) : ℕ) K)) (h : p ≠ 2) :
  norm K (zeta (p ^ (k + 1)) K L - 1) = p :=
(zeta_spec _ K L).sub_one_norm_prime_ne_two hirr h

/-- If `irreducible (cyclotomic p K)` (in particular for `K = ℚ`) and `p` is an odd prime,
then the norm of `zeta p K L - 1` is `p`. -/
lemma prime_ne_two_norm_zeta_sub_one [hpri : fact (p : ℕ).prime]
  [hcyc : is_cyclotomic_extension {p} K L] (hirr : irreducible (cyclotomic p K)) (h : p ≠ 2) :
  norm K (zeta p K L - 1) = p :=
(zeta_spec _ K L).sub_one_norm_prime hirr h

/-- If `irreducible (cyclotomic (2 ^ k) K)` (in particular for `K = ℚ`) and `k` is at least `2`,
then the norm of `zeta (2 ^ k) K L - 1` is `2`. -/
lemma two_pow_norm_zeta_sub_one {k : ℕ} (hk : 2 ≤ k)
  [is_cyclotomic_extension {2 ^ k} K L] (hirr : irreducible (cyclotomic (2 ^ k) K)) :
  norm K (zeta (2 ^ k) K L - 1) = 2 :=
sub_one_norm_two (zeta_spec (2 ^ k) K L) hk hirr

end is_cyclotomic_extension

end norm
