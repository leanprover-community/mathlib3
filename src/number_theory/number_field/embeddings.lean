/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Xavier Roblot
-/

import analysis.normed_space.basic
import number_theory.number_field.basic
import topology.algebra.polynomial

/-!
# Embeddings of number fields
This file defines the embeddings of a number field into an algebraic closed field.

## Main Results
* `number_field.embeddings.eq_roots`: let `x ∈ K` with `K` number field and let `A` be an algebraic
  closed field of char. 0, then the images of `x` by the embeddings of `K` in `A` are exactly the
  roots in `A` of the minimal polynomial of `x` over `ℚ`.
* `number_field.embeddings.pow_eq_one_of_norm_eq_one`: an algebraic integer whose conjugates are
  all of norm one is a root of unity.

## Tags
number field, embeddings
-/

namespace number_field.embeddings

section fintype

open finite_dimensional

variables (K : Type*) [field K] [number_field K]
variables (A : Type*) [field A] [char_zero A]

/-- There are finitely many embeddings of a number field. -/
noncomputable instance : fintype (K →+* A) := fintype.of_equiv (K →ₐ[ℚ] A)
ring_hom.equiv_rat_alg_hom.symm

variables [is_alg_closed A]

/-- The number of embeddings of a number field is equal to its finrank. -/
lemma card : fintype.card (K →+* A) = finrank ℚ K :=
by rw [fintype.of_equiv_card ring_hom.equiv_rat_alg_hom.symm, alg_hom.card]

end fintype

section roots

open set polynomial

/-- Let `A` an algebraically closed field and let `x ∈ K`, with `K` a number field. For `F`,
subfield of `K`, the images of `x` by the `F`-algebra morphisms from `K` to `A` are exactly
the roots in `A` of the minimal polynomial of `x` over `F`. -/
-- ! should be moved to another namespace
lemma range_eq_roots (F K A : Type*) [field F] [field K] [field A] [is_alg_closed A]
  [algebra F K] (hK : algebra.is_algebraic F K) [algebra F A] (x : K) :
  range (λ ψ : K →ₐ[F] A, ψ x) = (minpoly F x).root_set A :=
begin
  have := algebra.is_algebraic_iff_is_integral.1 hK,
  ext a, rw mem_root_set_iff (minpoly.ne_zero $ this x) a,
  refine ⟨_, λ ha, _⟩,
  { rintro ⟨ψ, rfl⟩, rw [aeval_alg_hom_apply ψ x, minpoly.aeval, map_zero] },
  { let Fx := adjoin_root (minpoly F x),
    haveI : fact (irreducible $ minpoly F x) := ⟨minpoly.irreducible $ this x⟩,
    have hx : aeval x (minpoly F x) = 0 := minpoly.aeval F x,
    letI : algebra Fx A := (adjoin_root.lift (algebra_map F A) a ha).to_algebra,
    letI : algebra Fx K := (adjoin_root.lift (algebra_map F K) x hx).to_algebra,
    haveI : is_scalar_tower F Fx A := is_scalar_tower.of_ring_hom (adjoin_root.lift_hom _ _ ha),
    haveI : is_scalar_tower F Fx K := is_scalar_tower.of_ring_hom (adjoin_root.lift_hom _ _ hx),
    let ψ₀ : K →ₐ[Fx] A := is_alg_closed.lift (algebra.is_algebraic_of_larger_base F Fx hK),
    exact ⟨ψ₀.restrict_scalars F, (congr_arg ψ₀ (adjoin_root.lift_root hx).symm).trans $
      (ψ₀.commutes _).trans $ adjoin_root.lift_root ha⟩ },
end

variables (K A : Type*) [field K] [number_field K] [field A] [char_zero A] [is_alg_closed A] (x : K)

/-- Let `A` be an algebraically closed field and let `x ∈ K`, with `K` a number field.
The images of `x` by the embeddings of `K` in `A` are exactly the roots in `A` of
the minimal polynomial of `x` over `ℚ`. -/
lemma rat_range_eq_roots : range (λ φ : K →+* A, φ x) = (minpoly ℚ x).root_set A :=
begin
  convert range_eq_roots ℚ K A (number_field.is_algebraic K) x using 1,
  ext a,
  exact ⟨λ ⟨φ, hφ⟩, ⟨φ.to_rat_alg_hom, hφ⟩, λ ⟨φ, hφ⟩, ⟨φ.to_ring_hom, hφ⟩⟩,
end

end roots

section bounded

open finite_dimensional polynomial set

variables {K : Type*} [field K] [number_field K]
variables {A : Type*} [normed_field A] [is_alg_closed A] [normed_algebra ℚ A]

lemma coeff_bdd_of_norm_le {B : ℝ} {x : K} (h : ∀ φ : K →+* A, ∥φ x∥ ≤ B) (i : ℕ) :
  ∥(minpoly ℚ x).coeff i∥ ≤ (max B 1) ^ (finrank ℚ K) * (finrank ℚ K).choose ((finrank ℚ K) / 2) :=
begin
  have hx : is_integral ℚ x := is_separable.is_integral _ _,
  rw [← norm_algebra_map' A, ← coeff_map (algebra_map ℚ A)],
  refine coeff_bdd_of_roots_le _ (minpoly.monic hx) (is_alg_closed.splits_codomain _)
    (minpoly.nat_degree_le hx) (λ z hz, _) i,
  classical, rw [← multiset.mem_to_finset, ← finset.mem_coe] at hz,
  haveI : char_zero A := char_zero_of_injective_algebra_map (algebra_map ℚ A).injective,
  obtain ⟨φ, rfl⟩ := (rat_range_eq_roots K A x).symm.subset (_ : z ∈ _), { exact h φ },
  rw root_set_def, convert hz using 5,
end

variables (K A)

/-- Let `B` be a real number. The set of algebraic integers in `K` whose conjugates are all
smaller in norm than `B` is finite. -/
lemma finite_of_norm_le (B : ℝ) :
  {x : K | is_integral ℤ x ∧ ∀ φ : K →+* A, ∥φ x∥ ≤ B}.finite :=
begin
  let C := nat.ceil ((max B 1) ^ (finrank ℚ K) * (finrank ℚ K).choose ((finrank ℚ K) / 2)),
  have := bUnion_roots_finite (algebra_map ℤ K) (finrank ℚ K) (finite_Icc (-C : ℤ) C),
  refine this.subset (λ x hx, _),
  have h_map_ℚ_minpoly := minpoly.gcd_domain_eq_field_fractions' ℚ hx.1,
  simp_rw mem_Union,
  refine ⟨_, ⟨_, λ i, _⟩, (mem_root_set_iff (minpoly.ne_zero hx.1) x).2 (minpoly.aeval ℤ x)⟩,
  { rw [← (minpoly.monic hx.1).nat_degree_map (_ : ℤ →+* ℚ), ← h_map_ℚ_minpoly],
    exact minpoly.nat_degree_le (is_integral_of_is_scalar_tower _ hx.1), },
  rw [mem_Icc, ← abs_le, ← @int.cast_le ℝ],
  apply le_trans _ (nat.le_ceil _),
  convert coeff_bdd_of_norm_le hx.2 i,
  rw [h_map_ℚ_minpoly, coeff_map, eq_int_cast, int.norm_cast_rat, int.norm_eq_abs, int.cast_abs],
end

/-- An algebraic integer whose conjugates are all of norm one is a root of unity. -/
lemma pow_eq_one_of_norm_eq_one {x : K}
  (hxi : is_integral ℤ x) (hx : ∀ φ : K →+* A, ∥φ x∥ = 1) :
  ∃ (n : ℕ) (hn : 0 < n), x ^ n = 1 :=
begin
  obtain ⟨a, -, b, -, habne, h⟩ := @set.infinite.exists_ne_map_eq_of_maps_to _ _ _ _
    ((^) x : ℕ → K) set.infinite_univ _ (finite_of_norm_le K A (1:ℝ)),
  { replace habne := habne.lt_or_lt,
    wlog : b < a := habne using [a b],
    refine ⟨a - b, tsub_pos_of_lt habne, _⟩,
    rw [← nat.sub_add_cancel habne.le, pow_add, mul_left_eq_self₀] at h,
    refine h.resolve_right (λ hp, _),
    specialize hx (is_alg_closed.lift (number_field.is_algebraic K)).to_ring_hom,
    rw [pow_eq_zero hp, map_zero, norm_zero] at hx, norm_num at hx },
  { rw set.maps_univ_to,
    exact λ a, ⟨hxi.pow a, λ φ, by simp [hx φ, norm_pow, one_pow]⟩, },
end

end bounded

end number_field.embeddings
