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
lemma range_eq_roots (F K A : Type*) [field F] [number_field F] [field K] [number_field K]
  [field A] [is_alg_closed A] [algebra F K] [algebra F A] (x : K) :
  range (λ ψ : K →ₐ[F] A, ψ x) = (minpoly F x).root_set A :=
begin
  haveI : finite_dimensional F K := finite_dimensional.right ℚ  _ _ ,
  have hx : is_integral F x := is_separable.is_integral F x,
  ext a, split,
  { rintro ⟨ψ, hψ⟩,
    rw [mem_root_set_iff, ←hψ],
    { rw aeval_alg_hom_apply ψ x (minpoly F x),
      simp only [minpoly.aeval, map_zero], },
    exact minpoly.ne_zero hx, },
  { intro ha,
    let Fx := adjoin_root (minpoly F x),
    haveI : fact (irreducible $ minpoly F x) := ⟨minpoly.irreducible hx⟩,
    have hK : (aeval x) (minpoly F x) = 0 := minpoly.aeval _ _,
    have hA : (aeval a) (minpoly F x) = 0,
    { rwa [aeval_def, ←eval_map, ←mem_root_set_iff'],
      exact monic.ne_zero (monic.map (algebra_map F A) (minpoly.monic hx)), },
    letI : algebra Fx A := ring_hom.to_algebra (by convert adjoin_root.lift (algebra_map F A) a hA),
    letI : algebra Fx K := ring_hom.to_algebra (by convert adjoin_root.lift (algebra_map F K) x hK),
    haveI : finite_dimensional Fx K := finite_dimensional.right ℚ  _ _ ,
    let ψ₀ : K →ₐ[Fx] A := is_alg_closed.lift (algebra.is_algebraic_of_finite _ _),
    haveI : is_scalar_tower F Fx K := is_scalar_tower.of_ring_hom (adjoin_root.lift_hom _ _ hK),
    haveI : is_scalar_tower F Fx A := is_scalar_tower.of_ring_hom (adjoin_root.lift_hom _ _ hA),
    let ψ : K →ₐ[F] A := alg_hom.restrict_scalars F ψ₀,
    refine ⟨ψ, _⟩,
    rw (_ : x = (algebra_map Fx K) (adjoin_root.root (minpoly F x))),
    rw (_ : a = (algebra_map Fx A) (adjoin_root.root (minpoly F x))),
    exact alg_hom.commutes _ _,
    exact (adjoin_root.lift_root hA).symm,
    exact (adjoin_root.lift_root hK).symm, },
end

variables (K A : Type*) [field K] [number_field K] [field A] [char_zero A] [is_alg_closed A] (x : K)

/-- Let `A` be an algebraically closed field and let `x ∈ K`, with `K` a number field.
The images of `x` by the embeddings of `K` in `A` are exactly the roots in `A` of
the minimal polynomial of `x` over `ℚ`. -/
lemma rat_range_eq_roots : range (λ φ : K →+* A, φ x) = (minpoly ℚ x).root_set A :=
begin
  convert range_eq_roots ℚ K A x using 1,
  ext a,
  exact ⟨λ ⟨φ, hφ⟩, ⟨φ.to_rat_alg_hom, hφ⟩, λ ⟨φ, hφ⟩, ⟨φ.to_ring_hom, hφ⟩⟩,
end

end roots

section bounded

open finite_dimensional polynomial set

variables {K : Type*} [field K] [number_field K]
variables {A : Type*} [normed_field A] [is_alg_closed A] [normed_algebra ℚ A]

lemma coeff_bdd_of_norm_le {B : ℝ} {x : K} (h : ∀ φ : K →+* A, ∥φ x∥ ≤ B) (i : ℕ):
  ∥(minpoly ℚ x).coeff i∥ ≤ (max B 1) ^ (finrank ℚ K) * (finrank ℚ K).choose ((finrank ℚ K) / 2) :=
begin
  have hx : is_integral ℚ x := is_separable.is_integral _ _,
  rw (by rw [coeff_map, norm_algebra_map'] :
    ∥(minpoly ℚ x).coeff i∥ = ∥(map (algebra_map ℚ A) (minpoly ℚ x)).coeff i∥),
  refine coeff_bdd_of_roots_le _ (minpoly.monic hx) (is_alg_closed.splits_codomain _)
    (minpoly.nat_degree_le hx) _ i,
  intros z hz,
  rsuffices ⟨φ, rfl⟩ : ∃ (φ : K →+* A), φ x = z, {exact h φ },
  letI : char_zero A := char_zero_of_injective_algebra_map (algebra_map ℚ _).injective,
  rw [← set.mem_range, rat_range_eq_roots, mem_root_set_iff, aeval_def],
  convert (mem_roots_map _).mp hz,
  repeat { exact monic.ne_zero (minpoly.monic hx), },
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
  have h_map_rat_minpoly := minpoly.gcd_domain_eq_field_fractions' ℚ hx.1,
  rw mem_Union,
  use minpoly ℤ x,
  rw [mem_Union, exists_prop],
  refine ⟨⟨_, λ i, _⟩, _⟩,
  { rw [← nat_degree_map_eq_of_injective (algebra_map ℤ ℚ).injective_int _, ← h_map_rat_minpoly],
    exact minpoly.nat_degree_le (is_integral_of_is_scalar_tower _ hx.1), },
  { rw [mem_Icc, ← abs_le, ← @int.cast_le ℝ],
    apply le_trans _ (nat.le_ceil _),
    convert coeff_bdd_of_norm_le hx.2 i,
    simp only [h_map_rat_minpoly, coeff_map, eq_int_cast, int.norm_cast_rat, int.norm_eq_abs,
      int.cast_abs], },
  { rw [finset.mem_coe, multiset.mem_to_finset, mem_roots, is_root.def, ← eval₂_eq_eval_map,
      ← aeval_def],
    { exact minpoly.aeval ℤ x, },
    { exact monic.ne_zero (monic.map (algebra_map ℤ K) (minpoly.monic hx.1)), }},
end

/-- An algebraic integer whose conjugates are all of norm one is a root of unity. -/
lemma pow_eq_one_of_norm_eq_one {x : K}
  (hxi : is_integral ℤ x)  (hx : ∀ φ : K →+* A, ∥φ x∥ = 1) :
  ∃ (n : ℕ) (hn : 0 < n), x ^ n = 1 :=
begin
  obtain ⟨a, -, b, -, habne, h⟩ := @set.infinite.exists_ne_map_eq_of_maps_to _ _ _ _
    ((^) x : ℕ → K) set.infinite_univ _ (finite_of_norm_le K A (1:ℝ)),
  { wlog hab : a ≤ b,
    { exact this hxi hx b a habne.symm h.symm (le_of_not_le hab) },
    refine ⟨b - a, tsub_pos_of_lt (hab.lt_of_ne habne), _⟩,
    have hxne : x ≠ 0,
    { contrapose! hx,
      simp only [hx, norm_zero, ring_hom.map_zero, ne.def, not_false_iff, zero_ne_one],
      use (is_alg_closed.lift (number_field.is_algebraic K)).to_ring_hom, },
    { rw [pow_sub₀ _ hxne hab, h, mul_inv_cancel (pow_ne_zero b hxne)], }},
  { rw set.maps_univ_to,
    exact λ a, ⟨hxi.pow a, λ φ, by simp [hx φ, norm_pow, one_pow]⟩, },
end

end bounded

end number_field.embeddings
