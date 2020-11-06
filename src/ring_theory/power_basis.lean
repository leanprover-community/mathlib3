/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import field_theory.adjoin
import field_theory.minimal_polynomial
import ring_theory.adjoin
import ring_theory.adjoin_root
import ring_theory.algebraic

/-!
# Power basis

This file defines a structure `power_basis R S`, giving a basis of the
`R`-algebra `S` as a finite list of powers `1, x, ..., x^n`.
There are also constructors for `power_basis` when adjoining an algebraic
element to a ring/field.

## Definitions

* `power_basis R A`: a structure containing an `x` and an `n` such that
`1, x, ..., x^n` is a basis for the `R`-algebra `A` (viewed as an `R`-module).

## Implementation notes

Throughout this file, `R`, `S`, ... are `comm_ring`s, `A`, `B`, ... are
`integral_domain`s and `K`, `L`, ... are `field`s.
`S` is an `R`-algebra, `B` is an `A`-algebra, `L` is a `K`-algebra.

## Tags

power basis, powerbasis

-/

open polynomial

variables {R S T : Type*} [comm_ring R] [comm_ring S] [comm_ring T]
variables [algebra R S] [algebra S T] [algebra R T] [is_scalar_tower R S T]
variables {A B : Type*} [integral_domain A] [integral_domain B] [algebra A B]
variables {K L : Type*} [field K] [field L] [algebra K L]

/-- `pb : power_basis R S` states that `1, pb.gen, ..., pb.gen ^ (pb.dim - 1)`
is a basis for the `R`-algebra `S` (viewed as `R`-module).

This is a structure, not a class, since the same algebra can have many power bases.
For the common case where `S` is defined by adjoining an integral element to `R`,
the canonical power basis is given by `{algebra,intermediate_field}.adjoin.power_basis`.
-/
@[nolint has_inhabited_instance]
structure power_basis (R S : Type*) [comm_ring R] [ring S] [algebra R S] :=
(gen : S)
(dim : ℕ)
(is_basis : is_basis R (λ (i : fin dim), gen ^ (i : ℕ)))

namespace power_basis

/-- Cannot be an instance because `power_basis` cannot be a class. -/
lemma finite_dimensional [algebra K S]
  (pb : power_basis K S) : finite_dimensional K S :=
finite_dimensional.of_fintype_basis pb.is_basis

/-- TODO: this mixes `polynomial` and `finsupp`, we should hide this behind a
new function `polynomial.of_finsupp`. -/
lemma polynomial.mem_supported_range {f : polynomial R} {d : ℕ} :
  (f : finsupp ℕ R) ∈ finsupp.supported R R (↑(finset.range d) : set ℕ) ↔ f.degree < d :=
by { simp_rw [finsupp.mem_supported', finset.mem_coe, finset.mem_range, not_lt,
              degree_lt_iff_coeff_zero],
     refl }

lemma mem_span_pow' {x y : S} {d : ℕ} :
  y ∈ submodule.span R (set.range (λ (i : fin d), x ^ (i : ℕ))) ↔
    ∃ f : polynomial R, f.degree < d ∧ y = aeval x f :=
begin
  have : set.range (λ (i : fin d), x ^ (i : ℕ)) = (λ (i : ℕ), x ^ i) '' ↑(finset.range d),
  { ext n,
    simp_rw [set.mem_range, set.mem_image, finset.mem_coe, finset.mem_range],
    exact ⟨λ ⟨⟨i, hi⟩, hy⟩, ⟨i, hi, hy⟩, λ ⟨i, hi, hy⟩, ⟨⟨i, hi⟩, hy⟩⟩ },
  rw [this, finsupp.mem_span_iff_total],
  -- In the next line we use that `polynomial R := finsupp ℕ R`.
  -- It would be nice to have a function `polynomial.of_finsupp`.
  apply exists_congr,
  rintro (f : polynomial R),
  simp only [exists_prop, polynomial.mem_supported_range, eq_comm],
  apply and_congr iff.rfl,
  split;
  { rintro rfl;
    rw [finsupp.total_apply, aeval_def, eval₂_eq_sum, eq_comm],
    apply finset.sum_congr rfl,
    rintro i -,
    simp only [algebra.smul_def] }
end

lemma mem_span_pow {x y : S} {d : ℕ} (hd : d ≠ 0) :
  y ∈ submodule.span R (set.range (λ (i : fin d), x ^ (i : ℕ))) ↔
    ∃ f : polynomial R, f.nat_degree < d ∧ y = aeval x f :=
begin
  rw mem_span_pow',
  split;
  { rintros ⟨f, h, hy⟩,
    refine ⟨f, _, hy⟩,
    by_cases hf : f = 0,
    { simp only [hf, nat_degree_zero, degree_zero] at h ⊢,
      exact lt_of_le_of_ne (nat.zero_le d) hd.symm <|> exact with_bot.bot_lt_some d },
    simpa only [degree_eq_nat_degree hf, with_bot.coe_lt_coe] using h },
end

end power_basis

lemma is_integral_algebra_map_iff {x : S} (hST : function.injective (algebra_map S T)) :
  is_integral R (algebra_map S T x) ↔ is_integral R x :=
begin
  split; rintros ⟨f, hf, hx⟩; use [f, hf],
  { exact is_scalar_tower.aeval_eq_zero_of_aeval_algebra_map_eq_zero R S T hST hx },
  { rw [is_scalar_tower.algebra_map_eq R S T, ← hom_eval₂, hx, ring_hom.map_zero] }
end

/-- If `y` is the image of `x` in an extension, their minimal polynomials coincide.

We take `h : y = algebra_map L T x` as an argument because `rw h` typically fails
since `is_integral R y` depends on y.
-/
lemma minimal_polynomial.eq_of_algebra_map_eq [algebra K S] [algebra K T]
  [is_scalar_tower K S T] (hST : function.injective (algebra_map S T))
  {x : S} {y : T} (hx : is_integral K x) (hy : is_integral K y)
  (h : y = algebra_map S T x) : minimal_polynomial hx = minimal_polynomial hy :=
minimal_polynomial.unique hy (minimal_polynomial.monic hx)
  (by rw [h, ← is_scalar_tower.algebra_map_aeval, minimal_polynomial.aeval hx, ring_hom.map_zero])
  (λ q q_monic root_q, minimal_polynomial.min _ q_monic
    (is_scalar_tower.aeval_eq_zero_of_aeval_algebra_map_eq_zero K S T hST
      (h ▸ root_q : aeval (algebra_map S T x) q = 0)))

namespace algebra

open power_basis

lemma mem_span_power_basis [nontrivial R] {x y : S} (hx : _root_.is_integral R x)
  (hy : ∃ f : polynomial R, y = aeval x f) :
  y ∈ submodule.span R (set.range (λ (i : fin (minimal_polynomial hx).nat_degree),
    x ^ (i : ℕ))) :=
begin
  obtain ⟨f, rfl⟩ := hy,
  rw mem_span_pow',
  have := minimal_polynomial.monic hx,
  refine ⟨f.mod_by_monic (minimal_polynomial hx),
    lt_of_lt_of_le (degree_mod_by_monic_lt _ this (ne_zero_of_monic this)) degree_le_nat_degree,
    _⟩,
  conv_lhs { rw ← mod_by_monic_add_div f this },
  simp only [add_zero, zero_mul, minimal_polynomial.aeval, aeval_add, alg_hom.map_mul]
end

lemma linear_independent_power_basis [algebra K S] {x : S} (hx : _root_.is_integral K x) :
  linear_independent K (λ (i : fin (minimal_polynomial hx).nat_degree), x ^ (i : ℕ)) :=
begin
  rw linear_independent_iff,
  intros p hp,
  let f : polynomial K := p.sum (λ i, monomial i),
  have f_def : ∀ (i : fin _), f.coeff i = p i,
  { intro i,
    -- TODO: how can we avoid unfolding here?
    change (p.sum (λ i pi, finsupp.single i pi) : ℕ →₀ K) i = p i,
    simp_rw [finsupp.sum_apply, finsupp.single_apply, finsupp.sum],
    rw [finset.sum_eq_single, if_pos rfl],
    { intros b _ hb,
      rw if_neg (mt (λ h, _) hb),
      exact fin.coe_injective h },
    { intro hi,
      split_ifs; { exact finsupp.not_mem_support_iff.mp hi } } },
  have f_def' : ∀ i, f.coeff i = if hi : i < _ then p ⟨i, hi⟩ else 0,
  { intro i,
    split_ifs with hi,
    { exact f_def ⟨i, hi⟩ },
    -- TODO: how can we avoid unfolding here?
    change (p.sum (λ i pi, finsupp.single i pi) : ℕ →₀ K) i = 0,
    simp_rw [finsupp.sum_apply, finsupp.single_apply, finsupp.sum],
    apply finset.sum_eq_zero,
    rintro ⟨j, hj⟩ -,
    apply if_neg (mt _ hi),
    rintro rfl,
    exact hj },
  suffices : f = 0,
  { ext i, rw [← f_def, this, coeff_zero, finsupp.zero_apply] },
  contrapose hp with hf,
  intro h,
  have : (minimal_polynomial hx).degree ≤ f.degree,
  { apply minimal_polynomial.degree_le_of_ne_zero hx hf,
    convert h,
    rw [finsupp.total_apply, aeval_def, eval₂_eq_sum, finsupp.sum_sum_index],
    { apply finset.sum_congr rfl,
      rintro i -,
      simp only [algebra.smul_def, monomial, finsupp.lsingle_apply, zero_mul, ring_hom.map_zero,
        finsupp.sum_single_index] },
    { intro, simp only [ring_hom.map_zero, zero_mul] },
    { intros, simp only [ring_hom.map_add, add_mul] } },
  have : ¬ (minimal_polynomial hx).degree ≤ f.degree,
  { apply not_le_of_lt,
    rw [degree_eq_nat_degree (minimal_polynomial.ne_zero hx), degree_lt_iff_coeff_zero],
    intros i hi,
    rw [f_def' i, dif_neg],
    exact not_lt_of_ge hi },
  contradiction
end

lemma power_basis_is_basis [algebra K S] {x : S} (hx : _root_.is_integral K x) :
  is_basis K (λ (i : fin (minimal_polynomial hx).nat_degree),
    (⟨x, subset_adjoin (set.mem_singleton x)⟩ ^ (i : ℕ) : adjoin K ({x} : set S))) :=
begin
  have hST : function.injective (algebra_map (adjoin K ({x} : set S)) S) := subtype.coe_injective,
  have hx' : _root_.is_integral K
    (show adjoin K ({x} : set S), from ⟨x, subset_adjoin (set.mem_singleton x)⟩),
  { apply (is_integral_algebra_map_iff hST).mp,
    convert hx,
    apply_instance },
  have minpoly_eq := minimal_polynomial.eq_of_algebra_map_eq hST hx' hx,
  refine ⟨_, _root_.eq_top_iff.mpr _⟩,
  { have := linear_independent_power_basis hx',
    rwa minpoly_eq at this,
    refl },
  { rintros ⟨y, hy⟩ _,
    have := mem_span_power_basis hx',
    rw minpoly_eq at this,
    apply this,
    { rw [adjoin_singleton_eq_range] at hy,
      obtain ⟨f, rfl⟩ := (aeval x).mem_range.mp hy,
      use f,
      ext,
      exact (is_scalar_tower.algebra_map_aeval K (adjoin K {x}) S ⟨x, _⟩ _).symm },
    { refl } }
end

/-- The power basis `1, x, ..., x ^ (d - 1)` for `K[x]`,
where `d` is the degree of the minimal polynomial of `x`. -/
noncomputable def adjoin.power_basis [algebra K S] {x : S} (hx : _root_.is_integral K x) :
  power_basis K (adjoin K ({x} : set S)) :=
{ gen := ⟨x, subset_adjoin (set.mem_singleton x)⟩,
  dim := (minimal_polynomial hx).nat_degree,
  is_basis := power_basis_is_basis hx }

end algebra

namespace intermediate_field

lemma adjoin_simple.exists_eq_aeval_gen (alg : algebra.is_algebraic K L) {x y : L} (hy : y ∈ K⟮x⟯) :
  ∃ f : polynomial K, y = aeval x f :=
begin
  refine adjoin_induction _ hy _ _ _ _ _ _,
  { intros x hx,
    rcases set.mem_singleton_iff.mp hx with rfl,
    exact ⟨X, (aeval_X _).symm⟩ },
  { intros x,
    refine ⟨C x, (aeval_C _ _).symm⟩ },
  { rintros x y ⟨fx, rfl⟩ ⟨fy, rfl⟩,
    exact ⟨fx + fy, (ring_hom.map_add _ _ _).symm⟩ },
  { rintros x ⟨fx, rfl⟩,
    exact ⟨-fx, (ring_hom.map_neg _ _).symm⟩ },
  { rintros x ⟨fx, x_eq⟩,
    by_cases hx0 : x = 0,
    { rw [hx0, inv_zero],
      exact ⟨0, (ring_hom.map_zero _).symm⟩ },
    have hx : is_integral K x := ((is_algebraic_iff_is_integral _).mp (alg x)),
    rw inv_eq_of_root_of_coeff_zero_ne_zero
      (minimal_polynomial.aeval hx) (minimal_polynomial.coeff_zero_ne_zero hx hx0),
    use - (C ((minimal_polynomial hx).coeff 0)⁻¹) * (minimal_polynomial hx).div_X.comp fx,
    rw aeval_def at x_eq,
    rw [div_eq_inv_mul, alg_hom.map_mul, alg_hom.map_neg, aeval_C, neg_mul_eq_neg_mul,
        ring_hom.map_inv, aeval_def, aeval_def, eval₂_comp, ← x_eq] },
  { rintros x y ⟨fx, rfl⟩ ⟨fy, rfl⟩,
    exact ⟨fx * fy, (ring_hom.map_mul _ _ _).symm⟩ },
end

lemma power_basis_is_basis (alg : algebra.is_algebraic K L) {x : L} (hx : is_integral K x) :
  is_basis K (λ (i : fin (minimal_polynomial hx).nat_degree), (adjoin_simple.gen K x ^ (i : ℕ))) :=
begin
  have hx' : is_integral K (adjoin_simple.gen K x),
  { apply (is_integral_algebra_map_iff (algebra_map K⟮x⟯ L).injective).mp,
    convert hx,
    apply_instance },
  have minpoly_eq :=
    minimal_polynomial.eq_of_algebra_map_eq ((algebra_map K⟮x⟯ L).injective) hx' hx,
  refine ⟨_, eq_top_iff.mpr _⟩,
  { have := algebra.linear_independent_power_basis hx',
    rwa minpoly_eq at this,
    refl },
  { rintros ⟨y, hy⟩ _,
    have := algebra.mem_span_power_basis hx',
    rw minpoly_eq at this,
    apply this,
    { obtain ⟨f, rfl⟩ := adjoin_simple.exists_eq_aeval_gen alg hy,
      use f,
      ext,
      exact (is_scalar_tower.algebra_map_aeval K K⟮x⟯ L (adjoin_simple.gen K x) _).symm },
    { refl } }
end

/-- The power basis `1, x, ..., x ^ (d - 1)` for `K⟮x⟯`,
where `d` is the degree of the minimal polynomial of `x`. -/
noncomputable def adjoin.power_basis (alg : algebra.is_algebraic K L) {x : L} :
  power_basis K K⟮x⟯ :=
{ gen := adjoin_simple.gen K x,
  dim := (minimal_polynomial ((is_algebraic_iff_is_integral K).mp (alg x))).nat_degree,
  is_basis := power_basis_is_basis alg _ }

end intermediate_field

namespace adjoin_root

variables {f : polynomial K}

lemma power_basis_is_basis (hf : f ≠ 0) : is_basis K (λ (i : fin f.nat_degree), (root f ^ i.val)) :=
begin
  set f' := f * C (f.leading_coeff⁻¹) with f'_def,
  have hC : f.leading_coeff ≠ 0,
  { simpa only [ne.def, C_eq_zero, inv_eq_zero, leading_coeff_eq_zero] using hf},
  have deg_f' : f'.nat_degree = f.nat_degree,
  { rw [nat_degree_mul hf (mt _ hC), nat_degree_C, add_zero],
    simp },
  have f'_monic : monic f' := monic_mul_leading_coeff_inv hf,
  have aeval_f' : aeval (root f) f' = 0,
  { rw [f'_def, alg_hom.map_mul, aeval_eq, mk_self, zero_mul] },
  have hx : is_integral K (root f) := ⟨f', f'_monic, aeval_f'⟩,
  have minpoly_eq : f' = minimal_polynomial hx,
  { apply minimal_polynomial.unique hx f'_monic aeval_f',
    intros q q_monic q_aeval,
    rw [degree_eq_nat_degree f'_monic.ne_zero, degree_eq_nat_degree q_monic.ne_zero],
    rw [with_bot.coe_le_coe, deg_f'],
    apply nat_degree_le_of_dvd,
    { rw [←ideal.mem_span_singleton, ←ideal.quotient.eq_zero_iff_mem],
      change mk f q = 0,
      have commutes : (lift (algebra_map K (adjoin_root f)) (root f) q_aeval).comp (mk q) = mk f,
      { ext,
        { simp only [mk_C, lift_of, algebra_map_eq, function.comp_app, ring_hom.coe_comp], refl },
        { simp only [mk_X, lift_root, function.comp_app, ring_hom.coe_comp] } },
      rw ← commutes,
      simp only [mk_self, ring_hom.map_zero, function.comp_app, ring_hom.coe_comp] },
    { exact q_monic.ne_zero } },
  refine ⟨_, eq_top_iff.mpr _⟩,
  { have := algebra.linear_independent_power_basis hx,
    rwa [←minpoly_eq, deg_f'] at this },
  { rintros y -,
    have := algebra.mem_span_power_basis hx,
    rw [←minpoly_eq, deg_f'] at this,
    apply this,
    obtain ⟨g⟩ := y,
    use g,
    rw aeval_eq,
    refl }
end

/-- The power basis `1, root f, ..., root f ^ (d - 1)` for `adjoin_root f`,
where `f` is an irreducible polynomial over a field of degree `d`. -/
noncomputable def power_basis (hf : f ≠ 0) :
  power_basis K (adjoin_root f) :=
{ gen := root f,
  dim := f.nat_degree,
  is_basis := power_basis_is_basis hf }

lemma finite_dimensional (hf : f ≠ 0) : finite_dimensional K (adjoin_root f) :=
finite_dimensional.of_fintype_basis (power_basis hf).is_basis

lemma findim (hf : f ≠ 0) : finite_dimensional.findim K (adjoin_root f) = f.nat_degree :=
begin
  rw [finite_dimensional.findim_eq_card_basis (power_basis hf).is_basis, fintype.card_fin],
  refl,
end

end adjoin_root
