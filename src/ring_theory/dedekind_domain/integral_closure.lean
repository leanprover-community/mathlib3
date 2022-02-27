/-
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenji Nakagawa, Anne Baanen, Filippo A. E. Nuccio
-/
import ring_theory.dedekind_domain.basic
import ring_theory.trace

/-!
# Integral closure of Dedekind domains

This file shows the integral closure of a Dedekind domain (in particular, the ring of integers
of a number field) is a Dedekind domain.

## Implementation notes

The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. The `..._iff` lemmas express this independence.

Often, definitions assume that Dedekind domains are not fields. We found it more practical
to add a `(h : ¬ is_field A)` assumption whenever this is explicitly needed.

## References

* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

dedekind domain, dedekind ring
-/

variables (R A K : Type*) [comm_ring R] [comm_ring A] [field K]

open_locale non_zero_divisors polynomial

variables [is_domain A]

section is_integral_closure

/-! ### `is_integral_closure` section

We show that an integral closure of a Dedekind domain in a finite separable
field extension is again a Dedekind domain. This implies the ring of integers
of a number field is a Dedekind domain. -/

open algebra
open_locale big_operators

variables {A K} [algebra A K] [is_fraction_ring A K]
variables {L : Type*} [field L] (C : Type*) [comm_ring C]
variables [algebra K L] [finite_dimensional K L] [algebra A L] [is_scalar_tower A K L]
variables [algebra C L] [is_integral_closure C A L] [algebra A C] [is_scalar_tower A C L]

lemma is_integral_closure.range_le_span_dual_basis [is_separable K L]
  {ι : Type*} [fintype ι] [decidable_eq ι] (b : basis ι K L)
  (hb_int : ∀ i, is_integral A (b i)) [is_integrally_closed A] :
  ((algebra.linear_map C L).restrict_scalars A).range ≤
    submodule.span A (set.range $ (trace_form K L).dual_basis (trace_form_nondegenerate K L) b) :=
begin
  let db := (trace_form K L).dual_basis (trace_form_nondegenerate K L) b,
  rintros _ ⟨x, rfl⟩,
  simp only [linear_map.coe_restrict_scalars_eq_coe, algebra.linear_map_apply],
  have hx : is_integral A (algebra_map C L x) :=
    (is_integral_closure.is_integral A L x).algebra_map,
  suffices : ∃ (c : ι → A), algebra_map C L x = ∑ i, c i • db i,
  { obtain ⟨c, x_eq⟩ := this,
    rw x_eq,
    refine submodule.sum_mem _ (λ i _, submodule.smul_mem _ _ (submodule.subset_span _)),
    rw set.mem_range,
    exact ⟨i, rfl⟩ },
  suffices : ∃ (c : ι → K), ((∀ i, is_integral A (c i)) ∧ algebra_map C L x = ∑ i, c i • db i),
  { obtain ⟨c, hc, hx⟩ := this,
    have hc' : ∀ i, is_localization.is_integer A (c i) :=
      λ i, is_integrally_closed.is_integral_iff.mp (hc i),
    use λ i, classical.some (hc' i),
    refine hx.trans (finset.sum_congr rfl (λ i _, _)),
    conv_lhs { rw [← classical.some_spec (hc' i)] },
    rw [← is_scalar_tower.algebra_map_smul K (classical.some (hc' i)) (db i)] },
  refine ⟨λ i, db.repr (algebra_map C L x) i, (λ i, _), (db.sum_repr _).symm⟩,
  rw bilin_form.dual_basis_repr_apply,
  exact is_integral_trace (is_integral_mul hx (hb_int i))
end

lemma integral_closure_le_span_dual_basis [is_separable K L]
  {ι : Type*} [fintype ι] [decidable_eq ι] (b : basis ι K L)
  (hb_int : ∀ i, is_integral A (b i)) [is_integrally_closed A] :
  (integral_closure A L).to_submodule ≤ submodule.span A (set.range $
    (trace_form K L).dual_basis (trace_form_nondegenerate K L) b) :=
begin
  refine le_trans _ (is_integral_closure.range_le_span_dual_basis (integral_closure A L) b hb_int),
  intros x hx,
  exact ⟨⟨x, hx⟩, rfl⟩
end

variables (A) (K)

include K

/-- Send a set of `x`'es in a finite extension `L` of the fraction field of `R`
to `(y : R) • x ∈ integral_closure R L`. -/
lemma exists_integral_multiples (s : finset L) :
  ∃ (y ≠ (0 : A)), ∀ x ∈ s, is_integral A (y • x) :=
begin
  haveI := classical.dec_eq L,
  refine s.induction _ _,
  { use [1, one_ne_zero],
    rintros x ⟨⟩ },
  { rintros x s hx ⟨y, hy, hs⟩,
    obtain ⟨x', y', hy', hx'⟩ := exists_integral_multiple
      ((is_fraction_ring.is_algebraic_iff A K L).mpr (is_algebraic_of_finite _ _ x))
      ((algebra_map A L).injective_iff.mp _),
    refine ⟨y * y', mul_ne_zero hy hy', λ x'' hx'', _⟩,
    rcases finset.mem_insert.mp hx'' with (rfl | hx''),
    { rw [mul_smul, algebra.smul_def, algebra.smul_def, mul_comm _ x'', hx'],
      exact is_integral_mul is_integral_algebra_map x'.2 },
    { rw [mul_comm, mul_smul, algebra.smul_def],
      exact is_integral_mul is_integral_algebra_map (hs _ hx'') },
    { rw is_scalar_tower.algebra_map_eq A K L,
      apply (algebra_map K L).injective.comp,
      exact is_fraction_ring.injective _ _ } }
end

variables (L)

/-- If `L` is a finite extension of `K = Frac(A)`,
then `L` has a basis over `A` consisting of integral elements. -/
lemma finite_dimensional.exists_is_basis_integral :
  ∃ (s : finset L) (b : basis s K L), (∀ x, is_integral A (b x)) :=
begin
  letI := classical.dec_eq L,
  letI : is_noetherian K L := is_noetherian.iff_fg.2 infer_instance,
  let s' := is_noetherian.finset_basis_index K L,
  let bs' := is_noetherian.finset_basis K L,
  obtain ⟨y, hy, his'⟩ := exists_integral_multiples A K (finset.univ.image bs'),
  have hy' : algebra_map A L y ≠ 0,
  { refine mt ((algebra_map A L).injective_iff.mp _ _) hy,
    rw is_scalar_tower.algebra_map_eq A K L,
    exact (algebra_map K L).injective.comp (is_fraction_ring.injective A K) },
  refine ⟨s', bs'.map { to_fun := λ x, algebra_map A L y * x,
                        inv_fun := λ x, (algebra_map A L y)⁻¹ * x,
                        left_inv := _,
                        right_inv := _,
                        .. algebra.lmul _ _ (algebra_map A L y) },
          _⟩,
  { intros x, simp only [inv_mul_cancel_left₀ hy'] },
  { intros x, simp only [mul_inv_cancel_left₀ hy'] },
  { rintros ⟨x', hx'⟩,
    simp only [algebra.smul_def, finset.mem_image, exists_prop, finset.mem_univ, true_and] at his',
    simp only [basis.map_apply, linear_equiv.coe_mk],
    exact his' _ ⟨_, rfl⟩ }
end

variables (A K L) [is_separable K L]
include L

/- If `L` is a finite separable extension of `K = Frac(A)`, where `A` is
integrally closed and Noetherian, the integral closure `C` of `A` in `L` is
Noetherian. -/
lemma is_integral_closure.is_noetherian_ring [is_integrally_closed A] [is_noetherian_ring A] :
  is_noetherian_ring C :=
begin
  haveI := classical.dec_eq L,
  obtain ⟨s, b, hb_int⟩ := finite_dimensional.exists_is_basis_integral A K L,
  rw is_noetherian_ring_iff,
  let b' := (trace_form K L).dual_basis (trace_form_nondegenerate K L) b,
  letI := is_noetherian_span_of_finite A (set.finite_range b'),
  let f : C →ₗ[A] submodule.span A (set.range b') :=
    (submodule.of_le (is_integral_closure.range_le_span_dual_basis C b hb_int)).comp
    ((algebra.linear_map C L).restrict_scalars A).range_restrict,
  refine is_noetherian_of_tower A (is_noetherian_of_ker_bot f _),
  rw [linear_map.ker_comp, submodule.ker_of_le, submodule.comap_bot, linear_map.ker_cod_restrict],
  exact linear_map.ker_eq_bot_of_injective (is_integral_closure.algebra_map_injective C A L)
end

variables {A K}

/- If `L` is a finite separable extension of `K = Frac(A)`, where `A` is
integrally closed and Noetherian, the integral closure of `A` in `L` is
Noetherian. -/
lemma integral_closure.is_noetherian_ring [is_integrally_closed A] [is_noetherian_ring A] :
  is_noetherian_ring (integral_closure A L) :=
is_integral_closure.is_noetherian_ring A K L (integral_closure A L)

variables (A K) [is_domain C]
/- If `L` is a finite separable extension of `K = Frac(A)`, where `A` is a Dedekind domain,
the integral closure `C` of `A` in `L` is a Dedekind domain.

Can't be an instance since `A`, `K` or `L` can't be inferred. See also the instance
`integral_closure.is_dedekind_domain_fraction_ring` where `K := fraction_ring A`
and `C := integral_closure A L`.
-/
lemma is_integral_closure.is_dedekind_domain [h : is_dedekind_domain A] :
  is_dedekind_domain C :=
begin
  haveI : is_fraction_ring C L := is_integral_closure.is_fraction_ring_of_finite_extension A K L C,
  exact
  ⟨is_integral_closure.is_noetherian_ring A K L C,
   h.dimension_le_one.is_integral_closure _ L _,
   (is_integrally_closed_iff L).mpr (λ x hx, ⟨is_integral_closure.mk' C x
      (is_integral_trans (is_integral_closure.is_integral_algebra A L) _ hx),
    is_integral_closure.algebra_map_mk' _ _ _⟩)⟩
end

/- If `L` is a finite separable extension of `K = Frac(A)`, where `A` is a Dedekind domain,
the integral closure of `A` in `L` is a Dedekind domain.

Can't be an instance since `K` can't be inferred. See also the instance
`integral_closure.is_dedekind_domain_fraction_ring` where `K := fraction_ring A`.
-/
lemma integral_closure.is_dedekind_domain [h : is_dedekind_domain A] :
  is_dedekind_domain (integral_closure A L) :=
is_integral_closure.is_dedekind_domain A K L (integral_closure A L)

omit K

variables [algebra (fraction_ring A) L] [is_scalar_tower A (fraction_ring A) L]
variables [finite_dimensional (fraction_ring A) L] [is_separable (fraction_ring A) L]

/- If `L` is a finite separable extension of `Frac(A)`, where `A` is a Dedekind domain,
the integral closure of `A` in `L` is a Dedekind domain.

See also the lemma `integral_closure.is_dedekind_domain` where you can choose
the field of fractions yourself.
-/
instance integral_closure.is_dedekind_domain_fraction_ring
  [is_dedekind_domain A] : is_dedekind_domain (integral_closure A L) :=
integral_closure.is_dedekind_domain A (fraction_ring A) L

end is_integral_closure
