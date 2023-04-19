/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin
-/
import algebra.module.dedekind_domain
import linear_algebra.free_module.pid
import algebra.module.projective
import algebra.category.Module.biproducts

/-!
# Structure of finitely generated modules over a PID

## Main statements

* `module.equiv_direct_sum_of_is_torsion` : A finitely generated torsion module over a PID is
  isomorphic to a direct sum of some `R ⧸ R ∙ (p i ^ e i)` where the `p i ^ e i` are prime powers.
* `module.equiv_free_prod_direct_sum` : A finitely generated module over a PID is isomorphic to the
  product of a free module (its torsion free part) and a direct sum of the form above (its torsion
  submodule).

## Notation

* `R` is a PID and `M` is a (finitely generated for main statements) `R`-module, with additional
  torsion hypotheses in the intermediate lemmas.
* `N` is a `R`-module lying over a higher type universe than `R`. This assumption is needed on the
  final statement for technical reasons.
* `p` is an irreducible element of `R` or a tuple of these.

## Implementation details

We first prove (`submodule.is_internal_prime_power_torsion_of_pid`) that a finitely generated
torsion module is the internal direct sum of its `p i ^ e i`-torsion submodules for some
(finitely many) prime powers `p i ^ e i`. This is proved in more generality for a Dedekind domain
at `submodule.is_internal_prime_power_torsion`.

Then we treat the case of a `p ^ ∞`-torsion module (that is, a module where all elements are
cancelled by scalar multiplication by some power of `p`) and apply it to the `p i ^ e i`-torsion
submodules (that are `p i ^ ∞`-torsion) to get the result for torsion modules.

Then we get the general result using that a torsion free module is free (which has been proved at
`module.free_of_finite_type_torsion_free'` at `linear_algebra/free_module/pid.lean`.)

## Tags

Finitely generated module, principal ideal domain, classification, structure theorem
-/

universes u v
open_locale big_operators

variables {R : Type u} [comm_ring R] [is_domain R] [is_principal_ideal_ring R]
variables {M : Type v} [add_comm_group M] [module R M]
variables {N : Type (max u v)} [add_comm_group N] [module R N]

open_locale direct_sum
open submodule

/--A finitely generated torsion module over a PID is an internal direct sum of its
`p i ^ e i`-torsion submodules for some primes `p i` and numbers `e i`.-/
theorem submodule.is_internal_prime_power_torsion_of_pid
  [module.finite R M] (hM : module.is_torsion R M) :
  ∃ (ι : Type u) [fintype ι] [decidable_eq ι] (p : ι → R) (h : ∀ i, irreducible $ p i) (e : ι → ℕ),
  by exactI direct_sum.is_internal (λ i, torsion_by R M $ p i ^ e i) :=
begin
  obtain ⟨P, dec, hP, e, this⟩ := is_internal_prime_power_torsion hM,
  refine ⟨P, infer_instance, dec, λ p, is_principal.generator (p : ideal R), _, e, _⟩,
  { rintro ⟨p, hp⟩,
    haveI := ideal.is_prime_of_prime (hP p hp),
    exact (is_principal.prime_generator_of_is_prime p (hP p hp).ne_zero).irreducible },
  { convert this, ext p : 1,
    rw [← torsion_by_span_singleton_eq, ideal.submodule_span_eq, ← ideal.span_singleton_pow,
      ideal.span_singleton_generator] }
end

namespace module
section p_torsion
variables {p : R} (hp : irreducible p) (hM : module.is_torsion' M (submonoid.powers p))
variables [dec : Π x : M, decidable (x = 0)]

open ideal submodule.is_principal
include dec

include hp hM
lemma _root_.ideal.torsion_of_eq_span_pow_p_order (x : M) :
  torsion_of R M x = span {p ^ p_order hM x} :=
begin
  dunfold p_order,
  rw [← (torsion_of R M x).span_singleton_generator, ideal.span_singleton_eq_span_singleton,
    ← associates.mk_eq_mk_iff_associated, associates.mk_pow],
  have prop : (λ n : ℕ, p ^ n • x = 0) =
    λ n : ℕ, (associates.mk $ generator $ torsion_of R M x) ∣ associates.mk p ^ n,
  { ext n, rw [← associates.mk_pow, associates.mk_dvd_mk, ← mem_iff_generator_dvd], refl },
  have := (is_torsion'_powers_iff p).mp hM x, rw prop at this,
  classical,
  convert associates.eq_pow_find_of_dvd_irreducible_pow ((associates.irreducible_mk p).mpr hp)
    this.some_spec,
end

lemma p_pow_smul_lift {x y : M} {k : ℕ} (hM' : module.is_torsion_by R M (p ^ p_order hM y))
  (h : p ^ k • x ∈ R ∙ y) : ∃ a : R, p ^ k • x = p ^ k • a • y :=
begin
  by_cases hk : k ≤ p_order hM y,
  { let f := ((R ∙ p ^ (p_order hM y - k) * p ^ k).quot_equiv_of_eq _ _).trans
      (quot_torsion_of_equiv_span_singleton R M y),
    have : f.symm ⟨p ^ k • x, h⟩ ∈
      R ∙ ideal.quotient.mk (R ∙ p ^ (p_order hM y - k) * p ^ k) (p ^ k),
    { rw [← quotient.torsion_by_eq_span_singleton, mem_torsion_by_iff, ← f.symm.map_smul],
      convert f.symm.map_zero, ext,
      rw [coe_smul_of_tower, coe_mk, coe_zero, smul_smul, ← pow_add, nat.sub_add_cancel hk, @hM' x],
      { exact mem_non_zero_divisors_of_ne_zero (pow_ne_zero _ hp.ne_zero) } },
    rw submodule.mem_span_singleton at this, obtain ⟨a, ha⟩ := this, use a,
    rw [f.eq_symm_apply, ← ideal.quotient.mk_eq_mk, ← quotient.mk_smul] at ha,
    dsimp only [smul_eq_mul, f, linear_equiv.trans_apply, submodule.quot_equiv_of_eq_mk,
      quot_torsion_of_equiv_span_singleton_apply_mk] at ha,
    rw [smul_smul, mul_comm], exact congr_arg coe ha.symm,
    { symmetry, convert ideal.torsion_of_eq_span_pow_p_order hp hM y,
      rw [← pow_add, nat.sub_add_cancel hk] } },
  { use 0, rw [zero_smul, smul_zero, ← nat.sub_add_cancel (le_of_not_le hk),
      pow_add, mul_smul, hM', smul_zero] }
end

open submodule.quotient

lemma exists_smul_eq_zero_and_mk_eq {z : M} (hz : module.is_torsion_by R M (p ^ p_order hM z))
  {k : ℕ} (f : (R ⧸ R ∙ p ^ k) →ₗ[R] M ⧸ R ∙ z) :
  ∃ x : M, p ^ k • x = 0 ∧ submodule.quotient.mk x = f 1 :=
begin
  have f1 := mk_surjective (R ∙ z) (f 1),
  have : p ^ k • f1.some ∈ R ∙ z,
  { rw [← quotient.mk_eq_zero, mk_smul, f1.some_spec, ← f.map_smul],
    convert f.map_zero, change _ • submodule.quotient.mk _ = _,
    rw [← mk_smul, quotient.mk_eq_zero, algebra.id.smul_eq_mul, mul_one],
    exact submodule.mem_span_singleton_self _ },
  obtain ⟨a, ha⟩ := p_pow_smul_lift hp hM hz this,
  refine ⟨f1.some - a • z, by rw [smul_sub, sub_eq_zero, ha], _⟩,
  rw [mk_sub, mk_smul, (quotient.mk_eq_zero _).mpr $ submodule.mem_span_singleton_self _,
    smul_zero, sub_zero, f1.some_spec]
end

open finset multiset
omit dec hM

/--A finitely generated `p ^ ∞`-torsion module over a PID is isomorphic to a direct sum of some
  `R ⧸ R ∙ (p ^ e i)` for some `e i`.-/
theorem torsion_by_prime_power_decomposition (hN : module.is_torsion' N (submonoid.powers p))
  [h' : module.finite R N] :
  ∃ (d : ℕ) (k : fin d → ℕ), nonempty $ N ≃ₗ[R] ⨁ (i : fin d), R ⧸ R ∙ (p ^ (k i : ℕ)) :=
begin
  obtain ⟨d, s, hs⟩ := @module.finite.exists_fin _ _ _ _ _ h', use d, clear h',
  unfreezingI { induction d with d IH generalizing N },
  { use λ i, fin_zero_elim i,
    rw [set.range_eq_empty, submodule.span_empty] at hs,
    haveI : unique N := ⟨⟨0⟩, λ x, by { rw [← mem_bot _, hs], trivial }⟩,
    exact ⟨0⟩ },
  { haveI : Π x : N, decidable (x = 0), classical, apply_instance,
    obtain ⟨j, hj⟩ := exists_is_torsion_by hN d.succ d.succ_ne_zero s hs,
    let s' : fin d → N ⧸ R ∙ s j := submodule.quotient.mk ∘ s ∘ j.succ_above,
    obtain ⟨k, ⟨f⟩⟩ := IH _ s' _; clear IH,
    { have : ∀ i : fin d, ∃ x : N,
        p ^ k i • x = 0 ∧ f (submodule.quotient.mk x) = direct_sum.lof R _ _ i 1,
      { intro i,
        let fi := f.symm.to_linear_map.comp (direct_sum.lof _ _ _ i),
        obtain ⟨x, h0, h1⟩ := exists_smul_eq_zero_and_mk_eq hp hN hj fi, refine ⟨x, h0, _⟩, rw h1,
        simp only [linear_map.coe_comp, f.symm.coe_to_linear_map, f.apply_symm_apply] },
      refine ⟨_, ⟨(((
        @lequiv_prod_of_right_split_exact _ _ _ _ _ _ _ _ _ _ _ _
          ((f.trans ulift.module_equiv.{u u v}.symm).to_linear_map.comp $ mkq _)
          ((direct_sum.to_module _ _ _ $ λ i, (liftq_span_singleton.{u u} (p ^ k i)
            (linear_map.to_span_singleton _ _ _) (this i).some_spec.left : R ⧸ _ →ₗ[R] _)).comp
            ulift.module_equiv.to_linear_map)
          (R ∙ s j).injective_subtype _ _).symm.trans $
        ((quot_torsion_of_equiv_span_singleton _ _ _).symm.trans $
          quot_equiv_of_eq _ _ $ ideal.torsion_of_eq_span_pow_p_order hp hN _).prod $
          ulift.module_equiv).trans $
        (@direct_sum.lequiv_prod_direct_sum R _ _ _
          (λ i, R ⧸ R ∙ p ^ @option.rec _ (λ _, ℕ) (p_order hN $ s j) k i) _ _).symm).trans $
        direct_sum.lequiv_congr_left R (fin_succ_equiv d).symm⟩⟩,
      { rw [range_subtype, linear_equiv.to_linear_map_eq_coe, linear_equiv.ker_comp, ker_mkq] },
      { rw [linear_equiv.to_linear_map_eq_coe, ← f.comp_coe, linear_map.comp_assoc,
          linear_map.comp_assoc, ← linear_equiv.to_linear_map_eq_coe,
          linear_equiv.to_linear_map_symm_comp_eq, linear_map.comp_id,
          ← linear_map.comp_assoc, ← linear_map.comp_assoc],
        suffices : (f.to_linear_map.comp (R ∙ s j).mkq).comp _ = linear_map.id,
        { rw [← f.to_linear_map_eq_coe, this, linear_map.id_comp] },
        ext i : 3,
        simp only [linear_map.coe_comp, function.comp_app, mkq_apply],
        rw [linear_equiv.coe_to_linear_map, linear_map.id_apply, direct_sum.to_module_lof,
          liftq_span_singleton_apply, linear_map.to_span_singleton_one,
          ideal.quotient.mk_eq_mk, map_one, (this i).some_spec.right] } },
    { exact (mk_surjective _).forall.mpr
      (λ x, ⟨(@hN x).some, by rw [← quotient.mk_smul, (@hN x).some_spec, quotient.mk_zero]⟩) },
    { have hs' := congr_arg (submodule.map $ mkq $ R ∙ s j) hs,
      rw [submodule.map_span, submodule.map_top, range_mkq] at hs', simp only [mkq_apply] at hs',
      simp only [s'], rw [set.range_comp (_ ∘ s), fin.range_succ_above],
      rw [← set.range_comp, ← set.insert_image_compl_eq_range _ j, function.comp_apply,
        (quotient.mk_eq_zero _).mpr (submodule.mem_span_singleton_self _), span_insert_zero] at hs',
      exact hs' } }
end
end p_torsion

/--A finitely generated torsion module over a PID is isomorphic to a direct sum of some
  `R ⧸ R ∙ (p i ^ e i)` where the `p i ^ e i` are prime powers.-/
theorem equiv_direct_sum_of_is_torsion [h' : module.finite R N] (hN : module.is_torsion R N) :
  ∃ (ι : Type u) [fintype ι] (p : ι → R) (h : ∀ i, irreducible $ p i) (e : ι → ℕ),
  nonempty $ N ≃ₗ[R] ⨁ (i : ι), R ⧸ R ∙ (p i ^ e i) :=
begin
  obtain ⟨I, fI, _, p, hp, e, h⟩ := submodule.is_internal_prime_power_torsion_of_pid hN,
  haveI := fI,
  have : ∀ i, ∃ (d : ℕ) (k : fin d → ℕ),
    nonempty $ torsion_by R N (p i ^ e i) ≃ₗ[R] ⨁ j, R ⧸ R ∙ (p i ^ k j),
  { haveI := is_noetherian_of_fg_of_noetherian' (module.finite_def.mp h'),
    haveI := λ i, is_noetherian_submodule' (torsion_by R N $ p i ^ e i),
    exact λ i, torsion_by_prime_power_decomposition (hp i)
      ((is_torsion'_powers_iff $ p i).mpr $ λ x, ⟨e i, smul_torsion_by _ _⟩) },
  classical,
  refine ⟨Σ i, fin (this i).some, infer_instance,
    λ ⟨i, j⟩, p i, λ ⟨i, j⟩, hp i, λ ⟨i, j⟩, (this i).some_spec.some j,
    ⟨(linear_equiv.of_bijective (direct_sum.coe_linear_map _) h).symm.trans $
      (dfinsupp.map_range.linear_equiv $ λ i, (this i).some_spec.some_spec.some).trans $
      (direct_sum.sigma_lcurry_equiv R).symm.trans
      (dfinsupp.map_range.linear_equiv $ λ i, quot_equiv_of_eq _ _ _)⟩⟩,
  cases i with i j, simp only
end

/--**Structure theorem of finitely generated modules over a PID** : A finitely generated
  module over a PID is isomorphic to the product of a free module and a direct sum of some
  `R ⧸ R ∙ (p i ^ e i)` where the `p i ^ e i` are prime powers.-/
theorem equiv_free_prod_direct_sum [h' : module.finite R N] :
  ∃ (n : ℕ) (ι : Type u) [fintype ι] (p : ι → R) (h : ∀ i, irreducible $ p i) (e : ι → ℕ),
  nonempty $ N ≃ₗ[R] (fin n →₀ R) × ⨁ (i : ι), R ⧸ R ∙ (p i ^ e i) :=
begin
  haveI := is_noetherian_of_fg_of_noetherian' (module.finite_def.mp h'),
  haveI := is_noetherian_submodule' (torsion R N),
  haveI := module.finite.of_surjective _ (torsion R N).mkq_surjective,
  obtain ⟨I, fI, p, hp, e, ⟨h⟩⟩ := equiv_direct_sum_of_is_torsion (@torsion_is_torsion R N _ _ _),
  obtain ⟨n, ⟨g⟩⟩ := @module.basis_of_finite_type_torsion_free' R _ _ _ (N ⧸ torsion R N) _ _ _ _,
  haveI : module.projective R (N ⧸ torsion R N) := module.projective_of_basis ⟨g⟩,
  obtain ⟨f, hf⟩ := module.projective_lifting_property _ linear_map.id (torsion R N).mkq_surjective,
  refine ⟨n, I, fI, p, hp, e,
    ⟨(lequiv_prod_of_right_split_exact (torsion R N).injective_subtype _ hf).symm.trans $
      (h.prod g).trans $ linear_equiv.prod_comm R _ _⟩⟩,
  rw [range_subtype, ker_mkq]
end
end module
