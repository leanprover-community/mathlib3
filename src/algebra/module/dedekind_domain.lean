/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin
-/
import algebra.module.torsion
import ring_theory.dedekind_domain.ideal

/-!
# Modules over a Dedekind domain

-/

universes u v
open_locale big_operators

variables {R : Type u} [comm_ring R] [is_domain R] {M : Type v} [add_comm_group M] [module R M]

open_locale direct_sum
open submodule

lemma is_torsion_by_ideal_of_finite_of_is_torsion [module.finite R M] (hM : module.is_torsion R M) :
  ∃ I : ideal R, I ≠ 0 ∧ module.is_torsion_by_set R M I :=
begin
  cases (module.finite_def.mp infer_instance : (⊤ : submodule R M).fg) with S h,
  refine ⟨∏ x in S, torsion_of R M x, _, _⟩,
  { rw finset.prod_ne_zero_iff,
    intros x hx h0, obtain ⟨⟨a, ha⟩, h1⟩ := @hM x,
    change a ∈ torsion_of R M x at h1, rw [h0, ideal.zero_eq_bot, ideal.mem_bot] at h1,
    rw h1 at ha, apply @one_ne_zero R, apply ha, apply mul_zero },
  { rw [is_torsion_by_set_iff_torsion_by_set_eq_top, eq_top_iff, ← h, span_le],
    intros x hx, apply torsion_by_set_le_torsion_by_set_of_subset,
    { apply ideal.le_of_dvd, exact finset.dvd_prod_of_mem _ hx },
    { rw mem_torsion_by_set_iff, rintro ⟨a, ha⟩, exact ha } }
end

section dedekind_domain
variables [is_dedekind_domain R]
open unique_factorization_monoid

lemma is_internal_prime_power_torsion_of_is_torsion_by_ideal {I : ideal R} (hI : I ≠ 0)
  (hM : module.is_torsion_by_set R M I) :
  ∃ (P : finset $ ideal R) [decidable_eq P] [∀ p ∈ P, prime p] (e : P → ℕ),
  by exactI direct_sum.is_internal (λ p : P, torsion_by_set R M (p ^ e p : ideal R)) :=
begin
  classical,
  let P := factors I,
  have prime_of_mem := λ p (hp : p ∈ P.to_finset), prime_of_factor p (multiset.mem_to_finset.mp hp),
  refine ⟨P.to_finset, infer_instance, prime_of_mem, λ i, P.count i, _⟩,
  apply @torsion_is_internal _ _ _ _ _ _ _ (λ p, p ^ P.count p) _,
  { intros p hp q hq pq, dsimp,
    rw irreducible_pow_sup,
    { suffices : (normalized_factors _).count p = 0,
      { rw [this, zero_min, pow_zero, ideal.one_eq_top] },
      { rw [multiset.count_eq_zero, normalized_factors_of_irreducible_pow
          (prime_of_mem q hq).irreducible, multiset.mem_repeat],
        exact λ H, pq $ H.2.trans $ normalize_eq q } },
    { rw ← ideal.zero_eq_bot, apply pow_ne_zero, exact (prime_of_mem q hq).ne_zero },
    { exact (prime_of_mem p hp).irreducible } },
  { convert hM,
    rw [← finset.inf_eq_infi, is_dedekind_domain.inf_prime_pow_eq_prod,
      ← finset.prod_multiset_count, ← associated_iff_eq],
    exact factors_prod hI,
    { exact prime_of_mem }, { exact λ _ _ _ _ ij, ij } }
end

theorem is_internal_prime_power_torsion [module.finite R M] (hM : module.is_torsion R M) :
  ∃ (P : finset $ ideal R) [decidable_eq P] [∀ p ∈ P, prime p] (e : P → ℕ),
  by exactI direct_sum.is_internal (λ p : P, torsion_by_set R M (p ^ e p : ideal R)) :=
begin
  obtain ⟨I, hI, hM'⟩ := is_torsion_by_ideal_of_finite_of_is_torsion hM,
  exact is_internal_prime_power_torsion_of_is_torsion_by_ideal hI hM'
end

end dedekind_domain
