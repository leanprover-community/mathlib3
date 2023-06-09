/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import linear_algebra.finite_dimensional
import linear_algebra.basic
import ring_theory.mv_polynomial.basic
import data.mv_polynomial.expand
import field_theory.finite.basic

/-!
## Polynomials over finite fields

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

namespace mv_polynomial
variables {σ : Type*}

/-- A polynomial over the integers is divisible by `n : ℕ`
if and only if it is zero over `zmod n`. -/
lemma C_dvd_iff_zmod (n : ℕ) (φ : mv_polynomial σ ℤ) :
  C (n:ℤ) ∣ φ ↔ map (int.cast_ring_hom (zmod n)) φ = 0 :=
C_dvd_iff_map_hom_eq_zero _ _ (char_p.int_cast_eq_zero_iff (zmod n) n) _

section frobenius

variables {p : ℕ} [fact p.prime]

lemma frobenius_zmod (f : mv_polynomial σ (zmod p)) : frobenius _ p f = expand p f :=
begin
  apply induction_on f,
  { intro a, rw [expand_C, frobenius_def, ← C_pow, zmod.pow_card], },
  { simp only [alg_hom.map_add, ring_hom.map_add], intros _ _ hf hg, rw [hf, hg] },
  { simp only [expand_X, ring_hom.map_mul, alg_hom.map_mul],
    intros _ _ hf, rw [hf, frobenius_def], },
end

lemma expand_zmod (f : mv_polynomial σ (zmod p)) : expand p f = f ^ p :=
(frobenius_zmod _).symm

end frobenius

end mv_polynomial

namespace mv_polynomial

noncomputable theory
open_locale big_operators classical
open set linear_map submodule

variables {K : Type*} {σ : Type*}

section indicator

variables [fintype K] [fintype σ]

/-- Over a field, this is the indicator function as an `mv_polynomial`. -/
def indicator [comm_ring K] (a : σ → K) : mv_polynomial σ K :=
∏ n, (1 - (X n - C (a n)) ^ (fintype.card K - 1))

section comm_ring

variables [comm_ring K]

lemma eval_indicator_apply_eq_one (a : σ → K) :
  eval a (indicator a) = 1 :=
begin
  nontriviality,
  have : 0 < fintype.card K - 1 := tsub_pos_of_lt fintype.one_lt_card,
  simp only [indicator, map_prod, map_sub, map_one, map_pow, eval_X, eval_C,
             sub_self, zero_pow this, sub_zero, finset.prod_const_one]
end

lemma degrees_indicator (c : σ → K) :
  degrees (indicator c) ≤ ∑ s : σ, (fintype.card K - 1) • {s} :=
begin
  rw [indicator],
  refine le_trans (degrees_prod _ _) (finset.sum_le_sum $ assume s hs, _),
  refine le_trans (degrees_sub _ _) _,
  rw [degrees_one, ← bot_eq_zero, bot_sup_eq],
  refine le_trans (degrees_pow _ _) (nsmul_le_nsmul_of_le_right _ _),
  refine le_trans (degrees_sub _ _) _,
  rw [degrees_C, ← bot_eq_zero, sup_bot_eq],
  exact degrees_X' _
end

lemma indicator_mem_restrict_degree (c : σ → K) :
  indicator c ∈ restrict_degree σ K (fintype.card K - 1) :=
begin
  rw [mem_restrict_degree_iff_sup, indicator],
  assume n,
  refine le_trans (multiset.count_le_of_le _ $ degrees_indicator _) (le_of_eq _),
  simp_rw [ ← multiset.coe_count_add_monoid_hom, (multiset.count_add_monoid_hom n).map_sum,
    add_monoid_hom.map_nsmul, multiset.coe_count_add_monoid_hom, nsmul_eq_mul, nat.cast_id],
  transitivity,
  refine finset.sum_eq_single n _ _,
  { assume b hb ne, rw [multiset.count_singleton, if_neg ne.symm, mul_zero] },
  { assume h, exact (h $ finset.mem_univ _).elim },
  { rw [multiset.count_singleton_self, mul_one] }
end

end comm_ring

variables [field K]

lemma eval_indicator_apply_eq_zero (a b : σ → K) (h : a ≠ b) :
  eval a (indicator b) = 0 :=
begin
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ b i := by rwa [(≠), function.funext_iff, not_forall] at h,
  simp only [indicator, map_prod, map_sub, map_one, map_pow, eval_X, eval_C,
             sub_self, finset.prod_eq_zero_iff],
  refine ⟨i, finset.mem_univ _, _⟩,
  rw [finite_field.pow_card_sub_one_eq_one, sub_self],
  rwa [(≠), sub_eq_zero],
end

end indicator

section
variables (K σ)

/-- `mv_polynomial.eval` as a `K`-linear map. -/
@[simps] def evalₗ [comm_semiring K] : mv_polynomial σ K →ₗ[K] (σ → K) → K :=
{ to_fun := λ p e, eval e p,
  map_add' := λ p q, by { ext x, rw ring_hom.map_add, refl, },
  map_smul' := λ a p, by { ext e, rw [smul_eq_C_mul, ring_hom.map_mul, eval_C], refl } }
end

variables [field K] [fintype K] [finite σ]

lemma map_restrict_dom_evalₗ : (restrict_degree σ K (fintype.card K - 1)).map (evalₗ K σ) = ⊤ :=
begin
  casesI nonempty_fintype σ,
  refine top_unique (set_like.le_def.2 $ assume e _, mem_map.2 _),
  refine ⟨∑ n : σ → K, e n • indicator n, _, _⟩,
  { exact sum_mem (assume c _, smul_mem _ _ (indicator_mem_restrict_degree _)) },
  { ext n,
    simp only [linear_map.map_sum, @finset.sum_apply (σ → K) (λ_, K) _ _ _ _ _,
      pi.smul_apply, linear_map.map_smul],
    simp only [evalₗ_apply],
    transitivity,
    refine finset.sum_eq_single n (λ b _ h, _) _,
    { rw [eval_indicator_apply_eq_zero _ _ h.symm, smul_zero] },
    { exact λ h, (h $ finset.mem_univ n).elim },
    { rw [eval_indicator_apply_eq_one, smul_eq_mul, mul_one] } }
end

end mv_polynomial

namespace mv_polynomial

open_locale classical cardinal
open linear_map submodule

universe u
variables (σ : Type u) (K : Type u) [fintype K]

/-- The submodule of multivariate polynomials whose degree of each variable is strictly less
than the cardinality of K. -/
@[derive [add_comm_group, module K, inhabited]]
def R [comm_ring K] : Type u := restrict_degree σ K (fintype.card K - 1)

/-- Evaluation in the `mv_polynomial.R` subtype. -/
def evalᵢ [comm_ring K] : R σ K →ₗ[K] (σ → K) → K :=
((evalₗ K σ).comp (restrict_degree σ K (fintype.card K - 1)).subtype)

section comm_ring

variables [comm_ring K]

noncomputable instance decidable_restrict_degree (m : ℕ) :
  decidable_pred (∈ {n : σ →₀ ℕ | ∀i, n i ≤ m }) :=
by simp only [set.mem_set_of_eq]; apply_instance

end comm_ring

variables [field K]

lemma rank_R [fintype σ] : module.rank K (R σ K) = fintype.card (σ → K) :=
calc module.rank K (R σ K) =
  module.rank K (↥{s : σ →₀ ℕ | ∀ (n : σ), s n ≤ fintype.card K - 1} →₀ K) :
    linear_equiv.rank_eq
      (finsupp.supported_equiv_finsupp {s : σ →₀ ℕ | ∀n:σ, s n ≤ fintype.card K - 1 })
  ... = #{s : σ →₀ ℕ | ∀ (n : σ), s n ≤ fintype.card K - 1} : by rw [rank_finsupp_self']
  ... = #{s : σ → ℕ | ∀ (n : σ), s n < fintype.card K } :
  begin
    refine quotient.sound ⟨equiv.subtype_equiv finsupp.equiv_fun_on_finite $ assume f, _⟩,
    refine forall_congr (assume n, le_tsub_iff_right _),
    exact fintype.card_pos_iff.2 ⟨0⟩
  end
  ... = #(σ → {n // n < fintype.card K}) :
    (@equiv.subtype_pi_equiv_pi σ (λ_, ℕ) (λs n, n < fintype.card K)).cardinal_eq
  ... = #(σ → fin (fintype.card K)) :
    (equiv.arrow_congr (equiv.refl σ) fin.equiv_subtype.symm).cardinal_eq
  ... = #(σ → K) :
    (equiv.arrow_congr (equiv.refl σ) (fintype.equiv_fin K).symm).cardinal_eq
  ... = fintype.card (σ → K) : cardinal.mk_fintype _

instance [finite σ] : finite_dimensional K (R σ K) :=
by { casesI nonempty_fintype σ,
  exact is_noetherian.iff_fg.1 (is_noetherian.iff_rank_lt_aleph_0.mpr $
    by simpa only [rank_R] using cardinal.nat_lt_aleph_0 (fintype.card (σ → K))) }

lemma finrank_R [fintype σ] : finite_dimensional.finrank K (R σ K) = fintype.card (σ → K) :=
finite_dimensional.finrank_eq_of_rank_eq (rank_R σ K)

lemma range_evalᵢ [finite σ] : (evalᵢ σ K).range = ⊤ :=
begin
  rw [evalᵢ, linear_map.range_comp, range_subtype],
  exact map_restrict_dom_evalₗ
end

lemma ker_evalₗ [finite σ] : (evalᵢ σ K).ker = ⊥ :=
begin
  casesI nonempty_fintype σ,
  refine (ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank _).mpr (range_evalᵢ _ _),
  rw [finite_dimensional.finrank_fintype_fun_eq_card, finrank_R]
end

lemma eq_zero_of_eval_eq_zero  [finite σ] (p : mv_polynomial σ K)
  (h : ∀v:σ → K, eval v p = 0) (hp : p ∈ restrict_degree σ K (fintype.card K - 1)) :
  p = 0 :=
let p' : R σ K := ⟨p, hp⟩ in
have p' ∈ (evalᵢ σ K).ker := funext h,
show p'.1 = (0 : R σ K).1, from congr_arg _ $ by rwa [ker_evalₗ, mem_bot] at this

end mv_polynomial
