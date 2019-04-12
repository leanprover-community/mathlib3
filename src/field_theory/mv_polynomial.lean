/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl

Multivariate functions of the form `α^n → α` are isomorphic to multivariate polynomials in
`n` variables.
-/
import linear_algebra.finsupp field_theory.finite
noncomputable theory

local attribute [instance, priority 0] classical.prop_decidable

open lattice set linear_map submodule

namespace mv_polynomial

variables {α : Type*} {σ : Type*}
variables [discrete_field α] [fintype α] [fintype σ] [decidable_eq σ]

def indicator (a : σ → α) : mv_polynomial σ α :=
finset.univ.prod (λn, 1 - (X n - C (a n))^(fintype.card α - 1))

lemma eval_indicator_apply_eq_one (a : σ → α) :
  eval a (indicator a) = 1 :=
have 0 < fintype.card α - 1,
begin
  rw [← finite_field.card_units, fintype.card_pos_iff],
  exact ⟨1⟩
end,
by simp only [indicator, (finset.prod_hom (eval a)).symm, eval_sub,
    is_ring_hom.map_one (eval a), is_semiring_hom.map_pow (eval a), eval_X, eval_C,
    sub_self, zero_pow this, sub_zero, finset.prod_const_one]

lemma eval_indicator_apply_eq_zero (a b : σ → α) (h : a ≠ b) :
  eval a (indicator b) = 0 :=
have ∃i, a i ≠ b i, by rwa [(≠), function.funext_iff, not_forall] at h,
begin
  rcases this with ⟨i, hi⟩,
  simp only [indicator, (finset.prod_hom (eval a)).symm, eval_sub,
    is_ring_hom.map_one (eval a), is_semiring_hom.map_pow (eval a), eval_X, eval_C,
    sub_self, finset.prod_eq_zero_iff],
  refine ⟨i, finset.mem_univ _, _⟩,
  rw [finite_field.pow_card_sub_one_eq_one, sub_self],
  rwa [(≠), sub_eq_zero],
end

lemma degrees_indicator (c : σ → α) :
  degrees (indicator c) ≤ finset.univ.sum (λs:σ, add_monoid.smul (fintype.card α - 1) {s}) :=
begin
  rw [indicator],
  refine le_trans (degrees_prod _ _) (finset.sum_le_sum $ assume s hs, _),
  refine le_trans (degrees_sub _ _) _,
  rw [degrees_one, ← bot_eq_zero, bot_sup_eq],
  refine le_trans (degrees_pow _ _) (add_monoid.smul_le_smul_of_le_right _ _),
  refine le_trans (degrees_sub _ _) _,
  rw [degrees_C, ← bot_eq_zero, sup_bot_eq],
  exact degrees_X _
end

set_option class.instance_max_depth 50
lemma indicator_mem_restrict_degree (c : σ → α) :
  indicator c ∈ restrict_degree σ α (fintype.card α - 1) :=
begin
  rw [mem_restrict_degree_iff_sup, indicator],
  assume n,
  refine le_trans (multiset.count_le_of_le _ $ degrees_indicator _) (le_of_eq _),
  rw [← finset.sum_hom (multiset.count n)],
  simp only [is_add_monoid_hom.map_smul (multiset.count n), multiset.singleton_eq_singleton,
    add_monoid.smul_eq_mul, nat.cast_id],
  transitivity,
  refine finset.sum_eq_single n _ _,
  { assume b hb ne, rw [multiset.count_cons_of_ne ne.symm, multiset.count_zero, mul_zero] },
  { assume h, exact (h $ finset.mem_univ _).elim },
  { rw [multiset.count_cons_self, multiset.count_zero, mul_one] }
end

section
variables (α σ)
def evalₗ : mv_polynomial σ α →ₗ[α] (σ → α) → α :=
⟨ λp e, p.eval e,
  assume p q, funext $ assume e, eval_add,
  assume a p, funext $ assume e, by rw [smul_eq_C_mul, eval_mul, eval_C]; refl ⟩
end

section
set_option class.instance_max_depth 50
lemma evalₗ_apply (p : mv_polynomial σ α) (e : σ → α) : evalₗ α σ p e = p.eval e :=
rfl
end

lemma map_restrict_dom_evalₗ : (restrict_degree σ α (fintype.card α - 1)).map (evalₗ α σ) = ⊤ :=
begin
  refine top_unique (submodule.le_def'.2 $ assume e _, mem_map.2 _),
  refine ⟨finset.univ.sum (λn:σ → α, e n • indicator n), _, _⟩,
  { exact sum_mem _ (assume c _, smul_mem _ _ (indicator_mem_restrict_degree _)) },
  { ext n,
    simp only [linear_map.map_sum, @pi.finset_sum_apply (σ → α) (λ_, α) _ _ _ _ _,
      pi.smul_apply, linear_map.map_smul],
    simp only [evalₗ_apply],
    transitivity,
    refine finset.sum_eq_single n _ _,
    { assume b _ h,
      rw [eval_indicator_apply_eq_zero _ _ h.symm, smul_zero] },
    { assume h, exact (h $ finset.mem_univ n).elim },
    { rw [eval_indicator_apply_eq_one, smul_eq_mul, mul_one] } }
end
end mv_polynomial

namespace mv_polynomial
universe u
variables (σ : Type u) (α : Type u) [decidable_eq σ] [fintype σ] [discrete_field α] [fintype α]

def R : Type u := restrict_degree σ α (fintype.card α - 1)

instance R.add_comm_group : add_comm_group (R σ α) := by dunfold R; apply_instance
instance R.vector_space : vector_space α (R σ α) := by dunfold R; apply_instance

set_option class.instance_max_depth 50
lemma dim_R : vector_space.dim α (R σ α) = fintype.card (σ → α) :=
calc vector_space.dim α (R σ α) =
  vector_space.dim α (↥{s : σ →₀ ℕ | ∀ (n : σ), s n ≤ fintype.card α - 1} →₀ α) :
    linear_equiv.dim_eq
      (finsupp.restrict_dom_equiv_finsupp α α {s : σ →₀ ℕ | ∀n:σ, s n ≤ fintype.card α - 1 })
  ... = cardinal.mk {s : σ →₀ ℕ | ∀ (n : σ), s n ≤ fintype.card α - 1} :
    by rw [finsupp.dim_eq, dim_of_field, mul_one]
  ... = cardinal.mk {s : σ → ℕ | ∀ (n : σ), s n < fintype.card α } :
  begin
    refine quotient.sound ⟨equiv.subtype_congr finsupp.equiv_fun_on_fintype $ assume f, _⟩,
    refine forall_congr (assume n, nat.le_sub_right_iff_add_le _),
    exact fintype.card_pos_iff.2 ⟨0⟩
  end
  ... = cardinal.mk (σ → {n // n < fintype.card α}) :
    quotient.sound ⟨@equiv.subtype_pi_equiv_pi σ (λ_, ℕ) (λs n, n < fintype.card α)⟩
  ... = cardinal.mk (σ → fin (fintype.card α)) :
    quotient.sound ⟨equiv.arrow_congr (equiv.refl σ) (equiv.fin_equiv_subtype _).symm⟩
  ... = cardinal.mk (σ → α) :
  begin
    refine (trunc.induction_on (fintype.equiv_fin α) $ assume (e : α ≃ fin (fintype.card α)), _),
    refine quotient.sound ⟨equiv.arrow_congr (equiv.refl σ) e.symm⟩
  end
  ... = fintype.card (σ → α) : cardinal.fintype_card _

def evalᵢ : R σ α →ₗ[α] (σ → α) → α :=
((evalₗ α σ).comp (restrict_degree σ α (fintype.card α - 1)).subtype)

lemma range_evalᵢ : (evalᵢ σ α).range = ⊤ :=
begin
  rw [evalᵢ, linear_map.range_comp, range_subtype],
  exact map_restrict_dom_evalₗ
end

lemma ker_evalₗ : (evalᵢ σ α).ker = ⊥ :=
begin
  refine injective_of_surjective _ _ _ (range_evalᵢ _ _),
  { rw [dim_R], exact cardinal.nat_lt_omega _ },
  { rw [dim_R, dim_fun, dim_of_field, mul_one] }
end

lemma eq_zero_of_eval_eq_zero (p : mv_polynomial σ α)
  (h : ∀v:σ → α, p.eval v = 0) (hp : p ∈ restrict_degree σ α (fintype.card α - 1)) :
  p = 0 :=
let p' : R σ α := ⟨p, hp⟩ in
have p' ∈ (evalᵢ σ α).ker := by rw [mem_ker]; ext v; exact h v,
show p'.1 = (0 : R σ α).1,
begin
  rw [ker_evalₗ, mem_bot] at this,
  rw [this]
end

end mv_polynomial
