import data.mv_polynomial
import linear_algebra.smodeq

open_locale big_operators

variables {I J R M : Type*} [add_comm_monoid M] [decidable_eq I] [comm_ring R]
namespace pi

@[elab_as_eliminator]
lemma single_induction_on [fintype I]
  (x : I → M) {P : (I → M) → Prop} (hP : P 0) (hP' : ∀ a b, P a → P b → P (a + b))
    (hP'' : ∀ i m, P (pi.single i m)) : P x :=
begin
  let e : (I →₀ M) ≃+ (I → M) :=
  { map_add' := λ x y, rfl, ..finsupp.equiv_fun_on_fintype },
  obtain ⟨x, rfl⟩ := e.surjective x,
  apply finsupp.induction_linear x,
  { rwa map_zero },
  { intros f g hf hg, rw map_add, apply_assumption; assumption },
  { intros i m, convert hP'' i m, ext j, change finsupp.single i m j = pi.single i m j,
    rw [finsupp.single_apply, pi.single_apply],
    congr' 1,
    rw @eq_comm _ i }
end

@[to_additive]
lemma apply_mul_single' {α β : Type*} [has_one α] [has_one β] (f : α → β)
  (hf : f 1 = 1) (i : I) (x : α) (j : I) : f (pi.mul_single i x j) = pi.mul_single i (f x) j :=
pi.apply_mul_single (λ _, f) (λ _, hf) i x j

lemma fintype_sum_single [fintype I] (f : I → M) :
  ∑ i : I, pi.single i (f i) = f :=
begin
  apply pi.single_induction_on f,
  { simp_rw [pi.zero_apply, pi.single_zero, finset.sum_const_zero] },
  { intros a b ha hb, simp_rw [pi.add_apply, pi.single_add, finset.sum_add_distrib, ha, hb] },
  { intros j a, simp [pi.single_apply, apply_ite (pi.single _)] }
end

end pi

namespace mv_polynomial

variable [fintype I]

@[elab_as_eliminator]
lemma fintype_to_induction
  (x : I → mv_polynomial J R)
  {P : (I → mv_polynomial J R) → Prop}
  (hzero : P 0)
  (hC : ∀ i (r : R), P (pi.single i $ C r))
  (hadd : ∀ x y, P x → P y → P (x + y))
  (hsmul : ∀ i j p, P (pi.single i p) →
    P ((X j : mv_polynomial J R) • pi.single i p)) : P x :=
begin
  apply pi.single_induction_on x,
  { assumption },
  { assumption },
  intros i p,
  apply induction_on p,
  { apply_assumption },
  { simp_rw pi.single_add, intros p q, apply_assumption },
  { intros q j h,
    rw [mul_comm, ← smul_eq_mul],
    convert hsmul i j q h,
    letI : distrib_mul_action (mv_polynomial J R) (mv_polynomial J R) := infer_instance,
    exact pi.single_smul i (X j : mv_polynomial J R) q },
end

namespace exists_smodeq_of_X_exists_smodeq

variables (p : submodule (mv_polynomial J R) (I → mv_polynomial J R))

instance : is_scalar_tower R (mv_polynomial J R) (I → mv_polynomial J R) :=
@@pi.is_scalar_tower _ _ _ _ (λ _, infer_instance)

local attribute [irreducible] mv_polynomial

instance : is_scalar_tower R (mv_polynomial J R) ((I → mv_polynomial J R) ⧸ p) :=
infer_instance

local attribute [semireducible] mv_polynomial

noncomputable
def mkq_constants : (I → R) →ₗ[R] ((I → mv_polynomial J R) ⧸ p) :=
(p.mkq.restrict_scalars R : _).comp
  (((algebra.of_id R $ mv_polynomial J R).comp_left I) : _).to_linear_map

lemma mkq_constants_single (i : I) (r : R) :
  mkq_constants p (pi.single i r) = p.mkq (pi.single i (C r)) :=
begin
  dsimp [mkq_constants],
  congr' 1,
  ext1 j,
  rw [alg_hom.comp_left_apply, ← pi.apply_single' _ C.map_zero],
  refl
end

lemma single_monomial_mem_mkq_constants_range
  (h : ∀ i j, p.mkq (pi.single i (X j)) ∈ (mkq_constants p).range)
  {s : multiset J}
  (hn : ∀ (q : I → mv_polynomial J R) (hq : ∀ i, (q i).total_degree < s.card),
    p.mkq q ∈ (mkq_constants p).range)
    (i : I) (r : R) :
    p.mkq (pi.single i (monomial s.to_finsupp r)) ∈ (mkq_constants p).range :=
begin
  rcases s.empty_or_exists_mem with (rfl|⟨j, hj⟩),
  { delta mkq_constants,
    rw [linear_map.range_comp],
    apply submodule.mem_map_of_mem,
    exact ⟨pi.single i r, funext $ λ j, pi.apply_single' _ C.map_zero i r j⟩ },
  { obtain ⟨s', rfl⟩ := multiset.exists_cons_of_mem hj,
    obtain ⟨v, e⟩ := h i j,
    rw [← multiset.singleton_add, map_add, multiset.to_finsupp_singleton,
      monomial_single_add, pow_one, mul_comm, ← smul_eq_mul, pi.single_smul', map_smul, ← e],
    clear e hj,
    apply pi.single_induction_on v,
    { rw [map_zero, smul_zero], exact zero_mem _ },
    { intros x y hx hy, rw [map_add, smul_add], exact add_mem hx hy },
    { intros i s,
      rw [mkq_constants_single, ← map_smul],
      apply hn,
      intros i',
      rw [pi.smul_apply, smul_eq_mul, multiset.card_cons, nat.lt_add_one_iff, ← add_zero s'.card],
      refine (total_degree_mul _ _).trans (add_le_add _ _),
      { refine (total_degree_le_degrees_card _).trans
          ((multiset.card_le_of_le $degrees_monomial _ _).trans _),
        rw multiset.to_finsupp_to_multiset },
      { dsimp,
        rw pi.single_apply,
        split_ifs,
        { change (C s).total_degree ≤ 0, rw total_degree_C },
        { rw total_degree_zero } } } }
end
.
lemma mem_mkq_constants_range_of_degree_le
  (h : ∀ i j, p.mkq (pi.single i (X j)) ∈ (mkq_constants p).range)
  (n : ℕ)
  (hn : ∀ (q : I → mv_polynomial J R) (hq : ∀ i, (q i).total_degree < n),
    p.mkq q ∈ (mkq_constants p).range)
  (q' : I → mv_polynomial J R) (hq' : ∀ i, (q' i).total_degree ≤ n) :
    p.mkq q' ∈ (mkq_constants p).range :=
begin
  rw [← pi.fintype_sum_single q', map_sum],
  apply sum_mem,
  rintros i -,
  rw [← mul_one (q' i), ← smul_eq_mul, pi.single_smul',
    ← (q' i).support_sum_monomial_coeff, finset.sum_smul, map_sum],
  apply sum_mem,
  intros c hc,
  obtain ⟨s, rfl⟩ := multiset.to_finsupp.surjective c,
  rw [← pi.single_smul', smul_eq_mul, mul_one],
  apply single_monomial_mem_mkq_constants_range _ h,
  intros q hq,
  refine hn q (λ j, (hq j).trans_le (le_trans _ (hq' i))),
  rw [total_degree_eq, ← s.to_finsupp_to_multiset],
  exact @finset.le_sup _ _ _ _ _ (λ m : J →₀ ℕ, m.to_multiset.card) _ hc,
end

lemma mkq_constants_surjective
  (h : ∀ i j, p.mkq (pi.single i (X j)) ∈ (mkq_constants p).range) :
    function.surjective (mkq_constants p) :=
begin
  suffices : ∀ n (q : I → mv_polynomial J R) (hq : ∀ i, (q i).total_degree < n),
    p.mkq q ∈ (mkq_constants p).range,
  { rw [← linear_map.range_eq_top, eq_top_iff],
    rintros q -,
    obtain ⟨q, rfl⟩ := p.mkq_surjective q,
    apply this (finset.univ.sup (λ i, (q i).total_degree) + 1),
    intro i,
    rw nat.lt_add_one_iff,
    exact @finset.le_sup _ _ _ _ _ (λ i, (q i).total_degree) _ (finset.mem_univ _) },
  intro n,
  induction n,
  { intros q hq,
    casesI is_empty_or_nonempty I,
    { obtain rfl : q = 0 := funext is_empty_elim, exact zero_mem _ },
    { exact (nat.not_lt_zero _ (hq (classical.arbitrary _))).elim } },
  { simp_rw nat.lt_succ_iff,
    apply mem_mkq_constants_range_of_degree_le _ h _ n_ih }
end

end exists_smodeq_of_X_exists_smodeq

open exists_smodeq_of_X_exists_smodeq

lemma exists_smodeq_of_X_exists_smodeq {I J R : Type*} [fintype I] [decidable_eq I] [comm_ring R]
  (p : submodule (mv_polynomial J R) (I → mv_polynomial J R))
  (h : ∀ i j, ∃ r : I → R, pi.single i (X j) ≡ C ∘ r [SMOD p]) :
  ∀ x, ∃ r : I → R, x ≡ C ∘ r [SMOD p] :=
begin
  intro x,
  simp_rw [smodeq.def] at h ⊢,
  obtain ⟨r, e⟩ := mkq_constants_surjective p _ (submodule.quotient.mk x),
  { exact ⟨r, e.symm⟩ },
  intros i j,
  obtain ⟨r, e⟩ := h i j,
  exact ⟨r, e.symm⟩
end

end mv_polynomial
