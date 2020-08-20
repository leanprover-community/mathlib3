import data.real.basic
import algebra.big_operators
import data.polynomial
import analysis.calculus.deriv
import tactic

noncomputable theory
open_locale big_operators

namespace small_lemmas

theorem aeval_sum' (s : finset ℕ) (f : ℕ -> (polynomial ℤ)) (t : ℝ) : @polynomial.aeval ℤ ℝ _ _ _ t (∑ i in s, f i) = ∑ i in s, @polynomial.aeval ℤ ℝ _ _ _ t (f i) :=
begin
  apply finset.induction_on s, simp only [finset.sum_empty, alg_hom.map_zero],
  intros a s ha ih, rw finset.sum_insert, simp only [alg_hom.map_add], rw ih,
  rw finset.sum_insert, exact ha, exact ha,
end

theorem eval₂_sum' (s : finset ℕ) (g : ℤ →+* ℝ) (f : ℕ -> (polynomial ℤ)) (t : ℝ) :
  polynomial.eval₂ g t (∑ i in s, f i) = ∑ i in s, polynomial.eval₂ g t (f i) :=
begin
  apply finset.induction_on s, simp only [finset.sum_empty, alg_hom.map_zero],
  exact is_ring_hom.map_zero (polynomial.eval₂ g t),
  intros a s ha ih, rw finset.sum_insert, simp only [polynomial.eval₂_add], rw ih,
  rw finset.sum_insert, exact ha, exact ha,
end

theorem eval_sum' (s : finset ℕ) (f : ℕ -> (polynomial ℤ)) (t : ℤ) : polynomial.eval t (∑ i in s, f i) = ∑ i in s, polynomial.eval t (f i) :=
begin
  apply finset.induction_on s, simp only [finset.sum_empty, polynomial.eval_zero],
  intros a s ha ih, rw finset.sum_insert, rw polynomial.eval_add, rw ih, rw finset.sum_insert, exact ha, exact ha,
end

theorem eval_prod' (s : finset ℕ) (f : ℕ -> (polynomial ℤ)) (t : ℤ) : polynomial.eval t (∏ i in s, f i) = ∏ i in s, polynomial.eval t (f i) :=
begin
  apply finset.induction_on s, simp only [polynomial.eval_one, finset.prod_empty],
  intros a s ha ih, rw finset.prod_insert, rw polynomial.eval_mul, rw ih, rw finset.prod_insert, exact ha, exact ha,
end

theorem same_sum {s : finset ℕ} (f g : ℕ -> ℝ) (h : ∀ i ∈ s, f i = g i) : (∑ i in s, f i) = ∑ i in s, g i :=
begin
exact finset.sum_congr rfl h,
end

/--
The trivial embedding of ℤ into ℝ
-/
def ℤembℝ : ℤ →+* ℝ := algebra_map ℤ ℝ

theorem ℤembℝ_inj : function.injective ℤembℝ := λ a b h, by {simp only [ring_hom.eq_int_cast, int.cast_inj] at h, exact h,}
theorem ℤembℝ_zero : ℤembℝ 0 = 0 := by exact ℤembℝ.map_zero

/--
f_eval_on_ℝ p is to evaluate p as a real polynomial
-/
def f_eval_on_ℝ (f : polynomial ℤ) (α : ℝ) : ℝ := (f.map ℤembℝ).eval α

theorem f_eval_on_ℝ_add (f g : polynomial ℤ) (t : ℝ) : f_eval_on_ℝ (f + g) t = (f_eval_on_ℝ f t) + (f_eval_on_ℝ g t) :=
begin
  simp only [f_eval_on_ℝ, polynomial.map_add, polynomial.eval_add],
end

theorem f_eval_on_ℝ_sum (s : finset ℕ) (f : ℕ -> polynomial ℤ) (t : ℝ) : f_eval_on_ℝ (∑ i in s, f i) t = ∑ i in s, f_eval_on_ℝ (f i) t :=
begin
  apply finset.induction_on s, simp only [f_eval_on_ℝ, finset.sum_empty, polynomial.eval_zero, polynomial.map_zero],
  intros n s hn ih, rw finset.sum_insert, rw f_eval_on_ℝ_add, rw ih, rw finset.sum_insert, assumption, assumption,
end

theorem f_eval_on_ℝ_mul (f g : polynomial ℤ) (t : ℝ) : f_eval_on_ℝ (f * g) t = (f_eval_on_ℝ f t) * (f_eval_on_ℝ g t) :=
begin
  simp only [f_eval_on_ℝ, polynomial.eval_mul, polynomial.map_mul],
end

theorem f_eval_on_ℝ_prod (s : finset ℕ) (f : ℕ -> polynomial ℤ) (t : ℝ) : f_eval_on_ℝ (∏ i in s, f i) t = ∏ i in s, f_eval_on_ℝ (f i) t :=
begin
  apply finset.induction_on s, simp only [f_eval_on_ℝ, polynomial.eval_one, finset.prod_empty, polynomial.map_one], intros n s hn ih, rw finset.prod_insert, rw f_eval_on_ℝ_mul, rw ih, rw finset.prod_insert, assumption, assumption,
end

private lemma f_eval_on_ℝ_nat (f : polynomial ℤ) (k : ℕ) : (f_eval_on_ℝ f (k:ℝ)) = ℤembℝ (polynomial.eval k f) :=
begin
  apply polynomial.induction_on f,
  {
    intro a, simp only [f_eval_on_ℝ, polynomial.map_C, polynomial.eval_C],
  },
  {
    intros p q hp hq,
    simp only [f_eval_on_ℝ_add, hp, hq, int.cast_add, ring_hom.eq_int_cast, polynomial.eval_add],
  },
  {
    intros m a ha, simp only [f_eval_on_ℝ, int.cast_coe_nat, polynomial.eval_X, polynomial.map_C, int.cast_pow, polynomial.eval_C,
 polynomial.map_X, int.cast_mul, polynomial.eval_pow, polynomial.map_pow, polynomial.eval_mul,
 polynomial.map_mul] at ha ⊢, simp only [int.cast_coe_nat, int.cast_pow, ring_hom.eq_int_cast, int.cast_mul],
  },
end

theorem f_eval_on_ℝ_deriv (f : polynomial ℤ) : (deriv (f_eval_on_ℝ f)) = (f_eval_on_ℝ (f.derivative)) :=
begin
  ext,
  simp_rw [f_eval_on_ℝ],
  have eq := @polynomial.deriv ℝ _ x (polynomial.map ℤembℝ f),
  rw <-polynomial.derivative_map,
  rw <-eq, refl,
end

-- compute list of coeff of a polynomial
-- def list_coeff (f : polynomial ℤ) : (finset ℤ) := f.support.image f.to_fun

-- lemma coeff_in_list_coeff (f : polynomial ℤ)  (n ∈ f.support): (f.coeff n) ∈ (list_coeff f) :=
-- begin
--     rw [list_coeff, finset.mem_image], use n,
--     split, assumption, exact rfl,
-- end

lemma not_in_support_iff_coeff_zero {α : Type} [_inst_ : comm_semiring α] (f : polynomial α) (n : ℕ): (f.coeff n) = 0 ↔ n ∉ f.support :=
begin
    split, exact finsupp.not_mem_support_iff.mpr, exact finsupp.not_mem_support_iff.mp,
end


-- f = 0 on an interval then f is zero (polynomial ℝ)
/--
n ↦ a + 1/(n+1)
-/

def function_ℕ_Icc (a : ℝ) : ℕ -> set.Icc (a-1) (a+1) := λ n,
⟨(n+1)⁻¹ + a,
 ⟨calc a - 1 ≤ a : by linarith
      ...    ≤ a + (n+1)⁻¹ : begin norm_num, norm_cast, norm_num, end
      ...    ≤ (n+1)⁻¹ + a : by linarith,
    begin
        have ineq1 : (n+1:ℝ)⁻¹ ≤ 1,
        have ineq2 := (@inv_le _ _ (n+1:ℝ) 1 _ _).2, simp only [forall_prop_of_true, inv_one, le_add_iff_nonneg_left, nat.cast_nonneg] at ineq2, exact ineq2,
        exact nat.cast_add_one_pos n, exact zero_lt_one, linarith,
    end⟩⟩

theorem function_ℕ_Icc_inj (a : ℝ) : function.injective $ function_ℕ_Icc a :=
begin
    intros m n hmn,
    rw [function_ℕ_Icc] at hmn, simp only [add_left_inj, inv_inj', subtype.mk_eq_mk, nat.cast_inj] at hmn, exact hmn,
end

theorem inf_set_cannot_be_subset_of_fin_set {a : Type} (S : set a) (T : set a) (hS : infinite S) (hT : set.finite T) : ¬ (S.subset T) :=
begin
    by_contra absurd,
    generalize hf : set.inclusion absurd = f,
    have absurd2 := @not_injective_infinite_fintype ↥S _ _ (set.finite.fintype hT) f,
    rw <-hf at absurd2,
    have contra := set.inclusion_injective absurd, simpa,
end

theorem f_zero_on_interval_f_zero {a : ℝ} (f : polynomial ℝ) (f_zero: ∀ x : ℝ, x ∈ (set.Icc (a-1) (a+1)) -> f.eval x = 0) : f = 0 :=
begin
    by_contra absurd,
    choose roots hroots using polynomial.exists_finset_roots absurd,
    have absurd2 : (set.Icc (a-1) (a+1)).subset ↑roots,
    {
        rw set.subset, intros a ha, apply (hroots.2 a).2,
        simp only [polynomial.is_root.def], exact f_zero a ha,
    },
    have inf : infinite (set.Icc (a-1) (a+1)),
    {
        exact infinite.of_injective (function_ℕ_Icc a) (function_ℕ_Icc_inj a),
    },

    have inf2 := @infinite.of_injective _ _ inf (set.inclusion absurd2) (set.inclusion_injective absurd2),
    have absurd3 := inf_set_cannot_be_subset_of_fin_set (set.Icc (a-1) (a+1)) (↑roots) inf _,
    exact absurd (false.rec (f = 0) (absurd3 absurd2)),
    exact finset.finite_to_set roots,
end

theorem zero_deriv_imp_const_poly_ℝ (f : polynomial ℝ) (h : f.derivative = 0) : f.nat_degree = 0 :=
begin
    by_cases hf : (f = 0), exact (congr_arg polynomial.nat_degree hf).trans rfl,

    rw polynomial.nat_degree_eq_zero_iff_degree_le_zero,
    by_contradiction absurd, simp only [not_le] at absurd,
    generalize hm : f.nat_degree - 1 = m,
    have f_nat_degree_pos : f.nat_degree > 0,
    {
        have H := polynomial.degree_eq_nat_degree hf,
        have ineq := @polynomial.degree_le_nat_degree _ _ f,
        have ineq2 := lt_of_lt_of_le absurd ineq, exact with_bot.coe_lt_coe.mp ineq2,
    },

    rw polynomial.ext_iff at h,
    rename_var n m at h, simp only [polynomial.coeff_zero] at h,
    replace h := h m,
    have H2 := polynomial.coeff_derivative f m, rw h at H2,
    simp only [zero_eq_mul] at H2, cases H2,
    {
        have hm : m + 1 = f.nat_degree,
        rw [<-hm],
        exact nat.sub_add_cancel f_nat_degree_pos,
        have H := (polynomial.coeff_derivative f m), rw h at H, simp only [zero_eq_mul] at H,
        cases H, rw hm at H,
        have H2 := @polynomial.leading_coeff_eq_zero _ _ f,
        rw [polynomial.leading_coeff] at H2,
        exact hf (H2.1 H),
        have ineq := nat.cast_add_one_pos m,
        rw H at ineq, linarith,
    },
    {
        have ineq := nat.cast_add_one_pos m, rw H2 at ineq, linarith,
    },
end

theorem prod_deg (s : ℕ) (f : ℕ -> polynomial ℤ) (hf : ∀ i ∈ finset.range s, f i ≠ 0) : (∏ i in finset.range s, f i).nat_degree = ∑ i in finset.range s, (f i).nat_degree :=
begin
  induction s with s ih,
  simp only [polynomial.nat_degree_one, finset.sum_empty, finset.range_zero, finset.prod_empty],

  rw finset.sum_range_succ, rw finset.prod_range_succ,
  have triv : (∀ (i : ℕ), i ∈ finset.range s → f i ≠ 0),
  {
    intros i hi, apply hf, simp only [finset.mem_range] at hi ⊢, exact nat.lt.step hi,
  },
  replace ih := ih triv, rw <-ih, apply polynomial.nat_degree_mul,
  apply hf, simp only [finset.self_mem_range_succ],
  intro rid, rw [finset.prod_eq_zero_iff] at rid,
  choose a ha using rid,
  refine hf a _ ha.2, simp only [finset.mem_range] at ha ⊢, exact nat.lt.step ha.left,
end

theorem degree_0_constant {α : Type} {inst : comm_semiring α} (f : polynomial α) (hf : f.nat_degree = 0) :
    ∃ a : α, f = (polynomial.C a) :=

begin
    classical,
    by_cases (f = 0), use 0, rw h, ext, simp only [polynomial.C_0],
    use f.coeff 0, ext, induction n with n hn,
    simp only [polynomial.coeff_C_zero], have ineq : n.succ > f.nat_degree,
    {
        suffices : n.succ > 0, rwa hf, exact nat.succ_pos n,
    },
    have zero1 : f.coeff n.succ = 0 := polynomial.coeff_eq_zero_of_nat_degree_lt ineq, rw zero1,
    have zero2 : (polynomial.C (f.coeff 0)).nat_degree = 0 := polynomial.nat_degree_C (f.coeff 0),
    have zero3 : (polynomial.C (f.coeff 0)).coeff n.succ = 0 := polynomial.coeff_eq_zero_of_nat_degree_lt _,
    rw zero3, rw zero2, exact nat.succ_pos n,
end

theorem derivative_emb (f : polynomial ℤ) : (polynomial.map ℤembℝ f.derivative) = (polynomial.map ℤembℝ f).derivative :=
begin
    ext, rw polynomial.coeff_derivative, rw polynomial.coeff_map, rw polynomial.coeff_derivative, rw polynomial.coeff_map,
    simp only [int.cast_coe_nat, int.cast_add, ring_hom.eq_int_cast, int.cast_mul, int.cast_one, int.nat_cast_eq_coe_nat],
end

-- power manipulation
lemma triv (r : ℝ) (n : ℕ) : r ^ n = r ^ (n : ℤ) := by norm_num

-- inequality
lemma a_ge_b_a_div_c_ge_b_div_c (a b c : ℝ) (hab : b ≤ a) (b_nonneg : 0 ≤ b) (hc : 0 < c) : b/ c ≤ a / c :=
begin
    apply div_le_div; linarith,
end

-- archmedian-like
theorem pow_big_enough (A : ℝ) : ∃ r : nat, 1/A ≤ 2 ^ r :=
begin
    have H := @pow_unbounded_of_one_lt ℝ _ _ (1/A) 2 _,
    choose n hn using H,
    use n, exact le_of_lt hn, exact lt_add_one 1,
end

lemma mul_eq_mul' (a b c d : ℝ) : a = c -> b = d -> a * b = c * d := λ h1 h2, by simp only [h1, h2]

-- lemma nonneg_nat (i : ℕ) : (i : ℝ) ≥ 0 :=
-- begin
--   norm_cast, exact bot_le,
-- end

/--
a number x is irrational if there is for every integers a and b
then x - a / b ≠ 0
-/
def irrational' (x : ℝ) := ∀ a b : ℤ, b > 0 -> x - a / b ≠ 0

end small_lemmas

-- #lint
