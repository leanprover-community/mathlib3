import data.real.basic
import algebra.big_operators
import data.polynomial
import analysis.calculus.deriv
import tactic

noncomputable theory
open_locale big_operators

namespace small_lemmas

--theorem int.cast_ring_hom ℝ_inj : function.injective int.cast_ring_hom ℝ := λ a b h, by {simp only [ring_hom.eq_int_cast, int.cast_inj] at h, exact h,}
--theorem int.cast_ring_hom ℝ_zero : int.cast_ring_hom ℝ 0 = 0 := by exact int.cast_ring_hom ℝ.map_zero

/--
f_eval_on_ℝ p is to evaluate p as a real polynomial
-/
def f_eval_on_ℝ (f : polynomial ℤ) (α : ℝ) : ℝ := polynomial.aeval α f

theorem f_eval_on_ℝ_add (f g : polynomial ℤ) (t : ℝ) : f_eval_on_ℝ (f + g) t = (f_eval_on_ℝ f t) + (f_eval_on_ℝ g t) :=
begin
  simp only [f_eval_on_ℝ, polynomial.map_add, polynomial.aeval_add],
end

theorem f_eval_on_ℝ_sum (s : finset ℕ) (f : ℕ -> polynomial ℤ) (t : ℝ) : f_eval_on_ℝ (∑ i in s, f i) t = ∑ i in s, f_eval_on_ℝ (f i) t :=
begin
  apply finset.induction_on s,
  {simp only [f_eval_on_ℝ, finset.sum_empty, polynomial.aeval_zero, polynomial.map_zero]},
  intros n s hn ih,
  rw finset.sum_insert, rw f_eval_on_ℝ_add, rw ih, rw finset.sum_insert, assumption, assumption,
end

theorem f_eval_on_ℝ_mul (f g : polynomial ℤ) (t : ℝ) : f_eval_on_ℝ (f * g) t = (f_eval_on_ℝ f t) * (f_eval_on_ℝ g t) :=
begin
  simp only [f_eval_on_ℝ, polynomial.aeval_mul, polynomial.map_mul],
end

theorem f_eval_on_ℝ_prod (s : finset ℕ) (f : ℕ -> polynomial ℤ) (t : ℝ) : f_eval_on_ℝ (∏ i in s, f i) t = ∏ i in s, f_eval_on_ℝ (f i) t :=
begin
  apply finset.induction_on s,
  {simp only [f_eval_on_ℝ, polynomial.aeval_one, finset.prod_empty, polynomial.map_one]},
  intros n s hn ih, rw finset.prod_insert, rw f_eval_on_ℝ_mul, rw ih, rw finset.prod_insert, assumption, assumption,
end

lemma f_eval_on_ℝ_nat (f : polynomial ℤ) (k : ℕ) : (f_eval_on_ℝ f (k:ℝ)) = int.cast_ring_hom ℝ (polynomial.eval k f) :=
begin
  apply polynomial.induction_on f,
  {
    intro a, simp only [f_eval_on_ℝ,
 int.cast_id,
 ring_hom.eq_int_cast,
 alg_hom.map_int_cast,
 int.cast_inj,
 eq_self_iff_true,
 polynomial.eval_int_cast],
  },
  {
    intros p q hp hq,
    simp only [f_eval_on_ℝ_add, hp, hq, int.cast_add, ring_hom.eq_int_cast, polynomial.eval_add],
  },
  {
    intros m a ha,
    simp only [f_eval_on_ℝ, int.cast_coe_nat, polynomial.eval_X, polynomial.map_C, int.cast_pow, polynomial.eval_C,
 polynomial.map_X, int.cast_mul, polynomial.eval_pow, polynomial.map_pow, polynomial.eval_mul,
 polynomial.map_mul] at ha ⊢,
 simp only [int.cast_coe_nat,
 int.cast_eq_zero,
 int.cast_pow,
 pow_left_inj,
 ring_hom.eq_int_cast,
 alg_hom.map_int_cast,
 int.cast_mul,
 mul_eq_mul_left_iff,
 true_or,
 eq_self_iff_true,
 nat.cast_inj,
 polynomial.aeval_X_pow,
 map_mul],
  },
end

theorem f_eval_on_ℝ_deriv (f : polynomial ℤ) : (deriv (f_eval_on_ℝ f)) = (f_eval_on_ℝ (f.derivative)) :=
begin
  ext,
  simp_rw [f_eval_on_ℝ, polynomial.aeval_def, polynomial.eval₂_eq_eval_map,
    ←polynomial.derivative_map, ←polynomial.deriv, polynomial.eval_map],
  refl,
end

lemma coe_f_eval (f : polynomial ℤ) (i : ℕ) : f_eval_on_ℝ f (i:ℝ) = ((@polynomial.eval ℤ _ (i : ℤ) f):ℝ) :=
begin
  rw [f_eval_on_ℝ_nat, ring_hom.eq_int_cast],
end

end small_lemmas
