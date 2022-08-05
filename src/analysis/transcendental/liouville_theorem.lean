import ring_theory.algebraic
import topology.algebra.polynomial
import analysis.calculus.mean_value
import analysis.transcendental.small_lemmas

open small_lemmas

noncomputable theory
open_locale classical

notation α`[X]` := polynomial α
notation `transcendental` x := ¬(is_algebraic ℤ x)
/--
- a number is transcendental ↔ a number is not algebraic
- a Liouville's number $x$ is a number such that
  for every natural number, there is a rational number a/b such that 0 < |x - a/b| < 1/bⁿ
-/

def liouville_number (x : ℝ) := ∀ n : ℕ, ∃ a b : ℤ, b > 1 ∧ 0 < abs(x - a / b) ∧ abs(x - a / b) < 1/b^n

-- x ↦ |f(x)| is continuous
theorem abs_f_eval_around_α_continuous (f : ℝ[X]) (α : ℝ) : continuous_on (λ x : ℝ, (abs (f.eval x))) (set.Icc (α-1) (α+1)) :=
begin
  have H : (λ x : ℝ, (abs (f.eval x))) = abs ∘ (λ x, f.eval x) := rfl,
  rw H,
  have H2 := polynomial.continuous f,
  have H3 := continuous.comp continuous_abs H2,
  exact continuous.continuous_on H3
end
/--
The next two lemmas state coefficient (support resp.) of $f ∈ ℤ[T]$ is the same as $f ∈ ℝ[T]$.
-/
lemma same_coeff (f : ℤ[X]) (n : ℕ): ℤembℝ (f.coeff n) = ((f.map ℤembℝ).coeff n) :=
begin
  simp only [ring_hom.eq_int_cast, polynomial.coeff_map],
end

lemma same_support (f : ℤ[X]) : f.support = (f.map ℤembℝ).support :=
begin
  ext,
  rw [polynomial.mem_support_iff, polynomial.mem_support_iff, polynomial.coeff_map],
  simp only [int.cast_eq_zero, ring_hom.eq_int_cast, iff_self, ne.def],
end

open_locale big_operators

private lemma sum_eq (S : finset ℕ) (f g : ℕ -> ℝ) : (∀ x ∈ S, f x = g x) -> ∑ i in S, f i = ∑ i in S, g i :=
  λ h, @finset.sum_congr _ _ S S f g _ rfl h

private lemma eval_f_a_div_b (f : ℤ[X]) (f_deg : f.nat_degree > 1) (a b : ℤ) (b_non_zero : b > 0) (a_div_b_not_root : (f.map ℤembℝ).eval ((a:ℝ)/(b:ℝ)) ≠ 0) :
  ((f.map ℤembℝ).eval ((a:ℝ)/(b:ℝ))) = ((1:ℝ)/(b:ℝ)^f.nat_degree) * (∑ i in f.support, (f.coeff i : ℝ)*(a:ℝ)^i*(b:ℝ)^(f.nat_degree - i)) :=
begin
  rw [finset.mul_sum, polynomial.eval_map, polynomial.eval₂, polynomial.sum, sum_eq], intros i hi,
  simp only [one_div, ring_hom.eq_int_cast, div_pow],
  rw [<-mul_assoc (↑b ^ f.nat_degree)⁻¹, <-mul_assoc (↑b ^ f.nat_degree)⁻¹],
  field_simp,

  suffices eq : ↑a ^ i / ↑b ^ i = ↑a ^ i * ↑b ^ (f.nat_degree - i) / ↑b ^ f.nat_degree,
  {
    have H := (@mul_left_inj' ℝ _ (↑a ^ i / ↑b ^ i) (↑a ^ i * ↑b ^ (f.nat_degree - i) / ↑b ^ f.nat_degree) ↑(f.coeff i) _).2 eq,
    conv_lhs at H {rw mul_comm, rw <-mul_div_assoc}, conv_rhs at H {rw mul_comm}, rw H, ring,
    norm_cast,
    exact polynomial.mem_support_iff.mp hi },
  have eq1 := @zpow_sub₀ ℝ _ (b:ℝ) _ (f.nat_degree - i) f.nat_degree,
  have eq2 : (f.nat_degree:ℤ) - (i:ℤ) - (f.nat_degree:ℤ) = - i,
  {
    rw [sub_sub, add_comm, <-sub_sub], simp only [zero_sub, sub_self],
  },
  rw eq2 at eq1, rw [zpow_neg, inv_eq_one_div] at eq1,
  have eqb1 : (b:ℝ) ^ (i:ℤ) = (b:ℝ) ^ i := by norm_num,
  rw eqb1 at eq1,
  have eq3 : (f.nat_degree : ℤ) - (i:ℤ) = int.of_nat (f.nat_degree - i),
  {
    norm_num, rw int.coe_nat_sub, by_contra rid, simp at rid,
    have hi' := polynomial.coeff_eq_zero_of_nat_degree_lt rid,
    rw polynomial.mem_support_iff at hi,
    exact hi hi', },
  have eqb2 : (b:ℝ) ^ ((f.nat_degree:ℤ) - (i:ℤ)) = (b:ℝ) ^ (f.nat_degree - i),
  {
    rw eq3, norm_num,
  }, rw eqb2 at eq1,

  have eqb3 : (b:ℝ)^(f.nat_degree:ℤ)= (b:ℝ)^f.nat_degree := by norm_num, rw eqb3 at eq1, conv_rhs {rw [mul_div_assoc, <-eq1]},
  simp only [one_div], rw <-div_eq_mul_inv,
  norm_cast, linarith,
end

private lemma cast1 (f : ℤ[X]) (f_deg : f.nat_degree > 1) (a b : ℤ) (b_non_zero : b > 0) (a_div_b_not_root : (f.map ℤembℝ).eval ((a:ℝ)/(b:ℝ)) ≠ 0) :
  ∑ i in f.support, (f.coeff i : ℝ)*(a:ℝ)^i*(b:ℝ)^(f.nat_degree - i) = (ℤembℝ (∑ i in f.support, (f.coeff i) * a^i * b ^ (f.nat_degree - i))) :=
begin
  rw ring_hom.map_sum, rw sum_eq, intros i hi, norm_num,
end

private lemma ineq1 (f : ℤ[X]) (f_deg : f.nat_degree > 1) (a b : ℤ) (b_non_zero : b > 0) (a_div_b_not_root : (f.map ℤembℝ).eval ((a:ℝ)/(b:ℝ)) ≠ 0) :
  ∑ i in f.support, (f.coeff i) * a^i * b ^ (f.nat_degree - i) ≠ 0 :=
begin
  suffices eq1 : ℤembℝ (∑ i in f.support, (f.coeff i) * a^i * b ^ (f.nat_degree - i)) ≠ 0,
  {
    intro rid, rw rid at eq1,
    conv_rhs at eq1 {rw <-ℤembℝ_zero}, simpa only [],
  },
  intro rid,
  have cast1 := cast1 f f_deg a b b_non_zero a_div_b_not_root, rw rid at cast1,
  have eq2 := (@mul_right_inj' ℝ _ ((1:ℝ)/(b:ℝ)^f.nat_degree) _ _ _).2 cast1,
  rw <-eval_f_a_div_b at eq2, simp only [mul_zero] at eq2, exact a_div_b_not_root eq2,
  exact f_deg, exact b_non_zero, exact a_div_b_not_root,

  intro rid, norm_num at rid, replace rid := pow_eq_zero rid, norm_cast at rid, linarith,
end

private lemma ineq2 (f : ℤ[X]) (f_deg : f.nat_degree > 1) (a b : ℤ) (b_non_zero : b > 0) (a_div_b_not_root : (f.map ℤembℝ).eval ((a:ℝ)/(b:ℝ)) ≠ 0) :
  ℤembℝ (∑ i in f.support, (f.coeff i) * a^i * b ^ (f.nat_degree - i)) ≠ 0 :=
begin
  have cast1 := cast1 f f_deg a b b_non_zero a_div_b_not_root,
  have ineq1 := ineq1 f f_deg a b b_non_zero a_div_b_not_root,
  norm_cast, intro rid, rw <-ℤembℝ_zero at rid, replace rid := ℤembℝ_inj rid,
  exact a_div_b_not_root (false.rec (polynomial.eval (↑a / ↑b) (polynomial.map ℤembℝ f) = 0) (ineq1 rid)),
end

private lemma ineqb (f : ℤ[X]) (f_deg : f.nat_degree > 1) (a b : ℤ) (b_non_zero : b > 0) (a_div_b_not_root : (f.map ℤembℝ).eval ((a:ℝ)/(b:ℝ)) ≠ 0) :
  abs (1/(b:ℝ)^f.nat_degree) = 1/(b:ℝ)^f.nat_degree :=
begin
  rw [abs_of_pos, one_div], simp only [one_div, inv_pos], norm_cast,
  refine pow_pos _ f.nat_degree, exact b_non_zero,
end

private lemma abs_ℤembℝ (x : ℤ) : ℤembℝ (abs x) = abs (ℤembℝ x) := by simp only [ring_hom.eq_int_cast, int.cast_abs]

private lemma ineq3 (x : ℤ) (hx : x ≥ 1) : ℤembℝ x ≥ 1 :=
begin
  simp only [ring_hom.eq_int_cast, ge_iff_le], norm_cast, exact hx,
end

/--
For an integer polynomial f of degree n > 1, if a/b is not a root of f then |f(a/b)| ≥ 1/bⁿ. (wlog b > 0).
If we write `f(T) = ∑ λᵢ Tⁱ`
This is because `|f(a/b)|=|∑ λᵢ aⁱ/bⁱ| = (1/bⁿ) |∑ λᵢ aⁱ b^(n-i)|`, but a/b is not a root, so `|∑ λᵢ aⁱ b^(n-i)| ≥ 1`.
- `ineq1` proves that if a/b is not a root of f then `∑ λᵢ aⁱ b^(n-i) ≠ 0`
-/

theorem abs_f_at_p_div_q_ge_1_div_q_pow_n (f : ℤ[X]) (f_deg : 1 < f.nat_degree) (a b : ℤ) (b_non_zero : 0 < b) (a_div_b_not_root : (f.map ℤembℝ).eval ((a:ℝ)/(b:ℝ)) ≠ 0) :
  1/(b:ℝ)^f.nat_degree ≤ @abs ℝ _ ((f.map ℤembℝ).eval ((a:ℝ)/(b:ℝ))) :=
begin
  have eval1 := eval_f_a_div_b f f_deg a b b_non_zero a_div_b_not_root,               -- This is `f(a/b)=∑ λᵢ aⁱ/bⁱ`
  have cast1 := cast1 f f_deg a b b_non_zero a_div_b_not_root,                        -- This is not maths, but casting types
  have ineq1 := ineq1 f f_deg a b b_non_zero a_div_b_not_root,                        -- This is `∑ λᵢ aⁱ b^(n-i) ≠ 0`
  have ineq2 := ineq2 f f_deg a b b_non_zero a_div_b_not_root,                        -- This is the same but casting types
  rw [eval1, abs_mul, ineqb f f_deg a b b_non_zero a_div_b_not_root, cast1],
  /-
  To prove |f(a/b)| ≥ 1/bⁿ we just need to prove |∑ λᵢ aⁱ b^(n-i)| ≥ 1
  -/
  suffices ineq3 : abs (ℤembℝ (∑ (i : ℕ) in f.support, f.coeff i * a ^ i * b ^ (f.nat_degree - i))) ≥ 1,
  {
    -- We are manipulating inequalities involving multiplication so we use mul_le_mul
    -- mul_le_mul (hac : a ≤ c) (hbd : b ≤ d) (nn_b : 0 ≤ b) (nn_c : 0 ≤ c) : a * b ≤ c * d
    -- Here mul_le_mul needs two things to be positive and the positivity is proved after the main point is proved.
    have H := @mul_le_mul ℝ _ 1 (1/(b:ℝ)^f.nat_degree) (abs (ℤembℝ (∑ (i : ℕ) in f.support, f.coeff i * a ^ i * b ^ (f.nat_degree - i)))) (1/(b:ℝ)^f.nat_degree) ineq3 _ _ _,
    rw one_mul at H, rw mul_comm at H, exact H,
    exact le_refl (1 / ↑b ^ polynomial.nat_degree f),

    -- here is the proof that the things should be positive are positive. All are more or less trival
    {simp only [one_div, inv_nonneg], norm_cast, exact pow_nonneg b_non_zero.le _},
    {exact abs_nonneg _},
  },
  rw <-abs_ℤembℝ, apply ineq3,
  rw [ge_iff_le, ←int.sub_one_lt_iff, sub_self],
  refine lt_of_le_of_ne (abs_nonneg _) _,
  rwa [ne.def, eq_comm, abs_eq_zero],
end

/--
This is the main lemma :
Let α be an irrational number which is a root of f(x) = Σ aⱼ Xᶨ ∈ Z[T] with f(x) ≢  0.

Then there is a constant A = A(α) > 0 such that:
  if a and b are integers with b > 0, then |α - a / b| > A / b^n

N.B. So neccessarily f has degree > 1, otherwise α is rational. But it doesn't hurt if we assume
     f to be an integer polynomial of degree > 1.
-/

lemma about_irrational_root (α : real) (hα : irrational' α) (f : ℤ[X])
  (f_deg : 1 < f.nat_degree) (α_root : f_eval_on_ℝ f α = 0) :
  ∃ A : real, 0 < A ∧ ∀ a b : ℤ, 0 < b -> (A / b ^ (f.nat_degree)) < abs(α - a / b) :=
begin
  have f_nonzero : f ≠ 0,                                                         -- f ∈ ℤ[T] is not zero
  {
    intro rid,
    have f_nat_deg_zero : f.nat_degree = 0 := (congr_arg polynomial.nat_degree rid).trans rfl,
    rw f_nat_deg_zero at f_deg, linarith,
  },
  generalize hfℝ: f.map ℤembℝ = f_ℝ,
  have hfℝ_nonzero : f_ℝ ≠ 0,                                                     -- f ∈ ℝ[T] is not zero
  {
    intro absurd, rw [polynomial.ext_iff] at absurd,
    apply f_nonzero,
      ext, replace absurd := absurd n, simp only [polynomial.coeff_zero] at absurd ⊢,
      rw [<-hfℝ, polynomial.coeff_map, ℤembℝ] at absurd,
      simp only [int.cast_eq_zero, ring_hom.eq_int_cast] at absurd, exact absurd,
  },
  generalize hDf: f_ℝ.derivative = Df_ℝ,                                         -- We use Df_ℝ to denote the (formal) derivative of f ∈ ℝ[T]
  have H := is_compact.exists_forall_ge (@is_compact_Icc _ _ _ _ (α-1) (α+1))      -- x ↦ abs |Df_ℝ| has a maximum on interval (α - 1, α + 1)
              begin rw set.nonempty, use α, rw set.mem_Icc, split; linarith end
              (abs_f_eval_around_α_continuous Df_ℝ α),

  choose x_max hx_max using H,                                                   -- Say the maximum is attained at x_max with M = Df_ℝ(x_max)
  generalize M_def: abs (Df_ℝ.eval x_max) = M,
  have hM := hx_max.2, rw M_def at hM,
  have M_non_zero : M ≠ 0,                                                       -- Then M is not zero :
  {
    intro absurd,                                                            -- Otherwise Df_ℝ(x) = 0 ∀ x ∈ (α-1, α+1)
    rw absurd at hM,
    replace hM : ∀ (y : ℝ), y ∈ set.Icc (α - 1) (α + 1) → (polynomial.eval y Df_ℝ) = 0,
    {
      intros y hy,
      have H := hM y hy, simp at H, rw H,
    },
    replace hM : Df_ℝ = 0 := f_zero_on_interval_f_zero Df_ℝ hM,                                                        -- Then Df_ℝ is the zero polyomial.
    rename hM Df_ℝ_zero,
    have f_ℝ_0 : f_ℝ.nat_degree = 0,                                              -- Then f ∈ ℝ[x] has degree zero
    {
      have H := zero_deriv_imp_const_poly_ℝ f_ℝ _, exact H,
      rw [<-hDf] at Df_ℝ_zero, assumption,
    },
    replace f_ℝ_0 := degree_0_constant f_ℝ f_ℝ_0,                                 -- Then f ∈ ℝ[x] is constant polynomial
    choose c hc using f_ℝ_0,
    have absurd2 : c = 0,                                                         -- But since f(α) = 0, f ∈ ℝ[x] is the zero polynomial
    {
      rw [f_eval_on_ℝ, hfℝ, hc] at α_root, simp only [polynomial.eval_C] at α_root, assumption,
    },
    rw absurd2 at hc,
    simp only [ring_hom.map_zero] at hc, rw <-hfℝ at hc,
    replace hc : polynomial.map ℤembℝ f = polynomial.map ℤembℝ 0, simp only [polynomial.map_zero], exact hc,
    exact f_nonzero (polynomial.map_injective ℤembℝ ℤembℝ_inj hc),                      -- But f ∈ ℤ[x] is not a zero polynomial.
  },
  have M_pos : M > 0,                                                             -- Since M is not zero, M > 0 being abs (sth.)
  {
    apply lt_of_le_of_ne _ M_non_zero.symm,
    rw ←M_def,
    apply abs_nonneg, },
  generalize roots_def :  f_ℝ.roots = f_roots,
  generalize roots'_def : f_roots.to_finset.erase α = f_roots',                             -- f_roots' is the root of f that is not α
  generalize roots_distance_to_α : f_roots'.image (λ x, abs (α - x)) = distances,
  generalize hdistances' : insert (1/M) (insert (1:ℝ) distances) = distances',    -- distances' is the (finite) set {1, 1/M} ⋃ { |β - α| | β ∈ f_roots' }
  have hnon_empty: distances'.nonempty,                                           -- which is not empty, say 1/M ∈ distances'
  {
    rw <-hdistances',
    rw [finset.nonempty], use (1/M), simp only [true_or, eq_self_iff_true, finset.mem_insert],
  },
  generalize hB : finset.min' distances' hnon_empty = B,                          -- Let B be the smallest of distances'.
  have allpos : ∀ x : ℝ, x ∈ distances' -> x > 0,                                 -- Every number in distances' is postive,
  {
    intros x hx, rw [<-hdistances', finset.mem_insert, finset.mem_insert] at hx,
    cases hx,                                                                     -- because it is either 1 / M which is positive
      rw hx, simp only [one_div, gt_iff_lt, inv_pos], exact M_pos,
    cases hx,                                                                     -- or 1
      rw hx, exact zero_lt_one,                                                   -- or |β - α| for some β which is a root of f but is not α.
      rw [<-roots_distance_to_α] at hx, simp only [exists_prop, finset.mem_image] at hx,
      obtain ⟨α0, hα0, hα0'⟩ := hx,
      rw [<-roots'_def] at hα0,
      rw <-hα0', simp only [gt_iff_lt],
      refine lt_of_le_of_ne (abs_nonneg _) _,
      rw [ne_comm, ne.def, abs_eq_zero, sub_eq_zero],
      contrapose! hα0,
      rw [hα0],
      apply finset.not_mem_erase,
  },
  have B_pos : B > 0,                                                             -- Then B is positive.
  {
    have h := allpos (finset.min' distances' hnon_empty) (finset.min'_mem distances' hnon_empty),
    rw <-hB, exact h,
  },
  generalize hA : B / 2 = A,                                                      -- Let A = B/2 > 0.
  use A, split,
  rw [<-hA], apply half_pos, exact B_pos,                                          -- Then A is postive as B is postive
  /- goal : ∀ (a b : ℤ), b > 0 → |α - a/b| > A / bⁿ where n is the degree of f.
     We use proof by contradiction -/
  by_contra absurd, simp only [gt_iff_lt, not_forall, not_lt, not_imp] at absurd,
  choose a ha using absurd,                                                       -- So assume a and b are integers such that |α - a/b| ≤ A / b^n
  choose b hb using ha,
  have hb2 : b ^ f.nat_degree ≥ 1,                                                -- Since b > 0 and n > 1, bⁿ ≥ 1                                                                               -- So A/bⁿ ≤ A
    change b^ f.nat_degree > 0, apply pow_pos, exact hb.1,
  have hb21 : abs (α - a / b) ≤ A,                                                -- Then we also have |α - a/b| ≤ A
  {
    suffices H : (A / b ^ f.nat_degree) ≤ A,
    exact le_trans hb.2 H,
    apply (@div_le_iff ℝ _ A (b ^ f.nat_degree) A _).2,
    apply (@le_mul_iff_one_le_right ℝ _ (b ^ f.nat_degree) A _).2, norm_cast at ⊢, exact hb2,
    rw [<-hA], apply half_pos, assumption, norm_cast, linarith,
  },
  have hb22 : abs (α - a/b) < B,                                                  -- Since A > 0, |α - a/b| ≤ A < 2A = B ≤ 1
  {
    have H := half_lt_self B_pos, rw hA at H, exact gt_of_gt_of_ge H hb21,
  },
  have hab0 : (a/b:ℝ) ∈ set.Icc (α-1) (α+1),                                      -- So a/b ∈ [α-1, α+1]
  {
    suffices : abs (α - a/b) ≤ 1,
    {rw [<-real.closed_ball_eq_Icc, metric.mem_closed_ball, real.dist_eq, abs_sub_comm], exact this},
    suffices : B ≤ 1, linarith,
    rw <-hB,
    refine finset.min'_le distances' 1 _,
    rw [<-hdistances', finset.mem_insert, finset.mem_insert], tauto,
  },
  have hab1 : (a/b:ℝ) ≠ α,                                                      -- a/b is not α because α is irrational
    have H := hα a b hb.1, rw sub_ne_zero at H, exact ne.symm H,
  have hab2 : (a/b:ℝ) ∉ f_roots,                                                -- a/b is not any root because
  {
    by_contra absurd,                                                             -- otherwise a/b ∈ f_roots' (roots of f other than α)
    have H : (a/b:ℝ) ∈ f_roots',
    { rw [<-roots'_def, finset.mem_erase, multiset.mem_to_finset], exact ⟨hab1, absurd⟩},
    have H2 : abs (α - a/b) ∈ distances',                                       -- Then |α - a/b| is in {1, 1/M} ∪ {|β - α| | β ∈ f_roots' }
    {
      rw [<-hdistances', finset.mem_insert, finset.mem_insert], right, right,
      rw [<-roots_distance_to_α, finset.mem_image], use (a/b:ℝ), split, exact H, refl,
    },
    have H3 := finset.min'_le distances' (abs (α - a/b)) H2,       -- Then B > |α - a/b| ≥ B. A contradiction
    generalize_proofs at hB H3,
    rw hB at H3, exact H3.not_lt hb22,
  },
  /- Since α ≠ a/b, either α > a/b or α < a/b, two cases essentially have the same proof. -/
  have hab3 := ne_iff_lt_or_gt.1 hab1,
  cases hab3,
  {
    have H := exists_deriv_eq_slope (λ x, f_ℝ.eval x) hab3 _ _,                   -- We mean value theorem in this case to find
    choose x0 hx0 using H,                                                        -- an x₀ ∈ (a/b, α) such that Df_ℝ(x₀) = (f(α) - f(a/b))/(α - a/b),
    have hx0r := hx0.2,                                                           -- since f(α) = 0, Df_ℝ(x₀) = - f(a/b) / (α - a/b).
    rw [polynomial.deriv, hDf, <-hfℝ] at hx0r,
    rw [f_eval_on_ℝ] at α_root, rw [α_root, hfℝ] at hx0r, simp only [zero_sub] at hx0r,
    have Df_x0_nonzero : Df_ℝ.eval x0 ≠ 0,                                        -- So Df_ℝ(x₀) is not zero. (a/b is not a root)
    {
      rw hx0r, intro rid, rw [neg_div, neg_eq_zero, div_eq_zero_iff] at rid, cases rid,
      rw [<-roots_def, polynomial.mem_roots, polynomial.is_root] at hab2, exact hab2 rid,
      exact hfℝ_nonzero, linarith,
    },

    have H2 : abs(α - a/b) = abs((f_ℝ.eval (a/b:ℝ)) / (Df_ℝ.eval x0)),          -- So |α - a/b| = |f(a/b)/Df_ℝ(x₀)|
    {
      norm_num [hx0r],
      rw [neg_div, div_neg, abs_neg, div_div_cancel'],
      rw [<-roots_def] at hab2, by_contra absurd, simp only [not_not] at absurd,
      have H := polynomial.mem_roots _, rw polynomial.is_root at H,
      replace H := H.2 absurd, exact hab2 H,
      exact hfℝ_nonzero,
    },

    have ineq' : polynomial.eval (a/b:ℝ) (polynomial.map ℤembℝ f) ≠ 0,
    {
      rw <-roots_def at hab2, intro rid, rw [hfℝ, <-polynomial.is_root, <-polynomial.mem_roots] at rid,
      exact hab2 rid, exact hfℝ_nonzero,
    },

    have ineq : abs (α - a/b) ≥ 1/(M*b^(f.nat_degree)),                       -- By previous theorem |f(a/b)| ≥ 1/bⁿ and by definition                                                                             -- |Df_ℝ(x₀)| ≤ M. [M is maximum of x ↦ abs(Df_ℝ x) on (α-1,α+1)
    { rw [H2, abs_div],                                                           -- and x₀ ∈ (α - 1, α + 1)]
      have ineq := abs_f_at_p_div_q_ge_1_div_q_pow_n f f_deg a b hb.1 ineq',      -- So |α - a/b| ≥ 1/(M*bⁿ) where n is degree of f
      rw [<-hfℝ],
      have ineq2 : abs (polynomial.eval x0 Df_ℝ) ≤ M,
      {
        have H := hM x0 _, exact H,
        have h2 := @set.Ioo_subset_Icc_self ℝ _ (α-1) (α+1),
        have h3 := (@set.Ioo_subset_Ioo_iff ℝ _ _ (α-1) _ (α+1) _ hab3).2 _,
        have h4 : set.Ioo (↑a / ↑b) α ⊆ set.Icc (α-1) (α+1), exact set.subset.trans h3 h2,
        exact set.mem_of_subset_of_mem h4 hx0.1, split,
        rw set.mem_Icc at hab0, exact hab0.1, linarith,
      },

      have ineq3 := a_ge_b_a_div_c_ge_b_div_c _ _ (abs (polynomial.eval x0 Df_ℝ)) ineq _ _,
      suffices : 1 / (b:ℝ) ^ f.nat_degree / abs (polynomial.eval x0 Df_ℝ) ≥ 1 / (M * ↑b ^ f.nat_degree),
        linarith,
      rw [div_div] at ineq3,
      have ineq4 : 1 / ((b:ℝ) ^ f.nat_degree * abs (polynomial.eval x0 Df_ℝ)) ≥ 1 / (M * ↑b ^ f.nat_degree),
      {
        rw [ge_iff_le, one_div_le_one_div], conv_rhs {rw mul_comm},
        have ineq := ((@mul_le_mul_left ℝ _ (abs (polynomial.eval x0 Df_ℝ)) M (↑b ^ f.nat_degree)) _).2 ineq2, exact ineq,
        replace ineq := pow_pos hb.1 f.nat_degree, norm_cast, exact ineq, have ineq' : (b:ℝ) ^ f.nat_degree > 0, norm_cast,
        exact pow_pos hb.1 f.nat_degree, exact (mul_pos M_pos ineq'),
        apply mul_pos, norm_cast, exact pow_pos hb.1 f.nat_degree, rw abs_pos, exact Df_x0_nonzero,
      },
      rw div_div, exact ineq4, have ineq5 := @div_nonneg ℝ _ 1 (↑b ^ f.nat_degree) _ _, exact ineq5, norm_cast,
      exact bot_le, norm_cast, refine pow_nonneg (le_of_lt hb.1) f.nat_degree, rw [abs_pos], exact Df_x0_nonzero,
    },
    have ineq2 : 1/(M*b^(f.nat_degree)) > A / (b^f.nat_degree),                   -- Also 1/(M*bⁿ) > A/bⁿ since A < B ≤ 1/M
    {
      have ineq : A < B, rw [<-hA], exact @half_lt_self ℝ _ B B_pos,
      have ineq2 : B ≤ 1/M, rw [<-hB], have H := finset.min'_le distances' (1/M) _, exact H,
      rw [<-hdistances', finset.mem_insert], left, refl,
      have ineq3 : A < 1/M, linarith,
      rw [<-div_div], have ineq' := (@div_lt_div_right ℝ _ A (1/M) (↑b ^ f.nat_degree) _).2 ineq3,
      rw <-gt_iff_lt at ineq', exact ineq', norm_cast, exact pow_pos hb.1 f.nat_degree,
    },
    have ineq3 : abs (α - a / b) > A / b ^ f.nat_degree := by linarith,           -- So |α - a/b| > A/bⁿ
    have ineq4 : abs (α - a / b) > abs (α - a / b) := by linarith, linarith,      -- But we assumed |α - a/b| ≤ A/bⁿ. This is the desired contradiction

    exact polynomial.continuous_on _,                -- Since we used mean value theorem, we need to show continuity and differentiablity of x ↦ f(x),
    exact polynomial.differentiable_on _,            -- these are built in.
  },
  /- The other case is similar, In fact I copied and pasted the above proof and exchanged positions of α and a/b. Then it worked. -/
  {
    have H := exists_deriv_eq_slope (λ x, f_ℝ.eval x) hab3 _ _,
    choose x0 hx0 using H,
    have hx0r := hx0.2,
    rw [polynomial.deriv, hDf, <-hfℝ] at hx0r,
    rw [f_eval_on_ℝ] at α_root, rw [α_root, hfℝ] at hx0r, simp only [sub_zero] at hx0r,
    have Df_x0_nonzero : Df_ℝ.eval x0 ≠ 0,
    {
      rw hx0r, intro rid, rw [div_eq_zero_iff] at rid,
      rw [<-roots_def, polynomial.mem_roots, polynomial.is_root] at hab2, cases rid, exact hab2 rid, linarith,
      exact hfℝ_nonzero,
    },

    have H2 : abs(α - a/b) = abs((f_ℝ.eval (a/b:ℝ)) / (Df_ℝ.eval x0)),
    {
      norm_num [hx0r],
      rw [div_div_cancel'], have : ↑a / ↑b - α = - (α - ↑a / ↑b), linarith, rw [this, abs_neg],
      by_contra absurd, simp only [not_not] at absurd,
      have H := polynomial.mem_roots _, rw polynomial.is_root at H,
      replace H := H.2 absurd, rw roots_def at H, exact hab2 H,
      exact hfℝ_nonzero,
    },

    have ineq' : polynomial.eval (a/b:ℝ) (polynomial.map ℤembℝ f) ≠ 0,
    {
      rw <-roots_def at hab2, intro rid, rw [hfℝ, <-polynomial.is_root, <-polynomial.mem_roots] at rid,
      exact hab2 rid, exact hfℝ_nonzero,
    },

    have ineq : abs (α - a/b) ≥ 1/(M*b^(f.nat_degree)),
    {
      rw [H2, abs_div],
      have ineq := abs_f_at_p_div_q_ge_1_div_q_pow_n f f_deg a b hb.1 ineq',
      rw [<-hfℝ],
      have ineq2 : abs (polynomial.eval x0 Df_ℝ) ≤ M,
      {
        have H := hM x0 _, exact H,
        have h2 := @set.Ioo_subset_Icc_self ℝ _ (α-1) (α+1),
        have h3 := (@set.Ioo_subset_Ioo_iff ℝ _ _ (α-1) _ (α+1) _ hab3).2 _,
        have h4 : set.Ioo α (↑a / ↑b) ⊆ set.Icc (α-1) (α+1), exact set.subset.trans h3 h2,
        exact set.mem_of_subset_of_mem h4 hx0.1, split,
        rw set.mem_Icc at hab0, linarith,
        exact (set.mem_Icc.1 hab0).2,
      },

      have ineq3 := a_ge_b_a_div_c_ge_b_div_c _ _ (abs (polynomial.eval x0 Df_ℝ)) ineq _ _,
      suffices : 1 / ↑b ^ f.nat_degree / abs (polynomial.eval x0 Df_ℝ) ≥ 1 / (M * ↑b ^ f.nat_degree),
        linarith,
      rw [div_div] at ineq3,
      have ineq4 : 1 / ((b:ℝ) ^ f.nat_degree * abs (polynomial.eval x0 Df_ℝ)) ≥ 1 / (M * ↑b ^ f.nat_degree),
      {
        rw [ge_iff_le, one_div_le_one_div], conv_rhs {rw mul_comm},
        have ineq := ((@mul_le_mul_left ℝ _ (abs (polynomial.eval x0 Df_ℝ)) M (↑b ^ f.nat_degree)) _).2 ineq2, exact ineq,
        replace ineq := pow_pos hb.1 f.nat_degree, norm_cast, exact ineq, have ineq' : (b:ℝ) ^ f.nat_degree > 0, norm_cast,
        exact pow_pos hb.1 f.nat_degree, exact (mul_pos M_pos ineq'),
        apply mul_pos, norm_cast, exact pow_pos hb.1 f.nat_degree, rw abs_pos, exact Df_x0_nonzero,
      },
      rw div_div, exact ineq4, have ineq5 := @div_nonneg ℝ _ 1 (↑b ^ f.nat_degree) _ _, exact ineq5, norm_cast,
      exact bot_le, norm_cast, refine pow_nonneg (le_of_lt hb.1) f.nat_degree, rw [abs_pos], exact Df_x0_nonzero,
    },

    have ineq2 : 1/(M*b^(f.nat_degree)) > A / (b^f.nat_degree),
    {
      have ineq : A < B, rw [<-hA], exact @half_lt_self ℝ _ B B_pos,
      have ineq2 : B ≤ 1/M, rw [<-hB], have H := finset.min'_le distances' (1/M) _, exact H,
      rw [<-hdistances', finset.mem_insert], left, refl,
      have ineq3 : A < 1/M, linarith,
      rw [<-div_div], have ineq' := (@div_lt_div_right ℝ _ A (1/M) (↑b ^ f.nat_degree) _).2 ineq3,
      rw <-gt_iff_lt at ineq', exact ineq', norm_cast, exact pow_pos hb.1 f.nat_degree,
    },
    have ineq3 : abs (α - a / b) > A / b ^ f.nat_degree := by linarith,
    have ineq4 : abs (α - a / b) > abs (α - a / b) := by linarith, linarith,

    exact polynomial.continuous_on _,
    exact polynomial.differentiable_on _,
  },
end

/--
We then prove that all liouville numbers cannot be rational. Hence we can apply the above lemma to any liouville number and show its
transcendence.
-/

lemma liouville_numbers_irrational: ∀ (x : real), (liouville_number x) -> irrational' x :=
begin
  intros x liouville_x a b hb rid, replace rid : x = ↑a / ↑b, linarith,                  -- Suppose x is a rational Liouville number: say x = a/b.
  -- rw liouville_number at liouville_x,
  generalize hn : b.nat_abs + 1 = n,                                              -- Let n = |b| + 1. Then 2^(n-1) > b
  have b_ineq : 2 ^ (n-1) > b,
  {
    rw <-hn, simp only [nat.add_succ_sub_one, add_zero, gt_iff_lt],
    have triv : b = b.nat_abs, rw <-int.abs_eq_nat_abs, rw abs_of_pos, assumption,rw triv, simp,
    have H := @nat.lt_pow_self 2 _ b.nat_abs,  norm_cast, exact H, exact lt_add_one 1,
  },
  choose p hp using liouville_x n,                                                       -- Then there is a rational number p/q where q > 1
  choose q hq using hp, rw rid at hq,                                             -- such that 0 < |x- p/q| < 1/qⁿ
  have q_pos : q > 0 := by linarith,                                                   -- i.e 0 < |(aq - bp)/bq| < 1/qⁿ
  rw div_sub_div at hq,
  rw abs_div at hq,

  by_cases (abs ((a:ℝ) * (q:ℝ) - (b:ℝ) * (p:ℝ)) = 0),                             -- Then aq ≠ bp
  {
    rw h at hq, simp only [one_div, gt_iff_lt, euclidean_domain.zero_div, inv_pos] at hq, have hq1 := hq.1, have hq2 := hq.2, have hq21 := hq2.1, have hq22 := hq2.2, linarith,
  },
  {
    have ineq2: (abs (a * q - b * p)) ≠ 0,
      by_contra rid, simp only [abs_eq_zero, not_not] at rid, norm_cast at h,
      simp only [abs_eq_zero] at h, exact h rid,
    have ineq2':= abs_pos.2 ineq2, rw [abs_abs] at ineq2',
    replace ineq2' : 1 ≤ abs (a * q - b * p), linarith,
    have ineq3 : 1 ≤ @abs ℝ _ (a * q - b * p), norm_cast, exact ineq2',           -- Then |aq - bp| ≠ 0, then |aq-bp| ≥ 1

    have eq : abs (↑b * ↑q) = (b:ℝ)*(q:ℝ), rw abs_of_pos, have eq' := mul_pos hb q_pos, norm_cast, exact eq',
    rw eq at hq,
    have ineq4 : 1 / (b * q : ℝ) ≤ (@abs ℝ _ (a * q - b * p)) / (b * q),          -- So |(aq - bp)/bq| = |aq - bp|/(bq) ≥ 1/(bq)
    {
      rw div_le_div_iff, simp only [one_mul], have H := (@le_mul_iff_one_le_left ℝ _ _ (b * q) _).2 ineq3, exact H,
      norm_cast, have eq' := mul_pos hb q_pos, exact eq', norm_cast, have eq' := mul_pos hb q_pos, exact eq', norm_cast, have eq' := mul_pos hb q_pos, exact eq',
    },
    have b_ineq' := @mul_lt_mul ℤ _ b q (2^(n-1)) q b_ineq _ _ _,                 -- But b < 2^(n-1) < q^(n-1)
    have b_ineq'' : (b * q : ℝ) < (2:ℝ) ^ (n-1) * (q : ℝ), norm_cast, simp only [int.coe_nat_zero, int.coe_nat_pow, int.coe_nat_succ, zero_add], exact b_ineq',

    have q_ineq1 : q ≥ 2, linarith,
    have q_ineq2 := @pow_le_pow_of_le_left ℤ _ 2 q _ _ (n-1),
    have q_ineq3 : 2 ^ (n - 1) * q ≤ q ^ (n - 1) * q, rw (mul_le_mul_right _), assumption, linarith,
    have triv : q ^ (n - 1) * q = q ^ n, rw <-hn, simp only [nat.add_succ_sub_one, add_zero], rw pow_add, simp only [pow_one], rw triv at q_ineq3,

    have b_ineq2 : b * q < q ^ n, linarith,                                       -- So bq < qⁿ
    have rid' := (@one_div_lt_one_div ℝ _ (q^n) (b*q) _ _).2 _,
    have rid'' : @abs ℝ _ (a * q - b * p) / (b * q : ℝ) > 1 / q ^ n, linarith,    -- Then |(aq - bp)/bq| > 1/qⁿ
    have hq1 := hq.1, have hq2 := hq.2, have hq21 := hq2.1, have hq22 := hq2.2,   -- This is the contradiction we are seeking for:
    linarith,                                                                     -- 1/qⁿ >  |(aq - bp)/bq| > 1/qⁿ

    /- other less important steps. We manipulated inequalities using multiplication and division, so we need to prove various things
       to be non-negative or postive. The proves are all more or less trivial. -/
    apply pow_pos, norm_cast, exact q_pos, norm_cast, apply mul_pos,
    exact hb, exact q_pos,
    norm_cast, exact b_ineq2,
    norm_cast, exact bot_le,
    exact q_ineq1,
    exact le_refl q,
    exact q_pos,
    apply pow_nonneg, norm_cast, exact bot_le,
  },
  norm_cast, linarith, norm_cast, linarith,
end

theorem liouville_numbers_transcendental : ∀ x : ℝ, liouville_number x -> transcendental x :=
begin
  intros x liouville_x,                                                                  -- Let $x$ be any Liouville's number,
  have irr_x : irrational' x, exact liouville_numbers_irrational x liouville_x,           -- Then by previous theorem, it is irrational.
  intros rid, rw is_algebraic at rid,                                             -- assume x is algebraic over ℤ,
  choose f hf using rid,                                                          -- Let f be an integer polynomial who admitts x as a root.
  have f_deg : f.nat_degree > 1, {                                                -- Then f must have degree > 1, otherwise f have degree 0 or 1.                                                                         --
    by_contra rid, simp only [not_lt] at rid, replace rid := lt_or_eq_of_le rid, cases rid,
    {                                                                             -- If f has degree 0 then f ∈ ℤ[T] = c for some c ∈ ℤ. So x is an irrational integer.
      replace rid : f.nat_degree = 0, linarith, rw polynomial.nat_degree_eq_zero_iff_degree_le_zero at rid, rw polynomial.degree_le_zero_iff at rid,
      rw rid at hf, simp only [polynomial.aeval_C] at hf, have hf1 := hf.1, have hf2 := hf.2, simp only [ring_hom.eq_int_cast, ne.def] at hf1,
      simp only [int.cast_eq_zero, ring_hom.eq_int_cast] at hf2, rw hf2 at hf1, norm_cast at hf1,
    },
    {                                                                             -- If f has degree 1, then f = aT + b
      have f_eq : f = polynomial.C (f.coeff 0) + (polynomial.C (f.coeff 1)) * polynomial.X,
      {
        ext,
        rw [polynomial.coeff_add, polynomial.coeff_C, polynomial.coeff_C_mul, polynomial.coeff_X], split_ifs, linarith,
        simp only [h, add_zero, mul_zero], simp only [h_1, mul_one, zero_add],
        replace h : n > 0, exact nat.pos_of_ne_zero h, replace h : n ≥ 1, exact nat.succ_le_iff.mpr h,
        replace h : 1 < n ∨ 1 = n, exact lt_or_eq_of_le h, cases h, rw polynomial.coeff_eq_zero_of_nat_degree_lt, simp only [add_zero, mul_zero],
        rwa rid, exfalso, exact h_1 h,
      },

      rw f_eq at hf, simp only [alg_hom.map_add, polynomial.aeval_X, ne.def, polynomial.aeval_C, alg_hom.map_mul] at hf, rw irrational' at irr_x,
      by_cases ((f.coeff 1) > 0),
      {
        replace irr_x := irr_x (-(f.coeff 0)) (f.coeff 1) h, simp only [ne.def, int.cast_neg] at irr_x, rw neg_div at irr_x, rw sub_neg_eq_add at irr_x, rw add_comm at irr_x,
        suffices : ↑(f.coeff 0) / ↑(f.coeff 1) + x = 0, exact irr_x this,
        rw add_eq_zero_iff_eq_neg, rw div_eq_iff, have triv : -x * ↑(f.coeff 1) = - (x * (f.coeff 1)), exact norm_num.mul_neg_pos x ↑(polynomial.coeff f 1) (x * ↑(polynomial.coeff f 1)) rfl,
        rw triv, rw <-add_eq_zero_iff_eq_neg, rw mul_comm, have hf2 := hf.2, simp [polynomial.aeval_def] at hf2, exact hf2,
        norm_cast, linarith,
      },
      {
        simp only [not_lt] at h, replace h := lt_or_eq_of_le h, cases h,
        {

         replace irr_x := irr_x (f.coeff 0) (-(f.coeff 1)) _, simp only [ne.def, int.cast_neg] at irr_x, rw div_neg at irr_x, rw sub_neg_eq_add at irr_x, rw add_comm at irr_x,
          suffices suff : ↑(f.coeff 0) / ↑(f.coeff 1) + x = 0, exact irr_x suff,
          rw add_eq_zero_iff_eq_neg, rw div_eq_iff, have triv : -x * ↑(f.coeff 1) = - (x * (f.coeff 1)), exact norm_num.mul_neg_pos x ↑(polynomial.coeff f 1) (x * ↑(polynomial.coeff f 1)) rfl,
          rw triv, rw <-add_eq_zero_iff_eq_neg, rw mul_comm, exact hf.2, norm_cast, linarith, exact neg_pos.mpr h,
        },
        rw <-rid at h,
        rw <-polynomial.leading_coeff at h,
        rw polynomial.leading_coeff_eq_zero at h, rw h at rid, simp only [polynomial.nat_degree_zero, zero_ne_one] at rid, exact rid,
      }
    },
  },
  have about_root : f_eval_on_ℝ f x = 0,
  {
    rw f_eval_on_ℝ, have H := hf.2, rw [polynomial.aeval_def] at H,
    rw [polynomial.eval, polynomial.eval₂_map], rw [polynomial.eval₂, polynomial.sum] at H ⊢,
    rw [<-H, sum_eq],
    intros m hm, simp only [ring_hom.eq_int_cast, id.def],
  },

  choose A hA using about_irrational_root x irr_x f f_deg about_root,             -- So we can apply the lemma about irrational root:
  have A_pos := hA.1,                                                             -- There is an A > 0 such that for any integers a b with b > 0
  have exists_r := pow_big_enough A,                           -- |x - a/b| > A/bⁿ where n is the degree of f.
  choose r hr using exists_r,                                                     -- Let r ∈ ℕ such tht 1/A ≤ 2^r (equivalently 1/2^r ≤ A)
  have hr' : 1/(2^r) ≤ A, rw [div_le_iff, mul_comm, <-div_le_iff], exact hr, exact A_pos, apply (pow_pos _), exact two_pos,
  generalize hm : r + f.nat_degree = m,                                           -- Let m := r + n
  replace liouville_x := liouville_x m,
  choose a ha using liouville_x,                                                         -- Since x is Liouville, there are integers a and b with b > 1
  choose b hb using ha,                                                           -- such that 0 < |x - a/b| < 1/bᵐ = 1/bⁿ * 1/b^r.

  have ineq := hb.2.2, rw <-hm at ineq, rw pow_add at ineq,
  have eq1 := div_mul_eq_div_mul_one_div 1 ((b:ℝ) ^ r) ((b:ℝ)^f.nat_degree), rw eq1 at ineq,
  have ineq2 : 1/((b:ℝ)^r) ≤ 1/((2:ℝ)^r),                                         -- But 1/b^r ≤ 1/2^r ≤ A. So 0 < |x - a/b| < A/bⁿ.
  {                                                                               -- This is the contradiction we seek by the choice of A.
    apply (@one_div_le_one_div ℝ _ ((b:ℝ)^r) ((2:ℝ)^r) _ _).2,
    suffices suff : 2 ^ r ≤ b^r,  norm_cast, norm_num, exact suff,
    have ineq' := @pow_le_pow_of_le_left ℝ _ 2 b _ _ r, norm_cast at ineq', norm_num at ineq', exact ineq',
    linarith, norm_cast, linarith, norm_cast, apply pow_pos, linarith, apply pow_pos, linarith,
  },
  have ineq3 : 1 / ↑b ^ r ≤ A, exact le_trans ineq2 hr',
  have ineq4 : 1 / ↑b ^ r * (1 / ↑b ^ f.nat_degree) ≤ A * (1 / ↑b ^ f.nat_degree),
  {
    have H := (@mul_le_mul_right ℝ _ (1 / ↑b ^ r) A (1 / ↑b ^ f.nat_degree) _).2 ineq3, exact H,
    apply div_pos, linarith, norm_cast, apply pow_pos, linarith,
  },
  conv_rhs at ineq4 {rw <-mul_div_assoc, rw mul_one},
  have ineq5 :  abs (x - a / b:ℝ) < A / ↑b ^ f.nat_degree, linarith,
  have rid := hA.2 a b _, linarith, linarith,
end


/-- ## define an example of Liouville number Σᵢ 1/2^(i!)
- In this section we explicitly define $\alpha := \sum_{i=0}^\infty ¼{1}{10^{i!}}$;
- We use comparison test to prove the convergence of α;
- Then we prove that α is indeed a Liouville number;
- From previous theorem we easily conclude α is transcendental.

function n ↦ 1/10^n!
-/
def ten_pow_n_fact_inverse (n : ℕ) : ℝ := ((1:ℝ)/(10:ℝ))^n.factorial
/--
function n ↦ 1/10^n
-/
def ten_pow_n_inverse (n : ℕ) : ℝ := ((1:ℝ)/(10:ℝ))^n

-- 1/10^{n!} is nonnegative.
lemma ten_pow_n_fact_inverse_ge_0 (n : nat) : 0 ≤ ten_pow_n_fact_inverse n :=
begin
    unfold ten_pow_n_fact_inverse,
    simp only [one_div, inv_nonneg, ge_iff_le, inv_pow],
    have h := le_of_lt (@pow_pos _ _ (10:real) _ n.factorial),
    norm_cast at h ⊢, exact h, norm_num,
end

-- n ≤ n!
lemma n_le_n_fact : ∀ n : nat, n ≤ n.factorial
| 0       := by norm_num
| 1       := by norm_num
| (n+2)   := begin
    have H := n_le_n_fact n.succ,
    conv_rhs {rw (nat.factorial_succ n.succ)},
    have ineq1 : n.succ.succ * n.succ ≤ n.succ.succ * n.succ.factorial,
    {exact nat.mul_le_mul_left (nat.succ (nat.succ n)) (n_le_n_fact (nat.succ n))},
    suffices ineq2 : n.succ.succ ≤ n.succ.succ * n.succ, {exact nat.le_trans ineq2 ineq1},
    have H' : ∀ m : nat, m.succ.succ ≤ m.succ.succ * m.succ,
    {
        intro m, induction m with m hm,
        norm_num, simp only [nat.mul_succ, zero_le, le_add_iff_nonneg_left] at hm ⊢,
    },
    exact H' n,
end

lemma ten_pow_n_fact_inverse_le_ten_pow_n_inverse (n : nat) : ten_pow_n_fact_inverse n ≤ ten_pow_n_inverse n :=
begin
  simp only [ten_pow_n_fact_inverse, ten_pow_n_inverse, one_div, inv_pow],
  rw [inv_le], simp only [inv_inv], apply pow_le_pow, linarith, apply n_le_n_fact, apply pow_pos,
  linarith, rw inv_pos, apply pow_pos, linarith,
end

-- Σᵢ 1/10ⁱ exists because it is a geometric sequence with 1/10 < 1. The sum equals 10/9
theorem summable_ten_pow_n_inverse : summable ten_pow_n_inverse :=
begin
  have H := @summable_geometric_of_abs_lt_1 (1/10:ℝ) _,
  have triv : ten_pow_n_inverse = (λ (n : ℕ), (1 / 10) ^ n) := rfl, rw triv, exact H,
  rw abs_of_pos, linarith, linarith,
end

/--
∑ i, 1/10^i
-/
def β : ℝ := classical.some summable_ten_pow_n_inverse

theorem β_eq :  (∑' (b : ℕ), ten_pow_n_inverse b) = (10 / 9:ℝ) :=
begin
  have eq0 := @tsum_geometric_of_abs_lt_1 (1/10) _,
  have eq1 : (∑' (n : ℕ), (1 / 10:ℝ) ^ n) = (∑' (b : ℕ), ten_pow_n_inverse b),
    apply congr_arg, ext, rw ten_pow_n_inverse,
  rw eq1 at eq0, rw eq0, norm_num, rw abs_of_pos, linarith, linarith,
end

-- Hence Σᵢ 1/10^i! exists by comparison test, call it α

theorem summable_ten_pow_n_fact_inverse : summable ten_pow_n_fact_inverse :=
begin
  exact @summable_of_nonneg_of_le _ ten_pow_n_inverse ten_pow_n_fact_inverse ten_pow_n_fact_inverse_ge_0 ten_pow_n_fact_inverse_le_ten_pow_n_inverse summable_ten_pow_n_inverse,
end

/--
 define α to be Σᵢ 1/10^i!
-/
def α := ∑' n, ten_pow_n_fact_inverse n


-- first k term
-- `α_k k` is the kth partial sum $\sum_{i=0}^k \frac{1}{10^{i!}}$.
notation `α_k` k := ∑ ii in finset.range (k+1), ten_pow_n_fact_inverse ii

-- `α_k k` is rational and can be written as $\frac{p}{10^{k!}}$ for some p ∈ ℕ.
theorem α_k_rat (k:ℕ) : ∃ (p : ℕ), (α_k k) = (p:ℝ) / ((10:ℝ) ^ k.factorial) :=
begin
  induction k with k IH,
  simp only [ten_pow_n_fact_inverse, pow_one, finset.sum_singleton, finset.range_one,
    nat.factorial_zero],
  use 1, norm_cast,

  choose pk hk using IH,                                                                 -- Then the (k+1)th partial sum = p/10^{k!} + 10^{(k+1)!}
  generalize hm : 10^((k+1).factorial - k.factorial) = m,
  have eqm : 10^k.factorial * m = 10^(k+1).factorial,                                       -- If we set m = 10^{(k+1)!-k!}, then pm+1 works. This is algebra.
  { rw [<-hm, <-pow_add], rw add_tsub_cancel_of_le, simp only [nat.factorial_succ],
    rw le_mul_iff_one_le_left, exact inf_eq_left.mp rfl, exact nat.factorial_pos k },
  have eqm' : (10:ℝ)^k.factorial * m = (10:ℝ)^(k+1).factorial,
  {norm_cast, exact eqm},
  generalize hp : pk * m + 1 = p,
  use p, rw finset.sum_range_succ, rw hk,

  rw [ten_pow_n_fact_inverse, div_pow], rw one_pow, rw nat.succ_eq_add_one,
  rw <-eqm', rw <-hp,
  conv_rhs
  { simp only [one_div, nat.cast_add, nat.cast_one, nat.cast_mul],
    rw <-div_add_div_same, simp only [one_div]},
  rw mul_div_mul_right, simp only [one_div], rw [←hm],
  simp only [nat.cast_bit0, nat.cast_bit1, nat.factorial_succ, ne.def, nat.cast_one, nat.cast_pow],
  apply pow_ne_zero,
  norm_num,
end

-- rest term `α_k_rest k` is $\sum_{i=0}^\infty \frac{1}{(i+k+1)!}=\sum_{i=k+1}^\infty \frac{1}{i!}$
notation `α_k_rest` k := ∑' ii, ten_pow_n_fact_inverse (ii + (k+1))

private lemma sum_ge_term (f : ℕ -> ℝ) (hf : ∀ x:ℕ, f x > 0) (hf' : summable f): (∑' i, f i)  ≥ f 0 :=
begin
  rw <-(@tsum_ite_eq ℝ ℕ _ _ _ 0 _ (f 0)),
  generalize hfunc : (λ b' : ℕ, ite (b' = 0) (f 0) 0) = fn,
  simp only [ge_iff_le],
  apply tsum_le_tsum _ _ hf',
  { intro n,
    rw ←hfunc, dsimp only, split_ifs,
    { rw h, },
    {exact le_of_lt (hf n)} },
  dsimp only,
  rw ←hfunc,
  exact (has_sum_ite_eq 0 (f 0)).summable,
end

-- Since each summand in `α_k_rest k` is positive, the sum is positive.
theorem α_k_rest_pos (k : ℕ) : 0 < (α_k_rest k) :=
begin
  generalize hfunc : (λ n:ℕ, ten_pow_n_fact_inverse (n + (k + 1))) = fn,
  have ineq2 : fn 0 > 0,
  { rw <-hfunc, simp only [gt_iff_lt, zero_add], rw ten_pow_n_fact_inverse, rw div_pow,
    apply div_pos,
    {simp only [one_zpow, ne.def, triv, not_false_iff, one_ne_zero], exact zero_lt_one},
    {apply pow_pos, linarith} },
  refine gt_of_ge_of_gt (sum_ge_term fn _ _) ineq2,

  { intro n, rw <-hfunc, simp only [gt_iff_lt], rw ten_pow_n_fact_inverse, rw div_pow, apply div_pos,
    {simp only [one_zpow, ne.def, triv, not_false_iff, one_ne_zero], exact zero_lt_one},
    {apply pow_pos, linarith}},
  rw <-hfunc,
  exact (@summable_nat_add_iff ℝ _ _ _ ten_pow_n_fact_inverse (k+1)).2 summable_ten_pow_n_fact_inverse,
end

-- We also have for any k ∈ ℕ, α = (α_k k) + (α_k_rest k)
theorem α_truncate_wd (k : ℕ) : α = (α_k k) + α_k_rest k :=
begin
  rw α,
  have eq1 := @sum_add_tsum_nat_add ℝ _ _ _ _ ten_pow_n_fact_inverse (k+1) _,
  rw eq1, exact summable_ten_pow_n_fact_inverse,
end

private lemma ten_pow_n_fact_gt_one (n : ℕ) : 10^(n.factorial) > 1 :=
begin
  induction n with n h,
  simp only [gt_iff_lt, zero_le, one_le_bit1, nat.one_lt_bit0_iff, nat.factorial_zero, pow_one],
  simp only [gt_iff_lt, nat.factorial_succ],
  rw pow_mul,
  have ineq := nat.factorial_pos n,
  refine gt_of_gt_of_ge _ ineq,
  refine @nat.lt_pow_self (10 ^ n.succ) _ n.factorial,
  exact nat.one_lt_pow' n 8,
end

private lemma nat.fact_succ' (n : ℕ) : n.succ.factorial = n.factorial * n.succ :=
begin
  rw [nat.factorial_succ, nat.succ_eq_add_one, mul_comm],
end

-- Here we prove for any n ∈ ℕ, $\sum_{i} \left(\frac{1}{10^i}\times\frac{1}{10^{(n+1)!}}\right) \le \frac{2}{10^{(n+1)!}}$
private lemma lemma_ineq3 (n:ℕ) : (∑' (i:ℕ), (1/10:ℝ)^i * (1/10:ℝ)^(n+1).factorial)
  ≤ (2/10^n.succ.factorial:ℝ) :=
begin
  rw tsum_mul_right,                                                              -- We factor out 1/10^{(n+1)!}
  have eq1 := β_eq, unfold ten_pow_n_inverse at eq1, rw eq1, rw div_pow, rw one_pow, field_simp,
  rw div_le_div_iff,
  { norm_cast,
    conv_rhs {rw <-mul_assoc},                     -- and use that what left is a geometric sum = 10/9
    norm_cast,
    have triv : 2 * 9 = 18 := by norm_num, rw triv,
    rw mul_le_mul_right (pow_pos _ _);
    norm_num },
  { apply mul_pos,
    {norm_num},
    {apply pow_pos, norm_num}},
  {apply pow_pos, norm_num},
end

-- We use induction to prove 2 < 10 ^ n!
private lemma aux_ineq (n:ℕ) : 2 < 10 ^ n.factorial :=
begin
  induction n with n ih,
  {simp only [nat.succ_pos', one_lt_bit1, bit0_lt_bit0, nat.factorial_zero, pow_one]},
  rw [nat.factorial_succ, pow_mul],
  have ineq : 10 ^ n.factorial ≤ (10 ^ n.succ) ^ n.factorial,
  { rw nat.pow_le_iff_le_left,
    { have h : ∀ m : ℕ, 10 ≤ 10 ^ m.succ,
      { intro m,
        induction m with m hm,
        { simp only [pow_one] },
        { rw pow_succ, linarith } },
      exact h n },
    linarith [nat.factorial_pos n] },
  linarith,
end

-- $\frac{2}{10^{(n+1)!}} < \frac{1}{(10^{n!})^n}$
private lemma lemma_ineq4 (n:ℕ) :
  (2 / 10 ^ (n.factorial * n.succ):ℝ) < (1 / ((10:ℝ) ^ n.factorial) ^ n) :=
begin
  rw div_lt_div_iff,
  { rw one_mul, -- This is also algebra plus checking a lot of thing non-negative or positive.
    conv_rhs {rw nat.succ_eq_add_one, rw mul_add, rw pow_add, rw mul_one, rw pow_mul, rw mul_comm},
    apply mul_lt_mul,
    { norm_cast, exact aux_ineq n },
    {linarith},
    {apply pow_pos, apply pow_pos, linarith},
    {apply pow_nonneg, linarith} },
  {apply pow_pos, linarith},
  {apply pow_pos, apply pow_pos, linarith},
end

-- This is i + n! ≤ (i+n)!. Proved by induction on n.
private lemma ineq_i (i n : ℕ) : i + n.succ.factorial ≤ (i + n.succ).factorial :=
begin
  induction n with n hn,
  { simp only [add_zero, nat.factorial_succ, nat.factorial_one],
    rw <-nat.succ_eq_add_one,
    have h := (@nat.mul_le_mul_right 1 i.factorial i.succ) _,
    { rwa [one_mul, mul_comm] at h },
    { exact nat.factorial_pos i } },

  generalize hm : n.succ = m, rw hm at hn,
  have triv : i + m.succ = (m+i).succ, rw nat.add_succ, rw add_comm, rw triv,
  conv_rhs {rw nat.factorial_succ, },

  have ineq1 : (m + i + 1) * (i + m.factorial) ≤ (m + i + 1) * (m + i).factorial,
  {apply mul_le_mul, linarith, rwa add_comm m, linarith, linarith},
  suffices : i + m.succ.factorial ≤ (m + i + 1) * (i + m.factorial), exact le_trans this ineq1,
  rw mul_add,
  have ineq2 : (m + i + 1) * m.factorial ≤ (m + i + 1) * i + (m + i + 1) * m.factorial := nat.le_add_left _ _,
  suffices : i + m.succ.factorial ≤ (m + i + 1) * m.factorial, {exact le_trans this ineq2},
  replace triv :  (m + i + 1) = (m + 1 + i), ring, rw triv, rw add_mul,
  rw <-nat.factorial_succ, rw add_comm,
  apply add_le_add_left,
  replace triv := (@nat.mul_le_mul_right 1 m.factorial i) _,
  { simp only [one_mul] at triv, rwa mul_comm at triv },
  { exact nat.factorial_pos m },
end


-- With all the auxilary inequalies, we can now prove α is a Liouville number.
-- Then α is a Liouville number hence a transcendental number.
theorem liouville_α : liouville_number α :=
begin
  intro n,                                                                        -- We fix n ∈ ℕ.
  have lemma1 := α_k_rat n,                                                      -- we are going to prove 0 < |α - p/10^{n!}| < 1/10^{n! * n}
  have lemma2 := α_truncate_wd n,
  replace lemma2 : (α_k_rest n) = α - α_k n,
    exact eq_sub_of_add_eq' (eq.symm lemma2),                                            -- We know that the first n terms sums to p/10^{n!}
  choose p hp using lemma1,                                                       -- for some p ∈ ℕ.
  use p, use 10^(n.factorial),
  suffices :  0 < abs (α_k_rest n) ∧ abs (α_k_rest n) < 1/(10^ n.factorial)^n,
  {
    split,
    { norm_cast, exact ten_pow_n_fact_gt_one n },
    { rw [lemma2, hp] at this,
      norm_cast at this,
      tidy } },
                                                                              -- and that 10^{n!} > 1
  split,                                                                      -- We first prove that 0 < |α - p/10^{n!}| or equivlanetly α ≠ p/10^{n!}
  {                                                                           -- otherwise the rest term from i=n+1 to infinity sum to zero, but we proved it to be positive.
    rw abs_pos,
    exact (α_k_rest_pos n).ne', },
  {                                                                             -- next we prove |α - p/10^{n!}| < 1/10^{n! * n}
    rw [abs_of_pos (α_k_rest_pos n)],
    have ineq2 : (∑' (j : ℕ), ten_pow_n_fact_inverse (j + (n + 1)))
        ≤ (∑' (i:ℕ), (1/10:ℝ)^i * (1/10:ℝ)^(n+1).factorial),
    {                                                                           -- Since for all i ∈ ℕ, 1/10^{(i+n+1)!} ≤  1/10ⁱ * 1/10^{(n+1)!}
      apply tsum_le_tsum,                                                       -- [this is because of one of previous inequalities plus some inequality manipulation]
      { intro i, rw ten_pow_n_fact_inverse, field_simp,
        rw one_div_le_one_div,
        { rw <-pow_add,
          apply pow_le_pow,
          { linarith },
          {                                                                         -- we have the rest of term sums to a number ≤ $\sum_i^\infty \frac{1}{10^i}\times\frac{1}{10^{(n+1)!}}$
            rw <-nat.factorial_succ, rw <-nat.succ_eq_add_one,
            exact ineq_i _ _, } },
        {apply pow_pos, norm_num},
        {rw <-pow_add, apply pow_pos, norm_num} },
      { exact (@summable_nat_add_iff ℝ _ _ _ ten_pow_n_fact_inverse (n+1)).2
          summable_ten_pow_n_fact_inverse},
      {
        have s0 : summable (λ (b : ℕ), (1 / 10:ℝ) ^ b),
        {
          have triv : (λ (b : ℕ), (1 / 10:ℝ) ^ b) = ten_pow_n_inverse, ext, rw ten_pow_n_inverse, rw triv,
          exact summable_ten_pow_n_inverse,
        },
        apply (summable_mul_right_iff _).1 s0, have triv : (1 / 10:ℝ) ^ (n + 1).factorial > 0, apply pow_pos, linarith, linarith,
      }
    },                                                                          -- by previous inequlity $\sum_i^\infty \frac{1}{10^i}\times\frac{1}{10^{(n+1)!}} < \frac{2}{10^{(n+1)!}} \le \frac{1}{10^{n!\times n}}$
    have ineq3 : (∑' (i:ℕ), (1/10:ℝ)^i * (1/10:ℝ)^(n+1).factorial) ≤ (2/10^n.succ.factorial:ℝ)
      := lemma_ineq3 _,
    rw nat.fact_succ' at ineq3,                                                 -- This what we want. So α is Liouville
    have ineq4 : (2 / 10 ^ (n.factorial * n.succ):ℝ) < (1 / ((10:ℝ) ^ n.factorial) ^ n)
      := lemma_ineq4 _,
    have ineq5 : (∑' (n_1 : ℕ), ten_pow_n_fact_inverse (n_1 + (n + 1)))
      < (1 / ((10:ℝ) ^ n.factorial) ^ n),
    {
      apply @lt_of_le_of_lt ℝ _
        (∑' (n_1 : ℕ), ten_pow_n_fact_inverse (n_1 + (n + 1)))
        (∑' (i : ℕ), (1 / 10) ^ i * (1 / 10) ^ (n + 1).factorial)
        (1 / (10 ^ n.factorial) ^ n)
        ineq2,
      norm_cast at ineq2 ineq3 ineq4 ⊢, rw <-nat.succ_eq_add_one, rw nat.factorial_succ,
      rw [←mul_comm n.factorial],
      exact lt_of_le_of_lt ineq3 ineq4,
    },
    exact ineq5, },
end

-- Then our general theory about Liouville number in particular applies to α giving us α transcendental number
theorem transcendental_α : transcendental α := liouville_numbers_transcendental α liouville_α

-- #lint
