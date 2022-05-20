import analysis.special_functions.trigonometric.basic
import measure_theory.integral.interval_integral
import analysis.special_functions.integrals
import data.real.irrational

noncomputable theory

open interval_integral measure_theory.measure_space nat real set
open_locale nat

def I (n : ℕ) (θ : ℝ) : ℝ := ∫ x in -1..1, (1 - x ^ 2) ^ n * cos (x * θ)

variables {n : ℕ} {θ : ℝ}

lemma I_zero : I 0 θ * θ = 2 * sin θ :=
begin
  rw [mul_comm, I],
  simp [two_mul],
end

lemma recursion' (n : ℕ) :
  I (n + 1) θ * θ ^ 2 = - (2 * 2 * ((n + 1) * (0 ^ n * cos θ))) +
    2 * (n + 1) * (2 * n + 1) * I n θ - 4 * (n + 1) * n * I (n - 1) θ :=
begin
  let i := interval (-1 : ℝ) 1,
  rw I,
  let f : ℝ → ℝ := λ x, 1 - x ^ 2,
  let u₁ : ℝ → ℝ := λ x, f x ^ (n + 1),
  let u₁' : ℝ → ℝ := λ x, - (2 * (n + 1) * x * f x ^ n),
  let v₁ : ℝ → ℝ := λ x, sin (x * θ),
  let v₁' : ℝ → ℝ := λ x, cos (x * θ) * θ,
  let u₂ : ℝ → ℝ := λ x, x * (f x) ^ n,
  let u₂' : ℝ → ℝ := λ x, (f x) ^ n - 2 * n * x ^ 2 * (f x) ^ (n - 1),
  let v₂ : ℝ → ℝ := λ x, cos (x * θ),
  let v₂' : ℝ → ℝ := λ x, -sin (x * θ) * θ,
  have hfd : continuous f := continuous_const.sub (continuous_pow 2),
  have hu₁d : continuous u₁' := ((continuous_mul_left _).mul (hfd.pow _)).neg,
  have hv₁d : continuous v₁' := (continuous_cos.comp (continuous_mul_right _)).mul continuous_const,
  have hu₂d : continuous u₂' :=
    (hfd.pow _).sub ((continuous_const.mul (continuous_pow 2)).mul (hfd.pow _)),
  have hv₂d : continuous v₂' :=
    (continuous_sin.comp (continuous_mul_right _)).neg.mul continuous_const,
  have hu₁_eval_one : u₁ 1 = 0 := by { simp only [u₁, f], simp },
  have hu₁_eval_neg_one : u₁ (-1) = 0 := by { simp only [u₁, f], simp },
  have t : u₂ 1 * v₂ 1 - u₂ (-1) * v₂ (-1) = 2 * (0 ^ n * cos θ),
  { simp only [u₂, v₂, f, one_pow, sub_self, one_mul, neg_one_sq, neg_mul, cos_neg, sub_neg_eq_add],
    simp only [←two_mul] },
  have hf : ∀ x ∈ i, has_deriv_at f (- 2 * x) x,
  { intros x hx,
    convert (has_deriv_at_pow 2 x).const_sub 1,
    simp only [nat.cast_two, pow_one, neg_mul] },
  have hu₁ : ∀ x ∈ i, has_deriv_at u₁ (u₁' x) x,
  { intros x hx,
    convert (hf x hx).pow,
    simp only [nat.add_succ_sub_one, u₁', nat.cast_add_one],
    ring },
  have hv₁ : ∀ x ∈ i, has_deriv_at v₁ (v₁' x) x := λ x hx, (has_deriv_at_mul_const θ).sin,
  have hu₂ : ∀ x ∈ i, has_deriv_at u₂ (u₂' x) x,
  { intros x hx,
    convert has_deriv_at.mul (has_deriv_at_id' x) (hf x hx).pow,
    simp only [u₂'],
    ring },
  have hv₂ : ∀ x ∈ i, has_deriv_at v₂ (v₂' x) x := λ x hx, (has_deriv_at_mul_const θ).cos,
  convert_to (∫ (x : ℝ) in -1..1, u₁ x * v₁' x) * θ = _ using 1,
  { simp_rw [←integral_mul_const, sq θ, mul_assoc] },
  rw [integral_mul_deriv_eq_deriv_mul hu₁ hv₁ (hu₁d.interval_integrable _ _)
    (hv₁d.interval_integrable _ _), hu₁_eval_one, hu₁_eval_neg_one, zero_mul,
    zero_mul, sub_zero, zero_sub, ←integral_neg, ←integral_mul_const],
  convert_to ((-2 : ℝ) * (n + 1)) * ∫ (x : ℝ) in -1..1, (u₂ x * v₂' x) = _ using 1,
  { rw [←integral_const_mul],
    congr' with x,
    dsimp [u₁', v₁, u₂, v₂'],
    ring },
  rw [integral_mul_deriv_eq_deriv_mul hu₂ hv₂ (hu₂d.interval_integrable _ _)
    (hv₂d.interval_integrable _ _), mul_sub, t, neg_mul, neg_mul, neg_mul, sub_neg_eq_add],
  have : ∀ x, u₂' x = (2 * n + 1) * f x ^ n - 2 * n * f x ^ (n - 1),
  { intro x,
    cases n,
    { simp [u₂'] },
    simp only [u₂', pow_succ _ n, f, nat.succ_sub_one, cast_succ],
    ring },
  simp_rw [this, mul_sub],
  rw [mul_mul_mul_comm, integral_sub],
  { simp_rw [mul_left_comm (v₂ _), integral_const_mul, mul_comm (v₂ _)],
    rw [mul_sub, ←mul_assoc, ←mul_assoc, ←mul_assoc, ←mul_assoc, mul_mul_mul_comm, add_sub_assoc],
    congr' 3,
    rw ←mul_assoc,
    norm_num },
  all_goals {
    refine ((continuous_cos.comp (continuous_mul_right _)).mul _).interval_integrable _ _,
    exact continuous_const.mul (hfd.pow _) },
end

lemma recursion (n : ℕ) :
  I (n + 2) θ * θ ^ 2 = 2 * (n + 2) * (2 * n + 3) * I (n + 1) θ - 4 * (n + 2) * (n + 1) * I n θ :=
by { rw [recursion' (n + 1), nat.cast_add_one, zero_pow (nat.succ_pos _)], ring }

lemma I_one : I 1 θ * θ ^ 3 = 4 * sin θ - 4 * θ * cos θ :=
begin
  rw [pow_succ', ←mul_assoc, recursion' 0, nat.cast_zero, mul_zero, mul_zero, zero_mul,
    sub_zero, zero_add, mul_one, mul_one, add_mul, mul_assoc, mul_assoc, I_zero],
  ring
end

open polynomial

noncomputable def sin_poly : ∀ n : ℕ, polynomial ℤ
| 0 := C 2
| 1 := C 4
| (n+2) := ((2 : ℤ) * (2 * n + 3)) • sin_poly (n + 1) + monomial 2 (-4) * sin_poly n

noncomputable def cos_poly : ∀ n : ℕ, polynomial ℤ
| 0 := 0
| 1 := monomial 1 (-4)
| (n+2) := ((2 : ℤ) * (2 * n + 3)) • cos_poly (n + 1) + monomial 2 (-4) * cos_poly n

lemma sin_poly_nat_degree_le : ∀ n : ℕ, (sin_poly n).nat_degree ≤ n
| 0 := by simp only [sin_poly, nat_degree_C, mul_zero]
| 1 := by simp only [nat_degree_C, mul_one, zero_le', sin_poly]
| (n+2) :=
  begin
    rw [sin_poly],
    refine nat_degree_add_le_of_degree_le ((nat_degree_smul_le _ _).trans _) _,
    { exact (sin_poly_nat_degree_le (n + 1)).trans (by simp) },
    refine nat_degree_mul_le.trans _,
    simp only [nat_degree_monomial, neg_eq_zero, bit0_eq_zero, one_ne_zero, if_false, mul_add],
    linarith [sin_poly_nat_degree_le n],
  end

lemma cos_poly_nat_degree_le : ∀ n : ℕ, (cos_poly n).nat_degree ≤ n
| 0 := by simp [cos_poly]
| 1 := (nat_degree_monomial_le _).trans (by simp)
| (n+2) :=
  begin
    rw [cos_poly],
    refine nat_degree_add_le_of_degree_le ((nat_degree_smul_le _ _).trans _) _,
    { exact (cos_poly_nat_degree_le (n + 1)).trans (by simp) },
    refine nat_degree_mul_le.trans _,
    simp only [nat_degree_monomial, neg_eq_zero, bit0_eq_zero, one_ne_zero, if_false, mul_add],
    linarith [cos_poly_nat_degree_le n],
  end

lemma sin_poly_add_cos_poly_eval (θ : ℝ) : ∀ n : ℕ,
  I n θ * θ ^ (2 * n + 1) = n! * ((sin_poly n).eval₂ (int.cast_ring_hom _) θ * sin θ +
    (cos_poly n).eval₂ (int.cast_ring_hom _) θ * cos θ)
| 0 := by simp [sin_poly, cos_poly, I_zero, eval₂_C]
| 1 :=
  begin
    simp only [I_one, cos_poly, sin_poly, factorial_one, cast_one, mul_one, eval₂_C,
      eval₂_monomial],
    simp [sub_eq_add_neg],
  end
| (n+2) :=
  begin
    rw [mul_succ, add_right_comm, add_comm (_ + _), pow_add, ←mul_assoc, recursion, sub_mul,
      mul_assoc, mul_assoc _ (I n θ), sin_poly_add_cos_poly_eval, mul_add_one 2, add_right_comm,
      pow_add, ←mul_assoc (I n θ), sin_poly_add_cos_poly_eval, sin_poly, cos_poly, eval₂_add,
      eval₂_add, eval₂_smul, eval₂_smul, eval₂_mul, eval₂_mul, eval₂_monomial],
    simp only [factorial_succ, nat.cast_add_one, nat.cast_mul, ring_hom.eq_int_cast, int.cast_neg,
      int.cast_bit0, int.cast_bit1, int.cast_mul, nat.cast_one, int.cast_one, int.cast_coe_nat,
      int.cast_add, neg_mul],
    ring,
  end

open_locale big_operators

lemma is_integer {p : polynomial ℤ} (a b : ℤ) {k : ℕ} (hp : p.nat_degree ≤ k) :
  ∃ z : ℤ, p.eval₂ (int.cast_ring_hom ℝ) (a / b) * b ^ k = z :=
begin
  rcases eq_or_ne b 0 with rfl | hb,
  { rcases k.eq_zero_or_pos with rfl | hk,
    { exact ⟨p.coeff 0, by simp⟩ },
    exact ⟨0, by simp only [int.cast_zero, zero_pow hk, mul_zero]⟩ },
  refine ⟨∑ i in p.support, p.coeff i * a ^ i * b ^ (k - i), _⟩,
  conv_lhs {rw [←sum_monomial_eq p]},
  rw [eval₂_sum, polynomial.sum, finset.sum_mul, int.cast_sum],
  simp only [eval₂_monomial, ring_hom.eq_int_cast, int.cast_mul, div_pow],
  refine finset.sum_congr rfl (λ i hi, _),
  have ik := (le_nat_degree_of_mem_supp i hi).trans hp,
  rw [mul_assoc, div_mul_comm, ←int.cast_pow, ←int.cast_pow, ←int.cast_pow, ←pow_sub_mul_pow b ik,
    ←int.cast_div_char_zero, int.mul_div_cancel _ (pow_ne_zero _ hb), ←mul_assoc, mul_right_comm],
  exact dvd_mul_left _ _,
end

open_locale real
open filter

lemma integral_pos {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hfc : continuous_on f (Icc a b))
  (hle : ∀ x ∈ Ioc a b, 0 ≤ f x) (hlt : ∃ c ∈ Icc a b, 0 < f c) :
  0 < ∫ x in a..b, f x :=
(integral_lt_integral_of_continuous_on_of_le_of_exists_lt hab
  continuous_on_const hfc hle hlt).trans_eq' (by simp)

lemma I_pos : 0 < I n (π / 2) :=
begin
  refine integral_pos (by norm_num) (continuous.continuous_on (by continuity)) _ ⟨0, by simp⟩,
  refine λ x hx, mul_nonneg (pow_nonneg _ _) _,
  { rw [sub_nonneg, sq_le_one_iff_abs_le_one, abs_le],
    exact ⟨hx.1.le, hx.2⟩, },
  refine cos_nonneg_of_neg_pi_div_two_le_of_le _ _;
  nlinarith [hx.1, hx.2, pi_pos],
end

lemma I_le (n : ℕ) : I n (π / 2) ≤ 2 :=
begin
  rw ←norm_of_nonneg I_pos.le,
  refine (norm_integral_le_of_norm_le_const _).trans (show (1 : ℝ) * _ ≤ _, by norm_num),
  intros x hx,
  simp only [interval_oc_of_le, neg_le_self_iff, zero_le_one, mem_Ioc] at hx,
  rw [norm_eq_abs, abs_mul, abs_pow],
  refine mul_le_one (pow_le_one _ (abs_nonneg _) _) (abs_nonneg _) (abs_cos_le_one _),
  rw abs_le,
  split;
  nlinarith,
end

lemma int.cast_lt_one {R : Type*} [nontrivial R] [ordered_ring R]  {z : ℤ} : (z : R) < 1 ↔ z < 1 :=
by simpa only [int.cast_one] using @int.cast_lt R _ _ z 1

lemma my_tendsto_pow_div_factorial_at_top (a : ℝ) :
  tendsto (λ n, (a : ℝ) ^ (2 * n + 1) / n!) at_top (nhds 0) :=
begin
  rw ←mul_zero a,
  refine ((tendsto_pow_div_factorial_at_top (a ^ 2)).const_mul a).congr (λ x, _),
  rw [←pow_mul, mul_div_assoc', pow_succ],
end

lemma not_irrational.exists_rep {x : ℝ} :
  ¬irrational x → ∃ (a : ℤ) (b : ℕ), 0 < b ∧ x = a / b :=
begin
  rw [irrational, not_not, mem_range],
  rintro ⟨q, rfl⟩,
  exact ⟨q.num, q.denom, q.pos, by exact_mod_cast rat.num_denom.symm⟩,
end

lemma irrational_pi : irrational π :=
begin
  apply irrational.of_div_nat 2,
  rw [nat.cast_two],
  by_contra h',
  obtain ⟨a, b, hb, h⟩ := not_irrational.exists_rep h',
  have ha : (0 : ℝ) < a,
  { have : 0 < (a : ℝ) / b := h ▸ pi_div_two_pos,
    rwa [lt_div_iff ((@nat.cast_pos ℝ _ _ _).2 hb), zero_mul] at this },
  have k : ∀ n, 0 < (a : ℝ) ^ (2 * n + 1) / n! :=
    λ n, div_pos (pow_pos ha _) (cast_pos.2 n.factorial_pos),
  have j : ∀ᶠ n : ℕ in at_top, (a : ℝ) ^ (2 * n + 1) / n! * I n (π / 2) < 1,
  { have := eventually_lt_of_tendsto_lt (show (0 : ℝ) < 1 / 2, by norm_num)
              (my_tendsto_pow_div_factorial_at_top a),
    filter_upwards [this] with n hn,
    rw lt_div_iff (zero_lt_two : (0 : ℝ) < 2) at hn,
    exact hn.trans_le' (mul_le_mul_of_nonneg_left (I_le _) (k n).le) },
  obtain ⟨n, hn⟩ := j.exists,
  have hn' : 0 < (a : ℝ) ^ (2 * n + 1) / n! * I n (π / 2) := mul_pos (k _) I_pos,
  have i : ∃ z : ℤ, (sin_poly n).eval₂ (int.cast_ring_hom ℝ) (a / b) * b ^ (2 * n + 1) = z,
  { exact is_integer a b ((sin_poly_nat_degree_le _).trans (by linarith)) },
  obtain ⟨z, hz⟩ := i,
  have e := sin_poly_add_cos_poly_eval (π / 2) n,
  rw [cos_pi_div_two, sin_pi_div_two, mul_zero, mul_one, add_zero] at e,
  have : (a : ℝ) ^ (2 * n + 1) / ↑n! * I n (π / 2) =
    eval₂ (int.cast_ring_hom ℝ) (π / 2) (sin_poly n) * b ^ (2 * n + 1),
  { rw [←mul_div_right_comm],
    refine div_eq_of_eq_mul (nat.cast_ne_zero.2 n.factorial_pos.ne') _,
    rw [mul_rotate, mul_assoc, ←e, h, mul_comm (I _ _), ←mul_assoc, div_pow, mul_div_cancel'],
    exact pow_ne_zero _ (nat.cast_ne_zero.2 hb.ne') },
  have : (0 : ℝ) < z ∧ (z : ℝ) < 1,
  { rw [←hz, ←h, ←this],
    exact ⟨hn', hn⟩ },
  rw [int.cast_pos, int.cast_lt_one, ←int.add_one_le_iff, zero_add] at this,
  exact this.1.not_lt this.2,
end
