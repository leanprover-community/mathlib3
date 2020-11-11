import analysis.calculus.deriv
import measure_theory.borel_space

noncomputable theory

open topological_space (second_countable_topology) set asymptotics filter
open_locale topological_space filter

namespace continuous_linear_map

variables {𝕜 E F : Type*} [nondiscrete_normed_field 𝕜]
  [normed_group E] [normed_space 𝕜 E] [normed_group F] [normed_space 𝕜 F]

instance : measurable_space (E →L[𝕜] F) := borel _

instance : borel_space (E →L[𝕜] F) := ⟨rfl⟩

lemma measurable_apply [measurable_space F] [borel_space F] (x : E) :
  measurable (λ f : E →L[𝕜] F, f x) :=
(apply 𝕜 F x).continuous.measurable

lemma measurable_apply' [measurable_space E] [opens_measurable_space E]
  [measurable_space F] [borel_space F] :
  measurable (λ (x : E) (f : E →L[𝕜] F), f x) :=
measurable_pi_lambda _ $ λ f, f.measurable

lemma measurable_apply₂ [measurable_space E] [opens_measurable_space E]
  [second_countable_topology E] [second_countable_topology (E →L[𝕜] F)]
  [measurable_space F] [borel_space F] :
  measurable (λ p : (E →L[𝕜] F) × E, p.1 p.2) :=
is_bounded_bilinear_map_apply.continuous.measurable

lemma measurable_coe [measurable_space F] [borel_space F] :
  measurable (λ (f : E →L[𝕜] F) (x : E), f x) :=
measurable_pi_lambda _ measurable_apply

end continuous_linear_map

variables {𝕜 E F : Type*} [nondiscrete_normed_field 𝕜] [normed_group E] [normed_space 𝕜 E]
  [normed_group F] [normed_space 𝕜 F] {f : E → F} {f' g' : E →L[𝕜] F} {x : E} {r R ε : ℝ}

def has_approx_fderiv_at_in_shell (f : E → F) (f' : E →L[𝕜] F) (x : E) (r R ε : ℝ) :=
∀ y, r ≤ dist y x → dist y x < R → ∥f y - f x - f' (y - x)∥ ≤ ε * ∥y - x∥

lemma has_fderiv_at.has_approx_fderiv_at_in_shell (h : has_fderiv_at f f' x) (hε : 0 < ε) :
  ∃ R₀ > 0, ∀ R < R₀, ∀ r, has_approx_fderiv_at_in_shell f f' x r R ε :=
begin
  rcases metric.eventually_nhds_iff.1 (is_o_iff.1 h hε) with ⟨R₀, R₀_pos, hR₀⟩,
  use [R₀, R₀_pos],
  rintros R hR r y hyr hy,
  exact hR₀ (hy.trans hR)
end

lemma has_approx_fderiv_at_in_shell.mono (hf : has_approx_fderiv_at_in_shell f f' x r R ε)
  {r' R' ε' : ℝ} (hr : r ≤ r') (hR : R' ≤ R) (hε : ε ≤ ε') :
  has_approx_fderiv_at_in_shell f f' x r' R' ε' :=
λ y h₁ h₂, (hf y (hr.trans h₁) (h₂.trans_le hR)).trans $
  mul_le_mul_of_nonneg_right hε (norm_nonneg _)

lemma has_approx_fderiv_at_in_shell.mono_pow {a : 𝕜} (ha : ∥a∥ < 1) {m n m' n' : ℕ}
  (hf : has_approx_fderiv_at_in_shell f f' x (∥a∥^m) (∥a∥^n) ε) (hm : m' ≤ m) (hn : n ≤ n') :
  has_approx_fderiv_at_in_shell f f' x (∥a∥^m') (∥a∥^n') ε :=
hf.mono (pow_le_pow_of_le_one (norm_nonneg a) ha.le hm)
  (pow_le_pow_of_le_one (norm_nonneg a) ha.le hn) le_rfl

lemma has_approx_fderiv_at_in_shell.dist_le (hf : has_approx_fderiv_at_in_shell f f' x r R ε)
  {ε'} (hg : has_approx_fderiv_at_in_shell f g' x r R ε') (hR : 0 < R) (hε : 0 ≤ ε) (hε' : 0 ≤ ε')
  {a : 𝕜} (ha₁ : ∥a∥ < 1) (hca : r ≤ ∥a∥ * R) :
  dist f' g' ≤ ε + ε' :=
begin
  rw [dist_eq_norm],
  refine continuous_linear_map.op_norm_le_of_shell' hR (add_nonneg hε hε') ha₁ _,
  intros y hay hy,
  have h₁ : dist (x + y) x < R, by simpa [dist_eq_norm],
  have h₂ : r ≤ dist (x + y) x,
    calc r ≤ ∥a∥ * R : hca
    ... ≤ dist (x + y) x : by rwa [dist_eq_norm, add_sub_cancel', mul_comm],
  calc ∥f' y - g' y∥ = ∥(f (x + y) - f x - g' (x + y - x)) - (f (x + y) - f x - f' (x + y - x))∥ :
    by simp
  ... ≤ _ : norm_sub_le _ _
  ... ≤ ε' * ∥x + y - x∥ + ε * ∥x + y - x∥ : add_le_add (hg _ h₂ h₁) (hf _ h₂ h₁)
  ... = (ε + ε') * ∥y∥ : by rw [add_sub_cancel', add_mul, add_comm]
end

lemma has_approx_fderiv_at_in_shell.dist_le' {a : 𝕜} (ha : ∥a∥ < 1) (ha₀ : a ≠ 0)
  {m n m' n' k k': ℕ}
  (hf : has_approx_fderiv_at_in_shell f f' x (∥a∥^m) (∥a∥^n) (1 / 2 ^ k))
  (hg : has_approx_fderiv_at_in_shell f g' x (∥a∥^m') (∥a∥^n') (1 / 2 ^ k'))
  (h : max n n' < min m m') :
  dist f' g' ≤ 1 / 2 ^ k + 1 / 2 ^ k' :=
(hf.mono_pow ha (min_le_left _ _) (le_max_left _ _)).dist_le
  (hg.mono_pow ha (min_le_right _ _) (le_max_right _ _)) (pow_pos (norm_pos_iff.2 ha₀) _)
  (div_nonneg zero_le_one (pow_nonneg zero_le_two _))
  (div_nonneg zero_le_one (pow_nonneg zero_le_two _)) ha $
  by { rw ← pow_succ, exact pow_le_pow_of_le_one (norm_nonneg a) ha.le h }

lemma has_fderiv_at_of_forall_shell {a : 𝕜} (ha : ∥a∥ < 1) (h₀ : a ≠ 0)
  {t : set (E →L[𝕜] F)} (ht : is_complete t)
  (hf : ∀ k : ℕ, ∃ n : ℕ, ∀ m : ℕ,
    ∃ f' ∈ t, has_approx_fderiv_at_in_shell f f' x (∥a∥^m) (∥a∥^n) (1 / 2 ^ k)) :
  ∃ f' ∈ t, has_fderiv_at f f' x :=
begin
  choose! n f' hf't H using hf,
  /- First we prove estimates on the distances between the approximate derivatives. -/
  have H₁ : ∀ ⦃K k k'⦄, K + 3 ≤ k → K + 3 ≤ k' → ∀ m m',
    dist (f' k (m + n k + 1)) (f' k' (m' + n k' + 1)) < (1 / 2) ^ K,
  { intro K,
    have : ∀ ⦃k : ℕ⦄, K + 3 ≤ k → (1 / 2 ^ k : ℝ) ≤ (1 / 2) ^ K / 8,
    { intros k h,
      rw [div_pow, one_pow, div_div_eq_div_mul],
      refine iff.mpr (one_div_le_one_div (pow_pos zero_lt_two _) (by norm_num)) _,
      have : (2 ^ 3 : ℝ) = 8, by norm_num,
      rw [← this, ← pow_add],
      exact pow_le_pow one_le_two h },
    set ε := (1 / 2 : ℝ) ^ K,
    have ε0 : 0 < ε := pow_pos one_half_pos _,
    have : ∀ ⦃k k' m m'⦄, K + 3 ≤ k → K + 3 ≤ k' → max (n k) (n k') < min m m' →
      dist (f' k m) (f' k' m') ≤ ε / 4,
    { intros k k' m m' hk hk' h,
      calc dist (f' k m) (f' k' m') ≤ 1 / 2 ^ k + 1 / 2 ^ k' :
        (H _ _).dist_le' ha h₀ (H _ _) h
      ... ≤ ε / 8 + ε / 8 : add_le_add (this hk) (this hk')
      ... = _ : _,
      rw [← add_div, ← two_mul, bit0_eq_two_mul (4:ℝ), mul_div_mul_left],
      exact two_ne_zero },
    intros k k' hk hk' m m',
    have A : dist (f' k (m + n k + 1)) (f' k (n k + n k' + 1)) ≤ ε / 4 :=
      this hk hk (by { simp only [max_self, lt_min_iff], omega }),
    have B : dist (f' k (n k + n k' + 1)) (f' k' (n k + n k' + 1)) ≤ ε / 4 :=
      this hk hk' (by { simp only [min_self, max_lt_iff], omega }),
    have C : dist (f' k' (n k + n k' + 1)) (f' k' (m' + n k' + 1)) ≤ ε / 4 :=
      this hk' hk' (by simp only [max_self, lt_min_iff]; omega),
    calc dist (f' k (m + n k + 1)) (f' k' (m' + n k' + 1)) ≤ _ + _ + _ :
      dist_triangle4 _ _ _ _
    ... ≤ ε / 4 + ε / 4 + ε / 4 :
      add_le_add (add_le_add A B) C
    ... < _ : _,
    rw [← add_div, ← add_div, div_lt_iff],
    linarith,
    norm_num },
  /- These estimates imply that `λ p, f' p.1 (p.2 + n p.1 + 1)` is a Cauchy sequence.
  We add `n p.1 + 1` to the second argument to ensure that the inner radius is less
  than the outer radius. -/
  have H₂ : cauchy_seq (λ p : ℕ × ℕ, f' p.1 (p.2 + n p.1 + 1)) :=
    (uniformity_basis_dist_pow_of_lt_1 one_half_pos one_half_lt_one).cauchy_seq_iff.2
      (λ K _, ⟨⟨K + 3, 0⟩, λ p p' hp hp', H₁ hp.1 hp'.1 _ _⟩),
  /- Now take the limit `F'` of this sequence. -/
  rcases cauchy_seq_tendsto_of_is_complete ht _ H₂ with ⟨F', hF't, hF'⟩,
  show ∀ p : ℕ × ℕ, f' _ _ ∈ t, from λ p, hf't _ _,
  /- This limit will be the derivative we are looking for. -/
  use [F', hF't],
  /- The estimate on the distances between `f' k m` imply an estimate on the distance
  between `f' (k + 3) m` and `F'`. -/
  have H₃ : ∀ k m, dist (f' (k + 3) (m + n (k + 3) + 1)) F' ≤ (1 / 2) ^ k :=
    λ k m, le_of_tendsto (tendsto_const_nhds.dist hF') $
      eventually_at_top.2 ⟨(k + 3, 0), λ p hp, (H₁ le_rfl hp.1 m p.2).le⟩,
  /- Take `ε > 0`. -/
  refine is_o_iff.2 (λ ε ε0, _),
  /- Without loss of generality, `ε = (1 / 2) ^ K`, `K : ℕ`. -/
  rcases ((tendsto_pow_at_top_nhds_0_of_lt_1 one_half_pos.le one_half_lt_one).eventually
    (gt_mem_nhds ε0)).exists with ⟨K, hK⟩,
  suffices : ∀ᶠ y in 𝓝 x, ∥f y - f x - F' (y - x)∥ ≤ (1 / 2) ^ K * ∥y - x∥,
    from this.mono (λ y hy, hy.trans (mul_le_mul_of_nonneg_right hK.le (norm_nonneg _))),
  clear hK ε0 ε,
  have h₀' : 0 < ∥a∥ := norm_pos_iff.2 h₀,
  /- The estimate will hold in the ball of radius `∥a∥ ^ n (K + 4)` around `x`. -/
  refine metric.eventually_nhds_iff.2 ⟨∥a∥ ^ n (K + 1 + 3), pow_pos h₀' _, λ y hy, _⟩,
  /- Take a point `y` in this ball. If `y = x`, then the inequality is trivial. -/
  by_cases hyx : y = x, { simp [hyx] },
  /- Otherwise there exists `m` such that `∥a∥^m < dist y x < ∥a∥ ^ n (K + 4)`. -/
  replace hyx : 0 < dist y x := dist_pos.2 hyx,
  rcases ((tendsto_pow_at_top_nhds_0_of_lt_1 h₀'.le ha).eventually (gt_mem_nhds hyx)).exists
    with ⟨m, hm⟩,
  have H₄ := (H (K + 1 + 3) (m + n (K + 1 + 3) + 1)).mono_pow ha
    (le_add_right (le_add_right le_rfl)) le_rfl y hm.le hy,
  have H₅ := H₃ (K + 1) m,
  rw [dist_eq_norm] at H₅,
  replace H₅ := continuous_linear_map.le_of_op_norm_le _ H₅ (y - x),
  rw [continuous_linear_map.sub_apply] at H₅,
  rw [← dist_eq_norm] at H₄ H₅ ⊢,
  refine (dist_triangle _ _ _).trans ((add_le_add H₄ H₅).trans _),
  rw [← add_mul, ← one_div_pow, pow_add, pow_add, mul_assoc, ← mul_add],
  refine mul_le_mul_of_nonneg_right _ (norm_nonneg _),
  refine mul_le_of_le_one_right (pow_nonneg _ _) _; norm_num
end

lemma set_of_has_fderiv_at_mem_set_eq {a : 𝕜} (ha : ∥a∥ < 1) (h₀ : a ≠ 0)
  {t : set (E →L[𝕜] F)} (ht : is_complete t) :
  {x | ∃ f' ∈ t, has_fderiv_at f f' x} =
    ⋂ k : ℕ, ⋃ n : ℕ, ⋂ m : ℕ,
      ⋃ (r : ℚ) (hr : (0 : ℝ) < r ∧ ↑r < ∥a∥^m) (R : ℚ) (hR : ∥a∥^n < R)
          (ε : ℚ) (hε : (0 : ℝ) < ε ∧ (ε : ℝ) < 1 / 2 ^ k),
        {x | ∃ f' ∈ t, has_approx_fderiv_at_in_shell f f' x r R ε} :=
begin
  have h₀' : 0 < ∥a∥ := norm_pos_iff.2 h₀,
  ext x : 1,
  simp only [mem_set_of_eq, mem_Inter, mem_Union],
  split,
  { rintros ⟨f', hf't, hf'⟩ k,
    rcases exists_rat_btwn (one_div_pos.2 (pow_pos (@zero_lt_two ℝ _ _) k)) with ⟨ε, hε⟩,
    rcases hf'.has_approx_fderiv_at_in_shell hε.1 with ⟨R₀, hR₀⟩,
    rcases exists_pow_lt_of_lt_1 (norm_nonneg a) ha hR₀.fst with ⟨n, hn⟩,
    rcases exists_rat_btwn hn with ⟨R, hR⟩,
    refine ⟨n, λ m, _⟩,
    rcases exists_rat_btwn (pow_pos h₀' m) with ⟨r, hr⟩,
    exact ⟨r, hr, R, hR.1, ε, hε, f', hf't, hR₀.snd _ hR.2 _⟩ },
  { intro H,
    choose n r hr R hR ε hε f' Hf't Hf' using H,
    refine has_fderiv_at_of_forall_shell ha h₀ ht (λ k, ⟨n k, λ m, ⟨f' k m, Hf't _ _, _⟩⟩),
    exact (Hf' k m).mono (hr _ _).2.le (hR _ _).le (hε _ _).2.le }
end

lemma is_measurable_set_of_has_fderiv_at_mem_set [measurable_space E] [opens_measurable_space E]
  {t : set (E →L[𝕜] F)} (ht : is_complete t) :
  is_measurable {x : E | ∃ f' ∈ t, has_fderiv_at f f' x} :=
begin
  rcases normed_field.exists_norm_lt_one 𝕜 with ⟨a, h₀', ha⟩,
  have h₀ : a ≠ 0 := norm_pos_iff.1 h₀',
  rw [set_of_has_fderiv_at_mem_set_eq ha h₀ ht],
  refine is_measurable.Inter (λ k, is_measurable.Union $ λ n, is_measurable.Inter $
    λ m, is_open.is_measurable $ is_open_iff_mem_nhds.2 $ λ x hx, _),
  simp only [mem_Union] at hx,
  rcases hx with ⟨r, hr, R, hR, ε, hε, f', hf't, hf'⟩,
  rcases exists_rat_btwn hr.2 with ⟨r', hr'⟩,
  rcases exists_rat_btwn hR with ⟨R', hR'⟩,
  rcases exists_rat_btwn hε.2 with ⟨ε', hε'⟩,
  suffices : ∀ᶠ x' in 𝓝 x, has_approx_fderiv_at_in_shell f f' x' r' R' ε',
  { simp only [← set_of_exists],
    exact this.mono (λ x' hx', ⟨r', ⟨hr.1.trans hr'.1, hr'.2⟩, R', hR'.1,
      ε', ⟨hε.1.trans hε'.1, hε'.2⟩, f', hf't, hx'⟩) },
  have hr'_subset : ∀ᶠ x' in 𝓝 x, ∀ y, ↑r' ≤ dist y x' → ↑r ≤ dist y x,
  { refine metric.eventually_nhds_iff.2 ⟨r' - r, sub_pos.2 hr'.1, λ x' hx' y hy, _⟩,
    calc (r : ℝ) = r' - (r' - r) : (sub_sub_cancel _ _).symm
    ... ≤ dist y x' - dist x' x : sub_le_sub hy hx'.le
    ... ≤ _ : sub_le_iff_le_add.2 (dist_triangle_right _ _ _) },
  have hR'_subset : ∀ᶠ x' in 𝓝 x, ∀ y, dist y x' < R' → dist y x < R :=
    metric.eventually_nhds_iff.2 ⟨R - R', sub_pos.2 hR'.2, λ x' hx' y hy,
      metric.ball_subset hx'.le hy⟩,
end
  
/-  
  (hf : ∀ k : ℕ, ∃ n : ℕ, ∀ m : ℕ,
    ∃ f' ∈ t, has_approx_fderiv_at_in_shell f f' x (∥a∥^m) (∥a∥^n) (1 / 2 ^ k)) :
  ∃ f' ∈ t, has_fderiv_at f f' x :=-/
