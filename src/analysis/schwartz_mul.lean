import analysis.schwartz_space

open_locale big_operators schwartz_space

universes uD uE uF uG

section mul_lemma

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
{D : Type uD} [normed_add_comm_group D] [normed_space 𝕜 D]
{E : Type uE} [normed_add_comm_group E] [normed_space 𝕜 E]
{F : Type uF} [normed_add_comm_group F] [normed_space 𝕜 F]
{G : Type uG} [normed_add_comm_group G] [normed_space 𝕜 G]

lemma continuous_linear_map.norm_iterated_fderiv_within_le_of_bilinear
  (B : E →L[𝕜] F →L[𝕜] G) {f : D → E} {g : D → F} {N : with_top ℕ} {s : set D} {x : D}
  (hf : cont_diff_on 𝕜 N f s) (hg : cont_diff_on 𝕜 N g s) (hs : unique_diff_on 𝕜 s) (hx : x ∈ s)
  {n : ℕ} (hn : (n : with_top ℕ) ≤ N) :
  ‖iterated_fderiv_within 𝕜 n (λ y, B (f y) (g y)) s x‖
      ≤ ‖B‖ * ∑ i in finset.range (n+1), (n.choose i : ℝ)
      * ‖iterated_fderiv_within 𝕜 i f s x‖ * ‖iterated_fderiv_within 𝕜 (n-i) g s x‖ :=
begin
  sorry,
end

lemma continuous_linear_map.norm_iterated_fderiv_le_of_bilinear
  (B : E →L[𝕜] F →L[𝕜] G) {f : D → E} {g : D → F} {N : with_top ℕ}
  (hf : cont_diff 𝕜 N f) (hg : cont_diff 𝕜 N g) (x : D)
  {n : ℕ} (hn : (n : with_top ℕ) ≤ N) :
  ‖iterated_fderiv 𝕜 n (λ y, B (f y) (g y)) x‖
    ≤ ‖B‖ * ∑ i in finset.range (n+1), (n.choose i : ℝ)
      * ‖iterated_fderiv 𝕜 i f x‖ * ‖iterated_fderiv 𝕜 (n-i) g x‖ :=
begin
  sorry,
end

end mul_lemma

noncomputable theory

variables {𝕜 𝕜' D E F G : Type*}

variables [nontrivially_normed_field 𝕜]
variables [normed_add_comm_group D] [normed_space ℝ D]
variables [normed_add_comm_group E] [normed_space ℝ E] [normed_space 𝕜 E]
variables [normed_add_comm_group F] [normed_space ℝ F] [normed_space 𝕜 F]
variables [normed_add_comm_group G] [normed_space ℝ G] [normed_space 𝕜 G]

def schwartz_seminorm_sup (k n : ℕ) : seminorm ℝ 𝓢(E, F) :=
  ((finset.range (k + 1)) ×ˢ (finset.range (n + 1))).sup (schwartz_seminorm_family ℝ E F)

lemma le_schwartz_seminorm_sup {k n k' n' : ℕ} (hk : k' ≤ k) (hn : n' ≤ n) :
  (schwartz_map.seminorm ℝ k' n' : seminorm ℝ 𝓢(E, F)) ≤ schwartz_seminorm_sup k n :=
begin
  have : (k', n') ∈ (finset.range (k + 1)).product (finset.range (n + 1)) :=
  begin
    simp only [finset.mem_range, finset.mem_product],
    exact ⟨nat.lt_succ_of_le hk, nat.lt_succ_of_le hn⟩,
  end,
  exact @finset.le_sup _ _ _ _ _ (schwartz_seminorm_family ℝ E F) _ this,
end

lemma le_schwartz_seminorm_sup_apply {k n k' n' : ℕ} (hk : k' ≤ k) (hn : n' ≤ n) (f : 𝓢(E, F)) (x : E) :
  ‖x‖ ^ k' * ‖iterated_fderiv ℝ n' f x‖ ≤ schwartz_seminorm_sup k n f :=
le_trans (schwartz_map.le_seminorm ℝ k' n' f x) (le_schwartz_seminorm_sup hk hn f)

/-- This is a rather bad estimate, but it is easy to prove. -/
lemma one_add_le_schwartz_seminorm_sup_apply {k n k' n' : ℕ} (hk : k' ≤ k) (hn : n' ≤ n) (f : 𝓢(E, F)) (x : E) :
  (1 + ‖x‖) ^ k' * ‖iterated_fderiv ℝ n' f x‖ ≤ 2^k * schwartz_seminorm_sup k n f :=
begin
  rw [add_comm, add_pow],
  simp only [one_pow, mul_one, finset.sum_congr],
  rw [finset.sum_mul],
  norm_cast,
  rw ← nat.sum_range_choose k,
  push_cast,
  rw [finset.sum_mul],
  have hk' : finset.range (k' + 1) ⊆ finset.range (k + 1) :=
  by rwa [finset.range_subset, add_le_add_iff_right],
  refine le_trans (finset.sum_le_sum_of_subset_of_nonneg hk' (λ _ _ _, by positivity)) _,
  refine finset.sum_le_sum (λ i hi, _),
  rw [mul_comm (‖x‖^i), mul_assoc],
  refine mul_le_mul _ _ (by positivity) (by positivity),
  { norm_cast,
    exact nat.choose_le_choose i hk },
  { apply le_schwartz_seminorm_sup_apply (finset.mem_range_succ_iff.mp hi) hn },
end

lemma growth_max {g : D → F}
  (hg_growth : ∀ n : ℕ, ∃ (k : ℕ) (C : ℝ), ∀ (x : D), ‖iterated_fderiv ℝ n g x‖ ≤ C * (1 + ‖x‖)^k) :
  ∀ n : ℕ, ∃ (k : ℕ) (C : ℝ) (hC : 0 ≤ C), ∀ (N : ℕ) (hN : N ≤ n) (x : D) ,
    ‖iterated_fderiv ℝ N g x‖ ≤ C * (1 + ‖x‖)^k :=
begin
  intro n,
  choose k C f using hg_growth,
  use (finset.range (n+1)).sup k,
  let C' := max (0 : ℝ) ((finset.range (n+1)).sup' (by simp) C),
  have hC' : 0 ≤ C' := by simp only [le_refl, finset.le_sup'_iff, true_or, le_max_iff],
  use [C', hC'],
  intros N hN x,
  rw ← finset.mem_range_succ_iff at hN,
  refine le_trans (f N x) (mul_le_mul _ _ (by positivity) hC'),
  { simp only [finset.le_sup'_iff, le_max_iff],
    right,
    exact ⟨N, hN, rfl.le⟩ },
  refine pow_le_pow (by simp only [le_add_iff_nonneg_right, norm_nonneg]) _,
  exact finset.le_sup hN,
end

def mul (B : E →L[ℝ] F →L[ℝ] G) (f : 𝓢(D, E)) {g : D → F} (hg_smooth : cont_diff ℝ ⊤ g)
  (hg_growth : ∀ n : ℕ, ∃ (k : ℕ) (C : ℝ), ∀ (x : D), ‖iterated_fderiv ℝ n g x‖ ≤ C * (1 + ‖x‖)^k) : 𝓢(D, G) :=
{ to_fun := λ x, B (f x) (g x),
  smooth' := B.is_bounded_bilinear_map.cont_diff.comp (cont_diff.prod f.smooth' hg_smooth),
  decay' :=
  begin
    intros k n,
    rcases growth_max hg_growth n with ⟨l, C, hC, hgrowth'⟩,
    let C' := schwartz_map.seminorm ℝ (l + k) n f,
    use ‖B‖ * ∑ (x_1 : ℕ) in finset.range (n + 1), n.choose (n / 2) *
      (C * (2 ^ (l + k) *schwartz_seminorm_sup (l + k) n f)),
    intro x,
    have hxk : 0 ≤ ‖x‖^k := by positivity,
    have := continuous_linear_map.norm_iterated_fderiv_le_of_bilinear B f.smooth' hg_smooth x le_top,
    refine le_trans (mul_le_mul_of_nonneg_left this hxk) _,
    rw [← mul_assoc, mul_comm (‖x‖^k), mul_assoc],
    refine mul_le_mul_of_nonneg_left _ (by positivity),
    rw [finset.mul_sum],
    refine finset.sum_le_sum (λ i hi, _),
    rw [← mul_assoc, mul_comm (‖x‖^k), mul_assoc, mul_assoc],
    refine mul_le_mul _ _ (by positivity) (by positivity),
    { norm_cast,
      exact i.choose_le_middle n },
    { specialize hgrowth' (n - i) (by simp only [tsub_le_self]) x,
      rw [← mul_assoc],
      refine le_trans (mul_le_mul_of_nonneg_left hgrowth' (by positivity)) _,
      rw [mul_comm _ (C * _), mul_assoc],
      refine mul_le_mul_of_nonneg_left _ hC,
      nth_rewrite 1 mul_comm,
      rw [← mul_assoc],
      rw finset.mem_range_succ_iff at hi,
      refine le_trans _ (one_add_le_schwartz_seminorm_sup_apply rfl.le hi f x ),
      refine mul_le_mul_of_nonneg_right _ (norm_nonneg _),
      rw [pow_add],
      refine mul_le_mul_of_nonneg_left _ (by positivity),
      refine pow_le_pow_of_le_left (norm_nonneg _) _ _,
      simp only [zero_le_one, le_add_iff_nonneg_left], },
  end,
}
