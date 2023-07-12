/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import analysis.normed.group.hom
import analysis.specific_limits.normed

/-! # Extending a backward bound on a normed group homomorphism from a dense set

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Possible TODO (from the PR's review, https://github.com/leanprover-community/mathlib/pull/8498 ):
"This feels a lot like the second step in the proof of the Banach open mapping theorem
(`exists_preimage_norm_le`) ... wonder if it would be possible to refactor it using one of [the
lemmas in this file]."
-/

open filter finset
open_locale topology big_operators

variables {G : Type*} [normed_add_comm_group G] [complete_space G]
variables {H : Type*} [normed_add_comm_group H]

/-- Given `f : normed_add_group_hom G H` for some complete `G` and a subgroup `K` of `H`, if every
element `x` of `K` has a preimage under `f` whose norm is at most `C*‖x‖` then the same holds for
elements of the (topological) closure of `K` with constant `C+ε` instead of `C`, for any
positive `ε`.
-/
lemma controlled_closure_of_complete  {f : normed_add_group_hom G H} {K : add_subgroup H}
  {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε) (hyp : f.surjective_on_with K C) :
  f.surjective_on_with K.topological_closure (C + ε) :=
begin
  rintros (h : H) (h_in : h ∈ K.topological_closure),
  /- We first get rid of the easy case where `h = 0`.-/
  by_cases hyp_h : h = 0,
  { rw hyp_h,
    use 0,
    simp },
  /- The desired preimage will be constructed as the sum of a series. Convergence of
  the series will be guaranteed by completeness of `G`. We first write `h` as the sum
  of a sequence `v` of elements of `K` which starts close to `h` and then quickly goes to zero.
  The sequence `b` below quantifies this. -/
  set b : ℕ → ℝ := λ i, (1/2)^i*(ε*‖h‖/2)/C,
  have b_pos : ∀ i, 0 < b i,
  { intro i,
    field_simp [b, hC],
    exact div_pos (mul_pos hε (norm_pos_iff.mpr hyp_h))
                  (mul_pos (by norm_num : (0 : ℝ) < 2^i*2) hC) },
  obtain ⟨v : ℕ → H, lim_v : tendsto (λ (n : ℕ), ∑ k in range (n + 1), v k) at_top (𝓝 h),
    v_in : ∀ n, v n ∈ K, hv₀ : ‖v 0 - h‖ < b 0, hv : ∀ n > 0, ‖v n‖ < b n⟩ :=
    controlled_sum_of_mem_closure h_in b_pos,
  /- The controlled surjectivity assumption on `f` allows to build preimages `u n` for all
  elements `v n` of the `v` sequence.-/
  have : ∀ n, ∃ m' : G, f m' = v n ∧ ‖m'‖ ≤ C * ‖v n‖ := λ (n : ℕ), hyp (v n) (v_in n),
  choose u hu hnorm_u using this,
  /- The desired series `s` is then obtained by summing `u`. We then check our choice of
  `b` ensures `s` is Cauchy. -/
  set s : ℕ → G := λ n, ∑ k in range (n+1), u k,
  have : cauchy_seq s,
  { apply normed_add_comm_group.cauchy_series_of_le_geometric'' (by norm_num) one_half_lt_one,
    rintro n (hn : n ≥ 1),
    calc ‖u n‖ ≤ C*‖v n‖ : hnorm_u n
    ... ≤ C * b n : mul_le_mul_of_nonneg_left (hv _ $ nat.succ_le_iff.mp hn).le hC.le
    ... = (1/2)^n * (ε * ‖h‖/2) : by simp [b, mul_div_cancel' _ hC.ne.symm]
    ... = (ε * ‖h‖/2) * (1/2)^n : mul_comm _ _ },
  /- We now show that the limit `g` of `s` is the desired preimage. -/
  obtain ⟨g : G, hg⟩ := cauchy_seq_tendsto_of_complete this,
  refine ⟨g, _, _⟩,
  { /- We indeed get a preimage. First note: -/
    have : f ∘ s = λ n, ∑ k in range (n + 1), v k,
    { ext n,
      simp [map_sum, hu] },
    /- In the above equality, the left-hand-side converges to `f g` by continuity of `f` and
       definition of `g` while the right-hand-side converges to `h` by construction of `v` so
       `g` is indeed a preimage of `h`. -/
    rw ← this at lim_v,
    exact tendsto_nhds_unique ((f.continuous.tendsto g).comp hg) lim_v },
  { /- Then we need to estimate the norm of `g`, using our careful choice of `b`. -/
    suffices : ∀ n, ‖s n‖ ≤ (C + ε) * ‖h‖,
      from le_of_tendsto' (continuous_norm.continuous_at.tendsto.comp hg) this,
    intros n,
    have hnorm₀ : ‖u 0‖ ≤ C*b 0 + C*‖h‖,
    { have := calc
      ‖v 0‖ ≤ ‖h‖ + ‖v 0 - h‖ : norm_le_insert' _ _
      ... ≤ ‖h‖ + b 0 : by apply add_le_add_left hv₀.le,
      calc ‖u 0‖ ≤ C*‖v 0‖ : hnorm_u 0
      ... ≤ C*(‖h‖ + b 0) : mul_le_mul_of_nonneg_left this hC.le
      ... = C * b 0 + C * ‖h‖ : by rw [add_comm, mul_add] },
    have : ∑ k in range (n + 1), C * b k ≤ ε * ‖h‖ := calc
      ∑ k in range (n + 1), C * b k = (∑ k in range (n + 1), (1 / 2) ^ k) * (ε * ‖h‖ / 2) :
                     by simp only [b, mul_div_cancel' _ hC.ne.symm, ← sum_mul]
      ... ≤  2 * (ε * ‖h‖ / 2) : mul_le_mul_of_nonneg_right (sum_geometric_two_le _)
                                                            (by nlinarith [hε, norm_nonneg h])
      ... = ε * ‖h‖ : mul_div_cancel' _ two_ne_zero,
    calc ‖s n‖ ≤ ∑ k in range (n+1), ‖u k‖ : norm_sum_le _ _
    ... = ∑ k in range n, ‖u (k + 1)‖ + ‖u 0‖ : sum_range_succ' _ _
    ... ≤ ∑ k in range n, C*‖v (k + 1)‖ + ‖u 0‖ : add_le_add_right (sum_le_sum (λ _ _, hnorm_u _)) _
    ... ≤ ∑ k in range n, C*b (k+1) + (C*b 0 + C*‖h‖) :
      add_le_add (sum_le_sum (λ k _, mul_le_mul_of_nonneg_left (hv _ k.succ_pos).le hC.le)) hnorm₀
    ... = ∑ k in range (n+1), C*b k + C*‖h‖ : by rw [← add_assoc, sum_range_succ']
    ... ≤ (C+ε)*‖h‖ : by { rw [add_comm, add_mul], apply add_le_add_left this } }
end

/-- Given `f : normed_add_group_hom G H` for some complete `G`, if every element `x` of the image of
an isometric immersion `j : normed_add_group_hom K H` has a preimage under `f` whose norm is at most
`C*‖x‖` then the same holds for elements of the (topological) closure of this image with constant
`C+ε` instead of `C`, for any positive `ε`.
This is useful in particular if `j` is the inclusion of a normed group into its completion
(in this case the closure is the full target group).
-/
lemma controlled_closure_range_of_complete {f : normed_add_group_hom G H}
  {K : Type*} [seminormed_add_comm_group K] {j : normed_add_group_hom K H} (hj : ∀ x, ‖j x‖ = ‖x‖)
  {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε) (hyp : ∀ k, ∃ g, f g = j k ∧ ‖g‖ ≤ C*‖k‖) :
  f.surjective_on_with j.range.topological_closure (C + ε) :=
begin
  replace hyp : ∀ h ∈ j.range, ∃ g, f g = h ∧ ‖g‖ ≤ C*‖h‖,
  { intros h h_in,
    rcases (j.mem_range _).mp h_in with ⟨k, rfl⟩,
    rw hj,
    exact hyp k },
  exact controlled_closure_of_complete hC hε hyp
end
