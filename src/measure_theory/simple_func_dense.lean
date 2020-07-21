/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
import measure_theory.l1_space

/-!
# Density of simple functions

Show that each Borel measurable function can be approximated,
both pointwise and in `L¹` norm, by a sequence of simple functions.
-/

noncomputable theory
open set filter topological_space
open_locale classical topological_space

universes u v
variables {α : Type u} {β : Type v} {ι : Type*}

namespace measure_theory
open ennreal nat metric

variables [measurable_space α] [normed_group β] [second_countable_topology β]
  [measurable_space β] [borel_space β]

local infixr ` →ₛ `:25 := simple_func

-- FIXME this monolithic proof used to cause a deterministic timeout with `-T50000`
-- It no longer does, but it should still be broken up into a sequence of more manageable pieces.
lemma simple_func_sequence_tendsto {f : α → β} (hf : measurable f) :
  ∃ (F : ℕ → (α →ₛ β)), ∀ x : α, tendsto (λ n, F n x) at_top (𝓝 (f x)) ∧
  ∀ n, ∥F n x∥ ≤ ∥f x∥ + ∥f x∥ :=
-- enumerate a countable dense subset {e k} of β
let ⟨D, ⟨D_countable, D_dense⟩⟩ := @separable_space.exists_countable_closure_eq_univ β _ _ in
let e := enumerate_countable D_countable 0 in
let E := range e in
have E_dense : closure E = univ :=
  dense_of_subset_dense (subset_range_enumerate D_countable 0) D_dense,
let A' (N k : ℕ) : set α :=
  f ⁻¹' (metric.ball (e k) (1 / (N+1 : ℝ)) \ metric.ball 0 (1 / (N+1 : ℝ))) in
let A N := disjointed (A' N) in
have is_measurable_A' : ∀ {N k}, is_measurable (A' N k) :=
  λ N k, hf $ is_measurable.inter is_measurable_ball $ is_measurable.compl is_measurable_ball,
have is_measurable_A : ∀ {N k}, is_measurable (A N k) :=
  λ N, is_measurable.disjointed $ λ k, is_measurable_A',
have A_subset_A' : ∀ {N k x}, x ∈ A N k → x ∈ A' N k := λ N k, inter_subset_left _ _,
have dist_ek_fx' : ∀ {x N k}, x ∈ A' N k → (dist (e k) (f x) < 1 / (N+1 : ℝ)) :=
  λ x N k, by { rw [dist_comm], simpa using (λ a b, a) },
have dist_ek_fx : ∀ {x N k}, x ∈ A N k → (dist (e k) (f x) < 1 / (N+1 : ℝ)) :=
  λ x N k h, dist_ek_fx' (A_subset_A' h),
have norm_fx' : ∀ {x N k}, x ∈ A' N k → (1 / (N+1 : ℝ)) ≤ ∥f x∥ := λ x N k, by simp [ball_0_eq],
have norm_fx : ∀ {x N k}, x ∈ A N k → (1 / (N+1 : ℝ)) ≤ ∥f x∥ := λ x N k h, norm_fx' (A_subset_A' h),
-- construct the desired sequence of simple functions
let M N x := nat.find_greatest (λ M, x ∈ ⋃ k ≤ N, (A M k)) N in
let k N x := nat.find_greatest (λ k, x ∈ A (M N x) k) N in
let F N x := if x ∈ ⋃ M ≤ N, ⋃ k ≤ N, A M k then e (k N x) else 0 in
-- prove properties of the construction above
have k_unique : ∀ {M k k' x},  x ∈ A M k ∧ x ∈ A M k' → k = k' := λ M k k' x h,
begin
  by_contradiction k_ne_k',
  have NE : (A M k ∩ A M k').nonempty, from ⟨x, h⟩,
  have E : A M k ∩ A M k' = ∅  := disjoint_disjointed' k k' k_ne_k',
  exact NE.ne_empty E,
end,
have x_mem_Union_k : ∀ {N x}, (x ∈ ⋃ M ≤ N, ⋃ k ≤ N, A M k) → x ∈ ⋃ k ≤ N, A (M N x) k :=
  λ N x h,
    @nat.find_greatest_spec (λ M, x ∈ ⋃ k ≤ N, (A M k)) _ N (
      let ⟨M, hM⟩ := mem_Union.1 (h) in
      let ⟨hM₁, hM₂⟩ := mem_Union.1 hM in
        ⟨M, ⟨hM₁, hM₂⟩⟩),
have x_mem_A : ∀ {N x}, (x ∈ ⋃ M ≤ N, ⋃ k ≤ N, A M k) → x ∈ A (M N x) (k N x) :=
  λ N x h,
    @nat.find_greatest_spec (λ k, x ∈ A (M N x) k) _ N (
      let ⟨k, hk⟩ := mem_Union.1 (x_mem_Union_k h) in
      let ⟨hk₁, hk₂⟩ := mem_Union.1 hk in
        ⟨k, ⟨hk₁, hk₂⟩⟩),
have x_mem_A' : ∀ {N x}, (x ∈ ⋃ M ≤ N, ⋃ k ≤ N, A M k) → x ∈ A' (M N x) (k N x) :=
  λ N x h, mem_of_subset_of_mem (inter_subset_left _ _) (x_mem_A h),
-- prove that for all N, (F N) has finite range
have F_finite : ∀ {N}, finite (range (F N)) :=
begin
  assume N, apply finite_range_ite,
  { rw range_comp, exact finite_range_find_greatest.image _ },
  { exact finite_range_const }
end,
-- prove that for all N, (F N) is a measurable function
have F_measurable : ∀ {N}, measurable (F N) :=
begin
  assume N, refine measurable.piecewise _ _ measurable_const,
  show is_measurable (⋃ (M : ℕ) (H : M ≤ N) (k : ℕ) (H : k ≤ N), A M k),
  { simp [is_measurable.Union, is_measurable.Union_Prop, is_measurable_A] },
  show measurable (λ x, e (k N x)),
  refine  measurable_from_nat.comp (measurable_find_greatest _),
  assume k' k'_le_N, by_cases k'_eq_0 : k' = 0,
  -- if k' = 0
  have : {x | k N x = 0} = (⋃ (M : ℕ) (H : M ≤ N) (k : ℕ) (H : k ≤ N), A M k)ᶜ ∪
                    (⋃ (m ≤ N), A m 0 \ ⋃ m' (hmm' : m < m') (hm'N : m' ≤ N) (k ≤ N), A m' k),
  { ext, split,
    { rw [mem_set_of_eq, mem_union_eq, or_iff_not_imp_left, mem_compl_eq, not_not_mem],
      assume k_eq_0 x_mem,
      simp only [not_exists, exists_prop, mem_Union, not_and, mem_diff],
      refine ⟨M N x, ⟨nat.find_greatest_le, ⟨by { rw ← k_eq_0, exact x_mem_A x_mem} , _⟩⟩⟩,
      assume m hMm hmN k k_le_N,
      have := nat.find_greatest_is_greatest _ m ⟨hMm, hmN⟩,
      { simp only [not_exists, exists_prop, mem_Union, not_and] at this, exact this k k_le_N },
      { exact ⟨M N x, ⟨nat.find_greatest_le, x_mem_Union_k x_mem⟩⟩ } },
    { simp only [mem_set_of_eq, mem_union_eq, mem_compl_eq],
      by_cases x_mem : (x ∉ ⋃ (M : ℕ) (H : M ≤ N) (k : ℕ) (H : k ≤ N), A M k),
      { intro, apply find_greatest_eq_zero, assume k k_le_N hx,
        have : x ∈ ⋃ (M : ℕ) (H : M ≤ N) (k : ℕ) (H : k ≤ N), A M k,
          { simp only [mem_Union], use [M N x, nat.find_greatest_le, k, k_le_N, hx] },
        contradiction },
      { rw not_not_mem at x_mem, assume h, cases h, contradiction,
        simp only [not_exists, exists_prop, mem_Union, not_and, mem_diff] at h,
        rcases h with ⟨m, ⟨m_le_N, ⟨hx, hm⟩⟩⟩,
        by_cases m_lt_M : m < M N x,
        { have := hm (M N x) m_lt_M nat.find_greatest_le (k N x) nat.find_greatest_le,
          have := x_mem_A x_mem,
          contradiction },
        rw not_lt at m_lt_M, by_cases m_gt_M : m > M N x,
        { have := nat.find_greatest_is_greatest _ m ⟨m_gt_M, m_le_N⟩,
          { have : x ∈ ⋃ k ≤ N, A m k,
            { exact mem_bUnion (nat.zero_le N) hx },
            contradiction },
          { exact ⟨m, m_le_N, mem_bUnion (nat.zero_le _) hx⟩ } },
        rw not_lt at m_gt_M, have M_eq_m := le_antisymm m_lt_M m_gt_M,
        rw ← k'_eq_0, exact k_unique ⟨x_mem_A x_mem, by { rw [k'_eq_0, M_eq_m], exact hx }⟩ } } },
  -- end of `have`
  rw [k'_eq_0, this], apply is_measurable.union,
  { apply is_measurable.compl,
    simp [is_measurable.Union, is_measurable.Union_Prop, is_measurable_A] },
  { simp [is_measurable.Union, is_measurable.Union_Prop, is_measurable.diff, is_measurable_A] },
  -- if k' ≠ 0
  have : {x | k N x = k'} = ⋃(m ≤ N), A m k' \ ⋃m' (hmm' : m < m') (hm'N : m' ≤ N) (k ≤ N), A m' k,
  { ext, split,
    { rw [mem_set_of_eq],
      assume k_eq_k',
      have x_mem : x ∈ ⋃ (M : ℕ) (H : M ≤ N) (k : ℕ) (H : k ≤ N), A M k,
      { have := find_greatest_of_ne_zero k_eq_k' k'_eq_0,
        simp only [mem_Union], use [M N x, nat.find_greatest_le, k', k'_le_N, this] },
      simp only [not_exists, exists_prop, mem_Union, not_and, mem_diff],
      refine ⟨M N x, ⟨nat.find_greatest_le, ⟨by { rw ← k_eq_k', exact x_mem_A x_mem} , _⟩⟩⟩,
      assume m hMm hmN k k_le_N,
      have := nat.find_greatest_is_greatest _ m ⟨hMm, hmN⟩,
        { simp only [not_exists, exists_prop, mem_Union, not_and] at this, exact this k k_le_N },
      exact ⟨M N x, ⟨nat.find_greatest_le, x_mem_Union_k x_mem⟩⟩ },
    { simp only [mem_set_of_eq, mem_union_eq, mem_compl_eq], assume h,
      have x_mem : x ∈ ⋃ (M : ℕ) (H : M ≤ N) (k : ℕ) (H : k ≤ N), A M k,
        { simp only [not_exists, exists_prop, mem_Union, not_and, mem_diff] at h,
          rcases h with ⟨m, hm, hx, _⟩,
          simp only [mem_Union], use [m, hm,  k', k'_le_N, hx] },
      simp only [not_exists, exists_prop, mem_Union, not_and, mem_diff] at h,
      rcases h with ⟨m, ⟨m_le_N, ⟨hx, hm⟩⟩⟩,
      by_cases m_lt_M : m < M N x,
      { have := hm (M N x) m_lt_M nat.find_greatest_le (k N x) nat.find_greatest_le,
        have := x_mem_A x_mem,
        contradiction },
      rw not_lt at m_lt_M, by_cases m_gt_M : m > M N x,
      { have := nat.find_greatest_is_greatest _ m ⟨m_gt_M, m_le_N⟩,
        have : x ∈ ⋃ k ≤ N, A m k := mem_bUnion k'_le_N hx,
        contradiction,
        { simp only [mem_Union], use [m, m_le_N, k', k'_le_N, hx] }},
      rw not_lt at m_gt_M, have M_eq_m := le_antisymm m_lt_M m_gt_M,
      exact k_unique ⟨x_mem_A x_mem, by { rw M_eq_m, exact hx }⟩ } },
  -- end of `have`
  rw this, simp [is_measurable.Union, is_measurable.Union_Prop, is_measurable.diff, is_measurable_A]
end,
-- start of proof
⟨λ N, ⟨F N, λ x, F_measurable (is_measurable_singleton _), F_finite⟩,
-- The pointwise convergence part of the theorem
λ x, ⟨metric.tendsto_at_top.2 $ λ ε hε, classical.by_cases
--first case : f x = 0
( assume fx_eq_0 : f x = 0,
  have x_not_mem_A' : ∀ {M k}, x ∉ A' M k := λ M k,
  begin
    simp only [mem_preimage, fx_eq_0, metric.mem_ball, one_div_eq_inv, norm_zero,
               not_and, not_lt, add_comm, not_le, dist_zero_right, mem_diff],
    assume h, rw add_comm, exact inv_pos_of_nat
  end,
  have x_not_mem_A  : ∀ {M k}, x ∉ A M k :=
    by { assume M k h, have := disjointed_subset h, exact absurd this x_not_mem_A' },
  have F_eq_0 : ∀ {N}, F N x = 0 := λ N, by simp [F, if_neg, mem_Union, x_not_mem_A],
  -- end of `have`
  ⟨0, λ n hn, show dist (F n x) (f x) < ε, by {rw [fx_eq_0, F_eq_0, dist_self], exact hε}⟩ )
--second case : f x ≠ 0
( assume fx_ne_0 : f x ≠ 0,
  let ⟨N₀, hN⟩ := exists_nat_one_div_lt (lt_min (norm_pos_iff.2 fx_ne_0) hε) in
  have norm_fx_gt : _ := (lt_min_iff.1 hN).1,
  have ε_gt : _ := (lt_min_iff.1 hN).2,
  have x_mem_Union_k_N₀ : x ∈ ⋃ k, A N₀ k :=
    let ⟨k, hk⟩ := mem_closure_range_iff_nat.1 (by { rw E_dense, exact mem_univ (f x) }) N₀ in
    begin
      rw [Union_disjointed, mem_Union], use k,
      rw [mem_preimage], simp, rw [← one_div_eq_inv],
      exact ⟨hk, le_of_lt norm_fx_gt⟩
    end,
  let ⟨k₀, x_mem_A⟩ := mem_Union.1 x_mem_Union_k_N₀ in
  let n := max N₀ k₀ in
  have x_mem_Union_Union : ∀ {N} (hN : n ≤ N), x ∈ ⋃ M ≤ N, ⋃ k ≤ N, A M k := assume N hN,
    mem_Union.2
      ⟨N₀, mem_Union.2
        ⟨le_trans (le_max_left _ _) hN, mem_Union.2
          ⟨k₀, mem_Union.2 ⟨le_trans (le_max_right _ _) hN, x_mem_A⟩⟩⟩⟩,
  have FN_eq : ∀ {N} (hN : n ≤ N), F N x = e (k N x) := assume N hN, if_pos $ x_mem_Union_Union hN,
  -- start of proof
  ⟨n, assume N hN,
  have N₀_le_N : N₀ ≤ N := le_trans (le_max_left _ _) hN,
  have k₀_le_N : k₀ ≤ N := le_trans (le_max_right _ _) hN,
  show dist (F N x) (f x) < ε, from
  calc
    dist (F N x) (f x) = dist (e (k N x)) (f x) : by rw FN_eq hN
    ... < 1 / ((M N x : ℝ) + 1) :
    begin
      have := x_mem_A' (x_mem_Union_Union hN),
      rw [mem_preimage, mem_diff, metric.mem_ball, dist_comm] at this, exact this.1
    end
    ... ≤ 1 / ((N₀ : ℝ) + 1)  :
    @one_div_le_one_div_of_le _ _  ((N₀ : ℝ) + 1) ((M N x : ℝ) + 1) (nat.cast_add_one_pos N₀)
    (add_le_add_right (nat.cast_le.2 (nat.le_find_greatest N₀_le_N (mem_bUnion k₀_le_N x_mem_A))) 1)
    ... < ε : ε_gt ⟩ ),
-- second part of the theorem
assume N, show ∥F N x∥ ≤ ∥f x∥ + ∥f x∥, from
classical.by_cases
( assume h : x ∈ ⋃ M ≤ N, ⋃ k ≤ N, A M k,
  calc
    ∥F N x∥ = dist (F N x) 0 : by simp
    ... = dist (e (k N x)) 0 : begin simp only [F], rw if_pos h end
    ... ≤ dist (e (k N x)) (f x) + dist (f x) 0 : dist_triangle _ _ _
    ... = dist (e (k N x)) (f x) + ∥f x∥ : by simp
    ... ≤ 1 / ((M N x : ℝ) + 1) + ∥f x∥ :
      le_of_lt $ add_lt_add_right (dist_ek_fx (x_mem_A h)) _
    ... ≤ ∥f x∥ + ∥f x∥ : add_le_add_right (norm_fx (x_mem_A h) ) _)
( assume h : x ∉ ⋃ M ≤ N, ⋃ k ≤ N, A M k,
  have F_eq_0 : F N x = 0 := if_neg h,
  by { simp only [F_eq_0, norm_zero], exact add_nonneg (norm_nonneg _) (norm_nonneg _) } )⟩⟩

lemma simple_func_sequence_tendsto' {μ : measure α} {f : α → β} (hfm : measurable f)
  (hfi : integrable f μ) :
    ∃ (F : ℕ → (α →ₛ β)), (∀n, integrable (F n) μ) ∧
   tendsto (λ n, ∫⁻ x,  nndist (F n x) (f x) ∂μ) at_top (𝓝 0) :=
let ⟨F, hF⟩ := simple_func_sequence_tendsto hfm in
let G : ℕ → α → ennreal := λn x, nndist (F n x) (f x) in
let g : α → ennreal := λx, nnnorm (f x) + nnnorm (f x) + nnnorm (f x) in
have hF_meas : ∀ n, measurable (G n) := λ n, measurable.comp measurable_coe $
  (F n).measurable.nndist hfm,
have hg_meas : measurable g := measurable.comp measurable_coe $ measurable.add
  (measurable.add hfm.nnnorm hfm.nnnorm) hfm.nnnorm,
have h_bound : ∀ n, G n ≤ᵐ[μ] g := λ n, ae_of_all _ $ λ x, coe_le_coe.2 $
  calc
    nndist (F n x) (f x) ≤ nndist (F n x) 0 + nndist 0 (f x) : nndist_triangle _ _ _
    ... = nnnorm (F n x) + nnnorm (f x) : by simp [nndist_eq_nnnorm]
    ... ≤ nnnorm (f x) + nnnorm (f x) + nnnorm (f x) :
      by { simp [nnreal.coe_le_coe.symm, (hF x).2, add_comm] },
have h_finite : ∫⁻ x, g x ∂μ < ⊤ :=
  calc
    ∫⁻ x, nnnorm (f x) + nnnorm (f x) + nnnorm (f x) ∂μ =
      ∫⁻ x, nnnorm (f x) ∂μ + ∫⁻ x, nnnorm (f x) ∂μ + ∫⁻ x, nnnorm (f x) ∂μ :
    by { rw [lintegral_add, lintegral_nnnorm_add],
      exacts [hfm, hfm, hfm.ennnorm.add hfm.ennnorm, hfm.ennnorm] }
    ... < ⊤ : by { simp only [and_self, add_lt_top], exact hfi},
have h_lim : ∀ᵐ x ∂μ, tendsto (λ n, G n x) at_top (𝓝 0) := ae_of_all _ $ λ x,
  begin
    apply (@tendsto_coe ℕ at_top (λ n, nndist (F n x) (f x)) 0).2,
    apply (@nnreal.tendsto_coe ℕ at_top (λ n, nndist (F n x) (f x)) 0).1,
    apply tendsto_iff_dist_tendsto_zero.1 (hF x).1
  end,
begin
  use F, split,
  { assume n,
    calc
      ∫⁻ a, nnnorm (F n a) ∂μ ≤ ∫⁻ a, nnnorm (f a) + nnnorm (f a) ∂μ :
        lintegral_mono
          (by { assume a, simp only [coe_add.symm, coe_le_coe], exact (hF a).2 n })
       ... = ∫⁻ a, nnnorm (f a) ∂μ + ∫⁻ a, nnnorm (f a) ∂μ :
         lintegral_nnnorm_add hfm hfm
       ... < ⊤ : by simp only [add_lt_top, and_self]; exact hfi },
  convert tendsto_lintegral_of_dominated_convergence g hF_meas h_bound h_finite h_lim,
  simp only [lintegral_zero]
end

end measure_theory
