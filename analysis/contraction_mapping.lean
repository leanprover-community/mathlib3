/-
Copyright (c) 2018 Rohan Mitta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Mitta, Kevin Buzzard, Alistair Tucker
-/
import analysis.limits analysis.normed_space
open nat filter

lemma fixed_point_of_iteration_limit {α : Type*} [topological_space α] [t2_space α] {f : α → α}
  {x : α} : continuous f → (∃ x₀ : α, tendsto (λ n, f ^[n] x₀) at_top (nhds x)) → x = f x :=
begin
  intros hf hx,
  cases hx with x₀ hx,
  apply @tendsto_nhds_unique α ℕ _ _ (λ n, f ^[succ n] x₀) at_top x (f x),
  { exact at_top_ne_bot },
  { rewrite @tendsto_comp_succ_at_top_iff α (λ n, f ^[n] x₀) (nhds x),
    exact hx },
  { rewrite funext (λ n, iterate_succ' f n x₀),
    exact tendsto.comp hx (continuous.tendsto hf x) },
end

def lipschitz {α : Type*} [metric_space α] (K : ℝ) (f : α → α) :=
0 ≤ K ∧ ∀ (x y : α), dist (f x) (f y) ≤ K * (dist x y)

lemma uniform_continuous_of_lipschitz {α : Type*} [metric_space α] {K : ℝ} {f : α → α} :
  lipschitz K f → uniform_continuous f :=
λ hf, uniform_continuous_of_metric.mpr (λ ε hε, or.elim (lt_or_le K ε)
  (λ h, ⟨(1 : ℝ), zero_lt_one, (λ x y hd, lt_of_le_of_lt (hf.right x y)
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_left (le_of_lt hd) hf.left) (symm (mul_one K) ▸ h)))⟩)
  (λ h, ⟨ε / K, div_pos_of_pos_of_pos hε (lt_of_lt_of_le hε h),
    (λ x y hd, lt_of_le_of_lt (hf.right x y)
      (mul_comm (dist x y) K ▸ mul_lt_of_lt_div (lt_of_lt_of_le hε h) hd))⟩))

lemma iterated_lipschitz_of_lipschitz {α : Type*} [metric_space α] {K : ℝ} {f : α → α} :
   lipschitz K f → ∀ (n : ℕ), lipschitz (K ^n) (f ^[n]) :=
begin
  intros hf n,
  induction n with n ih,
  { apply and.intro,
    { exact pow_zero K ▸ zero_le_one, },
    { intros x y,
      rewrite [pow_zero K, one_mul, iterate_zero f x, iterate_zero f y], }, },
  { apply and.intro,
    { exact mul_nonneg hf.left ih.left, },
    { intros x y,
      rewrite [iterate_succ', iterate_succ'],
      apply le_trans (hf.right (f ^[n] x) (f ^[n] y)),
      rewrite [pow_succ K n, mul_assoc],
      exact mul_le_mul_of_nonneg_left (ih.right x y) hf.left, }, },
end

lemma dist_inequality_of_contraction {α : Type*} [metric_space α] {K : ℝ} {f : α → α} (hK₁ : K < 1) :
  lipschitz K f → ∀ (x y : α), dist x y ≤ (dist x (f x) + dist y (f y)) / (1 - K) :=
begin
  intros hf x y,
  apply le_div_of_mul_le (sub_pos_of_lt hK₁),
  rewrite [mul_comm, sub_mul, one_mul],
  apply sub_left_le_of_le_add,
  apply le_trans,
    exact dist_triangle_right x y (f x),
  apply le_trans,
    apply add_le_add_left,
    exact dist_triangle_right y (f x) (f y),
  rewrite [←add_assoc, add_comm],
  apply add_le_add_right,
  exact hf.right x y,
end

theorem fixed_point_unique_of_contraction {α : Type*} [metric_space α] {K : ℝ} {f : α → α} :
  K < 1 → lipschitz K f → ∀ (x : α), x = f x → ∀ (y : α), y = f y → x = y :=
begin
  intros hK₁ hf x hx y hy,
  apply iff.mp dist_le_zero,
  apply le_trans,
  exact dist_inequality_of_contraction hK₁ hf x y,
  rewrite [iff.mpr dist_eq_zero hx, iff.mpr dist_eq_zero hy],
  norm_num,
end

lemma dist_bound_of_contraction {α : Type*} [metric_space α] {K : ℝ} {f : α → α} :
  K < 1 → lipschitz K f → ∀ (x₀ : α) (n : ℕ × ℕ),
  dist (f ^[n.1] x₀) (f ^[n.2] x₀) ≤ (K ^n.1 + K ^n.2) * dist x₀ (f x₀) / (1 - K) :=
begin
  intros hK₁ hf x₀ n,
  apply le_trans,
  exact dist_inequality_of_contraction hK₁ hf (f ^[n.1] x₀) (f ^[n.2] x₀),
  apply div_le_div_of_le_of_pos _ (sub_pos_of_lt hK₁),
  have h : ∀ (m : ℕ), dist (f ^[m] x₀) (f (f ^[m] x₀)) ≤ K ^m * dist x₀ (f x₀),
    intro m,
    rewrite [←iterate_succ' f m x₀, iterate_succ f m x₀],
    exact and.right (iterated_lipschitz_of_lipschitz hf m) x₀ (f x₀),
  rewrite add_mul,
  apply add_le_add,
  { exact h n.1, },
  { exact h n.2, },
end

section prod
  open lattice

  local attribute [instance]
  def prod_has_le {β₁ β₂ : Type*} [has_le β₁] [has_le β₂] : has_le (prod β₁ β₂) :=
  { le            := λ m n, m.1 ≤ n.1 ∧ m.2 ≤ n.2 }

  local attribute [instance]
  def prod_partial_order {β₁ β₂ : Type*} [partial_order β₁] [partial_order β₂] :
    partial_order (prod β₁ β₂) :=
  { le_refl       := λ n, ⟨le_refl n.1, le_refl n.2⟩,
    le_trans      := λ k m n h₁ h₂, ⟨le_trans h₁.1 h₂.1, le_trans h₁.2 h₂.2⟩,
    le_antisymm   := λ m n h₁ h₂, prod.ext (le_antisymm h₁.1 h₂.1) (le_antisymm h₁.2 h₂.2),
    .. prod_has_le }

  local attribute [instance]
  def prod_semilattice_sup {β₁ β₂ : Type*} [semilattice_sup β₁] [semilattice_sup β₂] :
    semilattice_sup (β₁ × β₂) :=
  { sup           := λ m n, ⟨m.1 ⊔ n.1, m.2 ⊔ n.2⟩,
    le_sup_left   := λ m n, ⟨le_sup_left, le_sup_left⟩,
    le_sup_right  := λ m n, ⟨le_sup_right, le_sup_right⟩,
    sup_le        := λ k m n h₁ h₂, ⟨sup_le h₁.1 h₂.1, sup_le h₁.2 h₂.2⟩,
    .. prod_partial_order}

  lemma prod_at_top_at_top_eq {β₁ β₂ : Type*} [inhabited β₁] [inhabited β₂] [semilattice_sup β₁]
    [semilattice_sup β₂] : filter.prod (@at_top β₁ _) (@at_top β₂ _) = @at_top (β₁ × β₂) _ :=
  filter.ext (λ s, iff.intro
    (λ h, let ⟨t₁, ht₁, t₂, ht₂, hs⟩ := mem_prod_iff.mp h in
      let ⟨N₁, hN₁⟩ := iff.mp mem_at_top_sets ht₁ in
      let ⟨N₂, hN₂⟩ := iff.mp mem_at_top_sets ht₂ in
      mem_at_top_sets.mpr ⟨⟨N₁, N₂⟩, (λ n hn, hs ⟨hN₁ n.1 hn.1, hN₂ n.2 hn.2⟩)⟩)
    (λ h, let ⟨N, hN⟩ := mem_at_top_sets.mp h in mem_prod_iff.mpr
      ⟨{n₁ | N.1 ≤ n₁}, mem_at_top N.1, {n₂ | N.2 ≤ n₂}, mem_at_top N.2, (λ n hn, hN n hn)⟩))

  lemma prod_map_def {α₁ α₂ β₁ β₂ : Type*} {u₁ : β₁ → α₁} {u₂ : β₂ → α₂} :
    prod.map u₁ u₂ = λ (n : β₁ × β₂), (u₁ n.1, u₂ n.2) :=
  funext (λ n, prod.ext (prod.map_fst u₁ u₂ n) (prod.map_snd u₁ u₂ n))

  lemma prod_filter_map_at_top {α₁ α₂ β₁ β₂ : Type*} [inhabited β₁] [inhabited β₂]
    [semilattice_sup β₁] [semilattice_sup β₂] (u₁ : β₁ → α₁) (u₂ : β₂ → α₂) :
    filter.prod (map u₁ at_top) (map u₂ at_top) = map (prod.map u₁ u₂) at_top :=
  by rw [prod_map_map_eq, prod_at_top_at_top_eq, prod_map_def]

  lemma prod_dist_eq {α β₁ β₂ : Type*} [metric_space α] (u₁ : β₁ → α) (u₂ : β₂ → α) (n : β₁ × β₂) :
    dist (prod.map u₁ u₂ n).1 (prod.map u₁ u₂ n).2 = dist (dist (u₁ n.1) (u₂ n.2)) 0 :=
  by rw [prod.map_fst, prod.map_snd, real.dist_0_eq_abs, abs_of_nonneg dist_nonneg]

  lemma cauchy_seq_iff {α β : Type*} [uniform_space α] [inhabited β] [semilattice_sup β]
    {u : β → α} : cauchy_seq u ↔ map (prod.map u u) at_top ≤ uniformity :=
  iff.trans (and_iff_right (map_ne_bot at_top_ne_bot)) (prod_filter_map_at_top u u ▸ iff.rfl)

  lemma cauchy_seq_iff' {α β : Type*} [metric_space α] [inhabited β] [semilattice_sup β]
    {u : β → α} : cauchy_seq u ↔ tendsto (λ (n : β × β), dist (u n.1) (u n.2)) at_top (nhds 0) :=
  iff.trans cauchy_seq_iff (iff.symm (iff.trans tendsto_nhds_topo_metric
    ⟨(λ h s hs, let ⟨ε, hε, hε'⟩ := mem_uniformity_dist.mp hs in
       let ⟨t, ht, ht'⟩ := h ε hε in mem_map_sets_iff.mpr
         ⟨t, ht, (λ p hp, @prod.mk.eta α α p ▸ hε' (let ⟨n, hn, hn'⟩ := hp in
           show dist p.1 p.2 < ε, from hn' ▸ symm (prod_dist_eq u u n) ▸ ht' n hn))⟩),
     (λ h ε hε, let ⟨s, hs, hs'⟩ := mem_map_sets_iff.mp (h (dist_mem_uniformity hε)) in
       ⟨s, hs, (λ n hn, prod_dist_eq u u n ▸ hs' (set.mem_image_of_mem (prod.map u u) hn))⟩)⟩))

  lemma tendsto_dist_bound_at_top_nhds_0 {K : ℝ} (hK₀ : 0 ≤ K) (hK₁ : K < 1) (z : ℝ) :
    tendsto (λ (n : ℕ × ℕ), (K ^n.1 + K ^n.2) * z / (1 - K)) at_top (nhds 0) :=
  begin
    let f := λ (n : ℕ × ℕ), (K ^n.1, K ^n.2),
    let g := λ (y : ℝ × ℝ), (y.1 + y.2) * z / (1 - K),
    show tendsto (g ∘ f) at_top (nhds 0),
    apply tendsto.comp,
    { show tendsto f at_top (nhds (0, 0)),
      rw ←prod_at_top_at_top_eq,
      apply tendsto_prod_mk_nhds,
      { apply tendsto.comp tendsto_fst,
        exact tendsto_pow_at_top_nhds_0_of_lt_1 hK₀ hK₁, },
      { apply tendsto.comp tendsto_snd,
        exact tendsto_pow_at_top_nhds_0_of_lt_1 hK₀ hK₁, }, },
    { show tendsto g (nhds (0, 0)) (nhds 0),
      have hg : g = λ (y : ℝ × ℝ), z / (1 - K) * (y.1 + y.2),
        ext,
        rewrite [mul_comm, ←mul_div_assoc],
      have hc : continuous g,
        rewrite hg,
        apply continuous.comp,
        exact continuous_add',
        exact continuous_prod_snd continuous_mul',
      have h₀ := continuous.tendsto hc (0, 0),
      suffices h : g (0, 0) = 0,
        rewrite h at h₀,
        exact h₀,
      rewrite hg,
      norm_num, },
  end
end prod

theorem fixed_point_exists_of_contraction {α : Type*} [inhabited α] [metric_space α]
  [complete_space α] {K : ℝ} {f : α → α} : K < 1 → lipschitz K f → ∃ (x : α), x = f x :=
begin
  intros hK₁ hf,
  let x₀ := default α,
  suffices h : cauchy_seq (λ n, f ^[n] x₀),
    cases cauchy_seq_tendsto_of_complete h with x hx,
    use x,
    apply @fixed_point_of_iteration_limit α _,
    { exact uniform_continuous.continuous (uniform_continuous_of_lipschitz hf), },
    { exact ⟨x₀, hx⟩, },
  apply iff.mpr cauchy_seq_iff',
  apply squeeze_zero,
  { intro x,
    exact dist_nonneg, },
  { exact dist_bound_of_contraction hK₁ hf x₀, },
  { exact tendsto_dist_bound_at_top_nhds_0 hf.left hK₁ (dist x₀ (f x₀)), },
end
