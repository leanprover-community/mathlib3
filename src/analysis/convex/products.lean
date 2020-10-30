import analysis.convex.basic
import analysis.normed_space.basic

/-! Assorted convexity lemmas, maybe not worth cleaning up or PR'ing given the refactor-in-progress
of the convexity library. -/

open_locale big_operators
open set
variables {E : Type*} {F : Type*}

section products
variables [add_comm_group E] [vector_space ℝ E] [add_comm_group F] [vector_space ℝ F]

/-- The product of convex subsets of `E`, `F` respectively is a convex subset of `E × F`. -/
lemma prod_convex {s : set E} {t : set F} (hs : convex s) (ht : convex t) :
  convex (s.prod t) :=
begin
  intros x y hx hy a b ha hb hab,
  split,
  { exact hs hx.1 hy.1 ha hb hab },
  { exact ht hx.2 hy.2 ha hb hab }
end

/-- The product of the convex hulls of two sets is the convex hull of their product. -/
lemma prod_convex_hull (s : set E) (t : set F) :
  convex_hull (s.prod t) = (convex_hull s).prod (convex_hull t) :=
begin
  ext p,
  split,
  { simp only [mem_Inter, mem_prod, convex_hull],
    intros hp,
    split,
    { intros s' hss' hs',
      have h : convex (s'.prod (convex_hull t)) := prod_convex hs' (convex_convex_hull t),
      exact (hp (s'.prod (convex_hull t)) (prod_mono hss' (subset_convex_hull t)) h).1 },
    { intros t' htt' ht',
      have h : convex ((convex_hull s).prod t') := prod_convex (convex_convex_hull s) ht',
      exact (hp ((convex_hull s).prod t') (prod_mono (subset_convex_hull s) htt') h).2 } },
  { rintros ⟨hs, ht⟩ K ⟨L, rfl⟩,
    rw convex_hull_eq at hs ht,
    obtain ⟨ι, a, w, S, hw, hw', hS, hSp⟩ := hs,
    obtain ⟨γ, b, v, T, hv, hv', hT, hTp⟩ := ht,
    have h_sum : ∑ (i : ι × γ) in a.product b, w i.fst * v i.snd = 1,
    { rw finset.sum_product,
      rw ← hw',
      congr,
      ext i,
      have : ∑ (y : γ) in b, w i * v y = ∑ (y : γ) in b, v y * w i,
      { congr, ext, simp [mul_comm] },
      rw this,
      rw ← finset.sum_mul,
      rw hv',
      simp },
    simp only [mem_Inter],
    intros hstL hL,
    apply convex_hull_min hstL hL,
    rw convex_hull_eq,
    use ι × γ,
    use a.product b,
    use λ p, (w p.1) * (v p.2),
    refine ⟨λ p, (S p.1, T p.2), _, _, _, _⟩,
    { intros p hp,
      rw finset.mem_product at hp,
      exact mul_nonneg (hw p.1 hp.1) (hv p.2 hp.2) },
    { exact h_sum },
    { intros p hp,
      rw finset.mem_product at hp,
      split,
      exact hS p.1 hp.1,
      exact hT p.2 hp.2 },
    { ext,
      { rw ← hSp,
        simp only [finset.center_mass],
        rw hw',
        rw h_sum,
        simp only [prod.fst_sum, prod.smul_mk, one_smul, inv_one],
        rw finset.sum_product,
        congr,
        ext i,
        have : ∑ (y : γ) in b, (w (i, y).fst * v (i, y).snd) • S (i, y).fst
          = ∑ (y : γ) in b, (v (i, y).snd) • (w (i, y).fst) • S (i, y).fst,
        { congr, ext, simp only [← mul_smul], congr' 1, exact mul_comm _ _ },
        rw this,
        simp only,
        rw ← finset.sum_smul,
        rw hv',
        simp },
      { -- same as the other case
        sorry } } }
end

end products

section normed_space

variables [normed_group E] [normed_space ℝ E]

lemma norm_convex : convex_on univ (norm : E → ℝ) :=
begin
  refine ⟨convex_univ, _⟩,
  intros x y hx hy a b ha hb hab,
  calc ∥a • x + b • y∥ ≤ ∥a • x∥ + ∥b • y∥ : norm_add_le _ _
  ... = a * ∥x∥ + b * ∥y∥ : by { congr; simp [norm_smul, real.norm_of_nonneg, *] }
end

theorem nonempty.product {s t : finset E} : s.nonempty → t.nonempty → (s.product t).nonempty :=
λ ⟨x, hx⟩ ⟨y, hy⟩, ⟨(x,y), by simp [hx, hy]⟩

noncomputable def max_dist (s : finset E) (h : s.nonempty) : ℝ :=
finset.max'
  (finset.image (λ p : E × E, norm (p.1 - p.2)) (s.product s))
  (finset.nonempty.image (nonempty.product h h) _)

/-- Among the pairs of points in the convex hull of `s`, the maximum distance apart is attained by
two points actually in `s`. -/
lemma foo5 (s : finset E) (h : s.nonempty)
  (z w : E) (hz: z ∈ convex_hull (↑s : set E)) (hw: w ∈ convex_hull (↑s : set E)) :
  dist z w
  ≤ max_dist s h :=
begin
  /- HM -/
  -- Introduce the map `diff`, defined as `⟨z, w⟩ ↦ z - w`, with this considered as an `ℝ`-linear
  -- map from `ℂ × ℂ → ℂ`.
  let diff : E × E →ₗ[ℝ] E :=
     (linear_map.fst ℝ E E) - (linear_map.snd ℝ E E),
  -- notice that `dist` is the composition of the convex function `norm` and the linear function `diff`.
  -- also notice that the domain of consideration, `s × s`, is equal
  -- to the convex hull of the 9 points in `s × s`.  This relies on the
  -- new lemma `prod_convex_hull` (above).
  suffices h' : ∀ p ∈ convex_hull ((↑s : set E).prod (↑s : set E)), (norm ∘ diff) p ≤ max_dist s h,
  { convert h' ⟨z, w⟩ _,
    { simp [dist_eq_norm] },
    rw prod_convex_hull,
    exact ⟨hz, hw⟩ },
  -- let `p` be a point in the convex hull of `s × s`.  Rewrite as a linear
  -- combination of points in `s × s`.
  intros p hp,
  rw convex_hull_eq at hp,
  obtain ⟨ι, ind, ρ, q, hρ₀, hρ₁, hq, hqp⟩ := hp,
  rw ← hqp,
  have h_pos : 0 < ∑ a in ind, ρ a,
  { rw hρ₁,
    norm_num },
  have h_in : ∀ (a : ι), a ∈ ind → q a ∈ convex_hull ((↑s : set E).prod (↑s : set E)),
  { intros a ha,
    exact subset_convex_hull _ (hq a ha) },
  -- by general theory, the function `norm ∘ diff` is convex, and in particular is convex on the set
  -- we consider.
  have convex_on_diff : convex_on (convex_hull ((↑s : set E).prod (↑s : set E))) (norm ∘ diff),
  { exact (norm_convex.comp_linear_map diff).subset subset_preimage_univ (convex_convex_hull _) },
  -- so it attains its maximum (over the convex hull of `s × s`) at one of
  -- the finitely many points in `s × s`.  Let `q a` be this point.
  obtain ⟨a, ha, haT⟩ := convex_on_diff.exists_ge_of_center_mass hρ₀ h_pos h_in,
  refine le_trans haT _,
  refine finset.le_max' _ _ _,
  rw finset.mem_image,
  refine ⟨q a, _, rfl⟩,
  rw finset.mem_product,
  exact hq a ha
end


end normed_space
