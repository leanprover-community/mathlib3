import analysis.convex.basic

open_locale big_operators
open set

variables {E : Type*} {F : Type*}
  [add_comm_group E] [vector_space ℝ E] [add_comm_group F] [vector_space ℝ F]

lemma prod_convex {s : set E} {t : set F} (hs : convex s) (ht : convex t) :
  convex (s.prod t) :=
begin
  intros x y hx hy a b ha hb hab,
  split,
  { exact hs hx.1 hy.1 ha hb hab },
  { exact ht hx.2 hy.2 ha hb hab }
end

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
