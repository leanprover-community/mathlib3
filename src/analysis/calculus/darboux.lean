/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.calculus.deriv.add
import analysis.calculus.deriv.mul
import analysis.calculus.local_extr.basic

/-!
# Darboux's theorem

In this file we prove that the derivative of a differentiable function on an interval takes all
intermediate values. The proof is based on the
[Wikipedia](https://en.wikipedia.org/wiki/Darboux%27s_theorem_(analysis)) page about this theorem.
-/

open filter set
open_locale topology classical

variables {a b : ℝ} {f f' : ℝ → ℝ}

/-- **Darboux's theorem**: if `a ≤ b` and `f' a < m < f' b`, then `f' c = m` for some
`c ∈ (a, b)`. -/
theorem exists_has_deriv_within_at_eq_of_gt_of_lt
  (hab : a ≤ b) (hf : ∀ x ∈ (Icc a b), has_deriv_within_at f (f' x) (Icc a b) x)
  {m : ℝ} (hma : f' a < m) (hmb : m < f' b) :
  m ∈ f' '' Ioo a b :=
begin
  rcases hab.eq_or_lt with rfl | hab',
  { exact (lt_asymm hma hmb).elim },
  set g : ℝ → ℝ := λ x, f x - m * x,
  have hg : ∀ x ∈ Icc a b, has_deriv_within_at g (f' x - m) (Icc a b) x,
  { intros x hx,
    simpa using (hf x hx).sub ((has_deriv_within_at_id x _).const_mul m) },
  obtain ⟨c, cmem, hc⟩ : ∃ c ∈ Icc a b, is_min_on g (Icc a b) c,
    from is_compact_Icc.exists_forall_le (nonempty_Icc.2 $ hab)
      (λ x hx, (hg x hx).continuous_within_at),
  have cmem' : c ∈ Ioo a b,
  { rcases cmem.1.eq_or_lt with rfl | hac,
    -- Show that `c` can't be equal to `a`
    { refine absurd (sub_nonneg.1 $ nonneg_of_mul_nonneg_right _ (sub_pos.2 hab'))
        (not_le_of_lt hma),
      have : b - a ∈ pos_tangent_cone_at (Icc a b) a,
        from mem_pos_tangent_cone_at_of_segment_subset (segment_eq_Icc hab ▸ subset.refl _),
      simpa [-sub_nonneg, -continuous_linear_map.map_sub]
        using hc.localize.has_fderiv_within_at_nonneg (hg a (left_mem_Icc.2 hab)) this },
    rcases cmem.2.eq_or_gt with rfl | hcb,
    -- Show that `c` can't be equal to `b`
    { refine absurd (sub_nonpos.1 $ nonpos_of_mul_nonneg_right _ (sub_lt_zero.2 hab'))
        (not_le_of_lt hmb),
      have : a - b ∈ pos_tangent_cone_at (Icc a b) b,
        from mem_pos_tangent_cone_at_of_segment_subset (by rw [segment_symm, segment_eq_Icc hab]),
      simpa [-sub_nonneg, -continuous_linear_map.map_sub]
        using hc.localize.has_fderiv_within_at_nonneg (hg b (right_mem_Icc.2 hab)) this },
    exact ⟨hac, hcb⟩ },
  use [c, cmem'],
  rw [← sub_eq_zero],
  have : Icc a b ∈ 𝓝 c, by rwa [← mem_interior_iff_mem_nhds, interior_Icc],
  exact (hc.is_local_min this).has_deriv_at_eq_zero ((hg c cmem).has_deriv_at this)
end

/-- **Darboux's theorem**: if `a ≤ b` and `f' b < m < f' a`, then `f' c = m` for some `c ∈ (a, b)`.
-/
theorem exists_has_deriv_within_at_eq_of_lt_of_gt
  (hab : a ≤ b) (hf : ∀ x ∈ (Icc a b), has_deriv_within_at f (f' x) (Icc a b) x)
  {m : ℝ} (hma : m < f' a) (hmb : f' b < m) :
  m ∈ f' '' Ioo a b :=
let ⟨c, cmem, hc⟩ := exists_has_deriv_within_at_eq_of_gt_of_lt hab (λ x hx, (hf x hx).neg)
  (neg_lt_neg hma) (neg_lt_neg hmb)
in ⟨c, cmem, neg_injective hc⟩

/-- **Darboux's theorem**: the image of an `ord_connected` set under `f'` is an `ord_connected`
set, `has_deriv_within_at` version. -/
theorem set.ord_connected.image_has_deriv_within_at {s : set ℝ} (hs : ord_connected s)
  (hf : ∀ x ∈ s, has_deriv_within_at f (f' x) s x) :
  ord_connected (f' '' s) :=
begin
  apply ord_connected_of_Ioo,
  rintros _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ - m ⟨hma, hmb⟩,
  cases le_total a b with hab hab,
  { have : Icc a b ⊆ s, from hs.out ha hb,
    rcases exists_has_deriv_within_at_eq_of_gt_of_lt hab
      (λ x hx, (hf x $ this hx).mono this) hma hmb
      with ⟨c, cmem, hc⟩,
    exact ⟨c, this $ Ioo_subset_Icc_self cmem, hc⟩ },
  { have : Icc b a ⊆ s, from hs.out hb ha,
    rcases exists_has_deriv_within_at_eq_of_lt_of_gt hab
      (λ x hx, (hf x $ this hx).mono this) hmb hma
      with ⟨c, cmem, hc⟩,
    exact ⟨c, this $ Ioo_subset_Icc_self cmem, hc⟩ }
end

/-- **Darboux's theorem**: the image of an `ord_connected` set under `f'` is an `ord_connected`
set, `deriv_within` version. -/
theorem set.ord_connected.image_deriv_within {s : set ℝ} (hs : ord_connected s)
  (hf : differentiable_on ℝ f s) :
  ord_connected (deriv_within f s '' s) :=
hs.image_has_deriv_within_at $ λ x hx, (hf x hx).has_deriv_within_at

/-- **Darboux's theorem**: the image of an `ord_connected` set under `f'` is an `ord_connected`
set, `deriv` version. -/
theorem set.ord_connected.image_deriv {s : set ℝ} (hs : ord_connected s)
  (hf : ∀ x ∈ s, differentiable_at ℝ f x) :
  ord_connected (deriv f '' s) :=
hs.image_has_deriv_within_at $ λ x hx, (hf x hx).has_deriv_at.has_deriv_within_at

/-- **Darboux's theorem**: the image of a convex set under `f'` is a convex set,
`has_deriv_within_at` version. -/
theorem convex.image_has_deriv_within_at {s : set ℝ} (hs : convex ℝ s)
  (hf : ∀ x ∈ s, has_deriv_within_at f (f' x) s x) :
  convex ℝ (f' '' s) :=
(hs.ord_connected.image_has_deriv_within_at hf).convex

/-- **Darboux's theorem**: the image of a convex set under `f'` is a convex set,
`deriv_within` version. -/
theorem convex.image_deriv_within {s : set ℝ} (hs : convex ℝ s)
  (hf : differentiable_on ℝ f s) :
  convex ℝ (deriv_within f s '' s) :=
(hs.ord_connected.image_deriv_within hf).convex

/-- **Darboux's theorem**: the image of a convex set under `f'` is a convex set,
`deriv` version. -/
theorem convex.image_deriv {s : set ℝ} (hs : convex ℝ s)
  (hf : ∀ x ∈ s, differentiable_at ℝ f x) :
  convex ℝ (deriv f '' s) :=
(hs.ord_connected.image_deriv hf).convex

/-- **Darboux's theorem**: if `a ≤ b` and `f' a ≤ m ≤ f' b`, then `f' c = m` for some
`c ∈ [a, b]`. -/
theorem exists_has_deriv_within_at_eq_of_ge_of_le
  (hab : a ≤ b) (hf : ∀ x ∈ (Icc a b), has_deriv_within_at f (f' x) (Icc a b) x)
  {m : ℝ} (hma : f' a ≤ m) (hmb : m ≤ f' b) :
  m ∈ f' '' Icc a b :=
(ord_connected_Icc.image_has_deriv_within_at hf).out
  (mem_image_of_mem _ (left_mem_Icc.2 hab)) (mem_image_of_mem _ (right_mem_Icc.2 hab)) ⟨hma, hmb⟩

/-- **Darboux's theorem**: if `a ≤ b` and `f' b ≤ m ≤ f' a`, then `f' c = m` for some
`c ∈ [a, b]`. -/
theorem exists_has_deriv_within_at_eq_of_le_of_ge
  (hab : a ≤ b) (hf : ∀ x ∈ (Icc a b), has_deriv_within_at f (f' x) (Icc a b) x)
  {m : ℝ} (hma : f' a ≤ m) (hmb : m ≤ f' b) :
  m ∈ f' '' Icc a b :=
(ord_connected_Icc.image_has_deriv_within_at hf).out
  (mem_image_of_mem _ (left_mem_Icc.2 hab)) (mem_image_of_mem _ (right_mem_Icc.2 hab)) ⟨hma, hmb⟩

/-- If the derivative of a function is never equal to `m`, then either
it is always greater than `m`, or it is always less than `m`. -/
theorem has_deriv_within_at_forall_lt_or_forall_gt_of_forall_ne {s : set ℝ} (hs : convex ℝ s)
  (hf : ∀ x ∈ s, has_deriv_within_at f (f' x) s x) {m : ℝ} (hf' : ∀ x ∈ s, f' x ≠ m) :
  (∀ x ∈ s, f' x < m) ∨ (∀ x ∈ s, m < f' x) :=
begin
  contrapose! hf',
  rcases hf' with ⟨⟨b, hb, hmb⟩, ⟨a, ha, hma⟩⟩,
  exact (hs.ord_connected.image_has_deriv_within_at hf).out (mem_image_of_mem f' ha)
    (mem_image_of_mem f' hb) ⟨hma, hmb⟩
end
