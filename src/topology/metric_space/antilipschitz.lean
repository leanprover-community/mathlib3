/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import topology.metric_space.lipschitz

/-!
# Antilipschitz functions

We say that a map `f : α → β` between two (extended) metric spaces is
`antilipschitz_with K`, `K ≥ 0`, if for all `x, y` we have `K * edist x y ≤ edist (f x) (f y)`.
For a metric space, the latter inequality is equivalent to `K * dist x y ≤ dist (f x) (f y)`.

## Implementation notes

The parameter `K` has type `nnreal`. This way we avoid conjuction in the definition and have
coercions both to `ℝ` and `ennreal`. We do not require `0 < K` in the definition, mostly because
we do not have a `posreal` type.
-/

variables {α : Type*} {β : Type*} {γ : Type*}

open_locale nnreal

/-- We say that `f : α → β` is `antilipschitz_with K` if for any two points `x`, `y` we have
`K * edist x y ≤ edist (f x) (f y)`. -/
def antilipschitz_with [emetric_space α] [emetric_space β] (K : ℝ≥0) (f : α → β) :=
∀ x y, ↑K * edist x y ≤ edist (f x) (f y)

lemma antilipschitz_with_iff_mul_dist_le [metric_space α] [metric_space β] {K : ℝ≥0} {f : α → β} :
  antilipschitz_with K f ↔ ∀ x y, ↑K * dist x y ≤ dist (f x) (f y) :=
by { simp only [antilipschitz_with, edist_nndist, dist_nndist], norm_cast }

alias antilipschitz_with_iff_mul_dist_le ↔ antilipschitz_with.mul_dist_le
  antilipschitz_with.of_mul_dist_le

namespace antilipschitz_with

variables [emetric_space α] [emetric_space β] [emetric_space γ] {K : ℝ≥0} {f : α → β}

protected lemma injective (hf : antilipschitz_with K f) (hK : 0 < K) :
  function.injective f :=
begin
  intros x y h,
  have := hf x y,
  rw [h, edist_self, le_zero_iff_eq, ennreal.mul_eq_zero, ennreal.coe_eq_zero, edist_eq_zero] at this,
  exact this.elim (λ hK', absurd hK' (ne_of_gt hK)) id
end

lemma edist_le (hf : antilipschitz_with K f) (hK : 0 < K) (x y) :
  edist x y ≤ K⁻¹ * edist (f x) (f y) :=
begin
  rw [mul_comm, ← ennreal.div_def, ennreal.le_div_iff_mul_le, mul_comm],
  { exact hf x y },
  { exact ne_of_gt (ennreal.coe_pos.2 hK) },
  { exact ennreal.coe_ne_top }
end

lemma id : antilipschitz_with 1 (id : α → α) :=
λ x y, by simp only [ennreal.coe_one, one_mul, id, le_refl]

lemma comp {Kg : ℝ≥0} {g : β → γ} (hg : antilipschitz_with Kg g)
  {Kf : ℝ≥0} {f : α → β} (hf : antilipschitz_with Kf f) :
  antilipschitz_with (Kg * Kf) (g ∘ f) :=
λ x y,
calc ↑(Kg * Kf) * edist x y = Kg * (Kf * edist x y) : by rw [ennreal.coe_mul, mul_assoc]
... ≤ Kg * edist (f x) (f y) : ennreal.mul_left_mono $ hf _ _
... ≤ edist (g (f x)) (g (f y)) : hg _ _

/-- Any function is `antilipschitz_with 0`. -/
protected lemma zero : antilipschitz_with 0 f :=
λ x y, by simp only [ennreal.coe_zero, zero_mul, zero_le]

lemma to_inverse (hf : antilipschitz_with K f) (hK : 0 < K)
  {g : β → α} (hg : function.right_inverse g f) :
  lipschitz_with K⁻¹ g :=
begin
  intros x y,
  have := hf.edist_le hK (g x) (g y),
  rwa [hg x, hg y, ← ennreal.coe_inv (ne_of_gt hK)] at this
end

lemma uniform_embedding (hf : antilipschitz_with K f) (hK : 0 < K) (hfc : uniform_continuous f) :
  uniform_embedding f :=
have hK' : (K : ennreal) ≠ 0 := ne_of_gt (ennreal.coe_pos.2 hK),
by refine emetric.uniform_embedding_iff.2 ⟨hf.injective hK, hfc, λ δ δ0,
  ⟨K * δ, canonically_ordered_semiring.mul_pos.2 ⟨ennreal.coe_pos.2 hK, δ0⟩,
  λ x y hxy, _⟩⟩;
calc edist x y ≤ K⁻¹ * edist (f x) (f y) : hf.edist_le hK x y
... < K⁻¹ * (K * δ) : (ennreal.mul_lt_mul_left (ennreal.inv_ne_zero.2 ennreal.coe_ne_top)
  (ennreal.inv_ne_top.2 $ hK')).2 hxy
... = δ : by rw [← mul_assoc, ennreal.inv_mul_cancel hK' ennreal.coe_ne_top, one_mul]

end antilipschitz_with

lemma lipschitz_with.to_inverse [emetric_space α] [emetric_space β] {K : ℝ≥0} {f : α → β}
  (hf : lipschitz_with K f) {g : β → α} (hg : function.right_inverse g f) :
  antilipschitz_with K⁻¹ g :=
begin
  intros x y,
  have := hf.edist_ge (g x) (g y),
  rw [hg x, hg y] at this,
  exact le_trans (ennreal.mul_right_mono ennreal.coe_inv_le) this
end
