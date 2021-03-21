/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import topology.metric_space.lipschitz
import topology.uniform_space.complete_separated

/-!
# Antilipschitz functions

We say that a map `f : α → β` between two (extended) metric spaces is
`antilipschitz_with K`, `K ≥ 0`, if for all `x, y` we have `edist x y ≤ K * edist (f x) (f y)`.
For a metric space, the latter inequality is equivalent to `dist x y ≤ K * dist (f x) (f y)`.

## Implementation notes

The parameter `K` has type `ℝ≥0`. This way we avoid conjuction in the definition and have
coercions both to `ℝ` and `ℝ≥0∞`. We do not require `0 < K` in the definition, mostly because
we do not have a `posreal` type.
-/

variables {α : Type*} {β : Type*} {γ : Type*}

open_locale nnreal
open set

/-- We say that `f : α → β` is `antilipschitz_with K` if for any two points `x`, `y` we have
`K * edist x y ≤ edist (f x) (f y)`. -/
def antilipschitz_with [pseudo_emetric_space α] [pseudo_emetric_space β] (K : ℝ≥0) (f : α → β) :=
∀ x y, edist x y ≤ K * edist (f x) (f y)

lemma antilipschitz_with_iff_le_mul_dist [pseudo_metric_space α] [pseudo_metric_space β] {K : ℝ≥0}
  {f : α → β} : antilipschitz_with K f ↔ ∀ x y, dist x y ≤ K * dist (f x) (f y) :=
by { simp only [antilipschitz_with, edist_nndist, dist_nndist], norm_cast }

alias antilipschitz_with_iff_le_mul_dist ↔ antilipschitz_with.le_mul_dist
  antilipschitz_with.of_le_mul_dist

lemma antilipschitz_with.mul_le_dist [pseudo_metric_space α] [pseudo_metric_space β] {K : ℝ≥0}
  {f : α → β} (hf : antilipschitz_with K f) (x y : α) : ↑K⁻¹ * dist x y ≤ dist (f x) (f y) :=
begin
  by_cases hK : K = 0, by simp [hK, dist_nonneg],
  rw [nnreal.coe_inv, ← div_eq_inv_mul],
  rw div_le_iff' (nnreal.coe_pos.2 $ pos_iff_ne_zero.2 hK),
  exact hf.le_mul_dist x y
end

namespace antilipschitz_with

variables [pseudo_emetric_space α] [pseudo_emetric_space β] [pseudo_emetric_space γ]
variables {K : ℝ≥0} {f : α → β}

/-- Extract the constant from `hf : antilipschitz_with K f`. This is useful, e.g.,
if `K` is given by a long formula, and we want to reuse this value. -/
@[nolint unused_arguments] -- uses neither `f` nor `hf`
protected def K (hf : antilipschitz_with K f) : ℝ≥0 := K

protected lemma injective {α : Type*} {β : Type*} [emetric_space α] [pseudo_emetric_space β]
  {K : ℝ≥0} {f : α → β} (hf : antilipschitz_with K f) : function.injective f :=
λ x y h, by simpa only [h, edist_self, mul_zero, edist_le_zero] using hf x y

lemma mul_le_edist (hf : antilipschitz_with K f) (x y : α) :
  ↑K⁻¹ * edist x y ≤ edist (f x) (f y) :=
begin
  by_cases hK : K = 0, by simp [hK],
  rw [ennreal.coe_inv hK, mul_comm, ← div_eq_mul_inv],
  apply ennreal.div_le_of_le_mul,
  rw mul_comm,
  exact hf x y
end

protected lemma id : antilipschitz_with 1 (id : α → α) :=
λ x y, by simp only [ennreal.coe_one, one_mul, id, le_refl]

lemma comp {Kg : ℝ≥0} {g : β → γ} (hg : antilipschitz_with Kg g)
  {Kf : ℝ≥0} {f : α → β} (hf : antilipschitz_with Kf f) :
  antilipschitz_with (Kf * Kg) (g ∘ f) :=
λ x y,
calc edist x y ≤ Kf * edist (f x) (f y) : hf x y
... ≤ Kf * (Kg * edist (g (f x)) (g (f y))) : ennreal.mul_left_mono (hg _ _)
... = _ : by rw [ennreal.coe_mul, mul_assoc]

lemma restrict (hf : antilipschitz_with K f) (s : set α) :
  antilipschitz_with K (s.restrict f) :=
λ x y, hf x y

lemma cod_restrict (hf : antilipschitz_with K f) {s : set β} (hs : ∀ x, f x ∈ s) :
  antilipschitz_with K (s.cod_restrict f hs) :=
λ x y, hf x y

lemma to_right_inv_on' {s : set α} (hf : antilipschitz_with K (s.restrict f))
  {g : β → α} {t : set β} (g_maps : maps_to g t s) (g_inv : right_inv_on g f t) :
  lipschitz_with K (t.restrict g) :=
λ x y, by simpa only [restrict_apply, g_inv x.mem, g_inv y.mem, subtype.edist_eq, subtype.coe_mk]
  using hf ⟨g x, g_maps x.mem⟩ ⟨g y, g_maps y.mem⟩

lemma to_right_inv_on (hf : antilipschitz_with K f) {g : β → α} {t : set β}
  (h : right_inv_on g f t) :
  lipschitz_with K (t.restrict g) :=
(hf.restrict univ).to_right_inv_on' (maps_to_univ g t) h

lemma to_right_inverse (hf : antilipschitz_with K f) {g : β → α} (hg : function.right_inverse g f) :
  lipschitz_with K g :=
begin
  intros x y,
  have := hf (g x) (g y),
  rwa [hg x, hg y] at this
end

lemma uniform_embedding {α : Type*} {β : Type*} [emetric_space α] [pseudo_emetric_space β] {K : ℝ≥0}
  {f : α → β} (hf : antilipschitz_with K f) (hfc : uniform_continuous f) : uniform_embedding f :=
begin
  refine emetric.uniform_embedding_iff.2 ⟨hf.injective, hfc, λ δ δ0, _⟩,
  by_cases hK : K = 0,
  { refine ⟨1, ennreal.zero_lt_one, λ x y _, lt_of_le_of_lt _ δ0⟩,
    simpa only [hK, ennreal.coe_zero, zero_mul] using hf x y },
  { refine ⟨K⁻¹ * δ, _, λ x y hxy, lt_of_le_of_lt (hf x y) _⟩,
    { exact canonically_ordered_semiring.mul_pos.2 ⟨ennreal.inv_pos.2 ennreal.coe_ne_top, δ0⟩ },
    { rw [mul_comm, ← div_eq_mul_inv] at hxy,
      have := ennreal.mul_lt_of_lt_div hxy,
      rwa mul_comm } }
end

lemma closed_embedding {α : Type*} {β : Type*} [emetric_space α] [emetric_space β] {K : ℝ≥0}
  {f : α → β} [complete_space α] (hf : antilipschitz_with K f) (hfc : uniform_continuous f) :
  closed_embedding f :=
{ closed_range :=
  begin
    apply is_complete.is_closed,
    rw ← complete_space_iff_is_complete_range (hf.uniform_embedding hfc),
    apply_instance,
  end,
  .. (hf.uniform_embedding hfc).embedding }

lemma subtype_coe (s : set α) : antilipschitz_with 1 (coe : s → α) :=
antilipschitz_with.id.restrict s

lemma of_subsingleton [subsingleton α] {K : ℝ≥0} : antilipschitz_with K f :=
λ x y, by simp only [subsingleton.elim x y, edist_self, zero_le]

end antilipschitz_with

namespace antilipschitz_with

open metric

variables [pseudo_metric_space α] [pseudo_metric_space β] {K : ℝ≥0} {f : α → β}

lemma bounded_preimage (hf : antilipschitz_with K f)
  {s : set β} (hs : bounded s) :
  bounded (f ⁻¹' s) :=
exists.intro (K * diam s) $ λ x y hx hy,
calc dist x y ≤ K * dist (f x) (f y) : hf.le_mul_dist x y
... ≤ K * diam s : mul_le_mul_of_nonneg_left (dist_le_diam_of_mem hs hx hy) K.2

/-- The image of a proper space under an expanding onto map is proper. -/
protected lemma proper_space {α : Type*} {β : Type*} [metric_space α] [metric_space β] {K : ℝ≥0}
  {f : α → β} [proper_space α] (hK : antilipschitz_with K f) (f_cont : continuous f)
  (hf : function.surjective f) : proper_space β :=
begin
  apply proper_space_of_compact_closed_ball_of_le 0 (λx₀ r hr, _),
  let K := f ⁻¹' (closed_ball x₀ r),
  have A : is_closed K := is_closed_ball.preimage f_cont,
  have B : bounded K := hK.bounded_preimage bounded_closed_ball,
  have : is_compact K := compact_iff_closed_bounded.2 ⟨A, B⟩,
  convert this.image f_cont,
  exact (hf.image_preimage _).symm
end

end antilipschitz_with

lemma lipschitz_with.to_right_inverse [emetric_space α] [pseudo_emetric_space β] {K : ℝ≥0}
  {f : α → β} (hf : lipschitz_with K f) {g : β → α} (hg : function.right_inverse g f) :
  antilipschitz_with K g :=
λ x y, by simpa only [hg _] using hf (g x) (g y)
