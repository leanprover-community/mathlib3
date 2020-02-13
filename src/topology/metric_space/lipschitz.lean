/-
Copyright (c) 2018 Rohan Mitta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Mitta, Kevin Buzzard, Alistair Tucker, Johannes Hölzl, Yury Kudryashov
-/
import topology.metric_space.basic
import category_theory.endomorphism category_theory.types

/-!

# Lipschitz continuous functions

A map `f : α → β` between two metric spaces is called *Lipschitz continuous* with constant `K ≥ 0`
if for all `x, y` we have `dist (f x) (f y) ≤ K * dist x y`.

In this file we provide various ways to prove that various combinations of Lipschitz continuous
functions are Lipschitz continuous. We also prove that Lipschitz continuous functions are
uniformly continuous.

## Implementation notes

The parameter `K` has type `nnreal`; this way we avoid conjuction in the definition.
Some constructors (`of_dist_le` and those ending with `'`) take `K : ℝ` as an argument,
and return `lipschitz_with (nnreal.of_real K) f`.
-/

universes u v w x

open filter
open_locale topological_space nnreal

variables {α : Type u} {β : Type v} {γ : Type w} {ι : Type x}

/-- A function `f` is Lipschitz continuous with constant `K ≥ 0` if for all `x, y`
we have `dist (f x) (f y) ≤ K * dist x y` -/
def lipschitz_with [metric_space α] [metric_space β] (K : ℝ≥0) (f : α → β) :=
∀x y, dist (f x) (f y) ≤ K * dist x y

namespace lipschitz_with

variables [metric_space α] [metric_space β] [metric_space γ] {K : ℝ≥0}

protected lemma of_dist_le {f : α → β} {K : ℝ} (h : ∀x y, dist (f x) (f y) ≤ K * dist x y) :
  lipschitz_with (nnreal.of_real K) f :=
λ x y, le_trans (h x y) (mul_le_mul_of_nonneg_right (nnreal.le_coe_of_real K) dist_nonneg)

protected lemma one_mk {f : α → β} (h : ∀ x y, dist (f x) (f y) ≤ dist x y) :
  lipschitz_with 1 f :=
λ x y, by simp only [nnreal.coe_one, one_mul, h]

/-- For functions to `ℝ`, it suffices to prove one of the two inequalities; this version
doesn't assume `0≤K`. -/
protected lemma of_le_add' {f : α → ℝ} (K : ℝ) (h : ∀x y, f x ≤ f y + K * dist x y) :
  lipschitz_with (nnreal.of_real K) f :=
have I : ∀ x y, f x - f y ≤ K * dist x y,
  from assume x y, sub_le_iff_le_add'.2 (h x y),
lipschitz_with.of_dist_le $
assume x y,
abs_sub_le_iff.2 ⟨I x y, dist_comm y x ▸ I y x⟩

/-- For functions to `ℝ`, it suffices to prove one of the two inequalities; this version
assumes `0≤K`. -/
protected lemma of_le_add {f : α → ℝ} (K : ℝ≥0) (h : ∀x y, f x ≤ f y + K * dist x y) :
  lipschitz_with K f :=
by simpa only [nnreal.of_real_coe] using lipschitz_with.of_le_add' K h

protected lemma one_of_le_add {f : α → ℝ} (h : ∀ x y, f x ≤ f y + dist x y) :
  lipschitz_with 1 f :=
lipschitz_with.of_le_add 1 $ by simpa only [nnreal.coe_one, one_mul]

protected lemma le_add {f : α → ℝ} {K : ℝ≥0} (h : lipschitz_with K f) (x y) :
  f x ≤ f y + K * dist x y :=
sub_le_iff_le_add'.1 $ le_trans (le_abs_self _) $ h x y

protected lemma iff_le_add {f : α → ℝ} {K : ℝ≥0} :
  lipschitz_with K f ↔ ∀ x y, f x ≤ f y + K * dist x y :=
⟨lipschitz_with.le_add, lipschitz_with.of_le_add K⟩

section
variables {f : α → β} (hf : lipschitz_with K f)

include hf

lemma nndist_map_le (x y : α) : nndist (f x) (f y) ≤ K * nndist x y :=
hf x y

lemma edist_map_le (x y : α) : edist (f x) (f y) ≤ K * edist x y :=
by simp only [edist_nndist, ennreal.coe_le_coe, ennreal.coe_mul.symm, hf.nndist_map_le]

lemma ediam_image_le (s : set α) :
  emetric.diam (f '' s) ≤ K * emetric.diam s :=
begin
  apply emetric.diam_le_of_forall_edist_le,
  rintros _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩,
  calc edist (f x) (f y) ≤ ↑K * edist x y : hf.edist_map_le x y
                     ... ≤ ↑K * emetric.diam s :
    canonically_ordered_semiring.mul_le_mul (le_refl _) (emetric.edist_le_diam_of_mem hx hy)
end

lemma diam_image_le (s : set α) (hs : metric.bounded s) :
  metric.diam (f '' s) ≤ K * metric.diam s :=
begin
  apply metric.diam_le_of_forall_dist_le (mul_nonneg K.2 metric.diam_nonneg),
  rintros _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩,
  calc dist (f x) (f y) ≤ ↑K * dist x y      : hf x y
                    ... ≤ ↑K * metric.diam s :
    mul_le_mul_of_nonneg_left (metric.dist_le_diam_of_mem hs hx hy) K.2
end

protected lemma weaken {K' : ℝ≥0} (h : K ≤ K') :
  lipschitz_with K' f :=
assume x y, le_trans (hf x y) $ mul_le_mul_of_nonneg_right h dist_nonneg

/-- A Lipschitz function is uniformly continuous -/
protected lemma to_uniform_continuous : uniform_continuous f :=
begin
  have : (0:ℝ) < max K 1 := lt_of_lt_of_le zero_lt_one (le_max_right K 1),
  refine metric.uniform_continuous_iff.2 (λε εpos, _),
  exact ⟨ε/max K 1, div_pos εpos this, assume y x Dyx, calc
    dist (f y) (f x) ≤ K * dist y x : hf y x
    ... ≤ max K 1 * dist y x : mul_le_mul_of_nonneg_right (le_max_left K 1) (dist_nonneg)
    ... < max K 1 * (ε/max K 1) : mul_lt_mul_of_pos_left Dyx this
    ... = ε : mul_div_cancel' _ (ne_of_gt this)⟩
end

/-- A Lipschitz function is continuous -/
protected lemma to_continuous {f : α → β} (hf : lipschitz_with K f) : continuous f :=
hf.to_uniform_continuous.continuous

end

protected lemma const (b : β) : lipschitz_with 0 (λa:α, b) :=
assume x y, by simp only [zero_mul, dist_self, nnreal.coe_zero]

protected lemma id : lipschitz_with 1 (@id α) :=
lipschitz_with.one_mk $ assume x y, le_refl _

protected lemma subtype_val (s : set α) : lipschitz_with 1 (subtype.val : s → α) :=
lipschitz_with.one_mk $ assume x y, le_refl _

protected lemma subtype_coe (s : set α) : lipschitz_with 1 (coe : s → α) :=
lipschitz_with.subtype_val s

protected lemma comp {Kf Kg : ℝ≥0} {f : β → γ} {g : α → β}
  (hf : lipschitz_with Kf f) (hg : lipschitz_with Kg g) : lipschitz_with (Kf * Kg) (f ∘ g) :=
assume x y,
calc dist (f (g x)) (f (g y)) ≤ Kf * dist (g x) (g y) : hf _ _
... ≤ Kf * (Kg * dist x y) : mul_le_mul_of_nonneg_left (hg _ _) Kf.2
... = (Kf * Kg) * dist x y : by rw mul_assoc

protected lemma prod_fst : lipschitz_with 1 (@prod.fst α β) :=
lipschitz_with.one_mk $ assume x y, le_max_left _ _

protected lemma prod_snd : lipschitz_with 1 (@prod.snd α β) :=
lipschitz_with.one_mk $ assume x y, le_max_right _ _

protected lemma prod {f : α → β} {Kf : ℝ≥0} (hf : lipschitz_with Kf f)
  {g : α → γ} {Kg : ℝ≥0} (hg : lipschitz_with Kg g) :
  lipschitz_with (max Kf Kg) (λ x, (f x, g x)) :=
begin
  assume x y,
  simp only [nnreal.coe_mono.map_max, prod.dist_eq, max_mul_of_nonneg _ _ dist_nonneg],
  exact max_le_max (hf x y) (hg x y)
end

protected lemma uncurry' {f : α → β → γ} {Kα Kβ : ℝ≥0} (hα : ∀ b, lipschitz_with Kα (λ a, f a b))
  (hβ : ∀ a, lipschitz_with Kβ (f a)) :
  lipschitz_with (Kα + Kβ) (function.uncurry' f) :=
begin
  rintros ⟨a₁, b₁⟩ ⟨a₂, b₂⟩,
  simp only [function.uncurry', nnreal.coe_add, add_mul],
  refine le_trans (dist_triangle _ (f a₂ b₁) _) (add_le_add _ _),
  { calc dist (f a₁ b₁) (f a₂ b₁) ≤ Kα * dist a₁ a₂ : hα _ _ _
    ... ≤ Kα * dist (a₁, b₁) (a₂, b₂) : mul_le_mul_of_nonneg_left (le_max_left _ _) Kα.2 },
  { calc dist (f a₂ b₁) (f a₂ b₂) ≤ Kβ * dist b₁ b₂ : hβ _ _ _
    ... ≤ Kβ * dist (a₁, b₁) (a₂, b₂) : mul_le_mul_of_nonneg_left (le_max_right _ _) Kβ.2 }
end

protected lemma uncurry {f : α → β → γ} {Kα Kβ : ℝ≥0} (hα : ∀ b, lipschitz_with Kα (λ a, f a b))
  (hβ : ∀ a, lipschitz_with Kβ (f a)) :
  lipschitz_with (Kα + Kβ) (function.uncurry f) :=
by { rw function.uncurry_def, apply lipschitz_with.uncurry'; assumption }

protected lemma dist_left (y : α) : lipschitz_with 1 (λ x, dist x y) :=
lipschitz_with.one_of_le_add $ assume x z,
by { rw [add_comm, dist_comm z], apply dist_triangle_right }

protected lemma dist_right (x : α) : lipschitz_with 1 (dist x) :=
by { convert lipschitz_with.dist_left x, funext y, apply dist_comm }

protected lemma dist : lipschitz_with 2 (function.uncurry' $ @dist α _) :=
lipschitz_with.uncurry' lipschitz_with.dist_left lipschitz_with.dist_right

protected lemma iterate {f : α → α} (hf : lipschitz_with K f) :
  ∀n, lipschitz_with (K ^ n) (f^[n])
| 0       := lipschitz_with.id
| (n + 1) := by rw [pow_succ']; exact (iterate n).comp hf

lemma dist_iterate_succ_le_geometric {f : α → α} (hf : lipschitz_with K f) (x n) :
  dist (f^[n] x) (f^[n + 1] x) ≤ dist x (f x) * K ^ n :=
begin
  rw [nat.iterate_succ, mul_comm],
  simpa only [is_monoid_hom.map_pow (coe : ℝ≥0 → ℝ)] using (hf.iterate n) x (f x)
end

open category_theory

protected lemma mul {f g : End α} {Kf Kg} (hf : lipschitz_with Kf f) (hg : lipschitz_with Kg g) :
  lipschitz_with (Kf * Kg) (f * g : End α) :=
hf.comp hg

/-- The product of a list of Lipschitz continuous endomorphisms is a Lipschitz continuous
endomorphism. -/
protected lemma list_prod (f : ι → End α) (K : ι → ℝ≥0) (h : ∀ i, lipschitz_with (K i) (f i)) :
  ∀ l : list ι, lipschitz_with (l.map K).prod (l.map f).prod
| [] := by simp [lipschitz_with.id]
| (i :: l) := by { simp only [list.map_cons, list.prod_cons], exact (h i).mul (list_prod l) }

protected lemma pow {f : End α} {K} (h : lipschitz_with K f) :
  ∀ n : ℕ, lipschitz_with (K^n) (f^n : End α)
| 0       := lipschitz_with.id
| (n + 1) := h.mul (pow n)

end lipschitz_with

/-- If a function is locally Lipschitz around a point, then it is continuous at this point. -/
lemma continuous_at_of_locally_lipschitz [metric_space α] [metric_space β] {f : α → β} {x : α}
  {r : ℝ} (hr : 0 < r) (K : ℝ) (h : ∀y, dist y x < r → dist (f y) (f x) ≤ K * dist y x) :
  continuous_at f x :=
begin
  refine metric.continuous_at_iff.2 (λε εpos, ⟨min r ((ε / 2) / max K 1), _, λ y hy, _⟩),
  { simp [hr, div_pos (half_pos εpos), zero_lt_one] },
  have A : max K 1 ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right K 1)),
  calc dist (f y) (f x)
    ≤ K * dist y x : h y (lt_of_lt_of_le hy (min_le_left _ _))
    ... ≤ max K 1 * dist y x : mul_le_mul_of_nonneg_right (le_max_left K 1) dist_nonneg
    ... ≤ max K 1 * (ε / 2 / max K 1) :
      mul_le_mul_of_nonneg_left (le_of_lt (lt_of_lt_of_le hy (min_le_right _ _)))
        (le_trans zero_le_one (le_max_right K 1))
    ... = ε / 2 : by { field_simp [A], ring }
    ... < ε : half_lt_self εpos
end
