/-
Copyright (c) 2022 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Dilations of emetric and metric spaces
Authors: Hanting Zhang
-/
import topology.metric_space.antilipschitz
import data.fun_like.basic

/-!
# Dilations

We define dilations, i.e., maps between emetric spaces that
satisfy `edist (f x) (f y) = r * edist x y`.

Defines `ratio f`, which is the ratio of the dilation `f`

Here `r : ℝ≥0`, so we do not exclude the degenerate case of dilations
which collapse into constant maps. Since there is no `ℝ>0` API defined in mathlib,
no matter where you choose to exclude r = 0, you will end up having to carry
it around with you anyways. So statements that do need strict dilations should
just say `f : dilation α β r` and `hr : r ≠ 0`.

TODO: Introduce dilation equivs. Refactor the isometry API
to match the `*_hom_class` API below.

Since a lot of elementary properties don't require `eq_of_dist_eq_zero` we start setting up the
theory for `pseudo_metric_space` and we specialize to `metric_space` when needed.
-/

noncomputable theory

open function set
open_locale topological_space ennreal nnreal

section setup

variables (α : Type*) (β : Type*) [pseudo_emetric_space α] [pseudo_emetric_space β]

/-- A dilation is a map that uniformly scales the edistance between any two points.  -/
structure dilation :=
(to_fun : α → β)
(edist_eq' : ∃ r : ℝ≥0, ∀ x y : α, edist (to_fun x) (to_fun y) = r * edist x y)

attribute [nolint has_inhabited_instance] dilation

/--
`dilation_class F α β r` states that `F` is a type of `r`-dilations.

You should extend this typeclass when you extend `dilation`.
-/
class dilation_class (F : Type*) (α β : out_param $ Type*)
  [pseudo_emetric_space α] [pseudo_emetric_space β] extends fun_like F α (λ _, β) :=
(edist_eq' : ∀ (f : F), ∃ r : ℝ≥0, ∀ (x y : α), edist (f x) (f y) = r * edist x y)

attribute [nolint dangerous_instance] dilation_class.to_fun_like

instance dilation.to_dilation_class :
  dilation_class (dilation α β) α β :=
{ coe := dilation.to_fun,
  coe_injective' := λ f g h, by { cases f; cases g; congr', },
  edist_eq' := λ f, dilation.edist_eq' f }

instance : has_coe_to_fun (dilation α β) (λ _, α → β) := fun_like.has_coe_to_fun

@[simp] lemma dilation.to_fun_eq_coe {f : dilation α β} : f.to_fun = (f : α → β) := rfl

@[ext] theorem dilation.ext {f g : dilation α β} (h : ∀ x, f x = g x) : f = g :=
fun_like.ext f g h

/-- Copy of a `dilation` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def dilation.copy (f : dilation α β) (f' : α → β) (h : f' = ⇑f) : dilation α β :=
{ to_fun := f',
  edist_eq' := h.symm ▸ f.edist_eq' }

/-- The ratio of a dilation `f`. Uses `Exists.some` -/
def ratio {α β} [pseudo_emetric_space α] [pseudo_emetric_space β] {F : Type*}
  [dilation_class F α β] (f : F) : ℝ≥0 :=
(dilation_class.edist_eq' f).some

end setup

namespace dilation

variables {α : Type*} {β : Type*} {γ : Type*} {F : Type*} {G : Type*}

@[simp] lemma edist_eq
  [pseudo_emetric_space α] [pseudo_emetric_space β] [dilation_class F α β]
  (f : F) (x y : α) : edist (f x) (f y) = ratio f * edist x y :=
(dilation_class.edist_eq' f).some_spec x y

@[simp] lemma dist_eq
  [pseudo_metric_space α] [pseudo_metric_space β] [dilation_class F α β]
  (f : F) (x y : α) : dist (f x) (f y) = ratio f * dist x y :=
by simp only [dist_edist, edist_eq, ennreal.to_real_mul, ennreal.coe_to_real]

theorem nndist_eq [pseudo_metric_space α] [pseudo_metric_space β] [dilation_class F α β]
  (f : F) (x y : α) : nndist (f x) (f y) = ratio f * nndist x y :=
begin
  apply subtype.ext _,
  simp only [coe_nndist, dist_eq, nonneg.coe_mul],
end

section pseudo_emetric_dilation

variables [pseudo_emetric_space α] [pseudo_emetric_space β] [pseudo_emetric_space γ]
variables [dilation_class F α β] [dilation_class G β γ]
variables (f : F) (g : G) {x y z : α}  {s : set α}

lemma lipschitz : lipschitz_with (ratio f) (f : α → β) :=
λ x y, (edist_eq f x y).le


-- TODO: add `instance ennreal.div_inv_comm_monoid`
-- TODO: fix `antilipschitz_with` decl header
lemma antilipschitz (hr : ratio f ≠ 0) : antilipschitz_with ((ratio f)⁻¹) (f : α → β) :=
λ x y, begin
  -- `div_eq_mul_inv` should be `div_eq_inv_mul`
  rw [mul_comm, ← ennreal.div_le_iff_le_mul, div_eq_mul_inv, mul_comm, ennreal.coe_inv hr],
  simp only [inv_inv, edist_eq, le_refl],
  left, simp [hr],
  left, simp [hr],
end

/-- A dilation from an emetric space is injective -/
lemma injective {α : Type*} [emetric_space α]  [dilation_class F α β] (f : F) (hr : ratio f ≠ 0) :
  injective f := (dilation.antilipschitz f hr).injective

/-- Any map on a subsingleton is a dilation -/
def of_subsingleton [subsingleton α] (f : α → β) : dilation α β :=
{ to_fun := f,
  edist_eq' := ⟨0, λ x y, by { rw subsingleton.elim x y, simp, }⟩ }

/-- The composition of similarities is a dilation -/
def comp (f : dilation α β) (g : dilation β γ):
  dilation α γ :=
{ to_fun := g ∘ f,
  edist_eq' := ⟨ratio f * ratio g, λ x y, by { simp only [edist_eq, ennreal.coe_mul], ring, }⟩ }

/-- The constant function of is a dilation -/
def const (b : β) :
  dilation α β :=
{ to_fun := λ _, b,
  edist_eq' := ⟨0, λ x y, by simp⟩ }

/-- A dilation from a metric space is a uniform inducing map -/
theorem uniform_inducing (hr : ratio f ≠ 0) :
  uniform_inducing (f : α → β) :=
(antilipschitz f hr).uniform_inducing (lipschitz f).uniform_continuous

lemma tendsto_nhds_iff {ι : Type*} {g : ι → α} {a : filter ι} {b : α} (hr : ratio f ≠ 0) :
  filter.tendsto g a (𝓝 b) ↔ filter.tendsto ((f : α → β) ∘ g) a (𝓝 (f b)) :=
(uniform_inducing f hr).inducing.tendsto_nhds_iff

/-- A dilation is continuous. -/
lemma to_continuous : continuous (f : α → β) :=
(lipschitz f).continuous

/-- Similarities multiply the diameter by their ratio in pseudoemetric spaces. -/
lemma ediam_image (s : set α) :
  emetric.diam ((f: α → β) '' s) = ratio f * emetric.diam s :=
begin
  apply le_antisymm,
  { exact lipschitz_with.ediam_image_le (lipschitz f) s },
  by_cases hr : ratio f ≠ 0,
  { rw [mul_comm, ← ennreal.le_div_iff_mul_le, div_eq_mul_inv, mul_comm, ← ennreal.coe_inv hr],
    refine antilipschitz_with.le_mul_ediam_image (antilipschitz f hr) s,
    left, simp [hr],
    left, simp [hr], },
  rw not_not at hr,
  simp [hr],
end

lemma ediam_range :
  emetric.diam (range (f : α → β)) = ratio f * emetric.diam (univ : set α) :=
by { rw ← image_univ, exact ediam_image f univ }

lemma maps_to_emetric_ball  (hr : ratio f ≠ 0) (x : α) (r' : ℝ≥0∞) :
  maps_to (f : α → β) (emetric.ball x r') (emetric.ball (f x) (ratio f * r')) :=
begin
  intros y hy,
  simp only [emetric.mem_ball, edist_eq] at *,
  rwa ennreal.mul_lt_mul_left _ _,
  simp [hr],
  simp [hr],
end

lemma maps_to_emetric_closed_ball (x : α) (r' : ℝ≥0∞) :
  maps_to (f : α → β) (emetric.closed_ball x r') (emetric.closed_ball (f x) (ratio f * r')) :=
begin
  by_cases hr : ratio f ≠ 0,
  { intros y hy,
    simp only [emetric.mem_closed_ball, edist_eq] at *,
    rwa ennreal.mul_le_mul_left _ _,
    simp [hr],
    simp [hr], },
  rw not_not at hr,
  simp [hr, maps_to],
end

lemma comp_continuous_on_iff
  {γ} [topological_space γ] {g : γ → α} {s : set γ} (hr : ratio f ≠ 0) :
  continuous_on ((f : α → β) ∘ g) s ↔ continuous_on g s :=
(uniform_inducing f hr).inducing.continuous_on_iff.symm

lemma comp_continuous_iff
  {γ} [topological_space γ] {g : γ → α} (hr : ratio f ≠ 0) :
  continuous ((f : α → β) ∘ g) ↔ continuous g :=
(uniform_inducing f hr).inducing.continuous_iff.symm

end pseudo_emetric_dilation --section

section emetric_dilation
variables [emetric_space α]

/-- A dilation from a metric space is a uniform embedding -/
theorem uniform_embedding [pseudo_emetric_space β] [dilation_class F α β]
  (f : F) (hr : ratio f ≠ 0) : uniform_embedding f :=
(antilipschitz f hr).uniform_embedding (lipschitz f).uniform_continuous

/-- A dilation from a metric space is an embedding -/
theorem embedding [pseudo_emetric_space β] [dilation_class F α β]
  (f : F) (hr : ratio f ≠ 0) : embedding (f : α → β) :=
(uniform_embedding f hr).embedding

/-- A dilation from a complete emetric space is a closed embedding -/
theorem closed_embedding
  [complete_space α] [emetric_space β] [dilation_class F α β]
  (f : F) (hr : ratio f ≠ 0) : closed_embedding (f : α → β) :=
(antilipschitz f hr).closed_embedding (lipschitz f).uniform_continuous

end emetric_dilation --section

section pseudo_metric_dilation
variables [pseudo_metric_space α] [pseudo_metric_space β] [dilation_class F α β] (f : F)

/-- An isometry preserves the diameter in pseudometric spaces. -/
lemma diam_image (s : set α) : metric.diam ((f : α → β) '' s) = ratio f * metric.diam s :=
by { simp [metric.diam, metric.diam, ediam_image, ennreal.to_real_mul], }

lemma diam_range : metric.diam (range (f : α → β)) = ratio f * metric.diam (univ : set α) :=
by rw [← image_univ, diam_image]

lemma maps_to_ball (hr : ratio f ≠ 0) (x : α) (r' : ℝ) :
  maps_to (f : α → β) (metric.ball x r') (metric.ball (f x) (ratio f * r')) :=
begin
  intros y hy,
  rw [metric.mem_ball, dist_eq],
  refine mul_lt_mul' (le_refl _) _ dist_nonneg _,
  rwa metric.mem_ball at hy,
  rwa [nnreal.coe_pos, pos_iff_ne_zero],
end

lemma maps_to_sphere (x : α) (r' : ℝ) :
  maps_to (f : α → β) (metric.sphere x r') (metric.sphere (f x) (ratio f * r')) :=
begin
  intros y hy,
  rw metric.mem_sphere at hy,
  rw [metric.mem_sphere, dist_eq, hy],
end

lemma maps_to_closed_ball (x : α) (r' : ℝ) :
  maps_to (f : α → β) (metric.closed_ball x r') (metric.closed_ball (f x) (ratio f * r')) :=
begin
  intros y hy,
  rw [metric.mem_closed_ball] at hy,
  rw [metric.mem_closed_ball, dist_eq],
  refine mul_le_mul (le_refl _) hy dist_nonneg nnreal.zero_le_coe,
end

end pseudo_metric_dilation -- section

end dilation
