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

We define dilations, i.e., maps between emetric spaces that satisfy
`edist (f x) (f y) = r * edist x y` for some `r ∉ {0, ∞}`.

The value `r = 0` is not allowed because we want dilations of (e)metric spaces to be automatically
injective. The value `r = ∞` is not allowed because this way we can define `dilation.ratio f : ℝ≥0`,
not `dilation.ratio f : ℝ≥0∞`. Also, we do not often need maps sending distinct points to points at
infinite distance.

## Main defintions

* `dilation.ratio f : ℝ≥0`: the value of `r` in the relation above, defaulting to 1 in the case
  where it is not well-defined.

## Implementation notes

The type of dilations defined in this file are also referred to as "similarities" or "similitudes"
by other authors. The name `dilation` was choosen to match the Wikipedia name.

Since a lot of elementary properties don't require `eq_of_dist_eq_zero` we start setting up the
theory for `pseudo_emetric_space` and we specialize to `pseudo_metric_space` and `metric_space` when
needed.

## TODO

- Introduce dilation equivs.
- Refactor the `isometry` API to match the `*_hom_class` API below.

## References

- https://en.wikipedia.org/wiki/Dilation_(metric_space)
- [Marcel Berger, *Geometry*][berger1987]
-/

noncomputable theory

open function set
open_locale topology ennreal nnreal classical

section defs

variables (α : Type*) (β : Type*) [pseudo_emetric_space α] [pseudo_emetric_space β]

/-- A dilation is a map that uniformly scales the edistance between any two points.  -/
structure dilation :=
(to_fun : α → β)
(edist_eq' : ∃ r : ℝ≥0, r ≠ 0 ∧ ∀ x y : α, edist (to_fun x) (to_fun y) = r * edist x y)

/--
`dilation_class F α β r` states that `F` is a type of `r`-dilations.
You should extend this typeclass when you extend `dilation`.
-/
class dilation_class (F : Type*) (α β : out_param $ Type*)
  [pseudo_emetric_space α] [pseudo_emetric_space β] extends fun_like F α (λ _, β) :=
(edist_eq' : ∀ (f : F), ∃ r : ℝ≥0, r ≠ 0 ∧ ∀ (x y : α), edist (f x) (f y) = r * edist x y)

end defs

namespace dilation
variables {α : Type*} {β : Type*} {γ : Type*} {F : Type*} {G : Type*}

section setup
variables [pseudo_emetric_space α] [pseudo_emetric_space β]

instance to_dilation_class :
  dilation_class (dilation α β) α β :=
{ coe := to_fun,
  coe_injective' := λ f g h, by { cases f; cases g; congr', },
  edist_eq' := λ f, edist_eq' f }

instance : has_coe_to_fun (dilation α β) (λ _, α → β) := fun_like.has_coe_to_fun

@[simp] lemma to_fun_eq_coe {f : dilation α β} : f.to_fun = (f : α → β) := rfl

@[simp] lemma coe_mk (f : α → β) (h) : ⇑(⟨f, h⟩ : dilation α β) = f := rfl

lemma congr_fun {f g : dilation α β} (h : f = g) (x : α) : f x = g x := fun_like.congr_fun h x
lemma congr_arg (f : dilation α β) {x y : α} (h : x = y) : f x = f y := fun_like.congr_arg f h

@[ext] theorem ext {f g : dilation α β} (h : ∀ x, f x = g x) : f = g :=
fun_like.ext f g h

lemma ext_iff {f g : dilation α β} : f = g ↔ ∀ x, f x = g x := fun_like.ext_iff

@[simp] lemma mk_coe (f : dilation α β) (h) : dilation.mk f h = f := ext $ λ _, rfl

/-- Copy of a `dilation` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
@[simps { fully_applied := ff }]
protected def copy (f : dilation α β) (f' : α → β) (h : f' = ⇑f) : dilation α β :=
{ to_fun := f',
  edist_eq' := h.symm ▸ f.edist_eq' }

lemma copy_eq_self (f : dilation α β) {f' : α → β} (h : f' = f) : f.copy f' h = f :=
fun_like.ext' h

/-- The ratio of a dilation `f`. If the ratio is undefined (i.e., the distance between any two
points in `α` is either zero or infinity), then we choose one as the ratio. -/
def ratio [dilation_class F α β] (f : F) : ℝ≥0 :=
if ∀ x y : α, edist x y = 0 ∨ edist x y = ⊤ then 1 else (dilation_class.edist_eq' f).some

lemma ratio_ne_zero [dilation_class F α β] (f : F) : ratio f ≠ 0 :=
begin
  rw ratio, split_ifs,
  { exact one_ne_zero, },
  exact (dilation_class.edist_eq' f).some_spec.1,
end

lemma ratio_pos [dilation_class F α β] (f : F) : 0 < ratio f :=
(ratio_ne_zero f).bot_lt

@[simp] lemma edist_eq [dilation_class F α β] (f : F) (x y : α) :
  edist (f x) (f y) = ratio f * edist x y :=
begin
  rw ratio, split_ifs with key,
  { rcases dilation_class.edist_eq' f with ⟨r, hne, hr⟩,
    replace hr := hr x y,
    cases key x y,
    { simp only [hr, h, mul_zero] },
    { simp [hr, h, hne] } },
  exact (dilation_class.edist_eq' f).some_spec.2 x y,
end

@[simp] lemma nndist_eq {α β F : Type*}  [pseudo_metric_space α] [pseudo_metric_space β]
  [dilation_class F α β] (f : F) (x y : α) : nndist (f x) (f y) = ratio f * nndist x y :=
by simp only [← ennreal.coe_eq_coe, ← edist_nndist, ennreal.coe_mul, edist_eq]

@[simp] lemma dist_eq {α β F : Type*} [pseudo_metric_space α] [pseudo_metric_space β]
  [dilation_class F α β] (f : F) (x y : α) : dist (f x) (f y) = ratio f * dist x y :=
by simp only [dist_nndist, nndist_eq, nnreal.coe_mul]

/-- The `ratio` is equal to the distance ratio for any two points with nonzero finite distance.
`dist` and `nndist` versions below -/
lemma ratio_unique [dilation_class F α β] {f : F} {x y : α} {r : ℝ≥0}
  (h₀ : edist x y ≠ 0) (htop : edist x y ≠ ⊤) (hr : edist (f x) (f y) = r * edist x y) :
  r = ratio f :=
by simpa only [hr, ennreal.mul_eq_mul_right h₀ htop, ennreal.coe_eq_coe] using edist_eq f x y

/-- The `ratio` is equal to the distance ratio for any two points
with nonzero finite distance; `nndist` version -/
lemma ratio_unique_of_nndist_ne_zero {α β F : Type*} [pseudo_metric_space α] [pseudo_metric_space β]
  [dilation_class F α β] {f : F} {x y : α} {r : ℝ≥0} (hxy : nndist x y ≠ 0)
  (hr : nndist (f x) (f y) = r * nndist x y) : r = ratio f :=
ratio_unique (by rwa [edist_nndist, ennreal.coe_ne_zero]) (edist_ne_top x y)
  (by rw [edist_nndist, edist_nndist, hr, ennreal.coe_mul])

/-- The `ratio` is equal to the distance ratio for any two points
with nonzero finite distance; `dist` version -/
lemma ratio_unique_of_dist_ne_zero {α β} {F : Type*} [pseudo_metric_space α] [pseudo_metric_space β]
  [dilation_class F α β] {f : F} {x y : α} {r : ℝ≥0}
  (hxy : dist x y ≠ 0) (hr : dist (f x) (f y) = r * dist x y) :
  r = ratio f :=
ratio_unique_of_nndist_ne_zero (nnreal.coe_ne_zero.1 hxy) $ nnreal.eq $
  by rw [coe_nndist, hr, nnreal.coe_mul, coe_nndist]

/-- Alternative `dilation` constructor when the distance hypothesis is over `nndist` -/
def mk_of_nndist_eq {α β}
  [pseudo_metric_space α] [pseudo_metric_space β]
  (f : α → β) (h : ∃ (r : ℝ≥0), r ≠ 0 ∧ ∀ (x y : α), nndist (f x) (f y) = r * nndist x y) :
  dilation α β :=
{ to_fun := f,
  edist_eq' :=
  begin
    rcases h with ⟨r, hne, h⟩,
    refine ⟨r, hne, λ x y, _⟩,
    rw [edist_nndist, edist_nndist, ← ennreal.coe_mul, h x y],
  end }

@[simp] lemma coe_mk_of_nndist_eq {α β}
  [pseudo_metric_space α] [pseudo_metric_space β]
  (f : α → β) (h) : ⇑(mk_of_nndist_eq f h : dilation α β) = f := rfl

@[simp] lemma mk_coe_of_nndist_eq {α β}
  [pseudo_metric_space α] [pseudo_metric_space β]
  (f : dilation α β) (h) : dilation.mk_of_nndist_eq f h = f :=
ext $ λ _, rfl

/-- Alternative `dilation` constructor when the distance hypothesis is over `dist` -/
def mk_of_dist_eq {α β}
  [pseudo_metric_space α] [pseudo_metric_space β]
  (f : α → β) (h : ∃ (r : ℝ≥0), r ≠ 0 ∧ ∀ (x y : α), dist (f x) (f y) = r * dist x y) :
  dilation α β :=
mk_of_nndist_eq f $ h.imp $ λ r hr,
  ⟨hr.1, λ x y, nnreal.eq $ by rw [coe_nndist, hr.2, nnreal.coe_mul, coe_nndist]⟩

@[simp] lemma coe_mk_of_dist_eq {α β}
  [pseudo_metric_space α] [pseudo_metric_space β]
  (f : α → β) (h) : ⇑(mk_of_dist_eq f h : dilation α β) = f := rfl

@[simp] lemma mk_coe_of_dist_eq {α β}
  [pseudo_metric_space α] [pseudo_metric_space β]
  (f : dilation α β) (h) : dilation.mk_of_dist_eq f h = f :=
ext $ λ _, rfl

end setup

section pseudo_emetric_dilation
variables [pseudo_emetric_space α] [pseudo_emetric_space β] [pseudo_emetric_space γ]
variables [dilation_class F α β] [dilation_class G β γ]
variables (f : F) (g : G) {x y z : α}  {s : set α}

lemma lipschitz : lipschitz_with (ratio f) (f : α → β) := λ x y, (edist_eq f x y).le

lemma antilipschitz : antilipschitz_with (ratio f)⁻¹ (f : α → β) :=
λ x y, have hr : ratio f ≠ 0 := ratio_ne_zero f, by exact_mod_cast
  (ennreal.mul_le_iff_le_inv (ennreal.coe_ne_zero.2 hr) ennreal.coe_ne_top).1 (edist_eq f x y).ge

/-- A dilation from an emetric space is injective -/
protected lemma injective {α : Type*} [emetric_space α]  [dilation_class F α β] (f : F) :
  injective f := (antilipschitz f).injective

/-- The identity is a dilation -/
protected def id (α) [pseudo_emetric_space α] : dilation α α :=
{ to_fun := _root_.id,
  edist_eq' := ⟨1, one_ne_zero, λ x y, by simp only [id.def, ennreal.coe_one, one_mul]⟩ }

instance : inhabited (dilation α α) := ⟨dilation.id α⟩

@[simp, protected] lemma coe_id : ⇑(dilation.id α) = id := rfl

lemma id_ratio : ratio (dilation.id α) = 1 :=
begin
  by_cases h : ∀ x y : α, edist x y = 0 ∨ edist x y = ∞,
  { rw [ratio, if_pos h] },
  { push_neg at h,
    rcases h with ⟨x, y, hne⟩,
    refine (ratio_unique hne.1 hne.2 _).symm,
    simp }
end

/-- The composition of dilations is a dilation -/
def comp (g : dilation β γ) (f : dilation α β) : dilation α γ :=
{ to_fun := g ∘ f,
  edist_eq' := ⟨ratio g * ratio f,
    mul_ne_zero (ratio_ne_zero g) (ratio_ne_zero f),
    λ x y, by { simp only [edist_eq, ennreal.coe_mul], ring, }⟩ }

lemma comp_assoc {δ : Type*} [pseudo_emetric_space δ]
  (f : dilation α β) (g : dilation β γ) (h : dilation γ δ) :
  (h.comp g).comp f = h.comp (g.comp f) := rfl

@[simp] lemma coe_comp (g : dilation β γ) (f : dilation α β) :
  (g.comp f : α → γ) = g ∘ f := rfl

lemma comp_apply (g : dilation β γ) (f : dilation α β) (x : α) :
  (g.comp f : α → γ) x = (g (f x)) := rfl

/-- Ratio of the composition `g.comp f` of two dilations is the product of their ratios. We assume
that the domain `α` of `f` is nontrivial, otherwise `ratio f = ratio (g.comp f) = 1` but `ratio g`
may have any value. -/
@[simp] lemma comp_ratio
  {g : dilation β γ} {f : dilation α β} (hne : ∃ x y : α, edist x y ≠ 0 ∧ edist x y ≠ ⊤) :
  ratio (g.comp f) = ratio g * ratio f :=
begin
  rcases hne with ⟨x, y, hα⟩,
  have hgf := (edist_eq (g.comp f) x y).symm,
  simp only [dist_eq, coe_comp, ← mul_assoc, mul_eq_mul_right_iff] at hgf,
  rw [edist_eq, edist_eq, ← mul_assoc, ennreal.mul_eq_mul_right hα.1 hα.2] at hgf,
  rwa [← ennreal.coe_eq_coe, ennreal.coe_mul],
end

@[simp] lemma comp_id (f : dilation α β) : f.comp (dilation.id α) = f := ext $ λ x, rfl

@[simp] lemma id_comp (f : dilation α β) : (dilation.id β).comp f = f := ext $ λ x, rfl

instance : monoid (dilation α α) :=
{ one := dilation.id α,
  mul := comp,
  mul_one := comp_id,
  one_mul := id_comp,
  mul_assoc := λ f g h, comp_assoc _ _ _ }

lemma one_def : (1 : dilation α α) = dilation.id α := rfl
lemma mul_def (f g : dilation α α) : f * g = f.comp g := rfl

@[simp] lemma coe_one : ⇑(1 : dilation α α) = _root_.id := rfl
@[simp] lemma coe_mul (f g : dilation α α) : ⇑(f * g) = f ∘ g := rfl

lemma cancel_right {g₁ g₂ : dilation β γ} {f : dilation α β} (hf : surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, dilation.ext $ hf.forall.2 (ext_iff.1 h), λ h, h ▸ rfl⟩

lemma cancel_left {g : dilation β γ} {f₁ f₂ : dilation α β} (hg : injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, dilation.ext $ λ x, hg $ by rw [← comp_apply, h, comp_apply], λ h, h ▸ rfl⟩

/-- A dilation from a metric space is a uniform inducing map -/
protected theorem uniform_inducing : uniform_inducing (f : α → β) :=
(antilipschitz f).uniform_inducing (lipschitz f).uniform_continuous

lemma tendsto_nhds_iff {ι : Type*} {g : ι → α} {a : filter ι} {b : α} :
  filter.tendsto g a (𝓝 b) ↔ filter.tendsto ((f : α → β) ∘ g) a (𝓝 (f b)) :=
(dilation.uniform_inducing f).inducing.tendsto_nhds_iff

/-- A dilation is continuous. -/
lemma to_continuous : continuous (f : α → β) :=
(lipschitz f).continuous

/-- Dilations scale the diameter by `ratio f` in pseudoemetric spaces. -/
lemma ediam_image (s : set α) :
  emetric.diam ((f : α → β) '' s) = ratio f * emetric.diam s :=
begin
  refine ((lipschitz f).ediam_image_le s).antisymm _,
  apply ennreal.mul_le_of_le_div',
  rw [div_eq_mul_inv, mul_comm, ← ennreal.coe_inv],
  exacts [(antilipschitz f).le_mul_ediam_image s, ratio_ne_zero f],
end

/-- A dilation scales the diameter of the range by `ratio f`. -/
lemma ediam_range :
  emetric.diam (range (f : α → β)) = ratio f * emetric.diam (univ : set α) :=
by { rw ← image_univ, exact ediam_image f univ }

/-- A dilation maps balls to balls and scales the radius by `ratio f`. -/
lemma maps_to_emetric_ball (x : α) (r : ℝ≥0∞) :
  maps_to (f : α → β) (emetric.ball x r) (emetric.ball (f x) (ratio f * r)) :=
λ y hy, (edist_eq f y x).trans_lt $
  (ennreal.mul_lt_mul_left (ennreal.coe_ne_zero.2 $ ratio_ne_zero f) ennreal.coe_ne_top).2 hy

/-- A dilation maps closed balls to closed balls and scales the radius by `ratio f`. -/
lemma maps_to_emetric_closed_ball (x : α) (r' : ℝ≥0∞) :
  maps_to (f : α → β) (emetric.closed_ball x r') (emetric.closed_ball (f x) (ratio f * r')) :=
λ y hy, (edist_eq f y x).trans_le $ mul_le_mul_left' hy _

lemma comp_continuous_on_iff {γ} [topological_space γ] {g : γ → α} {s : set γ} :
  continuous_on ((f : α → β) ∘ g) s ↔ continuous_on g s :=
(dilation.uniform_inducing f).inducing.continuous_on_iff.symm

lemma comp_continuous_iff {γ} [topological_space γ] {g : γ → α} :
  continuous ((f : α → β) ∘ g) ↔ continuous g :=
(dilation.uniform_inducing f).inducing.continuous_iff.symm

end pseudo_emetric_dilation --section

section emetric_dilation
variables [emetric_space α]

/-- A dilation from a metric space is a uniform embedding -/
protected theorem uniform_embedding [pseudo_emetric_space β] [dilation_class F α β]
  (f : F) : uniform_embedding f :=
(antilipschitz f).uniform_embedding (lipschitz f).uniform_continuous

/-- A dilation from a metric space is an embedding -/
protected theorem embedding [pseudo_emetric_space β] [dilation_class F α β]
  (f : F) : embedding (f : α → β) :=
(dilation.uniform_embedding f).embedding

/-- A dilation from a complete emetric space is a closed embedding -/
protected theorem closed_embedding [complete_space α] [emetric_space β] [dilation_class F α β]
  (f : F) : closed_embedding f :=
(antilipschitz f).closed_embedding (lipschitz f).uniform_continuous

end emetric_dilation --section

section pseudo_metric_dilation
variables [pseudo_metric_space α] [pseudo_metric_space β] [dilation_class F α β] (f : F)

/-- A dilation scales the diameter by `ratio f` in pseudometric spaces. -/
lemma diam_image (s : set α) : metric.diam ((f : α → β) '' s) = ratio f * metric.diam s :=
by { simp [metric.diam, ediam_image, ennreal.to_real_mul], }

lemma diam_range : metric.diam (range (f : α → β)) = ratio f * metric.diam (univ : set α) :=
by rw [← image_univ, diam_image]

/-- A dilation maps balls to balls and scales the radius by `ratio f`. -/
lemma maps_to_ball (x : α) (r' : ℝ) :
  maps_to (f : α → β) (metric.ball x r') (metric.ball (f x) (ratio f * r')) :=
λ y hy, (dist_eq f y x).trans_lt $ (mul_lt_mul_left $ nnreal.coe_pos.2 $ ratio_pos f).2 hy

/-- A dilation maps spheres to spheres and scales the radius by `ratio f`. -/
lemma maps_to_sphere (x : α) (r' : ℝ) :
  maps_to (f : α → β) (metric.sphere x r') (metric.sphere (f x) (ratio f * r')) :=
λ y hy, metric.mem_sphere.mp hy ▸ dist_eq f y x

/-- A dilation maps closed balls to closed balls and scales the radius by `ratio f`. -/
lemma maps_to_closed_ball (x : α) (r' : ℝ) :
  maps_to (f : α → β) (metric.closed_ball x r') (metric.closed_ball (f x) (ratio f * r')) :=
λ y hy, (dist_eq f y x).trans_le $ mul_le_mul_of_nonneg_left hy (nnreal.coe_nonneg _)

end pseudo_metric_dilation -- section

end dilation
