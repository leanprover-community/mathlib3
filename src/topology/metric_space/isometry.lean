/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Isometries of emetric and metric spaces
Authors: Sébastien Gouëzel
-/
import topology.metric_space.antilipschitz

/-!
# Isometries

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define isometries, i.e., maps between emetric spaces that preserve
the edistance (on metric spaces, these are exactly the maps that preserve distances),
and prove their basic properties. We also introduce isometric bijections.

Since a lot of elementary properties don't require `eq_of_dist_eq_zero` we start setting up the
theory for `pseudo_metric_space` and we specialize to `metric_space` when needed.
-/

noncomputable theory

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

open function set
open_locale topology ennreal

/-- An isometry (also known as isometric embedding) is a map preserving the edistance
between pseudoemetric spaces, or equivalently the distance between pseudometric space.  -/
def isometry [pseudo_emetric_space α] [pseudo_emetric_space β] (f : α → β) : Prop :=
∀x1 x2 : α, edist (f x1) (f x2) = edist x1 x2

/-- On pseudometric spaces, a map is an isometry if and only if it preserves nonnegative
distances. -/
lemma isometry_iff_nndist_eq [pseudo_metric_space α] [pseudo_metric_space β] {f : α → β} :
  isometry f ↔ (∀x y, nndist (f x) (f y) = nndist x y) :=
by simp only [isometry, edist_nndist, ennreal.coe_eq_coe]

/-- On pseudometric spaces, a map is an isometry if and only if it preserves distances. -/
lemma isometry_iff_dist_eq [pseudo_metric_space α] [pseudo_metric_space β] {f : α → β} :
  isometry f ↔ (∀x y, dist (f x) (f y) = dist x y) :=
by simp only [isometry_iff_nndist_eq, ← coe_nndist, nnreal.coe_eq]

/-- An isometry preserves distances. -/
alias isometry_iff_dist_eq ↔ isometry.dist_eq _

/-- A map that preserves distances is an isometry -/
alias isometry_iff_dist_eq ↔ _ isometry.of_dist_eq

/-- An isometry preserves non-negative distances. -/
alias isometry_iff_nndist_eq ↔ isometry.nndist_eq _

/-- A map that preserves non-negative distances is an isometry. -/
alias isometry_iff_nndist_eq ↔ _ isometry.of_nndist_eq

namespace isometry

section pseudo_emetric_isometry

variables [pseudo_emetric_space α] [pseudo_emetric_space β] [pseudo_emetric_space γ]
variables {f : α → β} {x y z : α}  {s : set α}

/-- An isometry preserves edistances. -/
theorem edist_eq (hf : isometry f) (x y : α) : edist (f x) (f y) = edist x y := hf x y

lemma lipschitz (h : isometry f) : lipschitz_with 1 f :=
lipschitz_with.of_edist_le $ λ x y, (h x y).le

lemma antilipschitz (h : isometry f) : antilipschitz_with 1 f :=
λ x y, by simp only [h x y, ennreal.coe_one, one_mul, le_refl]

/-- Any map on a subsingleton is an isometry -/
@[nontriviality] theorem _root_.isometry_subsingleton [subsingleton α] : isometry f :=
λx y, by rw subsingleton.elim x y; simp

/-- The identity is an isometry -/
lemma _root_.isometry_id : isometry (id : α → α) := λ x y, rfl

lemma prod_map {δ} [pseudo_emetric_space δ] {f : α → β} {g : γ → δ} (hf : isometry f)
  (hg : isometry g) : isometry (prod.map f g) :=
λ x y, by simp only [prod.edist_eq, hf.edist_eq, hg.edist_eq, prod_map]

lemma _root_.isometry_dcomp {ι} [fintype ι] {α β : ι → Type*} [Π i, pseudo_emetric_space (α i)]
  [Π i, pseudo_emetric_space (β i)] (f : Π i, α i → β i) (hf : ∀ i, isometry (f i)) :
  isometry (dcomp f) :=
λ x y, by simp only [edist_pi_def, (hf _).edist_eq]

/-- The composition of isometries is an isometry. -/
theorem comp {g : β → γ} {f : α → β} (hg : isometry g) (hf : isometry f) : isometry (g ∘ f) :=
λ x y, (hg _ _).trans (hf _ _)

/-- An isometry from a metric space is a uniform continuous map -/
protected theorem uniform_continuous (hf : isometry f) : uniform_continuous f :=
hf.lipschitz.uniform_continuous

/-- An isometry from a metric space is a uniform inducing map -/
protected theorem uniform_inducing (hf : isometry f) : uniform_inducing f :=
hf.antilipschitz.uniform_inducing hf.uniform_continuous

lemma tendsto_nhds_iff {ι : Type*} {f : α → β} {g : ι → α} {a : filter ι} {b : α}
  (hf : isometry f) :
  filter.tendsto g a (𝓝 b) ↔ filter.tendsto (f ∘ g) a (𝓝 (f b)) :=
hf.uniform_inducing.inducing.tendsto_nhds_iff

/-- An isometry is continuous. -/
protected lemma continuous (hf : isometry f) : continuous f := hf.lipschitz.continuous

/-- The right inverse of an isometry is an isometry. -/
lemma right_inv {f : α → β} {g : β → α} (h : isometry f) (hg : right_inverse g f) :
  isometry g :=
λ x y, by rw [← h, hg _, hg _]

lemma preimage_emetric_closed_ball (h : isometry f) (x : α) (r : ℝ≥0∞) :
  f ⁻¹' (emetric.closed_ball (f x) r) = emetric.closed_ball x r :=
by { ext y, simp [h.edist_eq] }

lemma preimage_emetric_ball (h : isometry f) (x : α) (r : ℝ≥0∞) :
  f ⁻¹' (emetric.ball (f x) r) = emetric.ball x r :=
by { ext y, simp [h.edist_eq] }

/-- Isometries preserve the diameter in pseudoemetric spaces. -/
lemma ediam_image (hf : isometry f) (s : set α) : emetric.diam (f '' s) = emetric.diam s :=
eq_of_forall_ge_iff $ λ d,
by simp only [emetric.diam_le_iff, ball_image_iff, hf.edist_eq]

lemma ediam_range (hf : isometry f) : emetric.diam (range f) = emetric.diam (univ : set α) :=
by { rw ← image_univ, exact hf.ediam_image univ }

lemma maps_to_emetric_ball (hf : isometry f) (x : α) (r : ℝ≥0∞) :
  maps_to f (emetric.ball x r) (emetric.ball (f x) r) :=
(hf.preimage_emetric_ball x r).ge

lemma maps_to_emetric_closed_ball (hf : isometry f) (x : α) (r : ℝ≥0∞) :
  maps_to f (emetric.closed_ball x r) (emetric.closed_ball (f x) r) :=
(hf.preimage_emetric_closed_ball x r).ge

/-- The injection from a subtype is an isometry -/
lemma _root_.isometry_subtype_coe {s : set α} : isometry (coe : s → α) :=
λx y, rfl

lemma comp_continuous_on_iff {γ} [topological_space γ] (hf : isometry f) {g : γ → α} {s : set γ} :
  continuous_on (f ∘ g) s ↔ continuous_on g s :=
hf.uniform_inducing.inducing.continuous_on_iff.symm

lemma comp_continuous_iff {γ} [topological_space γ] (hf : isometry f) {g : γ → α} :
  continuous (f ∘ g) ↔ continuous g :=
hf.uniform_inducing.inducing.continuous_iff.symm

end pseudo_emetric_isometry --section

section emetric_isometry
variables [emetric_space α] [pseudo_emetric_space β] {f : α → β}

/-- An isometry from an emetric space is injective -/
protected lemma injective (h : isometry f) : injective f := h.antilipschitz.injective

/-- An isometry from an emetric space is a uniform embedding -/
protected theorem uniform_embedding (hf : isometry f) : uniform_embedding f :=
hf.antilipschitz.uniform_embedding hf.lipschitz.uniform_continuous

/-- An isometry from an emetric space is an embedding -/
protected theorem embedding (hf : isometry f) : embedding f :=
hf.uniform_embedding.embedding

/-- An isometry from a complete emetric space is a closed embedding -/
theorem closed_embedding [complete_space α] [emetric_space γ]
  {f : α → γ} (hf : isometry f) : closed_embedding f :=
hf.antilipschitz.closed_embedding hf.lipschitz.uniform_continuous

end emetric_isometry --section

section pseudo_metric_isometry

variables [pseudo_metric_space α] [pseudo_metric_space β] {f : α → β}

/-- An isometry preserves the diameter in pseudometric spaces. -/
lemma diam_image (hf : isometry f) (s : set α) : metric.diam (f '' s) = metric.diam s :=
by rw [metric.diam, metric.diam, hf.ediam_image]

lemma diam_range (hf : isometry f) : metric.diam (range f) = metric.diam (univ : set α) :=
by { rw ← image_univ, exact hf.diam_image univ }

lemma preimage_set_of_dist (hf : isometry f) (x : α) (p : ℝ → Prop) :
  f ⁻¹' {y | p (dist y (f x))} = {y | p (dist y x)} :=
by { ext y, simp [hf.dist_eq] }

lemma preimage_closed_ball (hf : isometry f) (x : α) (r : ℝ) :
  f ⁻¹' (metric.closed_ball (f x) r) = metric.closed_ball x r :=
hf.preimage_set_of_dist x (≤ r)

lemma preimage_ball (hf : isometry f) (x : α) (r : ℝ) :
  f ⁻¹' (metric.ball (f x) r) = metric.ball x r :=
hf.preimage_set_of_dist x (< r)

lemma preimage_sphere (hf : isometry f) (x : α) (r : ℝ) :
  f ⁻¹' (metric.sphere (f x) r) = metric.sphere x r :=
hf.preimage_set_of_dist x (= r)

lemma maps_to_ball (hf : isometry f) (x : α) (r : ℝ) :
  maps_to f (metric.ball x r) (metric.ball (f x) r) :=
(hf.preimage_ball x r).ge

lemma maps_to_sphere (hf : isometry f) (x : α) (r : ℝ) :
  maps_to f (metric.sphere x r) (metric.sphere (f x) r) :=
(hf.preimage_sphere x r).ge

lemma maps_to_closed_ball (hf : isometry f) (x : α) (r : ℝ) :
  maps_to f (metric.closed_ball x r) (metric.closed_ball (f x) r) :=
(hf.preimage_closed_ball x r).ge

end pseudo_metric_isometry -- section

end isometry -- namespace

/-- A uniform embedding from a uniform space to a metric space is an isometry with respect to the
induced metric space structure on the source space. -/
lemma uniform_embedding.to_isometry {α β} [uniform_space α] [metric_space β] {f : α → β}
  (h : uniform_embedding f) :
  @isometry α β
    (@pseudo_metric_space.to_pseudo_emetric_space α
      (@metric_space.to_pseudo_metric_space α (h.comap_metric_space f)))
    (by apply_instance) f :=
begin
  apply isometry.of_dist_eq,
  assume x y,
  refl
end

/-- An embedding from a topological space to a metric space is an isometry with respect to the
induced metric space structure on the source space. -/
lemma embedding.to_isometry {α β} [topological_space α] [metric_space β] {f : α → β}
  (h : embedding f) :
  @isometry α β
    (@pseudo_metric_space.to_pseudo_emetric_space α
      (@metric_space.to_pseudo_metric_space α (h.comap_metric_space f)))
    (by apply_instance) f :=
begin
  apply isometry.of_dist_eq,
  assume x y,
  refl
end

/-- `α` and `β` are isometric if there is an isometric bijection between them. -/
@[nolint has_nonempty_instance] -- such a bijection need not exist
structure isometry_equiv (α β : Type*) [pseudo_emetric_space α] [pseudo_emetric_space β]
  extends α ≃ β :=
(isometry_to_fun  : isometry to_fun)

infix ` ≃ᵢ `:25 := isometry_equiv

namespace isometry_equiv

section pseudo_emetric_space
variables [pseudo_emetric_space α] [pseudo_emetric_space β] [pseudo_emetric_space γ]

instance : has_coe_to_fun (α ≃ᵢ β) (λ _, α → β) := ⟨λe, e.to_equiv⟩

lemma coe_eq_to_equiv (h : α ≃ᵢ β) (a : α) : h a = h.to_equiv a := rfl

@[simp] lemma coe_to_equiv (h : α ≃ᵢ β) : ⇑h.to_equiv = h := rfl

protected lemma isometry (h : α ≃ᵢ β) : isometry h := h.isometry_to_fun

protected lemma bijective (h : α ≃ᵢ β) : bijective h := h.to_equiv.bijective
protected lemma injective (h : α ≃ᵢ β) : injective h := h.to_equiv.injective
protected lemma surjective (h : α ≃ᵢ β) : surjective h := h.to_equiv.surjective

protected lemma edist_eq (h : α ≃ᵢ β) (x y : α) : edist (h x) (h y) = edist x y :=
h.isometry.edist_eq x y

protected lemma dist_eq {α β : Type*} [pseudo_metric_space α] [pseudo_metric_space β] (h : α ≃ᵢ β)
  (x y : α) : dist (h x) (h y) = dist x y :=
h.isometry.dist_eq x y

protected lemma nndist_eq {α β : Type*} [pseudo_metric_space α] [pseudo_metric_space β] (h : α ≃ᵢ β)
  (x y : α) : nndist (h x) (h y) = nndist x y :=
h.isometry.nndist_eq x y

protected lemma continuous (h : α ≃ᵢ β) : continuous h := h.isometry.continuous

@[simp] lemma ediam_image (h : α ≃ᵢ β) (s : set α) : emetric.diam (h '' s) = emetric.diam s :=
h.isometry.ediam_image s

lemma to_equiv_inj : ∀ ⦃h₁ h₂ : α ≃ᵢ β⦄, (h₁.to_equiv = h₂.to_equiv) → h₁ = h₂
| ⟨e₁, h₁⟩ ⟨e₂, h₂⟩ H := by { dsimp at H, subst e₁ }

@[ext] lemma ext ⦃h₁ h₂ : α ≃ᵢ β⦄ (H : ∀ x, h₁ x = h₂ x) : h₁ = h₂ :=
to_equiv_inj $ equiv.ext H

/-- Alternative constructor for isometric bijections,
taking as input an isometry, and a right inverse. -/
def mk' {α : Type u} [emetric_space α] (f : α → β) (g : β → α) (hfg : ∀ x, f (g x) = x)
  (hf : isometry f) : α ≃ᵢ β :=
{ to_fun := f,
  inv_fun := g,
  left_inv := λ x, hf.injective $ hfg _,
  right_inv := hfg,
  isometry_to_fun := hf }

/-- The identity isometry of a space. -/
protected def refl (α : Type*) [pseudo_emetric_space α] : α ≃ᵢ α :=
{ isometry_to_fun := isometry_id, .. equiv.refl α }

/-- The composition of two isometric isomorphisms, as an isometric isomorphism. -/
protected def trans (h₁ : α ≃ᵢ β) (h₂ : β ≃ᵢ γ) : α ≃ᵢ γ :=
{ isometry_to_fun  := h₂.isometry_to_fun.comp h₁.isometry_to_fun,
  .. equiv.trans h₁.to_equiv h₂.to_equiv }

@[simp] lemma trans_apply (h₁ : α ≃ᵢ β) (h₂ : β ≃ᵢ γ) (x : α) : h₁.trans h₂ x = h₂ (h₁ x) := rfl

/-- The inverse of an isometric isomorphism, as an isometric isomorphism. -/
protected def symm (h : α ≃ᵢ β) : β ≃ᵢ α :=
{ isometry_to_fun  := h.isometry.right_inv h.right_inv,
  to_equiv := h.to_equiv.symm }

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def simps.apply (h : α ≃ᵢ β) : α → β := h
/-- See Note [custom simps projection] -/
def simps.symm_apply (h : α ≃ᵢ β) : β → α := h.symm

initialize_simps_projections isometry_equiv
  (to_equiv_to_fun → apply, to_equiv_inv_fun → symm_apply)

@[simp] lemma symm_symm (h : α ≃ᵢ β) : h.symm.symm = h := to_equiv_inj h.to_equiv.symm_symm

@[simp] lemma apply_symm_apply (h : α ≃ᵢ β) (y : β) : h (h.symm y) = y :=
h.to_equiv.apply_symm_apply y

@[simp] lemma symm_apply_apply (h : α ≃ᵢ β) (x : α) : h.symm (h x) = x :=
h.to_equiv.symm_apply_apply x

lemma symm_apply_eq (h : α ≃ᵢ β) {x : α} {y : β} :
  h.symm y = x ↔ y = h x :=
h.to_equiv.symm_apply_eq

lemma eq_symm_apply (h : α ≃ᵢ β) {x : α} {y : β} :
  x = h.symm y ↔ h x = y :=
h.to_equiv.eq_symm_apply

lemma symm_comp_self (h : α ≃ᵢ β) : ⇑h.symm ∘ ⇑h = id :=
funext $ assume a, h.to_equiv.left_inv a

lemma self_comp_symm (h : α ≃ᵢ β) : ⇑h ∘ ⇑h.symm = id :=
funext $ assume a, h.to_equiv.right_inv a

@[simp] lemma range_eq_univ (h : α ≃ᵢ β) : range h = univ :=
h.to_equiv.range_eq_univ

lemma image_symm (h : α ≃ᵢ β) : image h.symm = preimage h :=
image_eq_preimage_of_inverse h.symm.to_equiv.left_inv h.symm.to_equiv.right_inv

lemma preimage_symm (h : α ≃ᵢ β) : preimage h.symm = image h :=
(image_eq_preimage_of_inverse h.to_equiv.left_inv h.to_equiv.right_inv).symm

@[simp] lemma symm_trans_apply (h₁ : α ≃ᵢ β) (h₂ : β ≃ᵢ γ) (x : γ) :
  (h₁.trans h₂).symm x = h₁.symm (h₂.symm x) := rfl

lemma ediam_univ (h : α ≃ᵢ β) : emetric.diam (univ : set α) = emetric.diam (univ : set β) :=
by rw [← h.range_eq_univ, h.isometry.ediam_range]

@[simp] lemma ediam_preimage (h : α ≃ᵢ β) (s : set β) : emetric.diam (h ⁻¹' s) = emetric.diam s :=
by rw [← image_symm, ediam_image]

@[simp] lemma preimage_emetric_ball (h : α ≃ᵢ β) (x : β) (r : ℝ≥0∞) :
  h ⁻¹' (emetric.ball x r) = emetric.ball (h.symm x) r :=
by rw [← h.isometry.preimage_emetric_ball (h.symm x) r, h.apply_symm_apply]

@[simp] lemma preimage_emetric_closed_ball (h : α ≃ᵢ β) (x : β) (r : ℝ≥0∞) :
  h ⁻¹' (emetric.closed_ball x r) = emetric.closed_ball (h.symm x) r :=
by rw [← h.isometry.preimage_emetric_closed_ball (h.symm x) r, h.apply_symm_apply]

@[simp] lemma image_emetric_ball (h : α ≃ᵢ β) (x : α) (r : ℝ≥0∞) :
  h '' (emetric.ball x r) = emetric.ball (h x) r :=
by rw [← h.preimage_symm, h.symm.preimage_emetric_ball, symm_symm]

@[simp] lemma image_emetric_closed_ball (h : α ≃ᵢ β) (x : α) (r : ℝ≥0∞) :
  h '' (emetric.closed_ball x r) = emetric.closed_ball (h x) r :=
by rw [← h.preimage_symm, h.symm.preimage_emetric_closed_ball, symm_symm]

/-- The (bundled) homeomorphism associated to an isometric isomorphism. -/
@[simps to_equiv] protected def to_homeomorph (h : α ≃ᵢ β) : α ≃ₜ β :=
{ continuous_to_fun  := h.continuous,
  continuous_inv_fun := h.symm.continuous,
  to_equiv := h.to_equiv }

@[simp] lemma coe_to_homeomorph (h : α ≃ᵢ β) : ⇑(h.to_homeomorph) = h := rfl

@[simp] lemma coe_to_homeomorph_symm (h : α ≃ᵢ β) : ⇑(h.to_homeomorph.symm) = h.symm := rfl

@[simp] lemma comp_continuous_on_iff {γ} [topological_space γ] (h : α ≃ᵢ β)
  {f : γ → α} {s : set γ} :
  continuous_on (h ∘ f) s ↔ continuous_on f s :=
h.to_homeomorph.comp_continuous_on_iff _ _

@[simp] lemma comp_continuous_iff {γ} [topological_space γ] (h : α ≃ᵢ β) {f : γ → α} :
  continuous (h ∘ f) ↔ continuous f :=
h.to_homeomorph.comp_continuous_iff

@[simp] lemma comp_continuous_iff' {γ} [topological_space γ] (h : α ≃ᵢ β) {f : β → γ} :
  continuous (f ∘ h) ↔ continuous f :=
h.to_homeomorph.comp_continuous_iff'

/-- The group of isometries. -/
instance : group (α ≃ᵢ α) :=
  { one := isometry_equiv.refl _,
    mul := λ e₁ e₂, e₂.trans e₁,
    inv := isometry_equiv.symm,
    mul_assoc := λ e₁ e₂ e₃, rfl,
    one_mul := λ e, ext $ λ _, rfl,
    mul_one := λ e, ext $ λ _, rfl,
    mul_left_inv := λ e, ext e.symm_apply_apply }

@[simp] lemma coe_one : ⇑(1 : α ≃ᵢ α) = id := rfl

@[simp] lemma coe_mul (e₁ e₂ : α ≃ᵢ α) : ⇑(e₁ * e₂) = e₁ ∘ e₂ := rfl

lemma mul_apply (e₁ e₂ : α ≃ᵢ α) (x : α) : (e₁ * e₂) x = e₁ (e₂ x) := rfl

@[simp] lemma inv_apply_self (e : α ≃ᵢ α) (x: α) : e⁻¹ (e x) = x := e.symm_apply_apply x

@[simp] lemma apply_inv_self (e : α ≃ᵢ α) (x: α) : e (e⁻¹ x) = x := e.apply_symm_apply x

protected lemma complete_space [complete_space β] (e : α ≃ᵢ β) : complete_space α :=
complete_space_of_is_complete_univ $ is_complete_of_complete_image e.isometry.uniform_inducing $
  by rwa [set.image_univ, isometry_equiv.range_eq_univ, ← complete_space_iff_is_complete_univ]

lemma complete_space_iff (e : α ≃ᵢ β) : complete_space α ↔ complete_space β :=
by { split; introI H, exacts [e.symm.complete_space, e.complete_space] }

end pseudo_emetric_space

section pseudo_metric_space

variables [pseudo_metric_space α] [pseudo_metric_space β] (h : α ≃ᵢ β)

@[simp] lemma diam_image (s : set α) : metric.diam (h '' s) = metric.diam s :=
h.isometry.diam_image s

@[simp] lemma diam_preimage (s : set β) : metric.diam (h ⁻¹' s) = metric.diam s :=
by rw [← image_symm, diam_image]

lemma diam_univ : metric.diam (univ : set α) = metric.diam (univ : set β) :=
congr_arg ennreal.to_real h.ediam_univ

@[simp] lemma preimage_ball (h : α ≃ᵢ β) (x : β) (r : ℝ) :
  h ⁻¹' (metric.ball x r) = metric.ball (h.symm x) r :=
by rw [← h.isometry.preimage_ball (h.symm x) r, h.apply_symm_apply]

@[simp] lemma preimage_sphere (h : α ≃ᵢ β) (x : β) (r : ℝ) :
  h ⁻¹' (metric.sphere x r) = metric.sphere (h.symm x) r :=
by rw [← h.isometry.preimage_sphere (h.symm x) r, h.apply_symm_apply]

@[simp] lemma preimage_closed_ball (h : α ≃ᵢ β) (x : β) (r : ℝ) :
  h ⁻¹' (metric.closed_ball x r) = metric.closed_ball (h.symm x) r :=
by rw [← h.isometry.preimage_closed_ball (h.symm x) r, h.apply_symm_apply]

@[simp] lemma image_ball (h : α ≃ᵢ β) (x : α) (r : ℝ) :
  h '' (metric.ball x r) = metric.ball (h x) r :=
by rw [← h.preimage_symm, h.symm.preimage_ball, symm_symm]

@[simp] lemma image_sphere (h : α ≃ᵢ β) (x : α) (r : ℝ) :
  h '' (metric.sphere x r) = metric.sphere (h x) r :=
by rw [← h.preimage_symm, h.symm.preimage_sphere, symm_symm]

@[simp] lemma image_closed_ball (h : α ≃ᵢ β) (x : α) (r : ℝ) :
  h '' (metric.closed_ball x r) = metric.closed_ball (h x) r :=
by rw [← h.preimage_symm, h.symm.preimage_closed_ball, symm_symm]

end pseudo_metric_space

end isometry_equiv

/-- An isometry induces an isometric isomorphism between the source space and the
range of the isometry. -/
@[simps to_equiv apply { simp_rhs := tt }]
def isometry.isometry_equiv_on_range [emetric_space α] [pseudo_emetric_space β] {f : α → β}
  (h : isometry f) : α ≃ᵢ range f :=
{ isometry_to_fun := λx y, by simpa [subtype.edist_eq] using h x y,
  to_equiv := equiv.of_injective f h.injective }
