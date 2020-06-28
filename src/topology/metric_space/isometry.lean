/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Isometries of emetric and metric spaces
Authors: Sébastien Gouëzel
-/
import topology.bounded_continuous_function
import topology.opens

/-!
# Isometries

We define isometries, i.e., maps between emetric spaces that preserve
the edistance (on metric spaces, these are exactly the maps that preserve distances),
and prove their basic properties. We also introduce isometric bijections.
-/

noncomputable theory

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

open function set

/-- An isometry (also known as isometric embedding) is a map preserving the edistance
between emetric spaces, or equivalently the distance between metric space.  -/
def isometry [emetric_space α] [emetric_space β] (f : α → β) : Prop :=
∀x1 x2 : α, edist (f x1) (f x2) = edist x1 x2

/-- On metric spaces, a map is an isometry if and only if it preserves distances. -/
lemma isometry_emetric_iff_metric [metric_space α] [metric_space β] {f : α → β} :
  isometry f ↔ (∀x y, dist (f x) (f y) = dist x y) :=
⟨assume H x y, by simp [dist_edist, H x y],
assume H x y, by simp [edist_dist, H x y]⟩

/-- An isometry preserves edistances. -/
theorem isometry.edist_eq [emetric_space α] [emetric_space β] {f : α → β} (hf : isometry f)
  (x y : α) :
  edist (f x) (f y) = edist x y :=
hf x y

/-- An isometry preserves distances. -/
theorem isometry.dist_eq [metric_space α] [metric_space β] {f : α → β} (hf : isometry f) (x y : α) :
  dist (f x) (f y) = dist x y :=
by rw [dist_edist, dist_edist, hf]

section emetric_isometry

variables [emetric_space α] [emetric_space β] [emetric_space γ]
variables {f : α → β} {x y z : α}  {s : set α}

lemma isometry.lipschitz (h : isometry f) : lipschitz_with 1 f :=
lipschitz_with.of_edist_le $ λ x y, le_of_eq (h x y)

lemma isometry.antilipschitz (h : isometry f) : antilipschitz_with 1 f :=
λ x y, by simp only [h x y, ennreal.coe_one, one_mul, le_refl]

/-- An isometry is injective -/
lemma isometry.injective (h : isometry f) : injective f := h.antilipschitz.injective

/-- Any map on a subsingleton is an isometry -/
theorem isometry_subsingleton [subsingleton α] : isometry f :=
λx y, by rw subsingleton.elim x y; simp

/-- The identity is an isometry -/
lemma isometry_id : isometry (id : α → α) :=
λx y, rfl

/-- The composition of isometries is an isometry -/
theorem isometry.comp {g : β → γ} {f : α → β} (hg : isometry g) (hf : isometry f) : isometry (g ∘ f) :=
assume x y, calc
  edist ((g ∘ f) x) ((g ∘ f) y) = edist (f x) (f y) : hg _ _
                            ... = edist x y : hf _ _

/-- An isometry is an embedding -/
theorem isometry.uniform_embedding (hf : isometry f) : uniform_embedding f :=
hf.antilipschitz.uniform_embedding hf.lipschitz.uniform_continuous

/-- An isometry is continuous. -/
lemma isometry.continuous (hf : isometry f) : continuous f :=
hf.lipschitz.continuous

/-- The right inverse of an isometry is an isometry. -/
lemma isometry.right_inv {f : α → β} {g : β → α} (h : isometry f) (hg : right_inverse g f) :
  isometry g :=
λ x y, by rw [← h, hg _, hg _]

/-- Isometries preserve the diameter in emetric spaces. -/
lemma isometry.ediam_image (hf : isometry f) (s : set α) :
  emetric.diam (f '' s) = emetric.diam s :=
eq_of_forall_ge_iff $ λ d,
by simp only [emetric.diam_le_iff_forall_edist_le, ball_image_iff, hf.edist_eq]

lemma isometry.ediam_range (hf : isometry f) :
  emetric.diam (range f) = emetric.diam (univ : set α) :=
by { rw ← image_univ, exact hf.ediam_image univ }

/-- The injection from a subtype is an isometry -/
lemma isometry_subtype_coe {s : set α} : isometry (coe : s → α) :=
λx y, rfl

end emetric_isometry --section

/-- An isometry preserves the diameter in metric spaces. -/
lemma isometry.diam_image [metric_space α] [metric_space β]
  {f : α → β} (hf : isometry f) (s : set α) : metric.diam (f '' s) = metric.diam s :=
by rw [metric.diam, metric.diam, hf.ediam_image]

lemma isometry.diam_range [metric_space α] [metric_space β] {f : α → β} (hf : isometry f) :
  metric.diam (range f) = metric.diam (univ : set α) :=
by { rw ← image_univ, exact hf.diam_image univ }

/-- `α` and `β` are isometric if there is an isometric bijection between them. -/
structure isometric (α : Type*) (β : Type*) [emetric_space α] [emetric_space β]
  extends α ≃ β :=
(isometry_to_fun  : isometry to_fun)

infix ` ≃ᵢ `:25 := isometric

namespace isometric
variables [emetric_space α] [emetric_space β] [emetric_space γ]

instance : has_coe_to_fun (α ≃ᵢ β) := ⟨λ_, α → β, λe, e.to_equiv⟩

lemma coe_eq_to_equiv (h : α ≃ᵢ β) (a : α) : h a = h.to_equiv a := rfl

protected lemma isometry (h : α ≃ᵢ β) : isometry h := h.isometry_to_fun

protected lemma edist_eq (h : α ≃ᵢ β) (x y : α) : edist (h x) (h y) = edist x y :=
h.isometry.edist_eq x y

protected lemma dist_eq {α β : Type*} [metric_space α] [metric_space β] (h : α ≃ᵢ β) (x y : α) :
  dist (h x) (h y) = dist x y :=
h.isometry.dist_eq x y

protected lemma continuous (h : α ≃ᵢ β) : continuous h := h.isometry.continuous

lemma to_equiv_inj : ∀ ⦃h₁ h₂ : α ≃ᵢ β⦄, (h₁.to_equiv = h₂.to_equiv) → h₁ = h₂
| ⟨e₁, h₁⟩ ⟨e₂, h₂⟩ H := by { dsimp at H, subst e₁ }

@[ext] lemma ext ⦃h₁ h₂ : α ≃ᵢ β⦄ (H : ∀ x, h₁ x = h₂ x) : h₁ = h₂ :=
to_equiv_inj $ equiv.ext H

/-- Alternative constructor for isometric bijections,
taking as input an isometry, and a right inverse. -/
def mk' (f : α → β) (g : β → α) (hfg : ∀ x, f (g x) = x) (hf : isometry f) : α ≃ᵢ β :=
{ to_fun := f,
  inv_fun := g,
  left_inv := λ x, hf.injective $ hfg _,
  right_inv := hfg,
  isometry_to_fun := hf }

/-- The identity isometry of a space. -/
protected def refl (α : Type*) [emetric_space α] : α ≃ᵢ α :=
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

lemma range_coe (h : α ≃ᵢ β) : range h = univ :=
eq_univ_of_forall $ assume b, ⟨h.symm b, congr_fun h.self_comp_symm b⟩

lemma image_symm (h : α ≃ᵢ β) : image h.symm = preimage h :=
image_eq_preimage_of_inverse h.symm.to_equiv.left_inv h.symm.to_equiv.right_inv

lemma preimage_symm (h : α ≃ᵢ β) : preimage h.symm = image h :=
(image_eq_preimage_of_inverse h.to_equiv.left_inv h.to_equiv.right_inv).symm

@[simp] lemma symm_trans_apply (h₁ : α ≃ᵢ β) (h₂ : β ≃ᵢ γ) (x : γ) :
  (h₁.trans h₂).symm x = h₁.symm (h₂.symm x) := rfl

/-- The (bundled) homeomorphism associated to an isometric isomorphism. -/
protected def to_homeomorph (h : α ≃ᵢ β) : α ≃ₜ β :=
{ continuous_to_fun  := h.continuous,
  continuous_inv_fun := h.symm.continuous,
  .. h }

@[simp] lemma coe_to_homeomorph (h : α ≃ᵢ β) : ⇑(h.to_homeomorph) = h := rfl

@[simp] lemma to_homeomorph_to_equiv (h : α ≃ᵢ β) :
  h.to_homeomorph.to_equiv = h.to_equiv :=
rfl

/-- The group of isometries. -/
instance : group (α ≃ᵢ α) :=
  { one := isometric.refl _,
    mul := λ e₁ e₂, e₁.trans e₂,
    inv := isometric.symm,
    mul_assoc := λ e₁ e₂ e₃, rfl,
    one_mul := λ e, ext $ λ _, rfl,
    mul_one := λ e, ext $ λ _, rfl,
    mul_left_inv := λ e, ext e.apply_symm_apply }

@[simp] lemma coe_one : ⇑(1 : α ≃ᵢ α) = id := rfl

@[simp] lemma coe_mul (e₁ e₂ : α ≃ᵢ α) : ⇑(e₁ * e₂) = e₂ ∘ e₁ := rfl

lemma mul_apply (e₁ e₂ : α ≃ᵢ α) (x : α) : (e₁ * e₂) x = e₂ (e₁ x) := rfl

@[simp] lemma inv_apply_self (e : α ≃ᵢ α) (x: α) : e⁻¹ (e x) = x := e.symm_apply_apply x

@[simp] lemma apply_inv_self (e : α ≃ᵢ α) (x: α) : e (e⁻¹ x) = x := e.apply_symm_apply x

section normed_group

variables {G : Type*} [normed_group G]

/-- Addition `y ↦ y + x` as an `isometry`. -/
protected def add_right (x : G) : G ≃ᵢ G :=
{ isometry_to_fun := isometry_emetric_iff_metric.2 $ λ y z, dist_add_right _ _ _,
  .. equiv.add_right x }

@[simp] lemma add_right_to_equiv (x : G) :
  (isometric.add_right x).to_equiv = equiv.add_right x := rfl

@[simp] lemma coe_add_right (x : G) : (isometric.add_right x : G → G) = λ y, y + x := rfl

lemma add_right_apply (x y : G) : (isometric.add_right x : G → G) y = y + x := rfl

@[simp] lemma add_right_symm (x : G) :
  (isometric.add_right x).symm = isometric.add_right (-x) :=
ext $ λ y, rfl

/-- Addition `y ↦ x + y` as an `isometry`. -/
protected def add_left (x : G) : G ≃ᵢ G :=
{ isometry_to_fun := isometry_emetric_iff_metric.2 $ λ y z, dist_add_left _ _ _,
  to_equiv := equiv.add_left x }

@[simp] lemma add_left_to_equiv (x : G) :
  (isometric.add_left x).to_equiv = equiv.add_left x := rfl

@[simp] lemma coe_add_left (x : G) : ⇑(isometric.add_left x) = (+) x := rfl

@[simp] lemma add_left_symm (x : G) :
  (isometric.add_left x).symm = isometric.add_left (-x) :=
ext $ λ y, rfl

variable (G)

/-- Negation `x ↦ -x` as an `isometry`. -/
protected def neg : G ≃ᵢ G :=
{ isometry_to_fun := isometry_emetric_iff_metric.2 $ λ x y, dist_neg_neg _ _,
  to_equiv := equiv.neg G }

variable {G}

@[simp] lemma neg_symm : (isometric.neg G).symm = isometric.neg G := rfl

@[simp] lemma neg_to_equiv : (isometric.neg G).to_equiv = equiv.neg G := rfl

@[simp] lemma coe_neg : ⇑(isometric.neg G) = has_neg.neg := rfl

end normed_group

end isometric

/-- An isometry induces an isometric isomorphism between the source space and the
range of the isometry. -/
def isometry.isometric_on_range [emetric_space α] [emetric_space β] {f : α → β} (h : isometry f) :
  α ≃ᵢ range f :=
{ isometry_to_fun := λx y, by simpa [subtype.edist_eq] using h x y,
  .. equiv.set.range f h.injective }

@[simp] lemma isometry.isometric_on_range_apply [emetric_space α] [emetric_space β]
  {f : α → β} (h : isometry f) (x : α) : h.isometric_on_range x = ⟨f x, mem_range_self _⟩ :=
rfl

/-- In a normed algebra, the inclusion of the base field in the extended field is an isometry. -/
lemma algebra_map_isometry (𝕜 : Type*) (𝕜' : Type*) [normed_field 𝕜] [normed_ring 𝕜']
  [normed_algebra 𝕜 𝕜'] : isometry (algebra_map 𝕜 𝕜') :=
begin
  refine isometry_emetric_iff_metric.2 (λx y, _),
  rw [dist_eq_norm, dist_eq_norm, ← ring_hom.map_sub, norm_algebra_map_eq],
end

/-- The space of bounded sequences, with its sup norm -/
@[reducible] def ℓ_infty_ℝ : Type := bounded_continuous_function ℕ ℝ
open bounded_continuous_function metric topological_space

namespace Kuratowski_embedding

/-! ### In this section, we show that any separable metric space can be embedded isometrically in ℓ^∞(ℝ) -/

variables {f g : ℓ_infty_ℝ} {n : ℕ} {C : ℝ} [metric_space α] (x : ℕ → α) (a b : α)

/-- A metric space can be embedded in `l^∞(ℝ)` via the distances to points in
a fixed countable set, if this set is dense. This map is given in the next definition,
without density assumptions. -/
def embedding_of_subset : ℓ_infty_ℝ :=
of_normed_group_discrete (λn, dist a (x n) - dist (x 0) (x n)) (dist a (x 0)) (λ_, abs_dist_sub_le _ _ _)

lemma embedding_of_subset_coe : embedding_of_subset x a n = dist a (x n) - dist (x 0) (x n) := rfl

/-- The embedding map is always a semi-contraction. -/
lemma embedding_of_subset_dist_le (a b : α) :
  dist (embedding_of_subset x a) (embedding_of_subset x b) ≤ dist a b :=
begin
  refine (dist_le dist_nonneg).2 (λn, _),
  have A : dist a (x n) + (dist (x 0) (x n) + (-dist b (x n) + -dist (x 0) (x n)))
    = dist a (x n) - dist b (x n), by ring,
  simp only [embedding_of_subset_coe, real.dist_eq, A, add_comm, neg_add_rev, _root_.neg_neg,
             sub_eq_add_neg, add_left_comm],
  exact abs_dist_sub_le _ _ _
end

/-- When the reference set is dense, the embedding map is an isometry on its image. -/
lemma embedding_of_subset_isometry (H : closure (range x) = univ) : isometry (embedding_of_subset x) :=
begin
  refine isometry_emetric_iff_metric.2 (λa b, _),
  refine le_antisymm (embedding_of_subset_dist_le x a b) (real.le_of_forall_epsilon_le (λe epos, _)),
  /- First step: find n with dist a (x n) < e -/
  have A : a ∈ closure (range x), by { have B := mem_univ a, rwa [← H] at B },
  rcases metric.mem_closure_range_iff.1 A (e/2) (half_pos epos) with ⟨n, hn⟩,
  /- Second step: use the norm control at index n to conclude -/
  have C : dist b (x n) - dist a (x n) = embedding_of_subset x b n - embedding_of_subset x a n :=
    by { simp only [embedding_of_subset_coe, sub_sub_sub_cancel_right] },
  have := calc
    dist a b ≤ dist a (x n) + dist (x n) b : dist_triangle _ _ _
    ...    = 2 * dist a (x n) + (dist b (x n) - dist a (x n)) : by { simp [dist_comm], ring }
    ...    ≤ 2 * dist a (x n) + abs (dist b (x n) - dist a (x n)) :
      by apply_rules [add_le_add_left, le_abs_self]
    ...    ≤ 2 * (e/2) + abs (embedding_of_subset x b n - embedding_of_subset x a n) :
      begin rw [C], apply_rules [add_le_add, mul_le_mul_of_nonneg_left, le_of_lt hn, le_refl], norm_num end
    ...    ≤ 2 * (e/2) + dist (embedding_of_subset x b) (embedding_of_subset x a) :
      begin rw [← sub_apply], apply add_le_add_left, rw [sub_apply, ←real.dist_eq], apply dist_coe_le_dist end
    ...    = dist (embedding_of_subset x b) (embedding_of_subset x a) + e : by ring,
  simpa [dist_comm] using this
end

/-- Every separable metric space embeds isometrically in ℓ_infty_ℝ. -/
theorem exists_isometric_embedding (α : Type u) [metric_space α] [separable_space α] :
  ∃(f : α → ℓ_infty_ℝ), isometry f :=
begin
  cases (univ : set α).eq_empty_or_nonempty with h h,
  { use (λ_, 0), assume x, exact absurd h (nonempty.ne_empty ⟨x, mem_univ x⟩) },
  { /- We construct a map x : ℕ → α with dense image -/
    rcases h with basepoint,
    haveI : inhabited α := ⟨basepoint⟩,
    have : ∃s:set α, countable s ∧ closure s = univ := separable_space.exists_countable_closure_eq_univ,
    rcases this with ⟨S, ⟨S_countable, S_dense⟩⟩,
    rcases countable_iff_exists_surjective.1 S_countable with ⟨x, x_range⟩,
    have : closure (range x) = univ :=
      univ_subset_iff.1 (by { rw [← S_dense], apply closure_mono, assumption }),
    /- Use embedding_of_subset to construct the desired isometry -/
    exact ⟨embedding_of_subset x, embedding_of_subset_isometry x this⟩ }
end
end Kuratowski_embedding

open topological_space Kuratowski_embedding

/-- The Kuratowski embedding is an isometric embedding of a separable metric space in ℓ^∞(ℝ) -/
def Kuratowski_embedding (α : Type u) [metric_space α] [separable_space α] : α → ℓ_infty_ℝ :=
  classical.some (Kuratowski_embedding.exists_isometric_embedding α)

/-- The Kuratowski embedding is an isometry -/
protected lemma Kuratowski_embedding.isometry (α : Type u) [metric_space α] [separable_space α] :
  isometry (Kuratowski_embedding α) :=
classical.some_spec (exists_isometric_embedding α)

/-- Version of the Kuratowski embedding for nonempty compacts -/
def nonempty_compacts.Kuratowski_embedding (α : Type u) [metric_space α] [compact_space α] [nonempty α] :
  nonempty_compacts ℓ_infty_ℝ :=
⟨range (Kuratowski_embedding α), range_nonempty _,
  compact_range (Kuratowski_embedding.isometry α).continuous⟩
