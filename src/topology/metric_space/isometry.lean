/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Isometries of emetric and metric spaces
Authors: Sébastien Gouëzel
We define isometries, i.e., maps between emetric spaces that preserve
the edistance (on metric spaces, these are exactly the maps that preserve distances),
and prove their basic properties. We also introduce isometric bijections.
-/

import topology.metric_space.basic
topology.bounded_continuous_function analysis.normed_space.basic topology.opens

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
theorem isometry.edist_eq [emetric_space α] [emetric_space β] {f : α → β} {x y : α} (hf : isometry f) :
  edist (f x) (f y) = edist x y :=
hf x y

/-- An isometry preserves distances. -/
theorem isometry.dist_eq [metric_space α] [metric_space β] {f : α → β} {x y : α} (hf : isometry f) :
  dist (f x) (f y) = dist x y :=
by rw [dist_edist, dist_edist, hf]

section emetric_isometry

variables [emetric_space α] [emetric_space β] [emetric_space γ]
variables {f : α → β} {x y z : α}  {s : set α}

/-- An isometry is injective -/
lemma isometry.injective (h : isometry f) : injective f :=
λx y hxy, edist_eq_zero.1 $
calc edist x y = edist (f x) (f y) : (h x y).symm
         ...   = 0 : by rw [hxy]; simp

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
begin
  refine emetric.uniform_embedding_iff.2 ⟨_, _, _⟩,
  { assume x y hxy,
    have : edist (f x) (f y) = 0 := by simp [hxy],
    have : edist x y = 0 :=
      begin have A := hf x y, rwa this at A, exact eq.symm A end,
    by simpa using this },
  { rw emetric.uniform_continuous_iff,
    assume ε εpos,
    existsi [ε, εpos],
    simp [hf.edist_eq] },
  { assume δ δpos,
    existsi [δ, δpos],
    simp [hf.edist_eq] }
end

/-- An isometry is continuous. -/
lemma isometry.continuous (hf : isometry f) : continuous f :=
hf.uniform_embedding.embedding.continuous

/-- The inverse of an isometry is an isometry. -/
lemma isometry.inv (e : α ≃ β) (h : isometry e.to_fun) : isometry e.inv_fun :=
λx y, by rw [← h, e.right_inv _, e.right_inv _]

/-- Isometries preserve the diameter -/
lemma emetric.isometry.diam_image (hf : isometry f) {s : set α}:
  emetric.diam (f '' s) = emetric.diam s :=
begin
  refine le_antisymm _ _,
  { apply lattice.Sup_le _,
    simp only [and_imp, set.mem_image, set.mem_prod, exists_imp_distrib, prod.exists],
    assume b x x' z zs xz z' z's x'z' hb,
    rw [← hb, ← xz, ← x'z', hf z z'],
    exact emetric.edist_le_diam_of_mem zs z's },
  { apply lattice.Sup_le _,
    simp only [and_imp, set.mem_image, set.mem_prod, exists_imp_distrib, prod.exists],
    assume b x x' xs x's hb,
    rw [← hb, ← hf x x'],
    exact emetric.edist_le_diam_of_mem (mem_image_of_mem _ xs) (mem_image_of_mem _ x's) }
end

/-- The injection from a subtype is an isometry -/
lemma isometry_subtype_val {s : set α} : isometry (subtype.val : s → α) :=
λx y, rfl

end emetric_isometry --section

/-- An isometry preserves the diameter in metric spaces -/
lemma metric.isometry.diam_image [metric_space α] [metric_space β]
  {f : α → β} {s : set α} (hf : isometry f) : metric.diam (f '' s) = metric.diam s :=
by rw [metric.diam, metric.diam, emetric.isometry.diam_image hf]

/-- α and β are isometric if there is an isometric bijection between them. -/
structure isometric (α : Type*) (β : Type*) [emetric_space α] [emetric_space β]
  extends α ≃ β :=
(isometry_to_fun  : isometry to_fun)
(isometry_inv_fun : isometry inv_fun)

infix ` ≃ᵢ`:25 := isometric

namespace isometric
variables [emetric_space α] [emetric_space β] [emetric_space γ]

instance : has_coe_to_fun (α ≃ᵢ β) := ⟨λ_, α → β, λe, e.to_equiv⟩

lemma coe_eq_to_equiv (h : α ≃ᵢ β) (a : α) : h a = h.to_equiv a := rfl

protected def to_homeomorph (h : α ≃ᵢ β) : α ≃ₜ β :=
{ continuous_to_fun  := (isometry_to_fun h).continuous,
  continuous_inv_fun := (isometry_inv_fun h).continuous,
  .. h.to_equiv }

lemma coe_eq_to_homeomorph (h : α ≃ᵢ β) (a : α) :
  h a = h.to_homeomorph a := rfl

lemma to_homeomorph_to_equiv (h : α ≃ᵢ β) :
  h.to_homeomorph.to_equiv = h.to_equiv :=
by ext; refl

protected def refl (α : Type*) [emetric_space α] : α ≃ᵢ α :=
{ isometry_to_fun := isometry_id, isometry_inv_fun := isometry_id, .. equiv.refl α }

protected def trans (h₁ : α ≃ᵢ β) (h₂ : β ≃ᵢ γ) : α ≃ᵢ γ :=
{ isometry_to_fun  := h₂.isometry_to_fun.comp h₁.isometry_to_fun,
  isometry_inv_fun := h₁.isometry_inv_fun.comp h₂.isometry_inv_fun,
  .. equiv.trans h₁.to_equiv h₂.to_equiv }

protected def symm (h : α ≃ᵢ β) : β ≃ᵢ α :=
{ isometry_to_fun  := h.isometry_inv_fun,
  isometry_inv_fun := h.isometry_to_fun,
  .. h.to_equiv.symm }

protected lemma isometry (h : α ≃ᵢ β) : isometry h := h.isometry_to_fun

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

end isometric

/-- An isometry induces an isometric isomorphism between the source space and the
range of the isometry. -/
lemma isometry.isometric_on_range [emetric_space α] [emetric_space β] {f : α → β} (h : isometry f) :
  α ≃ᵢ range f :=
{ isometry_to_fun := λx y,
  begin
    change edist ((equiv.set.range f _) x) ((equiv.set.range f _) y) = edist x y,
    rw [equiv.set.range_apply f h.injective, equiv.set.range_apply f h.injective],
    exact h x y
  end,
  isometry_inv_fun :=
  begin
    apply isometry.inv,
    assume x y,
    change edist ((equiv.set.range f _) x) ((equiv.set.range f _) y) = edist x y,
    rw [equiv.set.range_apply f h.injective, equiv.set.range_apply f h.injective],
    exact h x y
  end,
  .. equiv.set.range f h.injective }

lemma isometry.isometric_on_range_apply [emetric_space α] [emetric_space β]
  {f : α → β} (h : isometry f) (x : α) : h.isometric_on_range x = ⟨f x, mem_range_self _⟩ :=
begin
  dunfold isometry.isometric_on_range,
  rw ← equiv.set.range_apply f h.injective x,
  refl
end

namespace Kuratowski_embedding
/- In this section, we show that any separable metric space can be embedded isometrically
in ℓ^∞(ℝ) -/

@[reducible] def ℓ_infty_ℝ : Type := bounded_continuous_function ℕ ℝ
open bounded_continuous_function metric topological_space

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
  rcases mem_closure_iff'.1 A (e/2) (half_pos epos) with ⟨d, ⟨drange, hd⟩⟩,
  cases drange with n dn,
  rw [← dn] at hd,
  /- Second step: use the norm control at index n to conclude -/
  have C : dist b (x n) - dist a (x n) = embedding_of_subset x b n - embedding_of_subset x a n :=
    by { simp [embedding_of_subset_coe], ring },
  have := calc
    dist a b ≤ dist a (x n) + dist (x n) b : dist_triangle _ _ _
    ...    = 2 * dist a (x n) + (dist b (x n) - dist a (x n)) : by { simp [dist_comm], ring }
    ...    ≤ 2 * dist a (x n) + abs (dist b (x n) - dist a (x n)) :
      by apply_rules [add_le_add_left, le_abs_self]
    ...    ≤ 2 * (e/2) + abs (embedding_of_subset x b n - embedding_of_subset x a n) :
      begin rw [C], apply_rules [add_le_add, mul_le_mul_of_nonneg_left, le_of_lt hd, le_refl], norm_num end
    ...    ≤ 2 * (e/2) + dist (embedding_of_subset x b) (embedding_of_subset x a) :
      begin rw [← coe_diff], apply add_le_add_left, rw [coe_diff, ←real.dist_eq], apply dist_coe_le_dist end
    ...    = dist (embedding_of_subset x b) (embedding_of_subset x a) + e : by ring,
  simpa [dist_comm] using this
end

/-- Every separable metric space embeds isometrically in ℓ_infty_ℝ. -/
theorem exists_isometric_embedding (α : Type u) [metric_space α] [separable_space α] :
  ∃(f : α → ℓ_infty_ℝ), isometry f :=
begin
  classical,
  by_cases h : (univ : set α) = ∅,
  { use (λ_, 0), assume x, exact (ne_empty_of_mem (mem_univ x) h).elim },
  { /- We construct a map x : ℕ → α with dense image -/
    rcases exists_mem_of_ne_empty h with basepoint,
    haveI : inhabited α := ⟨basepoint⟩,
    have : ∃s:set α, countable s ∧ closure s = univ := separable_space.exists_countable_closure_eq_univ _,
    rcases this with ⟨S, ⟨S_countable, S_dense⟩⟩,
    rcases countable_iff_exists_surjective.1 S_countable with ⟨x, x_range⟩,
    have : closure (range x) = univ :=
      univ_subset_iff.1 (by { rw [← S_dense], apply closure_mono, assumption }),
    /- Use embedding_of_subset to construct the desired isometry -/
    exact ⟨embedding_of_subset x, embedding_of_subset_isometry x this⟩ }
end

/-- The Kuratowski embedding is an isometric embedding of a separable metric space in ℓ^∞(ℝ) -/
def Kuratowski_embedding (α : Type u) [metric_space α] [separable_space α] : α → ℓ_infty_ℝ :=
  classical.some (exists_isometric_embedding α)

/-- The Kuratowski embedding is an isometry -/
lemma Kuratowski_embedding_isometry (α : Type u) [metric_space α] [separable_space α] :
  isometry (Kuratowski_embedding α) :=
classical.some_spec (exists_isometric_embedding α)

/-- Version of the Kuratowski embedding for nonempty compacts -/
def nonempty_compacts.Kuratowski_embedding (α : Type u) [metric_space α] [compact_space α] [nonempty α] :
  nonempty_compacts ℓ_infty_ℝ :=
⟨range (Kuratowski_embedding α),
begin
  split,
  { rcases exists_mem_of_nonempty α with ⟨x, hx⟩,
    have A : Kuratowski_embedding α x ∈ range (Kuratowski_embedding α) := ⟨x, by simp⟩,
    apply ne_empty_of_mem A },
  { rw ← image_univ,
    exact compact_image compact_univ (Kuratowski_embedding_isometry α).continuous },
end⟩

end Kuratowski_embedding --namespace
