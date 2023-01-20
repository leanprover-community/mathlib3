/-
Copyright (c) 2023 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
import topology.metric_space.isometry

/-!
# Congruences

We define congruence, i.e., the equivalence between sets of points in a metric space where all
corresponding pairwise distances are the same. The motivating example is triangles in the plane.

## Main results

In the case of an `emetric_space` we show an `isometry_equiv` between the points:
set.range v₁ ≃ᵢ set.range v₂.


## Notation

- (v₁ ≅ v₂ : Prop) represents that (v₁ : ι → P₁) and (v₂ : ι → P₂) are congruent.

-/

variables {ι ι' : Type*} {P₁ P₂ P₃ : Type*} {v₁ : ι → P₁} {v₂ : ι → P₂} {v₃ : ι → P₃}

noncomputable theory

/-- Congruence between indexed sets of vertices v₁ and v₂. Use
`open_locale congruence` to access the `v₁ ≅ v₂` notation. -/

def congruence (v₁ : ι → P₁) (v₂ : ι → P₂)
  [pseudo_emetric_space P₁] [pseudo_emetric_space P₂] : Prop :=
∀ (i₁ i₂ : ι), (edist (v₁ i₁) (v₁ i₂) = edist (v₂ i₁) (v₂ i₂))

localized "infix (name := congruence) ` ≅ `:25 := congruence" in congruence


namespace congruence

section

variables [pseudo_emetric_space P₁] [pseudo_emetric_space P₂] [pseudo_emetric_space P₃]

lemma congruence_of_edist : (∀ (i₁ i₂ : ι), (edist (v₁ i₁) (v₁ i₂) = edist (v₂ i₁) (v₂ i₂))) →
  congruence v₁ v₂ :=
id

lemma to_edist (h : v₁ ≅ v₂) (i₁ i₂ : ι) :
  edist (v₁ i₁) (v₁ i₂) = edist (v₂ i₁) (v₂ i₂) :=
h i₁ i₂

@[refl] protected lemma refl (v₁ : ι → P₁): v₁ ≅ v₁ := λ i₁ i₂, rfl

@[symm] protected lemma symm (h : v₁ ≅ v₂) : v₂ ≅ v₁ := λ i₁ i₂, (h i₁ i₂).symm

lemma _root_.congruence_comm : v₁ ≅ v₂ ↔ v₂ ≅ v₁ := ⟨congruence.symm, congruence.symm⟩

@[trans] protected lemma trans (h₁₂ : v₁ ≅ v₂) (h₂₃ : v₂ ≅ v₃) : v₁ ≅ v₃ :=
λ i₁ i₂, (h₁₂ i₁ i₂).trans (h₂₃ i₁ i₂)


/-- this lemma is useful for changing the index set ι. -/
lemma sub_congruence (h : v₁ ≅ v₂) (f : ι' → ι) : (v₁ ∘ f) ≅ (v₂ ∘ f) :=
λ i₁ i₂, h.to_edist (f i₁) (f i₂)

/-- this lemma is useful for changing the index set ι. -/
@[simp]
lemma index_equiv_congruence {F : Type*} [equiv_like F ι' ι] (f : F) (v₁ : ι → P₁) (v₂ : ι → P₂):
  v₁ ∘ equiv_like.coe f ≅ v₂ ∘ equiv_like.coe f ↔ v₁ ≅ v₂ :=
begin
  refine ⟨λ h i₁ i₂, _, λ h, h.sub_congruence (equiv_like.coe f)⟩,
  have := h.to_edist (equiv_like.inv f i₁) (equiv_like.inv f i₂),
  simp [equiv_like.right_inv f i₁, equiv_like.right_inv f i₂] at this, exact this,
end

end


section

variables [pseudo_metric_space P₁] [pseudo_metric_space P₂]

lemma congruence_of_dist (h : ∀ (i₁ i₂ : ι), (dist (v₁ i₁) (v₁ i₂) = dist (v₂ i₁) (v₂ i₂))) :
  congruence v₁ v₂ := λ i₁ i₂, by rw [edist_dist, edist_dist, h i₁ i₂]
lemma congruence_of_nndist (h : ∀ (i₁ i₂ : ι), (nndist (v₁ i₁) (v₁ i₂) = nndist (v₂ i₁) (v₂ i₂))) :
  congruence v₁ v₂ := λ i₁ i₂, by rw [edist_nndist, edist_nndist, h i₁ i₂]

lemma to_dist (h : v₁ ≅ v₂) (i₁ i₂ : ι) :
  dist (v₁ i₁) (v₁ i₂) = dist (v₂ i₁) (v₂ i₂) :=
by rw [dist_edist, dist_edist, h i₁ i₂]
lemma to_nndist (h : v₁ ≅ v₂) (i₁ i₂ : ι) :
  nndist (v₁ i₁) (v₁ i₂) = nndist (v₂ i₁) (v₂ i₂) :=
by rw [nndist_edist, nndist_edist, h i₁ i₂]

end




section

variables [emetric_space P₁] [emetric_space P₂]

/--
this function maps the congruent points in one space to the corresponding points
in the other space.
-/
def congruence_map (v₁ : ι → P₁) (v₂ : ι → P₂) : set.range v₁ → set.range v₂ :=
λ a, set.range_factorization v₂ $ set.range_splitting v₁ a

/-- `congruence_map` does indeed preserve corresponding points -/
lemma map_sound (h : v₁ ≅ v₂) (i : ι) :
  ↑(congruence_map v₁ v₂ (set.range_factorization v₁ i)) = v₂ i :=
begin
  unfold congruence_map,
  rw set.range_factorization_coe v₂,
  rw ← edist_eq_zero,
  rw ← h,
  rw edist_eq_zero,
  rw set.apply_range_splitting v₁,
  rw set.range_factorization_coe v₁,
end

/-- `congruence_map v₁ v₂` and `congruence_map v₂ v₁` are inverses to eachother -/
protected lemma map_inverse_self (h : v₁ ≅ v₂) :
  function.left_inverse (congruence_map v₂ v₁) (congruence_map v₁ v₂) :=
begin
  intro x,
  rw subtype.ext_iff,
  rw ← set.apply_range_splitting v₁ x,
  apply h.symm.map_sound (set.range_splitting v₁ x),
end

/-- `congruence_map` as an `equiv` -/
protected def equiv (h : v₁ ≅ v₂) : set.range v₁ ≃ set.range v₂ :=
{ to_fun := congruence_map v₁ v₂,
  inv_fun := congruence_map v₂ v₁,
  left_inv := h.map_inverse_self,
  right_inv := h.symm.map_inverse_self }

lemma equiv_sound (h : v₁ ≅ v₂) (i : ι) : ↑(h.equiv (set.range_factorization v₁ i)) = v₂ i :=
h.map_sound i

/-- `congruence_map` as an `isometry_equiv` -/
protected def isometry (h : v₁ ≅ v₂) : set.range v₁ ≃ᵢ set.range v₂ :=
{ to_equiv := h.equiv,
  isometry_to_fun :=
  begin
    intros fx fy,
    rw subtype.edist_eq fx fy,
    rw [← set.apply_range_splitting v₁ fx, ← set.apply_range_splitting v₁ fy],
    rw h.to_edist,
    refl,
  end}

lemma isometry_sound (h : v₁ ≅ v₂) (i : ι) :
  ↑(h.isometry (set.range_factorization v₁ i)) = v₂ i :=
h.map_sound i

end
end congruence
