/-
Copyright (c) 2023 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
import topology.metric_space.isometry

/-!
# Similarities

We define similarity, i.e., the equivalence between sets of points in a metric space where all
corresponding pairwise distances have the same ratio.
The motivating example is triangles in the plane.


## Notation

- (v₁ ∼ v₂ : Prop) represents that (v₁ : ι → P₁) and (v₂ : ι → P₂) are similar.

-/

variables {ι ι' : Type*} {P₁ P₂ P₃ : Type*}
          {v₁ : ι → P₁} {v₂ : ι → P₂} {v₃ : ι → P₃}

noncomputable theory

/-- similarity between indexed sets of vertices v₁ and v₂.
Use `open_locale similarity` to access the `v₁ ∼ v₂` notation. -/

def similarity (v₁ : ι → P₁) (v₂ : ι → P₂)
  [pseudo_emetric_space P₁] [pseudo_emetric_space P₂] : Prop :=
∃ r : nnreal, r ≠ 0 ∧ ∀ (i₁ i₂ : ι), (edist (v₁ i₁) (v₁ i₂) = r * edist (v₂ i₁) (v₂ i₂))

localized "infix (name := similarity) ` ∼ `:25 := similarity" in similarity

/-- similarity holds if and only if and only if all extended distances are the same. -/
lemma similarity_iff_exists_edist_eq [pseudo_emetric_space P₁] [pseudo_emetric_space P₂] :
  similarity v₁ v₂ ↔
    (∃ r : nnreal, r ≠ 0 ∧ ∀ (i₁ i₂ : ι), (edist (v₁ i₁) (v₁ i₂) = r * edist (v₂ i₁) (v₂ i₂))) :=
refl _

/-- similarity holds if and only if all non-negative distances are the same. -/
lemma similarity_iff_exists_nndist_eq [pseudo_metric_space P₁] [pseudo_metric_space P₂] :
  similarity v₁ v₂ ↔
    (∃ r : nnreal, r ≠ 0 ∧ ∀ (i₁ i₂ : ι), (nndist (v₁ i₁) (v₁ i₂) = r * nndist (v₂ i₁) (v₂ i₂))) :=
exists_congr $ λ _, and_congr iff.rfl $ forall₂_congr $
  λ _ _, by { rw [edist_nndist, edist_nndist], norm_cast }

/-- similarity holds if and only if all distances are the same. -/
lemma similarity_iff_exists_dist_eq [pseudo_metric_space P₁] [pseudo_metric_space P₂] :
  similarity v₁ v₂ ↔
    (∃ r : nnreal, r ≠ 0 ∧ ∀ (i₁ i₂ : ι), (dist (v₁ i₁) (v₁ i₂) = r * dist (v₂ i₁) (v₂ i₂))) :=
similarity_iff_exists_nndist_eq.trans
  (exists_congr $ λ _, and_congr iff.rfl $ forall₂_congr $
    λ _ _, by { rw [dist_nndist, dist_nndist], norm_cast })


namespace similarity

/-- A similarity preserves extended distance. -/
alias similarity_iff_exists_edist_eq ↔ exists_edist_eq _

/-- similarity follows from preserved extended distance -/
alias similarity_iff_exists_edist_eq ↔ _ of_exists_edist_eq

/-- A similarity preserves non-negative distance. -/
alias similarity_iff_exists_nndist_eq ↔ exists_nndist_eq _

/-- similarity follows from preserved non-negative distance -/
alias similarity_iff_exists_nndist_eq ↔ _ of_exists_nndist_eq

/-- A similarity preserves distance. -/
alias similarity_iff_exists_dist_eq ↔ exists_dist_eq _

/-- similarity follows from preserved distance -/
alias similarity_iff_exists_dist_eq ↔ _ of_exists_dist_eq

/-- similarity follows from pairwise preserved extended distance -/
lemma of_pairwise_exists_edist_eq [pseudo_emetric_space P₁] [pseudo_emetric_space P₂]
  [decidable_eq ι] {r : nnreal} (hr : r ≠ 0)
  (h : pairwise (λ i₁ i₂, (edist (v₁ i₁) (v₁ i₂) = r * edist (v₂ i₁) (v₂ i₂)))) :
    v₁ ∼ v₂ :=
⟨r, hr, λ i₁ i₂, if g : i₁ = i₂ then by { rw g, simp } else h g⟩

/-- similarity follows from pairwise preserved non-negative distance -/
lemma of_pairwise_exists_nndist_eq [pseudo_metric_space P₁] [pseudo_metric_space P₂]
  [decidable_eq ι] {r : nnreal} (hr : r ≠ 0)
  (h : pairwise (λ i₁ i₂, (nndist (v₁ i₁) (v₁ i₂) = r * nndist (v₂ i₁) (v₂ i₂)))) :
    v₁ ∼ v₂ :=
of_pairwise_exists_edist_eq hr (λ i₁ i₂ hn,
  by { rw [edist_nndist, edist_nndist, h hn], norm_cast})

/-- similarity follows from pairwise preserved distance -/
lemma of_pairwise_exists_dist_eq [pseudo_metric_space P₁] [pseudo_metric_space P₂]
  [decidable_eq ι] {r : nnreal} (hr : r ≠ 0)
  (h : pairwise (λ i₁ i₂, dist (v₁ i₁) (v₁ i₂) = r * dist (v₂ i₁) (v₂ i₂))) :
    v₁ ∼ v₂ :=
of_pairwise_exists_nndist_eq hr (λ i₁ i₂ hn,
  by { have := h hn, rw [dist_nndist, dist_nndist] at this, norm_cast at this, exact this })


section pseudo_emetric_space

variables [pseudo_emetric_space P₁] [pseudo_emetric_space P₂] [pseudo_emetric_space P₃]


@[refl] protected lemma refl (v₁ : ι → P₁): v₁ ∼ v₁ :=
⟨1, one_ne_zero, λ _ _, by {norm_cast, rw one_mul}⟩

@[symm] protected lemma symm (h : v₁ ∼ v₂) : v₂ ∼ v₁ :=
begin
  rcases h with ⟨r, hr, h⟩,
  refine ⟨r⁻¹, inv_ne_zero hr, λ _ _, _⟩,
  rw [ennreal.coe_inv hr, ← ennreal.div_eq_inv_mul, ennreal.eq_div_iff _ ennreal.coe_ne_top, h],
  norm_cast, exact hr,
end

@[simp] lemma _root_.similarity_comm : v₁ ∼ v₂ ↔ v₂ ∼ v₁ := ⟨similarity.symm, similarity.symm⟩

@[trans] protected lemma trans (h₁ : v₁ ∼ v₂) (h₂ : v₂ ∼ v₃) : v₁ ∼ v₃ :=
begin
  rcases h₁ with ⟨r₁, hr₁, h₁⟩, rcases h₂ with ⟨r₂, hr₂, h₂⟩,
  refine ⟨r₁ * r₂, mul_ne_zero hr₁ hr₂, λ _ _, _⟩,
  rw [ennreal.coe_mul, mul_assoc, h₁, h₂],
end


/-- we can change the index set ι to an index ι' that maps to ι. -/
lemma index_map (h : v₁ ∼ v₂) (f : ι' → ι) : (v₁ ∘ f) ∼ (v₂ ∘ f) :=
begin
  rcases h with ⟨r, hr, h⟩,
  refine ⟨r, hr, λ _ _, _⟩,
  apply h,
end

/-- we can change between equivalent index sets ι and ι'. -/
@[simp]
lemma index_equiv (f : ι' ≃ ι) (v₁ : ι → P₁) (v₂ : ι → P₂):
  v₁ ∘ f ∼ v₂ ∘ f ↔ v₁ ∼ v₂ :=
begin
  refine ⟨λ h, _, λ h, h.index_map f⟩,
  rcases h with ⟨r, hr, h⟩,
  refine ⟨r, hr, λ i₁ i₂, _⟩,
  simpa [f.right_inv i₁, f.right_inv i₂] using h (f.symm i₁) (f.symm i₂),
end

end pseudo_emetric_space -- section

end similarity
