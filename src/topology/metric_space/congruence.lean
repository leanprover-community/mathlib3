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

variables {ι ι' : Type*} {P₁ P₂ P₃ : Type*}
          {v₁ : ι → P₁} {v₂ : ι → P₂} {v₃ : ι → P₃}

noncomputable theory

/-- Congruence between indexed sets of vertices v₁ and v₂.
Use `open_locale congruence` to access the `v₁ ≅ v₂` notation. -/

def congruence (v₁ : ι → P₁) (v₂ : ι → P₂)
  [pseudo_emetric_space P₁] [pseudo_emetric_space P₂] : Prop :=
∀ (i₁ i₂ : ι), (edist (v₁ i₁) (v₁ i₂) = edist (v₂ i₁) (v₂ i₂))

localized "infix (name := congruence) ` ≅ `:25 := congruence" in congruence

/-- Congruence holds if and only if and only if all extended distances are the same. -/
lemma congruence_iff_edist_eq [pseudo_emetric_space P₁] [pseudo_emetric_space P₂] :
  congruence v₁ v₂ ↔ (∀ (i₁ i₂ : ι), (edist (v₁ i₁) (v₁ i₂) = edist (v₂ i₁) (v₂ i₂))) :=
refl _

/-- Congruence holds if and only if all non-negative distances are the same. -/
lemma congruence_iff_nndist_eq [pseudo_metric_space P₁] [pseudo_metric_space P₂] :
  congruence v₁ v₂ ↔ (∀ (i₁ i₂ : ι), (nndist (v₁ i₁) (v₁ i₂) = nndist (v₂ i₁) (v₂ i₂))) :=
forall₂_congr (λ _ _, by { rw [edist_nndist, edist_nndist], norm_cast })

/-- Congruence holds if and only if all distances are the same. -/
lemma congruence_iff_dist_eq [pseudo_metric_space P₁] [pseudo_metric_space P₂] :
  congruence v₁ v₂ ↔ (∀ (i₁ i₂ : ι), (dist (v₁ i₁) (v₁ i₂) = dist (v₂ i₁) (v₂ i₂))) :=
congruence_iff_nndist_eq.trans
  (forall₂_congr (λ _ _, by { rw [dist_nndist, dist_nndist], norm_cast }))


namespace congruence

/-- A congruence preserves extended distance. -/
alias congruence_iff_edist_eq ↔ edist_eq _

/-- Congruence follows from preserved extended distance -/
alias congruence_iff_edist_eq ↔ _ of_edist_eq

/-- A congruence preserves non-negative distance. -/
alias congruence_iff_nndist_eq ↔ nndist_eq _

/-- Congruence follows from preserved non-negative distance -/
alias congruence_iff_nndist_eq ↔ _ of_nndist_eq

/-- A congruence preserves distance. -/
alias congruence_iff_dist_eq ↔ dist_eq _

/-- Congruence follows from preserved distance -/
alias congruence_iff_dist_eq ↔ _ of_dist_eq

/-- Congruence follows from pairwise preserved extended distance -/
lemma of_pairwise_edist_eq [pseudo_emetric_space P₁] [pseudo_emetric_space P₂]
  [decidable_eq ι] (h : pairwise (λ i₁ i₂, (edist (v₁ i₁) (v₁ i₂) = edist (v₂ i₁) (v₂ i₂)))) :
    v₁ ≅ v₂ :=
λ i₁ i₂, if g : i₁ = i₂ then by { rw g, simp } else h g

/-- Congruence follows from pairwise preserved non-negative distance -/
lemma of_pairwise_nndist_eq [pseudo_metric_space P₁] [pseudo_metric_space P₂]
  [decidable_eq ι] (h : pairwise (λ i₁ i₂, (nndist (v₁ i₁) (v₁ i₂) = nndist (v₂ i₁) (v₂ i₂)))) :
    v₁ ≅ v₂ :=
of_pairwise_edist_eq (λ i₁ i₂ hn,
  by { rw [edist_nndist, edist_nndist], norm_cast, exact h hn})

/-- Congruence follows from pairwise preserved distance -/
lemma of_pairwise_dist_eq [pseudo_metric_space P₁] [pseudo_metric_space P₂]
  [decidable_eq ι] (h : pairwise (λ i₁ i₂, dist (v₁ i₁) (v₁ i₂) = dist (v₂ i₁) (v₂ i₂))) :
    v₁ ≅ v₂ :=
of_pairwise_nndist_eq (λ i₁ i₂ hn,
  by { have := h hn, rw [dist_nndist, dist_nndist] at this, norm_cast at this, exact this })


section pseudo_emetric_space

variables [pseudo_emetric_space P₁] [pseudo_emetric_space P₂] [pseudo_emetric_space P₃]


@[refl] protected lemma refl (v₁ : ι → P₁): v₁ ≅ v₁ := λ i₁ i₂, rfl

@[symm] protected lemma symm (h : v₁ ≅ v₂) : v₂ ≅ v₁ := λ i₁ i₂, (h i₁ i₂).symm

@[simp] lemma _root_.congruence_comm : v₁ ≅ v₂ ↔ v₂ ≅ v₁ := ⟨congruence.symm, congruence.symm⟩

@[trans] protected lemma trans (h₁₂ : v₁ ≅ v₂) (h₂₃ : v₂ ≅ v₃) : v₁ ≅ v₃ :=
λ i₁ i₂, (h₁₂ i₁ i₂).trans (h₂₃ i₁ i₂)


/-- we can change the index set ι to an index ι' that maps to ι. -/
lemma index_map (h : v₁ ≅ v₂) (f : ι' → ι) : (v₁ ∘ f) ≅ (v₂ ∘ f) :=
λ i₁ i₂, h.edist_eq (f i₁) (f i₂)

/-- we can change between equivalent index sets ι and ι'. -/
@[simp]
lemma index_equiv (f : ι' ≃ ι) (v₁ : ι → P₁) (v₂ : ι → P₂):
  v₁ ∘ f ≅ v₂ ∘ f ↔ v₁ ≅ v₂ :=
begin
  refine ⟨λ h i₁ i₂, _, λ h, h.index_map f⟩,
  simpa [equiv.right_inv f i₁, equiv.right_inv f i₂] using h.edist_eq (f.symm i₁) (f.symm i₂),
end

end pseudo_emetric_space -- section



section emetric_space

variables [emetric_space P₁] [emetric_space P₂] [emetric_space P₃]

/-- `congruence_map` maps the congruent points in one space to the corresponding points
in the other space. -/
def congruence_map (v₁ : ι → P₁) (v₂ : ι → P₂) : set.range v₁ → set.range v₂ :=
λ a, set.range_factorization v₂ $ set.range_splitting v₁ a

lemma map_refl_apply (a : set.range v₁) : congruence_map v₁ v₁ a = a :=
begin
  rw subtype.ext_iff,
  apply set.apply_range_splitting v₁,
end

/-- `congruence_map` does indeed preserve corresponding points -/
lemma map_sound (h : v₁ ≅ v₂) (i : ι):
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

lemma map_comp_apply (h : v₂ ≅ v₃) (a : set.range v₁):
  congruence_map v₂ v₃ (congruence_map v₁ v₂ a) = congruence_map v₁ v₃ a :=
begin
  rw subtype.ext_iff,
  unfold congruence_map,
  rw set.range_factorization_coe v₃,
  exact h.map_sound (set.range_splitting v₁ a),
end

lemma map_comp (v₁ : ι → P₁) (h : v₂ ≅ v₃) :
  (congruence_map v₂ v₃) ∘ congruence_map v₁ v₂ = congruence_map v₁ v₃ :=
funext $ λ a, map_comp_apply h a

/-- `congruence_map v₁ v₂` and `congruence_map v₂ v₁` are inverses to eachother -/
lemma map_inverse_self (h : v₁ ≅ v₂) :
  function.left_inverse (congruence_map v₂ v₁) (congruence_map v₁ v₂) :=
begin
  intro x,
  rw map_comp_apply h.symm,
  exact map_refl_apply x,
end

/-- `congruence_map` as an `isometry_equiv` -/
protected def isometry (h : v₁ ≅ v₂) : set.range v₁ ≃ᵢ set.range v₂ :=
{ to_fun := congruence_map v₁ v₂,
  inv_fun := congruence_map v₂ v₁,
  left_inv := h.map_inverse_self,
  right_inv := h.symm.map_inverse_self,
  isometry_to_fun :=
  begin
    intros fx fy,
    rw subtype.edist_eq fx fy,
    rw [← set.apply_range_splitting v₁ fx, ← set.apply_range_splitting v₁ fy],
    rw h.edist_eq,
    refl,
  end}

lemma isometry_refl_apply (a : set.range v₁) : (congruence.refl v₁).isometry a = a :=
map_refl_apply a

lemma isometry_symm (h : v₁ ≅ v₂) : h.symm.isometry = h.isometry.symm :=
rfl

lemma isometry_sound (h : v₁ ≅ v₂) (i : ι) :
  ↑(h.isometry (set.range_factorization v₁ i)) = v₂ i :=
h.map_sound i

lemma isometry_comp_apply (h₁₂ : v₁ ≅ v₂) (h₂₃ : v₂ ≅ v₃) (a : set.range v₁) :
  h₂₃.isometry (h₁₂.isometry a) = (h₁₂.trans h₂₃).isometry a :=
map_comp_apply h₂₃ a

lemma isometry_comp (h₁₂ : v₁ ≅ v₂) (h₂₃ : v₂ ≅ v₃) :
  h₂₃.isometry ∘ h₁₂.isometry = (h₁₂.trans h₂₃).isometry :=
map_comp v₁ h₂₃

lemma isometry_trans (h₁₂ : v₁ ≅ v₂) (h₂₃ : v₂ ≅ v₃) :
  (h₁₂.trans h₂₃).isometry = h₁₂.isometry.trans h₂₃.isometry :=
begin
  unfold congruence.isometry,
  congr,
  rw ← map_comp v₁ h₂₃, refl,
  rw ← map_comp v₃ h₁₂.symm, refl,
end

end emetric_space -- section

end congruence
