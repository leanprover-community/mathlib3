import geometry.manifold.vector_bundle.tangent

open_locale manifold

variables (𝕜 : Type*) [nontrivially_normed_field 𝕜]
  (𝕜₂ : Type*) [nontrivially_normed_field 𝕜₂] [normed_algebra 𝕜₂ 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F] {H : Type*} [topological_space H]
  [normed_space 𝕜₂ E] [is_scalar_tower 𝕜₂ 𝕜 E]
  [normed_space 𝕜₂ F] [is_scalar_tower 𝕜₂ 𝕜 F]
  {I : model_with_corners 𝕜 E H} {I₂ : model_with_corners 𝕜₂ E H}
  {M : Type*} [topological_space M] [charted_space H M]
  -- {E₂ : Type*} [normed_add_comm_group E₂] [normed_space 𝕜₂ E₂]
  -- {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F] {H : Type*} [topological_space H]
  {f : E → F}
-- todo: move to various files with various type-class conditions

-- lemma cont_diff_within_at.restrict_scalars {n : ℕ∞} {s : set E} {x : E}
--   (h : cont_diff_within_at 𝕜 n f s x) :
--   cont_diff_within_at 𝕜₂ n f s x :=
-- sorry

open filter
lemma tangent_cone_at_mono_scalars {s : set E} {x : E} :
  tangent_cone_at 𝕜₂ s x ⊆ tangent_cone_at 𝕜 s x :=
begin
  rintros x ⟨c, d, hd, hc, hcd⟩,
  refine ⟨algebra_map 𝕜₂ 𝕜 ∘ c, d, hd, _, _⟩,
  { simp_rw [function.comp, norm_algebra_map, norm_one, mul_one, hc] },
  simp_rw [function.comp, algebra.algebra_map_eq_smul_one, smul_assoc, one_smul, hcd],
end

section
open submodule
lemma span_mono_scalars {s : set E} :
  (span 𝕜₂ s : set E) ⊆ span 𝕜 s :=
begin
  intros x hx,
  rw [set_like.mem_coe, mem_span] at hx ⊢,
  exact λ p hp, hx (p.restrict_scalars 𝕜₂) hp
end

variables {𝕜₂}
lemma unique_diff_within_at.extend_scalars {s : set E} {x : E}
  (h : unique_diff_within_at 𝕜₂ s x) :
  unique_diff_within_at 𝕜 s x :=
{ dense_tangent_cone := h.dense_tangent_cone.mono $
    (span_mono_scalars 𝕜 𝕜₂).trans $ span_mono $ tangent_cone_at_mono_scalars 𝕜 𝕜₂,
  mem_closure := h.mem_closure }


lemma unique_diff_on.extend_scalars {s : set E} (h : unique_diff_on 𝕜₂ s) :
  unique_diff_on 𝕜 s :=
λ x hx, (h x hx).extend_scalars 𝕜

section extend -- probably useless
/-- Extend the scalars of a `model_with_corners`. -/
def model_with_corners.extend_scalars (I₂ : model_with_corners 𝕜₂ E H) :
  model_with_corners 𝕜 E H :=
{ unique_diff' := I₂.unique_diff'.extend_scalars 𝕜,
  ..I₂ }


variables (𝕜 𝕜₂)
lemma cont_diff_groupoid_extend_scalars {n : ℕ∞} :
  cont_diff_groupoid n (I₂.extend_scalars 𝕜) ≤ cont_diff_groupoid n I₂ :=
begin
  apply groupoid_of_pregroupoid_le,
  intros f s hf,
  exact hf.restrict_scalars 𝕜₂
end

lemma smooth_manifold_with_corners.of_extend_scalars
  (h : smooth_manifold_with_corners (I₂.extend_scalars 𝕜) M) :
  smooth_manifold_with_corners I₂ M :=
{ compatible := λ e e' he he', cont_diff_groupoid_extend_scalars 𝕜 𝕜₂
    ((cont_diff_groupoid ∞ $ I₂.extend_scalars 𝕜).compatible he he') }

end extend


section
variables {𝕜} (𝕜₂)
/-- Extend the scalars of a boundaryless `model_with_corners`. We cannot do this with arbitrary
  models with corners, although we could do it with assumptions much weaker than `boundaryless`. -/
def model_with_corners.restrict_scalars (I : model_with_corners 𝕜 E H) [I.boundaryless] :
  model_with_corners 𝕜₂ E H :=
{ unique_diff' := by
    simp_rw [I.target_eq, model_with_corners.boundaryless.range_eq_univ, unique_diff_on_univ]
  ..I }

end

variables [I .boundaryless]

@[simp]
lemma model_with_corners.restrict_scalars_to_local_equiv :
  (I.restrict_scalars 𝕜₂).to_local_equiv = I.to_local_equiv := rfl
@[simp]
lemma model_with_corners.restrict_scalars_coe : (I.restrict_scalars 𝕜₂ : H → E) = I := rfl
@[simp]
lemma model_with_corners.restrict_scalars_symm_coe :
  ((I.restrict_scalars 𝕜₂).symm : E → H) = I.symm := rfl
lemma model_with_corners.restrict_scalars_apply (x : H) : I.restrict_scalars 𝕜₂ x = I x := rfl
lemma model_with_corners.restrict_scalars_symm_apply (x : E) :
  (I.restrict_scalars 𝕜₂).symm x = I.symm x := rfl

variables (𝕜 𝕜₂)
lemma cont_diff_groupoid_restrict_scalars [I.boundaryless] {n : ℕ∞} :
  cont_diff_groupoid n I ≤ cont_diff_groupoid n (I.restrict_scalars 𝕜₂) :=
begin
  apply groupoid_of_pregroupoid_le,
  intros f s hf,
  exact hf.restrict_scalars 𝕜₂
end

instance smooth_manifold_with_corners.restrict_scalars
  (h : smooth_manifold_with_corners I M) :
  smooth_manifold_with_corners (I.restrict_scalars 𝕜₂) M :=
{ compatible := λ e e' he he', cont_diff_groupoid_restrict_scalars 𝕜 𝕜₂
  ((cont_diff_groupoid ∞ I).compatible he he') }

open bundle
variables {V : M → Type*} [topological_space (total_space V)]
  [Π b, topological_space (V b)] [fiber_bundle F V]
  [Π b, add_comm_group (V b)] [Π b, module 𝕜 (V b)]
  [Π b, module 𝕜₂ (V b)] [Π b, is_scalar_tower 𝕜₂ 𝕜 (V b)]
  [vector_bundle 𝕜 F V]

include 𝕜
instance vector_bundle.restrict_scalars : vector_bundle 𝕜₂ F V :=
{ trivialization_linear' := by { introsI e he, constructor, intros x hx, sorry  },
  continuous_on_coord_change' := by { introsI e e' he he', sorry } }

end
