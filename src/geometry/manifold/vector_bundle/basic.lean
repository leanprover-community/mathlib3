/-
Copyright (c) 2022 Floris van Doorn, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
import geometry.manifold.vector_bundle.fiberwise_linear
import topology.vector_bundle.constructions

/-! # Smooth vector bundles

This file defines smooth vector bundles over a smooth manifold.

Let `E` be a topological vector bundle, with model fiber `F` and base space `B`.  We consider `E` as
carrying a charted space structure given by its trivializations -- these are charts to `B × F`.
Then, by "composition", if `B` is itself a charted space over `H` (e.g. a smooth manifold), then `E`
is also a charted space over `H × F`

Now, we define `smooth_vector_bundle` as the `Prop` of having smooth transition functions.
Recall the structure groupoid `smooth_fiberwise_linear` on `B × F` consisting of smooth, fiberwise
linear local homeomorphisms.  We show that our definition of "smooth vector bundle" implies
`has_groupoid` for this groupoid, and show (by a "composition" of `has_groupoid` instances) that
this means that a smooth vector bundle is a smooth manifold.

Since `smooth_vector_bundle` is a mixin, it should be easy to make variants and for many such
variants to coexist -- vector bundles can be smooth vector bundles over several different base
fields, they can also be C^k vector bundles, etc.

## Main definitions and constructions

* `fiber_bundle.charted_space`: A fiber bundle `E` over a base `B` with model fiber `F` is naturally
  a charted space modelled on `B × F`.

* `fiber_bundle.charted_space'`: Let `B` be a charted space modelled on `HB`.  Then a fiber bundle
  `E` over a base `B` with model fiber `F` is naturally a charted space modelled on `HB.prod F`.

* `smooth_vector_bundle`: Mixin class stating that a (topological) `vector_bundle` is smooth, in the
  sense of having smooth transition functions.

* `smooth_fiberwise_linear.has_groupoid`: For a smooth vector bundle `E` over `B` with fiber
  modelled on `F`, the change-of-co-ordinates between two trivializations `e`, `e'` for `E`,
  considered as charts to `B × F`, is smooth and fiberwise linear, in the sense of belonging to the
  structure groupoid `smooth_fiberwise_linear`.

* `bundle.total_space.smooth_manifold_with_corners`: A smooth vector bundle is naturally a smooth
  manifold.

* `vector_bundle_core.smooth_vector_bundle`: If a (topological) `vector_bundle_core` is smooth, in
  the sense of having smooth transition functions, then the vector bundle constructed from it is a
  smooth vector bundle.

* `bundle.prod.smooth_vector_bundle`: The direct sum of two smooth vector bundles is a smooth vector
  bundle.
-/

assert_not_exists mfderiv

open bundle set local_homeomorph
open_locale manifold bundle

variables {𝕜 B B' F M : Type*} {E : B → Type*}

/-! ### Charted space structure on a fiber bundle -/

section
variables [topological_space F] [topological_space (total_space E)] [∀ x, topological_space (E x)]
  {HB : Type*} [topological_space HB]
  [topological_space B] [charted_space HB B] [fiber_bundle F E]

/-- A fiber bundle `E` over a base `B` with model fiber `F` is naturally a charted space modelled on
`B × F`. -/
instance fiber_bundle.charted_space : charted_space (B × F) (total_space E) :=
{ atlas := (λ e : trivialization F (π E), e.to_local_homeomorph) '' trivialization_atlas F E,
  chart_at := λ x, (trivialization_at F E x.proj).to_local_homeomorph,
  mem_chart_source := λ x, (trivialization_at F E x.proj).mem_source.mpr
    (mem_base_set_trivialization_at F E x.proj),
  chart_mem_atlas := λ x, mem_image_of_mem _ (trivialization_mem_atlas F E _) }

section
local attribute [reducible] model_prod

/-- Let `B` be a charted space modelled on `HB`.  Then a fiber bundle `E` over a base `B` with model
fiber `F` is naturally a charted space modelled on `HB.prod F`. -/
instance fiber_bundle.charted_space' : charted_space (model_prod HB F) (total_space E) :=
charted_space.comp _ (model_prod B F) _
end

lemma fiber_bundle.charted_space_chart_at (x : total_space E) :
  chart_at (model_prod HB F) x =
  (trivialization_at F E x.proj).to_local_homeomorph ≫ₕ
  (chart_at HB x.proj).prod (local_homeomorph.refl F) :=
begin
  dsimp only [fiber_bundle.charted_space', charted_space.comp, fiber_bundle.charted_space,
    prod_charted_space, charted_space_self],
  rw [trivialization.coe_coe,
    trivialization.coe_fst' _ (mem_base_set_trivialization_at F E x.proj)]
end

end

/-! ### Smooth vector bundles -/

variables [nontrivially_normed_field 𝕜] [∀ x, add_comm_monoid (E x)] [∀ x, module 𝕜 (E x)]
  [normed_add_comm_group F] [normed_space 𝕜 F]
  [topological_space (total_space E)] [∀ x, topological_space (E x)]

  {EB : Type*} [normed_add_comm_group EB] [normed_space 𝕜 EB]
  {HB : Type*} [topological_space HB] (IB : model_with_corners 𝕜 EB HB)
  [topological_space B] [charted_space HB B] [smooth_manifold_with_corners IB B]

variables (F E) [fiber_bundle F E] [vector_bundle 𝕜 F E]

/-- When `B` is a smooth manifold with corners with respect to a model `IB` and `E` is a
topological vector bundle over `B` with fibers isomorphic to `F`, then `smooth_vector_bundle F E IB`
registers that the bundle is smooth, in the sense of having smooth transition functions.
This is a mixin, not carrying any new data`. -/
class smooth_vector_bundle : Prop :=
(smooth_on_coord_change : ∀ (e e' : trivialization F (π E))
  [mem_trivialization_atlas e] [mem_trivialization_atlas e'],
  smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ b : B, (e.coord_changeL 𝕜 e' b : F →L[𝕜] F))
  (e.base_set ∩ e'.base_set))

export smooth_vector_bundle (smooth_on_coord_change)

variables [smooth_vector_bundle F E IB]


/-- For a smooth vector bundle `E` over `B` with fiber modelled on `F`, the change-of-co-ordinates
between two trivializations `e`, `e'` for `E`, considered as charts to `B × F`, is smooth and
fiberwise linear. -/
instance : has_groupoid (total_space E) (smooth_fiberwise_linear B F IB) :=
{ compatible := begin
    rintros _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩,
    haveI : mem_trivialization_atlas e := ⟨he⟩,
    haveI : mem_trivialization_atlas e' := ⟨he'⟩,
    resetI,
    rw mem_smooth_fiberwise_linear_iff,
    refine ⟨_, _, e.open_base_set.inter e'.open_base_set, smooth_on_coord_change e e', _, _, _⟩,
    { rw inter_comm,
      apply cont_mdiff_on.congr (smooth_on_coord_change e' e),
      { intros b hb,
        rw e.symm_coord_changeL e' hb },
      { apply_instance },
      { apply_instance }, },
    { simp only [e.symm_trans_source_eq e', fiberwise_linear.local_homeomorph,
      trans_to_local_equiv, symm_to_local_equiv]},
    { rintros ⟨b, v⟩ hb,
      have hb' : b ∈ e.base_set ∩ e'.base_set,
      { simpa only [trans_to_local_equiv, symm_to_local_equiv, e.symm_trans_source_eq e',
          coe_coe_symm, prod_mk_mem_set_prod_eq, mem_univ, and_true] using hb },
      exact e.apply_symm_apply_eq_coord_changeL e' hb' v, }
  end }

/-- A smooth vector bundle `E` is naturally a smooth manifold. -/
instance : smooth_manifold_with_corners (IB.prod 𝓘(𝕜, F)) (total_space E) :=
begin
  refine { .. structure_groupoid.has_groupoid.comp (smooth_fiberwise_linear B F IB) _ },
  intros e he,
  rw mem_smooth_fiberwise_linear_iff at he,
  obtain ⟨φ, U, hU, hφ, h2φ, heφ⟩ := he,
  rw [is_local_structomorph_on_cont_diff_groupoid_iff],
  refine ⟨cont_mdiff_on.congr _ heφ.eq_on, cont_mdiff_on.congr _ heφ.symm'.eq_on⟩,
  { rw heφ.source_eq,
    apply smooth_on_fst.prod_mk,
    exact (hφ.comp cont_mdiff_on_fst $ prod_subset_preimage_fst _ _).clm_apply cont_mdiff_on_snd },
  { rw heφ.target_eq,
    apply smooth_on_fst.prod_mk,
    exact (h2φ.comp cont_mdiff_on_fst $ prod_subset_preimage_fst _ _).clm_apply cont_mdiff_on_snd },
end

/-! ### Core construction for smooth vector bundles -/

namespace vector_bundle_core
variables {ι : Type*} {F} (Z : vector_bundle_core 𝕜 B F ι)

/-- Mixin for a `vector_bundle_core` stating smoothness (of transition functions). -/
class is_smooth (IB : model_with_corners 𝕜 EB HB) : Prop :=
(smooth_on_coord_change [] :
  ∀ i j, smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (Z.coord_change i j) (Z.base_set i ∩ Z.base_set j))

export is_smooth (renaming smooth_on_coord_change → vector_bundle_core.smooth_on_coord_change)

variables [Z.is_smooth IB]

/-- If a `vector_bundle_core` has the `is_smooth` mixin, then the vector bundle constructed from it
is a smooth vector bundle. -/
instance smooth_vector_bundle : smooth_vector_bundle F Z.fiber IB :=
{ smooth_on_coord_change := begin
    rintros - - ⟨i, rfl⟩ ⟨i', rfl⟩,
    refine (Z.smooth_on_coord_change IB i i').congr (λ b hb, _),
    ext v,
    exact Z.local_triv_coord_change_eq i i' hb v,
  end }

end vector_bundle_core

/-! ### The trivial smooth vector bundle -/

/-- A trivial vector bundle over a smooth manifold is a smooth vector bundle. -/
instance bundle.trivial.smooth_vector_bundle : smooth_vector_bundle F (bundle.trivial B F) IB :=
{ smooth_on_coord_change := begin
    introsI e e' he he',
    unfreezingI { obtain rfl := bundle.trivial.eq_trivialization B F e },
    unfreezingI { obtain rfl := bundle.trivial.eq_trivialization B F e' },
    simp_rw bundle.trivial.trivialization.coord_changeL,
    exact smooth_const.smooth_on
  end }

/-! ### Direct sums of smooth vector bundles -/

section prod
variables (F₁ : Type*) [normed_add_comm_group F₁] [normed_space 𝕜 F₁]
  (E₁ : B → Type*) [topological_space (total_space E₁)]
  [Π x, add_comm_monoid (E₁ x)] [Π x, module 𝕜 (E₁ x)]

variables (F₂ : Type*) [normed_add_comm_group F₂] [normed_space 𝕜 F₂]
  (E₂ : B → Type*) [topological_space (total_space E₂)]
  [Π x, add_comm_monoid (E₂ x)] [Π x, module 𝕜 (E₂ x)]

variables [Π x : B, topological_space (E₁ x)] [Π x : B, topological_space (E₂ x)]
  [fiber_bundle F₁ E₁] [fiber_bundle F₂ E₂]
  [vector_bundle 𝕜 F₁ E₁] [vector_bundle 𝕜 F₂ E₂]
  [smooth_vector_bundle F₁ E₁ IB] [smooth_vector_bundle F₂ E₂ IB]

/-- The direct sum of two smooth vector bundles over the same base is a smooth vector bundle. -/
instance bundle.prod.smooth_vector_bundle :
  smooth_vector_bundle (F₁ × F₂) (E₁ ×ᵇ E₂) IB :=
{ smooth_on_coord_change := begin
    rintros _ _ ⟨e₁, e₂, i₁, i₂, rfl⟩ ⟨e₁', e₂', i₁', i₂', rfl⟩,
    resetI,
    rw [smooth_on],
    refine cont_mdiff_on.congr _ (e₁.coord_changeL_prod 𝕜 e₁' e₂ e₂'),
    refine cont_mdiff_on.clm_prod_map _ _,
    { refine (smooth_on_coord_change e₁ e₁').mono _,
      simp only [trivialization.base_set_prod] with mfld_simps,
      mfld_set_tac },
    { refine (smooth_on_coord_change e₂ e₂').mono _,
      simp only [trivialization.base_set_prod] with mfld_simps,
      mfld_set_tac },
  end }

end prod
