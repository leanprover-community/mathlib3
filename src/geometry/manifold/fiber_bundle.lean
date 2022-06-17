/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import topology.fiber_bundle
import geometry.manifold.diffeomorph

/-!
# Smooth Fiber bundles

A smooth fiber bundle with fiber `F` over a base `B` is a space projecting on `B` for which the
fibers are all diffeomorphic to `F`, such that the local situation around each point is a direct
product. We define a predicate `is_smooth_fiber_bundle I I₂ I₃ F p` saying that `p : Z → B` is a
smooth fiber bundle with fiber `F`.
-/


open filter set
open_locale topological_space manifold classical
noncomputable theory

/-! ### General definition of smooth fiber bundles -/

variables {𝕜 E E' E₂ E₃ E₄ E₅ H H' H₂ H₃ H₄ H₅ : Type*}
variables [nondiscrete_normed_field 𝕜]
variables [normed_group E] [normed_space 𝕜 E] [normed_group E'] [normed_space 𝕜 E']
variables [normed_group E₂] [normed_space 𝕜 E₂] [normed_group E₃] [normed_space 𝕜 E₃]
variables [normed_group E₄] [normed_space 𝕜 E₄] [normed_group E₅] [normed_space 𝕜 E₅]
variables [topological_space H] [topological_space H'] [topological_space H₂] [topological_space H₃]
variables [topological_space H₄] [topological_space H₅]
variables (I : model_with_corners 𝕜 E H) {I' : model_with_corners 𝕜 E' H'}
variables (I₂ : model_with_corners 𝕜 E₂ H₂) (I₃ : model_with_corners 𝕜 E₃ H₃)
variables {I₄ : model_with_corners 𝕜 E₄ H₄} {I₅ : model_with_corners 𝕜 E₅ H₅}
variables {B B' F F' Z Z' : Type*}
variables [topological_space B]  [charted_space H B] -- [smooth_manifold_with_corners I B]
variables [topological_space B'] [charted_space H' B'] -- [smooth_manifold_with_corners I' B']
variables [topological_space F]  [charted_space H₂ F]  -- [smooth_manifold_with_corners I₂ F]
variables [topological_space F'] [charted_space H₅ F'] -- [smooth_manifold_with_corners I₅ F']
variables [topological_space Z]  [charted_space H₃ Z]  -- [smooth_manifold_with_corners I₃ Z]
variables [topological_space Z'] [charted_space H₄ Z'] -- [smooth_manifold_with_corners I₄ Z']
variables {proj : Z → B}
variables (F)

/--
A structure extending local homeomorphisms, defining a local smooth trivialization of a projection
`proj : Z → B` with fiber `F`, as a local diffeomorphism between `Z` and `B × F` defined between two
sets of the form `proj ⁻¹' base_set` and `base_set × F`, acting trivially on the first coordinate.
-/
@[nolint has_inhabited_instance]
structure smooth_fiber_bundle.trivialization (proj : Z → B) extends
  to_topological_pretrivialization : topological_fiber_bundle.pretrivialization F proj :=
(open_source : is_open source)
(smooth_on_to_fun  : smooth_on I₃ (I.prod I₂) to_fun source)
(smooth_on_inv_fun  : smooth_on (I.prod I₂) I₃ inv_fun target)

open smooth_fiber_bundle

namespace smooth_fiber_bundle.trivialization

variables {I I₂ I₃ F} (e : trivialization I I₂ I₃ F proj) {x : Z}

/-- Natural identification as a `trivialization` of a topological vector bundle. -/
def to_topological : topological_fiber_bundle.trivialization F proj :=
{ continuous_to_fun := e.smooth_on_to_fun.continuous_on,
  continuous_inv_fun := e.smooth_on_inv_fun.continuous_on,
  ..e }

/-- The local homeomorph defined by the trivialization. -/
def to_local_homeomorph : local_homeomorph Z (B × F) :=
e.to_topological.to_local_homeomorph

instance : has_coe_to_fun (trivialization I I₂ I₃ F proj) (λ _, Z → B × F) := ⟨λ e, e.to_fun⟩
instance : has_coe (trivialization I I₂ I₃ F proj)
  (topological_fiber_bundle.trivialization F proj) :=
⟨to_topological⟩

protected lemma smooth_on : smooth_on I₃ (I.prod I₂) e e.source :=
e.smooth_on_to_fun

protected lemma smooth_on_symm :
  smooth_on (I.prod I₂) I₃ e.to_local_homeomorph.symm e.target :=
e.smooth_on_inv_fun

@[simp, mfld_simps] lemma coe_coe : ⇑e.to_topological_pretrivialization = e := rfl
@[simp, mfld_simps] lemma coe_coe2 : e.to_topological.to_local_homeomorph = e.to_local_homeomorph :=
rfl
@[simp, mfld_simps] lemma coe_coe3 : e.to_local_homeomorph.to_local_equiv = e.to_local_equiv :=
rfl
@[simp, mfld_simps] lemma coe_fst (ex : x ∈ e.source) : (e x).1 = proj x := e.proj_to_fun x ex
protected lemma eq_on : eq_on (prod.fst ∘ e) proj e.source := λ x hx, e.coe_fst hx
lemma mem_source : x ∈ e.source ↔ proj x ∈ e.base_set := by rw [e.source_eq, mem_preimage]
lemma coe_fst' (ex : proj x ∈ e.base_set) : (e x).1 = proj x := e.coe_fst (e.mem_source.2 ex)
lemma mk_proj_snd (ex : x ∈ e.source) : (proj x, (e x).2) = e x := prod.ext (e.coe_fst ex).symm rfl
lemma mk_proj_snd' (ex : proj x ∈ e.base_set) : (proj x, (e x).2) = e x :=
prod.ext (e.coe_fst' ex).symm rfl

lemma source_inter_preimage_target_inter (s : set (B × F)) :
  e.source ∩ (e ⁻¹' (e.target ∩ s)) = e.source ∩ (e ⁻¹' s) :=
e.to_topological.source_inter_preimage_target_inter s

-- @[simp, mfld_simps] lemma coe_mk (e : local_homeomorph Z (B × F)) (i j k l m) (x : Z) :
  -- (trivialization.mk e i j k l m : trivialization I I₂ I₃ F proj) x = e x := rfl

lemma mem_target {x : B × F} : x ∈ e.target ↔ x.1 ∈ e.base_set :=
e.to_topological.mem_target

lemma map_target {x : B × F} (hx : x ∈ e.target) : e.to_local_homeomorph.symm x ∈ e.source :=
e.to_topological.map_target hx

lemma proj_symm_apply {x : B × F} (hx : x ∈ e.target) : proj (e.to_local_homeomorph.symm x) = x.1 :=
e.to_topological.proj_symm_apply hx

lemma proj_symm_apply' {b : B} {x : F}
  (hx : b ∈ e.base_set) : proj (e.to_local_homeomorph.symm (b, x)) = b :=
e.to_topological.proj_symm_apply' hx

lemma proj_surj_on_base_set [nonempty F] : set.surj_on proj e.source e.base_set :=
e.to_topological.proj_surj_on_base_set

lemma apply_symm_apply {x : B × F} (hx : x ∈ e.target) : e (e.to_local_homeomorph.symm x) = x :=
e.to_local_homeomorph.right_inv hx

lemma apply_symm_apply'
  {b : B} {x : F} (hx : b ∈ e.base_set) : e (e.to_local_homeomorph.symm (b, x)) = (b, x) :=
e.to_topological.apply_symm_apply' hx

@[simp, mfld_simps] lemma symm_apply_mk_proj (ex : x ∈ e.source) :
  e.to_local_homeomorph.symm (proj x, (e x).2) = x :=
e.to_topological.symm_apply_mk_proj ex

lemma symm_trans_source_eq (e e' : trivialization I I₂ I₃ F proj) :
  (e.to_local_equiv.symm.trans e'.to_local_equiv).source
  = (e.base_set ∩ e'.base_set) ×ˢ (univ : set F) :=
topological_fiber_bundle.trivialization.symm_trans_source_eq e.to_topological e'

lemma symm_trans_target_eq (e e' : trivialization I I₂ I₃ F proj) :
  (e.to_local_equiv.symm.trans e'.to_local_equiv).target
  = (e.base_set ∩ e'.base_set) ×ˢ (univ : set F) :=
topological_fiber_bundle.trivialization.symm_trans_target_eq e.to_topological e'

lemma coe_fst_eventually_eq_proj (ex : x ∈ e.source) : prod.fst ∘ e =ᶠ[𝓝 x] proj :=
e.to_topological.coe_fst_eventually_eq_proj ex

lemma coe_fst_eventually_eq_proj' (ex : proj x ∈ e.base_set) : prod.fst ∘ e =ᶠ[𝓝 x] proj :=
e.to_topological.coe_fst_eventually_eq_proj' ex

lemma map_proj_nhds (ex : x ∈ e.source) : map proj (𝓝 x) = 𝓝 (proj x) :=
e.to_topological.map_proj_nhds ex

/-- In the domain of a bundle trivialization, the projection is smooth. -/
lemma smooth_on_proj : smooth_on I₃ I proj e.source :=
(smooth_fst.comp_smooth_on e.smooth_on).congr $ λ p hp, (e.coe_fst hp).symm

/-- In the domain of a bundle trivialization, the projection is smooth. -/
lemma smooth_at_proj (ex : x ∈ e.source) : smooth_at I₃ I proj x :=
(e.smooth_on_proj x ex).cont_mdiff_at $ e.open_source.mem_nhds ex

/-- Composition of a `trivialization` and a `homeomorph`. -/
def comp_diffeomorph (h : Z' ≃ₘ⟮I₄, I₃⟯ Z) : trivialization I I₂ I₄ F (proj ∘ h) :=
{ smooth_on_to_fun := e.smooth_on.comp h.smooth.smooth_on
  (by simp [topological_fiber_bundle.trivialization.comp_homeomorph]),
  smooth_on_inv_fun := h.symm.smooth.comp_smooth_on
    (by { convert e.smooth_on_symm, dsimp [topological_fiber_bundle.trivialization.comp_homeomorph], refine inter_univ _ }), -- comp_homeomorph has very poor definitional behavior
  .. e.to_topological.comp_homeomorph h.to_homeomorph }

end smooth_fiber_bundle.trivialization

/-- A smooth fiber bundle with fiber `F` over a base `B` is a space projecting on `B`
for which the fibers are all diffeomorphic to `F`, such that the local situation around each point
is a direct product. -/
def is_smooth_fiber_bundle (proj : Z → B) : Prop :=
∀ x : B, ∃ e : trivialization I I₂ I₃ F proj, x ∈ e.base_set

/-- A trivial smooth fiber bundle with fiber `F` over a base `B` is a space `Z`
projecting on `B` for which there exists a diffeomorphism to `B × F` that sends `proj`
to `prod.fst`. -/
def is_trivial_smooth_fiber_bundle (proj : Z → B) : Prop :=
∃ e : Z ≃ₘ⟮I₃, I.prod I₂⟯ B × F, ∀ x, (e x).1 = proj x

variables {I I₂ I₃ F}

lemma is_trivial_smooth_fiber_bundle.is_trivial_topological_fiber_bundle
  (h : is_trivial_smooth_fiber_bundle I I₂ I₃ F proj) :
  is_trivial_topological_fiber_bundle F proj :=
let ⟨e, he⟩ := h in ⟨e.to_homeomorph, he⟩

lemma is_smooth_fiber_bundle.is_topological_fiber_bundle
  (h : is_smooth_fiber_bundle I I₂ I₃ F proj) :
  is_topological_fiber_bundle F proj :=
λ x, let ⟨e, he⟩ := h x in ⟨e.to_topological, he⟩

lemma is_trivial_smooth_fiber_bundle.is_smooth_fiber_bundle
  (h : is_trivial_smooth_fiber_bundle I I₂ I₃ F proj) :
  is_smooth_fiber_bundle I I₂ I₃ F proj :=
-- todo: we cannot reuse `is_trivial_topological_fiber_bundle.is_topological_fiber_bundle`
-- since all the work is hidden inside an existential
let ⟨e, he⟩ := h in λ x,
⟨⟨⟨e.to_equiv.to_local_equiv, is_open_univ, univ, is_open_univ, rfl, univ_prod_univ.symm, λ x _, he x⟩,
  is_open_univ, e.smooth.smooth_on, e.symm.smooth.smooth_on⟩, mem_univ x⟩

lemma is_smooth_fiber_bundle.map_proj_nhds (h : is_smooth_fiber_bundle I I₂ I₃ F proj) (x : Z) :
  map proj (𝓝 x) = 𝓝 (proj x) :=
let ⟨e, ex⟩ := h (proj x) in e.map_proj_nhds $ e.mem_source.2 ex

/-- The projection from a smooth fiber bundle to its base is smooth. -/
lemma is_smooth_fiber_bundle.smooth_proj (h : is_smooth_fiber_bundle I I₂ I₃ F proj) :
  smooth I₃ I proj :=
λ x, let ⟨e, ex⟩ := h (proj x) in e.smooth_at_proj $ e.mem_source.mpr ex

/-- The projection from a smooth fiber bundle to its base is an open map. -/
lemma is_smooth_fiber_bundle.is_open_map_proj (h : is_smooth_fiber_bundle I I₂ I₃ F proj) :
  is_open_map proj :=
h.is_topological_fiber_bundle.is_open_map_proj

/-- The projection from a smooth fiber bundle with a nonempty fiber to its base is a surjective
map. -/
lemma is_smooth_fiber_bundle.surjective_proj [nonempty F]
  (h : is_smooth_fiber_bundle I I₂ I₃ F proj) :
  function.surjective proj :=
h.is_topological_fiber_bundle.surjective_proj

/-- The projection from a smooth fiber bundle with a nonempty fiber to its base is a quotient
map. -/
lemma is_smooth_fiber_bundle.quotient_map_proj [nonempty F]
  (h : is_smooth_fiber_bundle I I₂ I₃ F proj) : quotient_map proj :=
h.is_topological_fiber_bundle.quotient_map_proj

/-- The first projection in a product is a trivial smooth fiber bundle. -/
lemma is_trivial_smooth_fiber_bundle_fst :
  is_trivial_smooth_fiber_bundle I I₂ (I.prod I₂) F (prod.fst : B × F → B) :=
⟨diffeomorph.refl _ _ _, λ x, rfl⟩

/-- The first projection in a product is a smooth fiber bundle. -/
lemma is_smooth_fiber_bundle_fst :
  is_smooth_fiber_bundle I I₂ (I.prod I₂) F (prod.fst : B × F → B) :=
is_trivial_smooth_fiber_bundle_fst.is_smooth_fiber_bundle

/-- The second projection in a product is a trivial smooth fiber bundle. -/
lemma is_trivial_smooth_fiber_bundle_snd :
  is_trivial_smooth_fiber_bundle I I₂ (I₂.prod I) F (prod.snd : F × B → B) :=
⟨diffeomorph.prod_comm I₂ I F B ⊤, λ x, rfl⟩

/-- The second projection in a product is a smooth fiber bundle. -/
lemma is_smooth_fiber_bundle_snd :
  is_smooth_fiber_bundle I I₂ (I₂.prod I) F (prod.snd : F × B → B) :=
is_trivial_smooth_fiber_bundle_snd.is_smooth_fiber_bundle

lemma is_smooth_fiber_bundle.comp_diffeomorph
  (e : is_smooth_fiber_bundle I I₂ I₃ F proj) (h : Z' ≃ₘ⟮I₄, I₃⟯ Z) :
  is_smooth_fiber_bundle I I₂ I₄ F (proj ∘ h) :=
λ x, let ⟨e, he⟩ := e x in
⟨e.comp_diffeomorph h, by simpa [smooth_fiber_bundle.trivialization.comp_diffeomorph] using he⟩

namespace smooth_fiber_bundle.trivialization

/-- If `e` is a `trivialization` of `proj : Z → B` with fiber `F` and `h` is a diffeomorphism
`F ≃ F'`, then `e.trans_fiber_diffeomorph h` is the trivialization of `proj` with the fiber `F'`
that sends `p : Z` to `((e p).1, h (e p).2)`. -/
def trans_fiber_diffeomorph (e : trivialization I I₂ I₃ F proj) (h : F ≃ₘ⟮I₂, I₅⟯ F') :
  trivialization I I₅ I₃ F' proj :=
{ smooth_on_to_fun := (smooth_id.prod_map h.smooth).comp_smooth_on e.smooth_on,
  smooth_on_inv_fun :=
    e.smooth_on_symm.comp (smooth_id.prod_map h.symm.smooth).smooth_on subset.rfl,
  ..e.to_topological.trans_fiber_homeomorph h.to_homeomorph }

@[simp] lemma trans_fiber_diffeomorph_apply
  (e : trivialization I I₂ I₃ F proj) (h : F ≃ₘ⟮I₂, I₅⟯ F') (x : Z) :
  e.trans_fiber_diffeomorph h x = ((e x).1, h (e x).2) :=
rfl

/-- Coordinate transformation in the fiber induced by a pair of smooth bundle trivializations.
  See also `trivialization.coord_change_diffeomorph` for a version bundled as `F ≃ₘ F`. -/
def coord_change (e₁ e₂ : trivialization I I₂ I₃ F proj) (b : B) (x : F) : F :=
(e₂ $ e₁.to_local_homeomorph.symm (b, x)).2

lemma mk_coord_change (e₁ e₂ : trivialization I I₂ I₃ F proj) {b : B}
  (h₁ : b ∈ e₁.base_set) (h₂ : b ∈ e₂.base_set) (x : F) :
  (b, e₁.coord_change e₂ b x) = e₂ (e₁.to_local_homeomorph.symm (b, x)) :=
e₁.to_topological.mk_coord_change e₂.to_topological h₁ h₂ x

lemma coord_change_apply_snd
  (e₁ e₂ : trivialization I I₂ I₃ F proj) {p : Z}
  (h : proj p ∈ e₁.base_set) :
  e₁.coord_change e₂ (proj p) (e₁ p).snd = (e₂ p).snd :=
e₁.to_topological.coord_change_apply_snd e₂.to_topological h

lemma coord_change_same_apply
  (e : trivialization I I₂ I₃ F proj) {b : B} (h : b ∈ e.base_set) (x : F) :
  e.coord_change e b x = x :=
e.to_topological.coord_change_same_apply h x

lemma coord_change_same (e : trivialization I I₂ I₃ F proj) {b : B} (h : b ∈ e.base_set) :
  e.coord_change e b = id :=
funext $ e.coord_change_same_apply h

lemma coord_change_coord_change
  (e₁ e₂ e₃ : trivialization I I₂ I₃ F proj) {b : B}
  (h₁ : b ∈ e₁.base_set) (h₂ : b ∈ e₂.base_set) (x : F) :
  e₂.coord_change e₃ b (e₁.coord_change e₂ b x) = e₁.coord_change e₃ b x :=
e₁.to_topological.coord_change_coord_change e₂.to_topological e₃.to_topological h₁ h₂ x

lemma smooth_coord_change (e₁ e₂ : trivialization I I₂ I₃ F proj) {b : B}
  (h₁ : b ∈ e₁.base_set) (h₂ : b ∈ e₂.base_set) :
  smooth I₂ I₂ (e₁.coord_change e₂ b) :=
begin
  refine smooth_snd.comp (e₂.smooth_on.comp_smooth
    (e₁.smooth_on_symm.comp_smooth _ _) _),
  { exact smooth_const.prod_mk smooth_id },
  { exact λ x, e₁.mem_target.2 h₁ },
  { intro x, rwa [e₂.mem_source, e₁.proj_symm_apply' h₁] }
end

/-- Coordinate transformation in the fiber induced by a pair of bundle trivializations,
as a diffeomorphism. -/
def coord_change_diffeomorph
  (e₁ e₂ : trivialization I I₂ I₃ F proj) {b : B} (h₁ : b ∈ e₁.base_set) (h₂ : b ∈ e₂.base_set) :
  F ≃ₘ⟮I₂, I₂⟯ F :=
{ cont_mdiff_to_fun := e₁.smooth_coord_change e₂ h₁ h₂,
  cont_mdiff_inv_fun := e₂.smooth_coord_change e₁ h₂ h₁,
  ..e₁.to_topological.coord_change_homeomorph e₂.to_topological h₁ h₂ }

@[simp] lemma coord_change_diffeomorph_coe
  (e₁ e₂ : trivialization I I₂ I₃ F proj) {b : B} (h₁ : b ∈ e₁.base_set) (h₂ : b ∈ e₂.base_set) :
  ⇑(e₁.coord_change_diffeomorph e₂ h₁ h₂) = e₁.coord_change e₂ b :=
rfl

end smooth_fiber_bundle.trivialization

namespace smooth_fiber_bundle.trivialization

-- lemma is_image_preimage_prod (e : trivialization I I₂ I₃ F proj) (s : set B) :
--   e.to_local_homeomorph.is_image (proj ⁻¹' s) (s ×ˢ (univ : set F)) :=
-- λ x hx, by simp [e.coe_fst', hx]

-- /-- Restrict a `trivialization` to an open set in the base. `-/
-- def restr_open (e : trivialization I I₂ I₃ F proj) (s : set B)
--   (hs : is_open s) : trivialization I I₂ I₃ F proj :=
-- { to_local_homeomorph := ((e.is_image_preimage_prod s).symm.restr
--     (is_open.inter e.open_target (hs.prod is_open_univ))).symm,
--   base_set := e.base_set ∩ s,
--   open_base_set := is_open.inter e.open_base_set hs,
--   source_eq := by simp [e.source_eq],
--   target_eq := by simp [e.target_eq, prod_univ],
--   proj_to_fun := λ p hp, e.proj_to_fun p hp.1 }

end smooth_fiber_bundle.trivialization

/-! ### Constructing smooth fiber bundles -/

namespace bundle

-- instance [I : topological_space F] : ∀ x : B, topological_space (trivial B F x) := λ x, I

-- instance [t₁ : topological_space B] [t₂ : topological_space F] :
--   topological_space (total_space (trivial B F)) :=
-- topological_space.induced (proj (trivial B F)) t₁ ⊓
--   topological_space.induced (trivial.proj_snd B F) t₂

end bundle

variables (B F I I₂)
/-- Core data defining a locally trivial smooth bundle with fiber `F` over a smooth
space `B`. Note that "bundle" is used in its mathematical sense. This is the (computer science)
bundled version, i.e., all the relevant data is contained in the following structure. A family of
local trivializations is indexed by a type `ι`, on open subsets `base_set i` for each `i : ι`.
Trivialization changes from `i` to `j` are given by smooth maps `coord_change i j` from
`base_set i ∩ base_set j` to the set of homeomorphisms of `F`, but we express them as maps
`B → F → F` and require continuity on `(base_set i ∩ base_set j) × F` to avoid the topology on the
space of smooth maps on `F`. -/
@[nolint has_inhabited_instance]
structure smooth_fiber_bundle_core :=
(coord_change      : atlas H B → atlas H B → B → F → F)
(coord_change_self : ∀ i : atlas H B, ∀ x ∈ i.1.source, ∀ v, coord_change i i x v = v)
(smooth_on_coord_change : ∀ i j : atlas H B,
  smooth_on (I.prod I₂) I₂ (λ p : B × F, coord_change i j p.1 p.2)
            ((i.1.source ∩ j.1.source) ×ˢ (univ : set F)))
(coord_change_comp : ∀ i j k : atlas H B, ∀ x ∈ i.1.source ∩ j.1.source ∩ k.1.source, ∀ v,
  coord_change j k x (coord_change i j x v) = coord_change i k x v)

namespace smooth_fiber_bundle_core

variables {B F I I₂} (X : smooth_fiber_bundle_core I I₂ B F)

variable (H)
-- todo: move
/-- The chart at `b`, as an element of `atlas H B`. -/
@[simps (mfld_cfg)] def achart_at (b : B) : atlas H B := ⟨chart_at H b, chart_mem_atlas H b⟩

@[simp, mfld_simps] lemma achart_at_val {b : B} : (achart_at H b).1 = chart_at H b := rfl

variable {H}
include X

/-- The base space of a smooth fiber bundle core, as a convenience function for dot notation -/
@[nolint unused_arguments, reducible]
def base := B

/-- The fiber of a smooth fiber bundle core, as a convenience function for dot notation and
typeclass inference -/
@[nolint unused_arguments has_inhabited_instance, derive [topological_space, charted_space H₂]]
def fiber (x : B) := F

/-- The total space of the smooth fiber bundle, as a convenience function for dot notation.
It is by definition equal to `bundle.total_space X.fiber`, a.k.a. `Σ x, X.fiber x` but with a
different name for typeclass inference. -/
@[nolint unused_arguments, reducible]
def total_space := bundle.total_space X.fiber

/-- The projection from the total space of a smooth fiber bundle core, on its base. -/
@[reducible, simp, mfld_simps] def proj : X.total_space → B := bundle.total_space.proj

/-- A `smooth_fiber_bundle_core` interpreted as a `topological_fiber_bundle_core`. -/
@[simps (mfld_cfg)]
def to_topological : topological_fiber_bundle_core (atlas H B) B F :=
{ base_set := λ i, i.1.source,
  is_open_base_set := λ i, i.1.open_source,
  index_at := achart_at H,
  mem_base_set_at := mem_chart_source H,
  coord_change_continuous := λ i j, (X.smooth_on_coord_change i j).continuous_on, .. X }

@[simp, mfld_simps]
lemma to_topological_local_triv_achart_at (b : B) :
  X.to_topological.local_triv (achart_at H b) =
  X.to_topological.local_triv_at b :=
rfl

/-- Local homeomorphism version of the trivialization change. -/
-- todo: upgrade to diffeomorphism
def triv_change (i j : atlas H B) : local_homeomorph (B × F) (B × F) :=
X.to_topological.triv_change i j

@[simp, mfld_simps] lemma mem_triv_change_source (i j : atlas H B) (p : B × F) :
  p ∈ (X.triv_change i j).source ↔ p.1 ∈ i.1.source ∩ j.1.source :=
X.to_topological.mem_triv_change_source i j p

/-- Associate to a trivialization index `i : ι` the corresponding trivialization, i.e., a bijection
between `proj ⁻¹ (base_set i)` and `base_set i × F`. As the fiber above `x` is `F` but read in the
chart with index `index_at x`, the trivialization in the fiber above x is by definition the
coordinate change from i to `index_at x`, so it depends on `x`.
The local trivialization will ultimately be a local diffeomorphism. For now, we only introduce the
local equiv version, denoted with a prime. In further developments, avoid this auxiliary version,
and use `X.local_triv` instead.
-/
def local_triv_as_local_equiv (i : atlas H B) : local_equiv X.total_space (B × F) :=
X.to_topological.local_triv_as_local_equiv i

variable (i : atlas H B)

lemma mem_local_triv_as_local_equiv_source (p : X.total_space) :
  p ∈ (X.local_triv_as_local_equiv i).source ↔ p.1 ∈ i.1.source :=
iff.rfl

lemma mem_local_triv_as_local_equiv_target (p : B × F) :
  p ∈ (X.local_triv_as_local_equiv i).target ↔ p.1 ∈ i.1.source :=
X.to_topological.mem_local_triv_as_local_equiv_target i p

lemma local_triv_as_local_equiv_apply (p : X.total_space) :
  (X.local_triv_as_local_equiv i) p = ⟨p.1, X.coord_change (achart_at H p.1) i p.1 p.2⟩ := rfl

/-- The composition of two local trivializations is the trivialization change X.triv_change i j. -/
lemma local_triv_as_local_equiv_trans (i j : atlas H B) :
  (X.local_triv_as_local_equiv i).symm.trans
    (X.local_triv_as_local_equiv j) ≈ (X.triv_change i j).to_local_equiv :=
X.to_topological.local_triv_as_local_equiv_trans i j

/-- Topological structure on the total space of a smooth bundle created from core, designed so
that all the local trivialization are continuous. -/
instance to_topological_space : topological_space X.total_space :=
X.to_topological.to_topological_space $ atlas H B

/-- A local trivialization as a local homeomorphism -/
def local_homeomorph_chart (i : atlas H B) (j : atlas H₂ F) :
  local_homeomorph X.total_space (model_prod H H₂) :=
(X.to_topological.local_triv i).to_local_homeomorph ≫ₕ i.1.prod j.1

/-- Charted space structure on the total space of a smooth bundle created from core, designed so
that all the local trivialization are smooth. -/
instance to_charted_space : charted_space (model_prod H H₂) X.total_space :=
{ atlas := ⋃ (i : atlas H B) (j : atlas H₂ F), {X.local_homeomorph_chart i j},
  chart_at := λ x, X.local_homeomorph_chart (achart_at H x.1) (achart_at H₂ x.2),
  mem_chart_source := λ x, by { simp only [local_homeomorph_chart] with mfld_simps },
  chart_mem_atlas := λ x, by { simp_rw [mem_Union, mem_singleton_iff], exact ⟨_, _, rfl⟩ } }

variables
[smooth_manifold_with_corners I B]
[smooth_manifold_with_corners I' B']
[smooth_manifold_with_corners I₂ F]
[smooth_manifold_with_corners I₅ F']
[smooth_manifold_with_corners I₃ Z]
[smooth_manifold_with_corners I₄ Z']

instance to_smooth_manifold_with_corners :
  smooth_manifold_with_corners (I.prod I₂) X.total_space :=
begin
  refine @smooth_manifold_with_corners.mk _ _ _ _ _ _ _ _ _ _ _ ⟨λ e e', _⟩,
  rintro ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, he⟩ ⟨_, ⟨i', rfl⟩, _, ⟨j', rfl⟩, he'⟩,
  rw [mem_singleton_iff] at he he', substs he he',
  simp_rw [local_homeomorph_chart, local_homeomorph.trans_symm_eq_symm_trans_symm],
  sorry
end


open smooth_fiber_bundle

lemma foo (i : atlas H B) (x : X.total_space) :
  ext_chart_at (I.prod I₂) ((X.to_topological.local_triv i) x) ∘ X.to_topological.local_triv i ∘ (ext_chart_at (I.prod I₂) x).symm = id :=
begin
  ext1 y,
  -- refine (congr_arg (ext_chart_at _ _) ((X.to_topological.local_triv i).apply_symm_apply _)).trans _,
  dsimp only [ext_chart_at_coe_symm, smooth_fiber_bundle_core.to_charted_space, function.comp,
    smooth_fiber_bundle_core.local_homeomorph_chart, local_homeomorph.coe_trans_symm],
  -- simp_rw [local_homeomorph.coe_trans_symm]
  -- dsimp,
  /-
(⇑I (⇑(chart_at H x.fst) (⇑((chart_at (model_prod H H₂) x).symm) (⇑((I.to_local_equiv.prod I₂.to_local_equiv).symm) (b, f))).fst), ⇑I₂ (⇑(chart_at H₂ (X.coord_change (X.index_at x.fst) i x.fst x.snd)) (X.coord_change (X.index_at (⇑((chart_at (model_prod H H₂) x).symm) (⇑((I.to_local_equiv.prod I₂.to_local_equiv).symm) (b, f))).fst) i (⇑((chart_at (model_prod H H₂) x).symm) (⇑((I.to_local_equiv.prod I₂.to_local_equiv).symm) (b, f))).fst (⇑((chart_at (model_prod H H₂) x).symm) (⇑((I.to_local_equiv.prod I₂.to_local_equiv).symm) (b, f))).snd)))
  -/
  sorry
end

-- (⇑I (⇑(chart_at H x.fst) (⇑((chart_at (model_prod H H₂) x).symm) (⇑((I.to_local_equiv.prod I₂.to_local_equiv).symm) (b, f))).fst),
-- ⇑I₂ (⇑(chart_at H₂ (X.coord_change (X.index_at x.fst) i x.fst x.snd)) (X.coord_change (X.index_at (⇑((chart_at (model_prod H H₂) x).symm) (⇑((I.to_local_equiv.prod I₂.to_local_equiv).symm) (b, f))).fst) i (⇑((chart_at (model_prod H H₂) x).symm) (⇑((I.to_local_equiv.prod I₂.to_local_equiv).symm) (b, f))).fst (⇑((chart_at (model_prod H H₂) x).symm) (⇑((I.to_local_equiv.prod I₂.to_local_equiv).symm) (b, f))).snd)))

/-- Extended version of the local trivialization of a fiber bundle constructed from core,
registering additionally in its type that it is a local bundle trivialization. -/
def local_triv (i : atlas H B) : trivialization I I₂ (I.prod I₂) F X.proj :=
{ smooth_on_to_fun := by { simp only [smooth_on] with mfld_simps, intros x hx,
  rw [cont_mdiff_within_at_iff],
  refine ⟨(X.to_topological.local_triv i).continuous_to_fun x hx, _⟩,
  sorry
   },
  smooth_on_inv_fun := sorry,
  ..X.to_topological.local_triv i }
  -- { source      := Z.proj ⁻¹' (Z.base_set i),
  -- target      := Z.base_set i ×ˢ (univ : set F),
  -- inv_fun     := λp, ⟨p.1, Z.coord_change i (Z.index_at p.1) p.1 p.2⟩,
  -- to_fun      := λp, ⟨p.1, Z.coord_change (Z.index_at p.1) i p.1 p.2⟩,
-- { base_set      := i.1.source,
--   open_base_set := X.is_open_base_set i,
--   source_eq     := rfl,
--   target_eq     := rfl,
--   proj_to_fun   := λ p hp, by { simp only with mfld_simps, refl },
--   open_source := X.open_source' i,
--   open_target := (X.is_open_base_set i).prod is_open_univ,
--   continuous_to_fun := begin
--     rw continuous_on_open_iff (X.open_source' i),
--     assume s s_open,
--     apply topological_space.generate_open.basic,
--     simp only [exists_prop, mem_Union, mem_singleton_iff],
--     exact ⟨i, s, s_open, rfl⟩
--   end,
--   continuous_inv_fun := begin
--     apply continuous_on_open_of_generate_from ((X.is_open_base_set i).prod is_open_univ),
--     assume t ht,
--     simp only [exists_prop, mem_Union, mem_singleton_iff] at ht,
--     obtain ⟨j, s, s_open, ts⟩ : ∃ j s, is_open s ∧ t =
--       (local_triv_as_local_equiv X j).source ∩ (local_triv_as_local_equiv X j) ⁻¹' s := ht,
--     rw ts,
--     simp only [local_equiv.right_inv, preimage_inter, local_equiv.left_inv],
--     let e := X.local_triv_as_local_equiv i,
--     let e' := X.local_triv_as_local_equiv j,
--     let f := e.symm.trans e',
--     have : is_open (f.source ∩ f ⁻¹' s),
--     { rw [(X.local_triv_as_local_equiv_trans i j).source_inter_preimage_eq],
--       exact (continuous_on_open_iff (X.triv_change i j).open_source).1
--         ((X.triv_change i j).continuous_on) _ s_open },
--     convert this using 1,
--     dsimp [local_equiv.trans_source],
--     rw [← preimage_comp, inter_assoc],
--     refl,
--   end,
--   to_local_equiv := X.local_triv_as_local_equiv i }

#exit

/-- A smooth fiber bundle constructed from core is indeed a smooth fiber bundle. -/
protected theorem is_smooth_fiber_bundle : is_smooth_fiber_bundle I I₂ (I.prod I₂) F X.proj :=
λx, ⟨X.local_triv (X.index_at x), X.mem_base_set_at x⟩

/-- The projection on the base of a smooth bundle created from core is smooth -/
lemma smooth_proj : smooth (I.prod I₂) I X.proj :=
X.is_smooth_fiber_bundle.smooth_proj

/-- The projection on the base of a smooth bundle created from core is an open map -/
lemma is_open_map_proj : is_open_map X.proj :=
X.is_smooth_fiber_bundle.is_open_map_proj

/-- Preferred local trivialization of a fiber bundle constructed from core, at a given point, as
a bundle trivialization -/
def local_triv_at (b : B) : trivialization I I₂ (I.prod I₂) F X.proj :=
X.local_triv (X.index_at b)

@[simp, mfld_simps] lemma local_triv_at_def (b : B) :
  X.local_triv (X.index_at b) = X.local_triv_at b := rfl

/-- If an element of `F` is invariant under all coordinate changes, then one can define a
corresponding section of the fiber bundle, which is smooth. This applies in particular to the
zero section of a vector bundle. Another example (not yet defined) would be the identity
section of the endomorphism bundle of a vector bundle. -/
lemma smooth_const_section (v : F)
  (h : ∀ i j, ∀ x ∈ i.1.source ∩ j.1.source, X.coord_change i j x v = v) :
  smooth I (I.prod I₂) (show B → X.total_space, from λ x, ⟨x, v⟩) :=
begin
  sorry
  -- apply smooth_iff_smooth_at.2 (λ x, _),
  -- have A : X.base_set (X.index_at x) ∈ 𝓝 x :=
  --   is_open.mem_nhds (X.is_open_base_set (X.index_at x)) (X.mem_base_set_at x),
  -- apply ((X.local_triv_at x).to_local_homeomorph.smooth_at_iff_smooth_at_comp_left _).2,
  -- { simp only [(∘)] with mfld_simps,
  --   apply smooth_at_id.prod,
  --   have : smooth_on (λ (y : B), v) (X.base_set (X.index_at x)) := smooth_on_const,
  --   apply (this.congr _).smooth_at A,
  --   assume y hy,
  --   simp only [h, hy, mem_base_set_at] with mfld_simps },
  -- { exact A }
end

@[simp, mfld_simps] lemma local_triv_as_local_equiv_coe :
  ⇑(X.local_triv_as_local_equiv i) = X.local_triv i := rfl

@[simp, mfld_simps] lemma local_triv_as_local_equiv_source :
  (X.local_triv_as_local_equiv i).source = (X.local_triv i).source := rfl

@[simp, mfld_simps] lemma local_triv_as_local_equiv_target :
  (X.local_triv_as_local_equiv i).target = (X.local_triv i).target := rfl

@[simp, mfld_simps] lemma local_triv_as_local_equiv_symm :
  (X.local_triv_as_local_equiv i).symm = (X.local_triv i).to_local_equiv.symm := rfl

@[simp, mfld_simps] lemma base_set_at : i.1.source = (X.local_triv i).base_set := rfl

@[simp, mfld_simps] lemma local_triv_apply (p : X.total_space) :
  (X.local_triv i) p = ⟨p.1, X.coord_change (X.index_at p.1) i p.1 p.2⟩ := rfl

@[simp, mfld_simps] lemma mem_local_triv_source (p : X.total_space) :
  p ∈ (X.local_triv i).source ↔ p.1 ∈ (X.local_triv i).base_set := iff.rfl

@[simp, mfld_simps] lemma mem_local_triv_target (p : B × F) :
  p ∈ (X.local_triv i).target ↔ p.1 ∈ (X.local_triv i).base_set :=
trivialization.mem_target _

@[simp, mfld_simps] lemma local_triv_symm_apply (p : B × F) :
  (X.local_triv i).to_local_homeomorph.symm p =
    ⟨p.1, X.coord_change i (X.index_at p.1) p.1 p.2⟩ := rfl

@[simp, mfld_simps] lemma local_triv_at_apply (b : B) (a : F) :
  ((X.local_triv_at b) ⟨b, a⟩) = ⟨b, a⟩ :=
by { rw [local_triv_at, local_triv_apply, coord_change_self], exact X.mem_base_set_at b }

@[simp, mfld_simps] lemma mem_local_triv_at_base_set (b : B) :
  b ∈ (X.local_triv_at b).base_set :=
by { rw [local_triv_at, ←base_set_at], exact X.mem_base_set_at b, }

open bundle

/-- The inclusion of a fiber into the total space is a smooth map. -/
@[continuity]
lemma smooth_total_space_mk (b : B) : smooth I₂ (I.prod I₂) (λ a, total_space_mk X.fiber b a) :=
begin
  sorry
  -- rw [smooth_iff_le_induced, smooth_fiber_bundle_core.to_topological_space],
  -- apply le_induced_generate_from,
  -- simp only [total_space_mk, mem_Union, mem_singleton_iff, local_triv_as_local_equiv_source,
  --   local_triv_as_local_equiv_coe],
  -- rintros s ⟨i, t, ht, rfl⟩,
  -- rw [←((X.local_triv i).source_inter_preimage_target_inter t), preimage_inter, ←preimage_comp,
  --   trivialization.source_eq],
  -- apply is_open.inter,
  -- { simp only [bundle.proj, proj, ←preimage_comp],
  --   by_cases (b ∈ (X.local_triv i).base_set),
  --   { rw preimage_const_of_mem h, exact is_open_univ, },
  --   { rw preimage_const_of_not_mem h, exact is_open_empty, }},
  -- { simp only [function.comp, local_triv_apply],
  --   rw [preimage_inter, preimage_comp],
  --   by_cases (b ∈ i.1.source),
  --   { have hc : smooth (λ (x : X.fiber b), (X.coord_change (X.index_at b) i b) x),
  --       from (X.smooth_on_coord_change (X.index_at b) i).comp_smooth
  --         (smooth_const.prod_mk smooth_id) (λ x, ⟨⟨X.mem_base_set_at b, h⟩, mem_univ x⟩),
  --     exact (((X.local_triv i).open_target.inter ht).preimage (smooth.prod.mk b)).preimage hc },
  --   { rw [(X.local_triv i).target_eq, ←base_set_at, mk_preimage_prod_right_eq_empty h,
  --       preimage_empty, empty_inter],
  --     exact is_open_empty, }}
end

end smooth_fiber_bundle_core
