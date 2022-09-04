/-
Copyright (c) 2022 Paul Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert, Yaël Dillies
-/
import analysis.convex.basic
import analysis.normed_space.add_torsor_bases
import analysis.normed_space.basic
import analysis.normed_space.linear_isometry
import data.real.basic
import data.set.pointwise
import linear_algebra.affine_space.pointwise

/-!
# Intrinsic frontier and interior

This file defines the intrinsic frontier and intrinsic interior of a set.

## References

See chapter 8 of [Barry Simon, *Convexity*][simon2011] or chapter 1 of
[Rolf Schneider, *Convex Bodies: The Brunn-Minkowski theory*][schneider2013].
-/

open_locale pointwise

-- MOVETO data.set.pointwise

lemma set.vadd_vsub_vadd_cancel_left {V : Type} [add_comm_group V]
  (x : V) (A B : set V) :
(x +ᵥ A) -ᵥ (x +ᵥ B) = A -ᵥ B :=
begin
  ext, split,
  { rintro ⟨-, -, ⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, rfl⟩,
    rw [vadd_vsub_vadd_cancel_left x],
    exact ⟨a, b, ha, hb, rfl⟩ },
  { rintro ⟨a, b, ha, hb, rfl⟩,
    rw [←vadd_vsub_vadd_cancel_left x],
    exact ⟨_, _, ⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, rfl⟩ },
end

-- MOVETO linear_algebra.affine_space.affine_subspace

/-- The inclusion of an affine subspace as an affine map. -/
def affine_subspace.inclusion_affine {R V P : Type} [ring R] [add_comm_group V] [module R V]
  [add_torsor V P] (E : affine_subspace R P) [nonempty E] : E →ᵃ[R] P :=
begin
  refine ⟨coe, E.direction.subtype, by tauto⟩,
end

/-- A nonempty affine subspace of a `normed_add_torsor` is itself a `normed_add_torsor`. -/
@[nolint fails_quickly] -- Because of the add_torsor.nonempty instance.
instance affine_subspace.to_normed_add_torsor {R V P : Type*} [ring R]
  [seminormed_add_comm_group V]
  [pseudo_metric_space P] [module R V] [normed_add_torsor V P]
  (s : affine_subspace R P) [nonempty s] : normed_add_torsor s.direction s :=
{ dist_eq_norm' := λ x y, normed_add_torsor.dist_eq_norm' ↑x ↑y,
  ..affine_subspace.to_add_torsor s }

/-- The inclusion of an affine subspace of a normed affine space as an affine isometry. -/
def affine_subspace.inclusion_affine_isometry {𝕜 V P : Type} [normed_field 𝕜]
  [seminormed_add_comm_group V] [normed_space 𝕜 V] [pseudo_metric_space P] [normed_add_torsor V P]
  (E : affine_subspace 𝕜 P) [nonempty E] : E →ᵃⁱ[𝕜] P :=
begin
  refine ⟨E.inclusion_affine, by tauto⟩,
end

instance affine_subspace.nonempty_map {R V₁ P₁ V₂ P₂ : Type}
  [ring R] [add_comm_group V₁] [add_comm_group V₂] [module R V₁] [module R V₂]
  [add_torsor V₁ P₁] [add_torsor V₂ P₂] {E : affine_subspace R P₁} [Ene : nonempty E]
  {φ : P₁ →ᵃ[R] P₂} : nonempty (E.map φ) :=
begin
  obtain ⟨x, hx⟩ := id Ene,
  refine ⟨⟨φ x, affine_subspace.mem_map.mpr ⟨x, hx, rfl⟩⟩⟩,
end

-- MOVETO algebra.module.linear_map

/-- Restrict domain and codomain of a linear map to the given submodules. -/
def linear_map.restrict' {R V₁ V₂ : Type}
  [ring R] [add_comm_group V₁] [add_comm_group V₂] [module R V₁] [module R V₂]
  (φ : V₁ →ₗ[R] V₂) {E : submodule R V₁} {F : submodule R V₂}
  (hEF : E.map φ ≤ F) : E →ₗ[R] F :=
begin
  refine ⟨_, _, _⟩,
  { exact λ x, ⟨φ x, hEF $ submodule.mem_map.mpr ⟨x, x.property, rfl⟩⟩ },
  all_goals { intros x y,
              simp only [subtype.ext_iff, subtype.coe_mk, submodule.coe_add, submodule.coe_smul],
              apply_rules [φ.map_add, φ.map_smul] },
end

lemma linear_map.restrict'.coe_apply {R V₁ V₂ : Type}
  [ring R] [add_comm_group V₁] [add_comm_group V₂] [module R V₁] [module R V₂]
  (φ : V₁ →ₗ[R] V₂) {E : submodule R V₁} {F : submodule R V₂}
  (hEF : E.map φ ≤ F) (x : E) :
↑(φ.restrict' hEF x) = φ x := rfl

-- MOVETO linear_algebra.affine_space.affine_map

/-- Restrict domain and codomain of an affine map to the given submodules. -/
def affine_map.restrict {R V₁ V₂ P₁ P₂ : Type}
  [ring R] [add_comm_group V₁] [add_comm_group V₂] [module R V₁]
  [module R V₂]
  [add_torsor V₁ P₁] [add_torsor V₂ P₂]
  (φ : P₁ →ᵃ[R] P₂) {E : affine_subspace R P₁} {F : affine_subspace R P₂}
  [nonempty E] [nonempty F]
  (hEF : E.map φ ≤ F) : E →ᵃ[R] F :=
begin
  refine ⟨_, _, _⟩,
  { exact λ x, ⟨φ x, hEF $ affine_subspace.mem_map.mpr ⟨x, x.property, rfl⟩⟩ },
  { refine φ.linear.restrict' _,
    rw [←affine_subspace.map_direction],
    exact affine_subspace.direction_le hEF },
  { intros p v,
    simp only [subtype.ext_iff, subtype.coe_mk, affine_subspace.coe_vadd],
    apply affine_map.map_vadd },
end

lemma affine_map.restrict.coe_apply {R V₁ V₂ P₁ P₂ : Type}
  [ring R] [add_comm_group V₁] [add_comm_group V₂] [module R V₁]
  [module R V₂]
  [add_torsor V₁ P₁] [add_torsor V₂ P₂]
  (φ : P₁ →ᵃ[R] P₂) {E : affine_subspace R P₁} {F : affine_subspace R P₂}
  [nonempty E] [nonempty F]
  (hEF : E.map φ ≤ F) (x : E) :
↑(φ.restrict hEF x) = φ x := rfl

lemma affine_map.restrict.linear {R V₁ V₂ P₁ P₂ : Type}
  [ring R] [add_comm_group V₁] [add_comm_group V₂] [module R V₁]
  [module R V₂]
  [add_torsor V₁ P₁] [add_torsor V₂ P₂]
  (φ : P₁ →ᵃ[R] P₂) {E : affine_subspace R P₁} {F : affine_subspace R P₂}
  [nonempty E] [nonempty F]
  (hEF : E.map φ ≤ F) :
(φ.restrict hEF).linear = φ.linear.restrict'
  (by { rw [←affine_subspace.map_direction], exact affine_subspace.direction_le hEF }) := rfl

lemma affine_map.restrict.injective {R V₁ V₂ P₁ P₂ : Type}
  [ring R] [add_comm_group V₁] [add_comm_group V₂] [module R V₁]
  [module R V₂]
  [add_torsor V₁ P₁] [add_torsor V₂ P₂]
  {φ : P₁ →ᵃ[R] P₂}
  (hφ : function.injective φ) {E : affine_subspace R P₁} {F : affine_subspace R P₂}
  [nonempty E] [nonempty F]
  (hEF : E.map φ ≤ F) :
function.injective (affine_map.restrict φ hEF) :=
begin
  intros x y h,
  simp only [subtype.ext_iff, subtype.coe_mk, affine_map.restrict.coe_apply] at h ⊢,
  exact hφ h,
end

lemma affine_map.restrict.surjective {R V₁ V₂ P₁ P₂ : Type}
  [ring R] [add_comm_group V₁] [add_comm_group V₂] [module R V₁]
  [module R V₂] [add_torsor V₁ P₁] [add_torsor V₂ P₂]
  (φ : P₁ →ᵃ[R] P₂) {E : affine_subspace R P₁} [nonempty E] :
function.surjective (affine_map.restrict φ (le_refl (E.map φ))) :=
begin
  rintro ⟨x, hx : x ∈ E.map φ⟩,
  rw [affine_subspace.mem_map] at hx,
  obtain ⟨y, hy, rfl⟩ := hx,
  exact ⟨⟨y, hy⟩, rfl⟩,
end

lemma affine_map.bijective_iff_linear_bijective {R V₁ V₂ P₁ P₂ : Type}
  [ring R] [add_comm_group V₁] [add_comm_group V₂] [module R V₁]
  [module R V₂] [add_torsor V₁ P₁] [add_torsor V₂ P₂]
  (φ : P₁ →ᵃ[R] P₂) :
function.bijective φ ↔ function.bijective φ.linear :=
begin
  simp only [function.bijective,
    φ.injective_iff_linear_injective, φ.surjective_iff_linear_surjective],
end

lemma affine_span_induction {R V P : Type} [ring R] [add_comm_group V] [module R V]
  [add_torsor V P] {x : P} {s : set P} {p : P → Prop} (h : x ∈ affine_span R s)
  (Hs : ∀ x : P, x ∈ s → p x)
  (Hc : ∀ (c : R) (u v w : P), p u → p v → p w → p (c • (u -ᵥ v) +ᵥ w)) : p x :=
(@affine_span_le _ _ _ _ _ _ _ _ ⟨p, Hc⟩).mpr Hs h

lemma affine_span_induction' {R V P : Type} [ring R] [add_comm_group V] [module R V]
  [add_torsor V P] {x : P} {s : set P} {p : Π x, x ∈ affine_span R s → Prop}
  (h : x ∈ affine_span R s)
  (Hs : ∀ y (hys : y ∈ s), p y (subset_affine_span R _ hys))
  (Hc : ∀ (c : R) u hu v hv w hw, p u hu → p v hv → p w hw →
    p (c • (u -ᵥ v) +ᵥ w) (affine_subspace.smul_vsub_vadd_mem _ _ hu hv hw)) : p x h :=
begin
  refine exists.elim _ (λ (hx : x ∈ affine_span R s) (hc : p x hx), hc),
  refine @affine_span_induction R V P _ _ _ _ _ _ _ h _ _,
  -- Why can't I substitute the following goals into the `refine` expression?
  { exact (λ y hy, ⟨subset_affine_span _ _ hy, Hs y hy⟩) },
  { exact (λ c u v w hu hv hw, exists.elim hu $ λ hu' hu, exists.elim hv $ λ hv' hv,
      exists.elim hw $ λ hw' hw,
        ⟨affine_subspace.smul_vsub_vadd_mem _ _ hu' hv' hw', Hc _ _ _ _ _ _ _ hu hv hw⟩) },
end

lemma affine_span_affine_span_coe_preimage (R : Type) {V P : Type}
  [ring R] [add_comm_group V] [module R V] [add_torsor V P] (A : set P) [nonempty A] :
affine_span R ((coe : affine_span R A → P) ⁻¹' A) = ⊤ :=
begin
  rw [eq_top_iff],
  rintro ⟨x, hx⟩ -,
  refine affine_span_induction' hx (λ y hy, _) (λ c u hu v hv w hw, _),
  { exact subset_affine_span _ _ hy },
  { exact affine_subspace.smul_vsub_vadd_mem _ _ },
end

-- MOVETO linear_algebra.affine_space.affine_equiv

/-- Bijective affine maps are affine isomorphisms. -/
noncomputable def affine_equiv.of_bijective {R V₁ V₂ P₁ P₂ : Type}
  [ring R] [add_comm_group V₁] [add_comm_group V₂] [module R V₁]
  [module R V₂]
  [add_torsor V₁ P₁] [add_torsor V₂ P₂]
  {φ : P₁ →ᵃ[R] P₂}
  (hφ : function.bijective φ) : P₁ ≃ᵃ[R] P₂ :=
begin
  refine ⟨equiv.of_bijective _ hφ, _, _⟩,
  { refine linear_equiv.of_bijective φ.linear _ _ ;
      obtain ⟨_, _⟩ := hφ ;
      simp only [φ.injective_iff_linear_injective, φ.surjective_iff_linear_surjective] ;
      assumption },
  simp only [equiv.of_bijective_apply, linear_equiv.of_bijective_apply, affine_map.map_vadd,
    eq_self_iff_true, forall_const],
end

lemma affine_equiv.of_bijective_apply {R V₁ V₂ P₁ P₂ : Type}
  [ring R] [add_comm_group V₁] [add_comm_group V₂] [module R V₁]
  [module R V₂]
  [add_torsor V₁ P₁] [add_torsor V₂ P₂]
  {φ : P₁ →ᵃ[R] P₂}
  (hφ : function.bijective φ) (x : P₁) :
affine_equiv.of_bijective hφ x = φ x := rfl

lemma affine_equiv.of_bijective.symm_eq {R V₁ V₂ P₁ P₂ : Type}
  [ring R] [add_comm_group V₁] [add_comm_group V₂] [module R V₁]
  [module R V₂]
  [add_torsor V₁ P₁] [add_torsor V₂ P₂]
  {φ : P₁ →ᵃ[R] P₂}
  (hφ : function.bijective φ) :
(affine_equiv.of_bijective hφ).symm.to_equiv = (equiv.of_bijective _ hφ).symm := rfl

lemma affine_equiv.of_bijective_linear {R V₁ V₂ P₁ P₂ : Type}
  [ring R] [add_comm_group V₁] [add_comm_group V₂] [module R V₁]
  [module R V₂]
  [add_torsor V₁ P₁] [add_torsor V₂ P₂]
  {φ : P₁ →ᵃ[R] P₂}
  (hφ : function.bijective φ) :
(affine_equiv.of_bijective hφ).linear = linear_equiv.of_bijective φ.linear
  (φ.injective_iff_linear_injective.mpr hφ.1)
  (φ.surjective_iff_linear_surjective.mpr hφ.2) := rfl

lemma affine_equiv.image_symm {R V₁ P₁ V₂ P₂ : Type} [ring R]
  [add_comm_group V₁] [add_comm_group V₂]
  [module R V₁] [module R V₂]
  [add_torsor V₁ P₁] [add_torsor V₂ P₂]
  (f : P₁ ≃ᵃ[R] P₂) :
set.image f.symm = set.preimage f :=
funext f.symm.to_equiv.image_eq_preimage

lemma affine_equiv.preimage_symm {R V₁ P₁ V₂ P₂ : Type} [ring R]
  [add_comm_group V₁] [add_comm_group V₂]
  [module R V₁] [module R V₂]
  [add_torsor V₁ P₁] [add_torsor V₂ P₂]
  (f : P₁ ≃ᵃ[R] P₂) :
set.preimage f.symm = set.image f :=
(funext f.to_equiv.image_eq_preimage).symm

lemma affine_equiv.comap_span {R V₁ P₁ V₂ P₂ : Type} [ring R]
  [add_comm_group V₁] [add_comm_group V₂]
  [module R V₁] [module R V₂]
  [add_torsor V₁ P₁] [add_torsor V₂ P₂]
  (f : P₁ ≃ᵃ[R] P₂) (A : set P₂) :
affine_subspace.comap f.to_affine_map (affine_span R A) = affine_span R (f ⁻¹' A) :=
begin
  ext1,
  simp only [affine_subspace.coe_comap, ←affine_equiv.image_symm],
  simp only [←affine_equiv.coe_to_affine_map],
  rw [←affine_subspace.map_span, affine_subspace.coe_map],
  exact (f.to_equiv.symm.image_eq_preimage _).symm,
end

-- MOVETO analysis.normed_space.affine_isometry

/-- Restriction of an affine isometry to an affine isomorphism, given a submodule of the domain. -/
noncomputable def affine_isometry.restrict_to_equiv {𝕜 V₁ V₂ P₁ P₂ : Type}
  [normed_field 𝕜] [seminormed_add_comm_group V₁] [seminormed_add_comm_group V₂] [normed_space 𝕜 V₁]
  [normed_space 𝕜 V₂] [metric_space P₁] [pseudo_metric_space P₂]
  [normed_add_torsor V₁ P₁] [normed_add_torsor V₂ P₂]
  (E : affine_subspace 𝕜 P₁) [nonempty E]
  (φ : P₁ →ᵃⁱ[𝕜] P₂) : E ≃ᵃⁱ[𝕜] E.map φ.to_affine_map :=
begin
  let f := φ.to_affine_map.restrict (le_refl (E.map φ.to_affine_map)),
  have fi : function.injective f := affine_map.restrict.injective φ.injective _,
  have fs : function.surjective f := affine_map.restrict.surjective _,
  have fb : function.bijective f := ⟨fi, fs⟩,
  refine ⟨affine_equiv.of_bijective fb, _⟩,
  { simp only [affine_equiv.of_bijective_linear, linear_equiv.of_bijective_apply],
    simp only [f, affine_map.restrict.linear],
    simp only [←submodule.norm_coe, linear_map.restrict'.coe_apply],
    simp only [affine_isometry.linear_eq_linear_isometry, linear_isometry.coe_to_linear_map,
      linear_isometry.norm_map, eq_self_iff_true, forall_const] },
end

lemma affine_isometry.restrict_to_equiv.apply_symm_apply {𝕜 V₁ V₂ P₁ P₂ : Type}
  [normed_field 𝕜] [seminormed_add_comm_group V₁] [seminormed_add_comm_group V₂] [normed_space 𝕜 V₁]
  [normed_space 𝕜 V₂] [metric_space P₁] [pseudo_metric_space P₂]
  [normed_add_torsor V₁ P₁] [normed_add_torsor V₂ P₂]
  {E : affine_subspace 𝕜 P₁} [nonempty E]
  {φ : P₁ →ᵃⁱ[𝕜] P₂} (x : E.map φ.to_affine_map) :
φ ((φ.restrict_to_equiv E).symm x) = x :=
begin
  simp only [affine_isometry.restrict_to_equiv,
    ←affine_isometry_equiv.coe_to_affine_equiv, ←affine_isometry_equiv.to_affine_equiv_symm],
  simp only [←affine_equiv.coe_to_equiv, affine_equiv.of_bijective.symm_eq],
  have := equiv.of_bijective_apply_symm_apply (φ.to_affine_map.restrict _) _ x,
  replace this := congr_arg (coe : E.map φ.to_affine_map → P₂) this,
  simp only [affine_map.restrict.coe_apply] at this,
  exact this,
end

lemma affine_isometry_equiv.comap_span {𝕜 V₁ P₁ V₂ P₂ : Type} [normed_field 𝕜]
  [normed_add_comm_group V₁] [normed_add_comm_group V₂]
  [pseudo_metric_space P₁] [pseudo_metric_space P₂] [normed_space 𝕜 V₁] [normed_space 𝕜 V₂]
  [normed_add_torsor V₁ P₁] [normed_add_torsor V₂ P₂]
  (f : P₁ ≃ᵃⁱ[𝕜] P₂) (A : set P₂) :
affine_subspace.comap f.to_affine_equiv.to_affine_map (affine_span 𝕜 A) =
  affine_span 𝕜 (f ⁻¹' A) :=
f.to_affine_equiv.comap_span A

lemma affine_isometry_equiv.map_span {𝕜 V₁ P₁ V₂ P₂ : Type} [normed_field 𝕜]
  [normed_add_comm_group V₁] [normed_add_comm_group V₂]
  [pseudo_metric_space P₁] [pseudo_metric_space P₂] [normed_space 𝕜 V₁] [normed_space 𝕜 V₂]
  [normed_add_torsor V₁ P₁] [normed_add_torsor V₂ P₂]
  (f : P₁ ≃ᵃⁱ[𝕜] P₂) (A : set P₁) :
affine_subspace.map f.to_affine_equiv.to_affine_map (affine_span 𝕜 A) =
  affine_span 𝕜 (f '' A) :=
affine_subspace.map_span f.to_affine_equiv.to_affine_map A

-- MOVETO analysis.normed.group.add_torsor

/-- In a normed additive torsor, translation is an affine isometry. -/
def normed_add_torsor.vadd_affine_isometry (R P : Type) {V : Type}
  [normed_field R] [seminormed_add_comm_group V] [normed_space R V] [pseudo_metric_space P]
  [normed_add_torsor V P] (x : V):
P →ᵃⁱ[R] P :=
begin
  refine ⟨⟨has_vadd.vadd x, linear_map.id, _⟩, _⟩,
  { intros p v,
    rw [vadd_vadd, vadd_vadd, add_comm],
    refl },
  { simp only [linear_map.id_coe, id.def, eq_self_iff_true, forall_const] },
end

-- MOVETO topology.homeomorph

lemma homeomorph.interior_nonempty_iff_image {α β : Type}
  [topological_space α] [topological_space β] (φ : α ≃ₜ β) (A : set α) :
(interior A).nonempty ↔ (interior (φ '' A)).nonempty :=
begin
  rw [←φ.image_interior, set.nonempty_image_iff],
end

lemma homeomorph.interior_nonempty_iff_preimage {α β : Type}
  [topological_space α] [topological_space β] (φ : α ≃ₜ β) (A : set β) :
(interior A).nonempty ↔ (interior (φ ⁻¹' A)).nonempty :=
begin
  rw [←φ.image_symm, φ.interior_nonempty_iff_image, ←set.image_comp, φ.self_comp_symm,
    set.image_id],
end

-- BEGIN intrinsic_interior.lean

/-- The intrinsic interior of a set is its interior considered as a set in its affine span. -/
def intrinsic_interior (R : Type) {V P : Type} [ring R] [seminormed_add_comm_group V] [module R V]
  [pseudo_metric_space P] [normed_add_torsor V P] -- have to redeclare variables to ensure that
                                                  -- all typeclasses are used
  (A : set P) := (coe : affine_span R A → P) '' interior ((coe : affine_span R A → P) ⁻¹' A)

/-- The intrinsic frontier of a set is its frontier considered as a set in its affine span. -/
def intrinsic_frontier (R : Type) {V P : Type} [ring R] [seminormed_add_comm_group V] [module R V]
  [pseudo_metric_space P] [normed_add_torsor V P] (A : set P) :=
(coe : affine_span R A → P) '' frontier ((coe : affine_span R A → P) ⁻¹' A)

/-- The intrinsic closure of a set is its closure considered as a set in its affine span. -/
def intrinsic_closure (R : Type) {V P : Type} [ring R] [seminormed_add_comm_group V] [module R V]
  [pseudo_metric_space P] [normed_add_torsor V P] (A : set P) :=
(coe : affine_span R A → P) '' closure ((coe : affine_span R A → P) ⁻¹' A)

lemma intrinsic_interior_def (R : Type) {V P : Type} [ring R] [seminormed_add_comm_group V]
  [module R V] [pseudo_metric_space P] [normed_add_torsor V P] (A : set P) :
intrinsic_interior R A =
  (coe : affine_span R A → P) '' interior ((coe : affine_span R A → P) ⁻¹' A) := rfl

lemma intrinsic_frontier_def (R : Type) {V P : Type} [ring R] [seminormed_add_comm_group V]
  [module R V] [pseudo_metric_space P] [normed_add_torsor V P] (A : set P) :
intrinsic_frontier R A =
  (coe : affine_span R A → P) '' frontier ((coe : affine_span R A → P) ⁻¹' A) := rfl

lemma intrinsic_closure_def (R : Type) {V P : Type} [ring R] [seminormed_add_comm_group V]
  [module R V] [pseudo_metric_space P] [normed_add_torsor V P] (A : set P) :
intrinsic_closure R A =
  (coe : affine_span R A → P) '' closure ((coe : affine_span R A → P) ⁻¹' A) := rfl

lemma intrinsic_interior_subset {R : Type} {V P : Type} [ring R] [seminormed_add_comm_group V]
  [module R V] [pseudo_metric_space P] [normed_add_torsor V P] (A : set P) :
intrinsic_interior R A ⊆ A :=
set.image_subset_iff.mpr interior_subset

lemma intrinsic_frontier_subset {R : Type} {V P : Type} [ring R] [seminormed_add_comm_group V]
  [module R V] [pseudo_metric_space P] [normed_add_torsor V P] {A : set P} (hA : is_closed A) :
intrinsic_frontier R A ⊆ A :=
set.image_subset_iff.mpr (hA.preimage continuous_induced_dom).frontier_subset

@[simp]
lemma intrinsic_interior_empty {R : Type} {V P : Type} [ring R] [seminormed_add_comm_group V]
  [module R V] [pseudo_metric_space P] [normed_add_torsor V P] :
intrinsic_interior R (∅ : set P) = ∅ :=
set.subset_empty_iff.mp $ intrinsic_interior_subset _

@[simp]
lemma intrinsic_frontier_empty {R : Type} {V P : Type} [ring R] [seminormed_add_comm_group V]
  [module R V] [pseudo_metric_space P] [normed_add_torsor V P] :
intrinsic_frontier R (∅ : set P) = ∅ :=
set.subset_empty_iff.mp $ intrinsic_frontier_subset is_closed_empty

lemma preimage_singleton_eq_univ {R : Type} {V P : Type} [ring R]
  [seminormed_add_comm_group V] [module R V] [pseudo_metric_space P] [normed_add_torsor V P]
  (x : P) : (coe : affine_span R ({x} : set P) → P) ⁻¹' {x} = set.univ :=
begin
  refine subset_antisymm (set.subset_univ _) _,
  rintro ⟨y, hy⟩ -,
  obtain rfl := (affine_subspace.mem_affine_span_singleton _ _ _ _).mp hy,
  exact subtype.coe_mk _ _,
end

@[simp] lemma intrinsic_interior_singleton {R : Type} {V P : Type} [ring R]
  [seminormed_add_comm_group V] [module R V] [pseudo_metric_space P] [normed_add_torsor V P]
  (x : P) : intrinsic_interior R ({x} : set P) = {x} :=
begin
  rw [intrinsic_interior_def, interior_eq_iff_open.mpr], swap,
  { convert is_open_univ,
    exact preimage_singleton_eq_univ x },
  { rw [set.eq_singleton_iff_unique_mem],
    refine ⟨⟨⟨x, _⟩, subtype.coe_mk _ _, subtype.coe_mk _ _⟩, _⟩,
    { exact (affine_subspace.mem_affine_span_singleton _ _ _ _).mpr rfl },
    { rintro - ⟨⟨y, hy₁⟩, hy₂, rfl⟩,
      simpa only [set.mem_preimage, subtype.coe_mk, set.mem_singleton_iff] using hy₂ } },
end

@[simp] lemma intrinsic_frontier_singleton  {R : Type} {V P : Type} [ring R]
  [seminormed_add_comm_group V] [module R V] [pseudo_metric_space P] [normed_add_torsor V P]
  (x : P) : intrinsic_frontier R ({x} : set P) = ∅ :=
begin
  rw [intrinsic_frontier_def, set.image_eq_empty],
  convert frontier_univ,
  exact preimage_singleton_eq_univ x,
end

@[simp] lemma intrinsic_closure_diff_intrinsic_interior {R : Type} {V P : Type} [ring R]
  [seminormed_add_comm_group V] [module R V] [pseudo_metric_space P] [normed_add_torsor V P]
  (A : set P) :
intrinsic_closure R A \ intrinsic_interior R A = intrinsic_frontier R A :=
begin
  rw [intrinsic_frontier_def, intrinsic_closure_def, intrinsic_interior_def,
    ←set.image_diff subtype.coe_injective],
  refl,
end

/--
The image of the intrinsic interior under an affine isometry is
the relative interior of the image.
-/
@[simp] -- not sure whether this is the correct direction for simp
lemma affine_isometry.image_intrinsic_interior {𝕜 V V₂ P P₂: Type}
  [normed_field 𝕜] [seminormed_add_comm_group V] [seminormed_add_comm_group V₂] [normed_space 𝕜 V]
  [normed_space 𝕜 V₂] [metric_space P] [pseudo_metric_space P₂] [normed_add_torsor V P]
  [normed_add_torsor V₂ P₂]
  (φ : P →ᵃⁱ[𝕜] P₂) (A : set P) :
intrinsic_interior 𝕜 (φ '' A) = φ '' intrinsic_interior 𝕜 A :=
begin
  rcases A.eq_empty_or_nonempty with rfl | hc,
  { simp only [intrinsic_interior_empty, set.image_empty] },
  haveI : nonempty A := hc.to_subtype,
  let f := φ.restrict_to_equiv (affine_span 𝕜 A),
  let f' := f.to_homeomorph,
  have : φ.to_affine_map ∘ (coe : affine_span 𝕜 A → P) ∘ f'.symm =
    (coe : (affine_span 𝕜 A).map φ.to_affine_map → P₂),
  { funext x,
    exact affine_isometry.restrict_to_equiv.apply_symm_apply _ },
  simp only [intrinsic_interior_def, ←φ.coe_to_affine_map],
  rw [intrinsic_interior_def],
  rw [←affine_subspace.map_span φ.to_affine_map A, ←this,
    ←function.comp.assoc, set.image_comp _ f'.symm,
    set.image_comp _ (coe : affine_span 𝕜 A → P), f'.symm.image_interior, f'.image_symm,
    ←set.preimage_comp, function.comp.assoc, f'.symm_comp_self, affine_isometry.coe_to_affine_map,
    function.comp.right_id, @set.preimage_comp _ P, φ.injective.preimage_image],
end

@[simp] lemma intrinsic_closure_eq_closure (𝕜 : Type)
  [nontrivially_normed_field 𝕜] [complete_space 𝕜]
  {V P : Type} [normed_add_comm_group V] [normed_space 𝕜 V]
  [metric_space P] [normed_add_torsor V P]
  (A : set P) [finite_dimensional 𝕜 V] :
intrinsic_closure 𝕜 A = closure A :=
begin
  simp only [intrinsic_closure_def],
  ext x,
  simp only [mem_closure_iff, set.mem_image],
  split,
  { rintro ⟨x, h, rfl⟩ o ho hxo,
    obtain ⟨z, hz₁, hz₂⟩ := h ((coe : affine_span 𝕜 A → P) ⁻¹' o)
                   (continuous_induced_dom.is_open_preimage o ho) hxo,
    exact ⟨z, hz₁, hz₂⟩ },
  { intro h,
    refine ⟨⟨x, _⟩, _⟩,
    { by_contradiction hc,
      obtain ⟨z, hz₁, hz₂⟩ := h
        (affine_span 𝕜 A)ᶜ
        (affine_subspace.closed_of_finite_dimensional (affine_span 𝕜 A)).is_open_compl
        hc,
      exact hz₁ (subset_affine_span 𝕜 A hz₂) },
    refine ⟨_, subtype.coe_mk _ _⟩,
    intros o ho hxo,
    have ho' := ho,
    rw [is_open_induced_iff] at ho,
    obtain ⟨o, ho, rfl⟩ := ho,
    rw [set.mem_preimage, subtype.coe_mk] at hxo,
    obtain ⟨w, hwo, hwA⟩ := h _ ho hxo,
    have : w ∈ affine_span 𝕜 A := subset_affine_span 𝕜 A hwA,
    refine ⟨⟨w, subset_affine_span 𝕜 A hwA⟩, hwo, hwA⟩ },
end

@[simp] lemma closure_diff_intrinsic_interior {𝕜 : Type}
  [nontrivially_normed_field 𝕜] [complete_space 𝕜]
  {V P : Type} [normed_add_comm_group V] [normed_space 𝕜 V] [finite_dimensional 𝕜 V]
  [metric_space P] [normed_add_torsor V P]
  (A : set P) :
closure A \ intrinsic_interior 𝕜 A = intrinsic_frontier 𝕜 A :=
(intrinsic_closure_eq_closure 𝕜 A) ▸ intrinsic_closure_diff_intrinsic_interior A

@[simp] lemma intrinsic_interior_vadd {𝕜 V P : Type}
  [normed_field 𝕜] [seminormed_add_comm_group V] [normed_space 𝕜 V]
  [metric_space P] [normed_add_torsor V P] (x : V) (A : set P) :
intrinsic_interior 𝕜 (x +ᵥ A) = x +ᵥ intrinsic_interior 𝕜 A :=
(normed_add_torsor.vadd_affine_isometry 𝕜 P x).image_intrinsic_interior A

lemma nonempty_intrinsic_interior_of_nonempty_of_convex
  {V : Type} [normed_add_comm_group V] [normed_space ℝ V] [finite_dimensional ℝ V]
  {A : set V} (Ane : A.nonempty) (Acv : convex ℝ A) :
(intrinsic_interior ℝ A).nonempty :=
begin
  haveI : nonempty A := set.nonempty_coe_sort.mpr Ane,
  rw [intrinsic_interior_def, set.nonempty_image_iff],
  obtain ⟨p, hp⟩ := Ane,
  let p' : affine_span ℝ A := ⟨p, subset_affine_span _ _ hp⟩,
  rw [(affine_isometry_equiv.const_vsub ℝ p').symm.to_homeomorph.interior_nonempty_iff_preimage,
    convex.interior_nonempty_iff_affine_span_eq_top],
  { rw [affine_isometry_equiv.coe_to_homeomorph,
      ←affine_isometry_equiv.comap_span (affine_isometry_equiv.const_vsub ℝ p').symm,
      affine_span_affine_span_coe_preimage ℝ A],
    exact affine_subspace.comap_top },
  { exact convex.affine_preimage ((affine_span ℝ A).inclusion_affine.comp
    (affine_isometry_equiv.const_vsub ℝ p').symm.to_affine_equiv.to_affine_map) Acv },
end
