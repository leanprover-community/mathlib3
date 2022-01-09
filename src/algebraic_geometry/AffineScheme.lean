/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebraic_geometry.Gamma_Spec_adjunction
import algebraic_geometry.open_immersion
import category_theory.limits.opposites

/-!
# Affine schemes

We define the category of `AffineScheme`s as the essential image of `Spec`.
We also define predicates about affine schemes and affine open sets.

## Main definitions

* `algebraic_geometry.AffineScheme`: The category of affine schemes.
* `algebraic_geometry.is_affine`: A scheme is affine if the canonical map `X ⟶ Spec Γ(X)` is an
  isomorphism.
* `algebraic_geometry.Scheme.iso_Spec`: The canonical isomorphism `X ≅ Spec Γ(X)` for an affine
  scheme.
* `algebraic_geometry.AffineScheme.equiv_CommRing`: The equivalence of categories
  `AffineScheme ≌ CommRingᵒᵖ` given by `AffineScheme.Spec : CommRingᵒᵖ ⥤ AffineScheme` and
  `AffineScheme.Γ : AffineSchemeᵒᵖ ⥤ CommRing`.
* `algebraic_geometry.is_affine_open`: An open subset of a scheme is affine if the open subscheme is
  affine.

-/

noncomputable theory

open category_theory category_theory.limits opposite topological_space

universe u

namespace algebraic_geometry

/-- The category of affine schemes -/
def AffineScheme := Scheme.Spec.ess_image

/-- A Scheme is affine if the canonical map `X ⟶ Spec Γ(X)` is an isomorphism. -/
class is_affine (X : Scheme) : Prop :=
(affine : is_iso (Γ_Spec.adjunction.unit.app X))

attribute [instance] is_affine.affine

/-- The canonical isomorphism `X ≅ Spec Γ(X)` for an affine scheme. -/
def Scheme.iso_Spec (X : Scheme) [is_affine X] :
  X ≅ Scheme.Spec.obj (op $ Scheme.Γ.obj $ op X) :=
as_iso (Γ_Spec.adjunction.unit.app X)

lemma mem_AffineScheme (X : Scheme) : X ∈ AffineScheme ↔ is_affine X :=
⟨λ h, ⟨functor.ess_image.unit_is_iso h⟩, λ h, @@mem_ess_image_of_unit_is_iso _ _ _ X h.1⟩

instance is_affine_AffineScheme (X : AffineScheme.{u}) : is_affine (X : Scheme.{u}) :=
(mem_AffineScheme _).mp X.prop

instance Spec_is_affine (R : CommRingᵒᵖ) : is_affine (Scheme.Spec.obj R) :=
(mem_AffineScheme _).mp (Scheme.Spec.obj_mem_ess_image R)

lemma is_affine_of_iso {X Y : Scheme} (f : X ⟶ Y) [is_iso f] [h : is_affine Y] :
  is_affine X :=
by { rw [← mem_AffineScheme] at h ⊢, exact functor.ess_image.of_iso (as_iso f).symm h }

namespace AffineScheme

/-- The `Spec` functor into the category of affine schemes. -/
@[derive [full, faithful, ess_surj], simps]
def Spec : CommRingᵒᵖ ⥤ AffineScheme := Scheme.Spec.to_ess_image

/-- The forgetful functor `AffineScheme ⥤ Scheme`. -/
@[derive [full, faithful], simps]
def forget_to_Scheme : AffineScheme ⥤ Scheme := Scheme.Spec.ess_image_inclusion

/-- The global section functor of an affine scheme. -/
def Γ : AffineSchemeᵒᵖ ⥤ CommRing := forget_to_Scheme.op ⋙ Scheme.Γ

/-- The category of affine schemes is equivalent to the category of commutative rings. -/
def equiv_CommRing : AffineScheme ≌ CommRingᵒᵖ :=
equiv_ess_image_of_reflective.symm

instance Γ_is_equiv : is_equivalence Γ.{u} :=
begin
  haveI : is_equivalence Γ.{u}.right_op.op := is_equivalence.of_equivalence equiv_CommRing.op,
  exact (functor.is_equivalence_trans Γ.{u}.right_op.op (op_op_equivalence _).functor : _),
end

instance : has_colimits AffineScheme.{u} :=
begin
  haveI := adjunction.has_limits_of_equivalence.{u} Γ.{u},
  haveI : has_colimits AffineScheme.{u} ᵒᵖᵒᵖ := has_colimits_op_of_has_limits,
  exactI adjunction.has_colimits_of_equivalence.{u} (op_op_equivalence AffineScheme.{u}).inverse
end

instance : has_limits AffineScheme.{u} :=
begin
  haveI := adjunction.has_colimits_of_equivalence Γ.{u},
  haveI : has_limits AffineScheme.{u} ᵒᵖᵒᵖ := limits.has_limits_op_of_has_colimits,
  exactI adjunction.has_limits_of_equivalence (op_op_equivalence AffineScheme.{u}).inverse
end

end AffineScheme

/-- An open subset of a scheme is affine if the open subscheme is affine. -/
def is_affine_open {X : Scheme} (U : opens X.carrier) : Prop :=
is_affine (X.restrict U.open_embedding)

lemma range_is_affine_open_of_open_immersion {X Y : Scheme} [is_affine X] (f : X ⟶ Y)
  [H : is_open_immersion f] : is_affine_open ⟨set.range f.1.base, H.base_open.open_range⟩ :=
begin
  refine is_affine_of_iso (is_open_immersion.iso_of_range_eq f (Y.of_restrict _) _).inv,
  exact subtype.range_coe.symm,
  apply_instance
end

lemma top_is_affine_open (X : Scheme) [is_affine X] : is_affine_open (⊤ : opens X.carrier) :=
begin
  convert range_is_affine_open_of_open_immersion (𝟙 X),
  ext1,
  exact set.range_id.symm
end

instance Scheme.affine_basis_cover_is_affine (X : Scheme) (i : X.affine_basis_cover.J) :
  is_affine (X.affine_basis_cover.obj i) :=
algebraic_geometry.Spec_is_affine _

lemma is_basis_affine_open (X : Scheme) :
  opens.is_basis { U : opens X.carrier | is_affine_open U } :=
begin
  rw opens.is_basis_iff_nbhd,
  rintros U x (hU : x ∈ (U : set X.carrier)),
  obtain ⟨S, hS, hxS, hSU⟩ := X.affine_basis_cover_is_basis.exists_subset_of_mem_open hU U.prop,
  refine ⟨⟨S, X.affine_basis_cover_is_basis.is_open hS⟩, _, hxS, hSU⟩,
  rcases hS with ⟨i, rfl⟩,
  exact range_is_affine_open_of_open_immersion _,
end

end algebraic_geometry
