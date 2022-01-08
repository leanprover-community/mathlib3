import algebraic_geometry.Gamma_Spec_adjunction
import algebraic_geometry.open_immersion

noncomputable theory

open topological_space
open category_theory
open Top
open opposite

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

instance (R : CommRingᵒᵖ) : is_affine (Scheme.Spec.obj R) :=
(mem_AffineScheme _).mp (Scheme.Spec.obj_mem_ess_image R)

lemma is_affine_of_iso {X Y : Scheme} (f : X ⟶ Y) [is_iso f] [h : is_affine Y] :
  is_affine X :=
by { rw [← mem_AffineScheme] at h ⊢, exact functor.ess_image.of_iso (as_iso f).symm h }

namespace AffineScheme

@[derive [full, faithful, ess_surj], simps]
def Spec : CommRingᵒᵖ ⥤ AffineScheme := Scheme.Spec.to_ess_image

@[derive [full, faithful], simps]
def forget_to_Scheme : AffineScheme ⥤ Scheme := Scheme.Spec.ess_image_inclusion

def Γ : AffineSchemeᵒᵖ ⥤ CommRing := to_Scheme.op ⋙ Scheme.Γ

def equiv_CommRing : AffineScheme ≌ CommRingᵒᵖ :=
{ functor := Γ.right_op,
  inverse := Spec,
  unit_iso := by { have := Spec_Γ_identity.symm, } }

end AffineScheme


def Spec_to_scheme : Spec ⋙ to_Scheme ≅ Scheme.Spec
  := Scheme.Spec.to_ess_image_comp_essential_image_inclusion

instance : faithful Spec := faithful.of_comp_iso Spec_to_scheme

instance : full Spec := by {
  haveI inst : full (Spec ⋙ to_Scheme) := full.of_iso Spec_to_scheme.symm,
  exactI @full.of_comp_faithful _ _ _ _ _ _ Spec to_Scheme inst _
}

instance : is_equivalence Spec := equivalence.of_fully_faithfully_ess_surj Spec

-- Though `as_equivalence Spec` also works, might as well have the inverse map defeq to `Γ`
local attribute[irreducible] Scheme.Spec Scheme.Γ
def equiv_CommRing : AffineScheme ≌ CommRingᵒᵖ
  := (mk_from_left_inv Spec Γ.right_op (nat_iso.op Spec.Spec_Γ_identity.symm)).symm

lemma equiv_CommRing_inverse : equiv_CommRing.inverse = Spec := rfl
lemma equiv_CommRing_functor : equiv_CommRing.functor = Γ.right_op := rfl

-- set_option trace.class_instances true
-- set_option pp.implicit true
set_option pp.universes true


instance Γ_is_equiv : is_equivalence Γ.{u} := by {
  haveI inst : is_equivalence Γ.{u}.right_op := is_equivalence.of_equivalence equiv_CommRing,
    change is_equivalence (Γ.right_op.op ⋙ (op_op _)),
    apply_instance
}

instance : has_colimits AffineScheme.{u} := by {
  haveI := adjunction.has_limits_of_equivalence Γ.{u},
  haveI : has_colimits AffineScheme.{u} ᵒᵖᵒᵖ := limits.has_colimits_op_of_has_limits,
  exactI adjunction.has_colimits_of_equivalence (unop_unop AffineScheme.{u})
}

instance : has_limits AffineScheme.{u} := by {
  haveI := adjunction.has_colimits_of_equivalence Γ.{u},
  haveI : has_limits AffineScheme.{u} ᵒᵖᵒᵖ := limits.has_limits_op_of_has_colimits,
  exactI adjunction.has_limits_of_equivalence (unop_unop AffineScheme.{u})
}


end AffineScheme

end algebraic_geometry
