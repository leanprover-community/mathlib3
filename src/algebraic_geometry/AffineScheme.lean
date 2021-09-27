import algebraic_geometry.Scheme
import category_theory.essential_image
import category_theory.adjunction.limits
import category_theory.limits.opposites
import ring_theory.tensor_product
import algebraic_geometry.Spec_fully_faithful

noncomputable theory

open topological_space
open category_theory
open Top
open opposite

universes v₁ v₂ v₃ u₁ u₂ u₃ u
variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]
variables {E : Type u₃} [category.{v₃} E]
variables (F : C ⥤ D) (G : D ⥤ E) (F' : D ⥤ C)

lemma full.of_comp_faithful [full $ F ⋙ G] [faithful G] : full F := {
  preimage := λ X Y f, (F ⋙ G).preimage (G.map f),
  witness' := λ X Y f, G.map_injective ((F ⋙ G).image_preimage _)
}

def mk_from_left_inv [e : is_equivalence F] (H : F ⋙ F' ≅ 𝟭 _) : C ≌ D
  := equivalence.mk F F' H.symm (by {
    have iso0 := nat_iso.hcomp (iso.refl F.inv) (nat_iso.hcomp H (iso.refl F)),
    have iso1 := nat_iso.hcomp e.counit_iso.symm (iso.refl (F' ⋙ F)),
    calc F' ⋙ F ≅ F.inv ⋙ F ⋙ F' ⋙ F : iso1
             ... ≅ F.inv ⋙ F           : iso0
             ... ≅ 𝟭 _                  : e.counit_iso
  })

instance : is_equivalence (op_op C) := is_equivalence.of_equivalence (op_op_equivalence _)
instance : is_equivalence (unop_unop C) :=
is_equivalence.of_equivalence_inverse (op_op_equivalence _)

instance is_equivalence.op [e : is_equivalence F] : is_equivalence F.op
  := is_equivalence.mk F.inv.op (nat_iso.op e.unit_iso.symm) (nat_iso.op e.counit_iso.symm)

namespace algebraic_geometry

def AffineScheme := Scheme.Spec.ess_image

namespace AffineScheme
open category_theory.limits

@[derive [ess_surj], simps]
def Spec : CommRingᵒᵖ ⥤ AffineScheme := Scheme.Spec.to_ess_image

@[derive [full, faithful], simps]
def to_Scheme : AffineScheme ⥤ Scheme := Scheme.Spec.ess_image_inclusion

def Γ : AffineSchemeᵒᵖ ⥤ CommRing := to_Scheme.op ⋙ Scheme.Γ

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
