/- might want to move this into Spec.lean or somewhere else ; not yet documentated -/
import algebraic_geometry.locally_ringed_space
import algebra.category.CommRing
import algebraic_geometry.Spec

universe u

noncomputable theory
open category_theory
open opposite
open algebraic_geometry.LocallyRingedSpace

namespace algebraic_geometry

namespace Spec

/- probably should be moved to CommRing.lean? -/
def to_localization (R : CommRing) (f : R) : R ⟶ CommRing.of (localization.away (f : R))
  := (algebra_map (R : Type _) (localization.away f) : CommRing.of _ ⟶ CommRing.of _)

instance localize_at_unit (R : CommRing) : is_iso (to_localization R 1) := sorry


def to_Spec_Γ (R : CommRing) : R ⟶ Γ.obj (op (Spec.to_LocallyRingedSpace.obj (op R)))
  := structure_sheaf.to_open R ⊤

lemma to_Spec_Γ_factor (R : CommRing) :
  to_Spec_Γ R = (to_localization R 1 ≫ (structure_sheaf.to_basic_open R 1)) ≫
    (structure_sheaf R).presheaf.map (eq_to_hom (by simp)).op := by {
  change to_Spec_Γ R = (structure_sheaf.to_basic_open R 1).comp (to_localization R 1) ≫ _,
  erw structure_sheaf.localization_to_basic_open R 1,
  erw structure_sheaf.to_open_res,
  refl
}

/- I couldn't find this anywhere; it is needed for `iso_Spec_Γ`. -/
instance op_iso {C : Type _} [category C] {X Y : C} (f : X ⟶ Y) [f_iso : is_iso f] : is_iso f.op
  := { out := exists.elim f_iso.out (λ g ⟨fg, gf⟩,
    exists.intro g.op ⟨congr_arg quiver.hom.op gf, congr_arg quiver.hom.op fg⟩) }

instance iso_Spec_Γ (R : CommRing) : is_iso (to_Spec_Γ R)
  := by rw to_Spec_Γ_factor; apply_instance

lemma Spec_Γ_naturality {R S : CommRing} (f : R ⟶ S)
  : f ≫ to_Spec_Γ S = to_Spec_Γ R ≫ Γ.map (Spec.to_LocallyRingedSpace.map f.op).op
:= by ext x p; symmetry; apply localization.local_ring_hom_to_map

/- without this, `Spec_Γ_identity` takes forever. -/
local attribute[irreducible] Spec.to_LocallyRingedSpace Γ

lemma Spec_Γ_identity : Spec.to_LocallyRingedSpace.right_op ⋙ Γ ≅ 𝟭 _ := by {
  symmetry,
  let nat : 𝟭 _ ⟶ Spec.to_LocallyRingedSpace.right_op ⋙ Γ := {
      app :=  λ R, to_Spec_Γ R,
      naturality' := λ R S f, Spec_Γ_naturality f
    },
  haveI : is_iso nat := by apply nat_iso.is_iso_of_is_iso_app,
  exact as_iso nat
}

instance : faithful Spec.to_LocallyRingedSpace := by {
  haveI Spec_op_faithful := faithful.of_comp_iso Spec_Γ_identity,
  haveI Spec_faithful : faithful Spec.to_LocallyRingedSpace.right_op.left_op
    := @functor.left_op_faithful _ _ _ _ _ Spec_op_faithful,
  exactI @faithful.of_iso _ _ _ _ _ _ Spec_faithful (functor.right_op_left_op_iso Spec.to_LocallyRingedSpace),
}

instance : full Spec.to_LocallyRingedSpace := {
  preimage := λ R S f,
    (to_Spec_Γ (unop S) ≫ Γ.map f.op ≫ inv (to_Spec_Γ (unop R))).op,
  witness' := λ R S f, sorry
}

end Spec

end algebraic_geometry
