/- Will be moved under structure_sheaf.lean ; not yet documentated -/
import algebraic_geometry.locally_ringed_space
import algebra.category.CommRing
import algebraic_geometry.Spec

universe u

noncomputable theory
open category_theory
open opposite
open algebraic_geometry.LocallyRingedSpace
open topological_space

namespace algebraic_geometry

namespace Spec

/- probably should be moved to CommRing.lean? -/
def to_localization (R : Type _) [comm_ring R] (f : R) : (CommRing.of R) ⟶ CommRing.of (localization.away (f : R))
  := (algebra_map (R : Type _) (localization.away f) : CommRing.of _ ⟶ CommRing.of _)

instance localize_at_unit (R : CommRing) : is_iso (to_localization R 1) := sorry

lemma to_Spec_Γ_factor (R : CommRing) :
  structure_sheaf.to_open R ⊤ = (to_localization R 1 ≫ (structure_sheaf.to_basic_open R 1)) ≫
    (structure_sheaf R).presheaf.map (eq_to_hom (by simp)).op := by {
  change structure_sheaf.to_open R ⊤ = (structure_sheaf.to_basic_open R 1).comp (to_localization R 1) ≫ _,
  erw structure_sheaf.localization_to_basic_open R 1,
  erw structure_sheaf.to_open_res,
}

/- I couldn't find this anywhere; it is needed for `iso_Spec_Γ`. -/
instance op_iso {C : Type _} [category C] {X Y : C} (f : X ⟶ Y) [f_iso : is_iso f] : is_iso f.op
  := { out := exists.elim f_iso.out (λ g ⟨fg, gf⟩,
    exists.intro g.op ⟨congr_arg quiver.hom.op gf, congr_arg quiver.hom.op fg⟩) }

lemma op_inv {C : Type _} [category C] {X Y : C} (f : X ⟶ Y) [f_iso : is_iso f] :
  (inv f).op = inv f.op := by ext; rw [← op_comp, is_iso.inv_hom_id, op_id]

@[instance]
lemma iso_to_global (R : CommRing) : is_iso (structure_sheaf.to_open R ⊤ : R ⟶ _)
  := by erw (to_Spec_Γ_factor R); apply_instance

def global_iso (R : CommRing) : R ≅ (structure_sheaf R).presheaf.obj (op ⊤)
  := by convert @as_iso _ _ _ _ _ (iso_to_global R); cases R; refl

/- The remaing stuff will probably go into Spec.lean -/

/- Lean complains with CommRing.of R.α not equal to R without this type annotation -/
def to_Spec_Γ (R : CommRing) : R ⟶ Γ.obj (op (Spec.to_LocallyRingedSpace.obj (op R)))
  := structure_sheaf.to_open R ⊤

instance is_iso_Spec_Γ (R : CommRing) : is_iso (to_Spec_Γ R)
  := by convert iso_to_global R; cases R; refl

def iso_Spec_Γ (R : CommRing) : R ≅ Γ.obj (op (Spec.to_LocallyRingedSpace.obj (op R)))
  := global_iso R

lemma Spec_Γ_naturality {R S : CommRing} (f : R ⟶ S)
  : f ≫ to_Spec_Γ S = to_Spec_Γ R ≫ Γ.map (Spec.to_LocallyRingedSpace.map f.op).op
:= by ext x p; symmetry; apply localization.local_ring_hom_to_map


/- without this, `Spec_Γ_identity` takes forever. (It still takes forever though.) -/
local attribute[irreducible] Spec.to_LocallyRingedSpace Γ

def Spec_Γ_identity : Spec.to_LocallyRingedSpace.right_op ⋙ Γ ≅ 𝟭 _ := by {
  symmetry,
  apply nat_iso.of_components,
  swap, intro R,
    convert global_iso R; cases R; dsimp; refl,
  intros R S f,
  convert Spec_Γ_naturality f; cases R; cases S; dsimp; refl
}

end Spec
end algebraic_geometry
