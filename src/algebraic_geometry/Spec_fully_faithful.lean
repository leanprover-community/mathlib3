/- might want to move this into Spec.lean or somewhere else ; not yet documentated -/
import algebraic_geometry.locally_ringed_space
import algebra.category.CommRing
import algebraic_geometry.Spec
import algebraic_geometry.morphism_into_affine

universe u

noncomputable theory
open category_theory
open opposite
open algebraic_geometry.LocallyRingedSpace
open topological_space

namespace algebraic_geometry

namespace Spec


instance : faithful Spec.to_LocallyRingedSpace := by {
  haveI Spec_op_faithful := faithful.of_comp_iso Spec_Γ_identity,
  haveI Spec_faithful : faithful Spec.to_LocallyRingedSpace.right_op.left_op
    := @functor.left_op_faithful _ _ _ _ _ Spec_op_faithful,
  exactI @faithful.of_iso _ _ _ _ _ _ Spec_faithful (functor.right_op_left_op_iso Spec.to_LocallyRingedSpace),
}

@[elementwise]
lemma Γ_to_stalk (R : CommRing) (x : Top_obj R)
  : inv (to_Spec_Γ R) ≫ structure_sheaf.to_stalk R x
   = (structure_sheaf R).presheaf.germ (⟨x, trivial⟩: (⊤ : opens (Top_obj R)))
  := by simpa using structure_sheaf.to_open_germ R ⊤

/- These helper lemmas might move to the corresponding files -/
instance stalk_to_fiber_is_iso (R : CommRing) (x : prime_spectrum.Top R) : is_iso (structure_sheaf.stalk_to_fiber_ring_hom R x)
  := by {
  change is_iso (structure_sheaf.stalk_iso R x).hom,
  apply_instance
}

lemma comap_iso {R S : CommRing} (f : R ⟶ S) [is_iso f] {p : prime_spectrum R} {q : prime_spectrum S}
  (H : p = prime_spectrum.comap f q) : q = prime_spectrum.comap (inv f) p
  := by {
    rw H,
    suffices : prime_spectrum.comap (inv f) ∘ prime_spectrum.comap f = id, {
        exact (congr_fun this q).symm,
      },
      rw ← prime_spectrum.comap_comp,
      change prime_spectrum.comap (inv f ≫ f) = id,
      rw is_iso.inv_hom_id,
      exact prime_spectrum.comap_id,
  }

lemma not_in_prime_iff_stalk_unit {R : CommRing} (p : prime_spectrum R) {x : R}
  : x ∉ p.as_ideal ↔ is_unit (structure_sheaf.to_stalk R p x)
  := by {
    change x ∈ p.as_ideal.prime_compl ↔ is_unit _,
    rw ← is_localization.at_prime.is_unit_to_map_iff (localization.at_prime p.as_ideal) p.as_ideal x,
    rw ← structure_sheaf.stalk_to_fiber_ring_hom_to_stalk,
    rw is_unit_map_iff,
  }


variables {R S : CommRing.{u}} (f : Spec.to_LocallyRingedSpace.obj (op R) ⟶ Spec.to_LocallyRingedSpace.obj (op S))

/- Should I make this definition private? -/
include f
def top_map_of : Top_obj R ⟶ Top_obj S := by {
  refine (eq_to_hom _) ≫ f.val.base ≫ (eq_to_hom _);
  dsimp only [to_LocallyRingedSpace, LocallyRingedSpace_obj, opposite.unop_op];
  refl
}

/- Show that the topological map of `f` indeed comes from the comap induced by `Γ.map(f.op)`. -/
lemma Γ_Spec_map_top :
  Spec.Top_map ((to_Spec_Γ S) ≫ Γ.map (f.op)) = Spec.Top_map (to_Spec_Γ R) ≫ (top_map_of f)
  := by {
    ext p x,
    rcases f with ⟨⟨f_top, f_sh⟩, f_prop⟩,
    let q := prime_spectrum.comap (to_Spec_Γ R) p,
    conv_lhs {
      change (structure_sheaf R).presheaf.map (𝟙 _) _ ∈ _,
      rw comap_iso (to_Spec_Γ R) (rfl : q = _),
    },
    simp only [category_theory.functor.map_id],

    /- Basically, we need to show that `f(q) = φ⁻¹ q`.
      It follows straight from the fact that `f` is a local homomorphism at the stalk of `q`.
      However, it is easier to check invertible-ness than to actually chase the image. -/
    rw ← not_iff_not,
    erw not_in_prime_iff_stalk_unit,
    erw not_in_prime_iff_stalk_unit,
    rw Γ_to_stalk_apply R q,
    erw ← PresheafedSpace.stalk_map_germ_apply ⟨f_top, f_sh⟩ ⊤,
    haveI := f_prop q,
    rw is_unit_map_iff,
    erw structure_sheaf.germ_to_open S _ _ x,
  }

/- Show that `f` coicides with `Γ.map (f.op)` after composing with the canonical isomorphisms. -/
lemma Γ_Spec_map:
  Spec.to_LocallyRingedSpace.map ((to_Spec_Γ S) ≫ Γ.map (f.op)).op
    = Spec.to_LocallyRingedSpace.map (to_Spec_Γ R).op ≫ f := by {
  apply hom_to_affine_eq_if_global_eq, exact Γ_Spec_map_top f,
  conv_rhs { rw [op_comp, Γ.map_comp] },
  rw ← is_iso.comp_inv_eq,
  simp only [← functor.map_inv, ← op_inv, ← functor.map_comp, ← op_comp],
  generalize H : (to_Spec_Γ S ≫ Γ.map f.op) ≫ inv (to_Spec_Γ R) = φ,
  have : Γ.map f.op = inv (to_Spec_Γ S) ≫ φ ≫ (to_Spec_Γ R) := by simp[← H],
  rw this,
  rw is_iso.eq_inv_comp,
  exact (Spec_Γ_naturality φ).symm,
}


local attribute[irreducible] Spec.to_LocallyRingedSpace Γ

instance : full Spec.to_LocallyRingedSpace := {
  preimage := λ R S f, (to_Spec_Γ (unop S) ≫ Γ.map f.op ≫ inv (to_Spec_Γ (unop R))).op,
  witness' := λ R S f, by {
    rw [← category.assoc, op_comp, op_inv, functor.map_comp, functor.map_inv],
    rw is_iso.inv_comp_eq,
    exact @Γ_Spec_map (unop R) (unop S) f,
  }
}

end Spec

end algebraic_geometry
