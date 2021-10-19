/-
Copyright (c) 2021 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import algebraic_geometry.Spec
import algebraic_geometry.ringed_space
import topology.sheaves.sheaf_condition.basis_le

/-!
# Adjunction between `Γ` and `Spec`

-/

noncomputable theory
universe variables u v

namespace algebraic_geometry
open opposite
open category_theory
open structure_sheaf
open prime_spectrum
open topological_space
open algebraic_geometry.LocallyRingedSpace
open Top.presheaf.sheaf_condition

def local_ring.closed_point (R : Type u) [comm_ring R] [local_ring R] :
  prime_spectrum R :=
⟨local_ring.maximal_ideal R, (local_ring.maximal_ideal.is_maximal R).is_prime⟩
-- move to local_ring
-- to do : maximal ideals are closed points in the prime spectrum of any ring
-- minimal primes are generic points of irreducible components

abbreviation Spec' (R : CommRing) := Spec.to_LocallyRingedSpace.obj (op R)

variable (R : CommRing)

/- basic opens on Spec R -/
def basic_open_B : @Top.opens_index_struct (Spec' R).to_Top := ⟨R, λ r, basic_open r⟩
-- lesson: better directly work with the indexing function than the range set!

private def idfo := induced_functor (op ∘ (basic_open_B R).f)

lemma basic_opens_is_basis : Top.is_basis_range (basic_open_B R) :=
begin
  unfold Top.is_basis_range opens.is_basis basic_open_B,
  convert is_topological_basis_basic_opens,
  rw ← set.range_comp, dsimp, congr,
end

lemma to_basic_open_epi (r : R) : epi (to_open R (basic_open r)) :=
⟨λ S f g h, by { change f.comp _ = g.comp _ at h,
  rw [←localization_to_basic_open, ←ring_hom.comp_assoc, ←ring_hom.comp_assoc] at h,
  apply (is_iso.epi_of_iso (show CommRing.of _ ⟶ _, from to_basic_open R r)).1,
  apply is_localization.ring_hom_ext _ h,
  swap, exact localization.is_localization }⟩


namespace LocallyRingedSpace
variable (X : LocallyRingedSpace)
abbreviation Γ' := Γ.obj (op X)

/- map from the global sections to a stalk -/
def Γ_to_stalk (x : X) : Γ' X ⟶ X.presheaf.stalk x :=
  X.presheaf.germ (⟨x,trivial⟩ : (⊤ : opens X))
  -- or @Top.presheaf.germ _ _ _ _ _ ⊤ ⟨x,trivial⟩

/- counit on the underlying set -/
def to_Γ_Spec_fun : X → Spec' (Γ' X) :=
λ x, comap (X.Γ_to_stalk x) (@local_ring.closed_point _ _ (X.local_ring x))

lemma mem_ideal_Γ_to_stalk_iff (r : Γ' X) (x : X) :
  r ∉ (X.to_Γ_Spec_fun x).as_ideal ↔ is_unit (X.Γ_to_stalk x r) :=
begin
  unfold to_Γ_Spec_fun,
  rw [comap_as_ideal, ideal.mem_comap],
  unfold local_ring.closed_point, rw local_ring.mem_maximal_ideal,
  unfold nonunits, rw [set.mem_set_of_eq, not_not],
end

/- preimage of a basic open under the counit is a basic open -/
lemma to_Γ_Spec_preim_basic_open_eq (r : Γ' X) :
  X.to_Γ_Spec_fun⁻¹' (basic_open r).1
  = (X.to_RingedSpace.basic_open r).1 :=
begin
  ext, dsimp,
  rw [set.mem_preimage, opens.mem_coe,
      mem_basic_open, X.to_RingedSpace.mem_basic_open],
  apply mem_ideal_Γ_to_stalk_iff,
end

/- counit is continuous -/
lemma to_Γ_Spec_continuous : continuous X.to_Γ_Spec_fun :=
begin
  apply is_topological_basis_basic_opens.continuous,
  rintro U ⟨r,rfl⟩, convert (X.to_RingedSpace.basic_open r).2,
  exact X.to_Γ_Spec_preim_basic_open_eq r,
end

def to_Γ_Spec_Top : continuous_map X (Spec' (Γ' X)) :=
  ⟨X.to_Γ_Spec_fun, X.to_Γ_Spec_continuous⟩

lemma to_Γ_Spec_opens_map_obj_basic_open_eq (r : Γ' X) :
  (opens.map X.to_Γ_Spec_Top).obj (basic_open r) = X.to_RingedSpace.basic_open r
  := subtype.eq (X.to_Γ_Spec_preim_basic_open_eq r)

def to_opens_map_basic_open (r : Γ' X) :=
  X.presheaf.map ((opens.map X.to_Γ_Spec_Top).obj (basic_open r)).le_top.op

def is_unit_res_opens_map_basic_open (r : Γ' X) :=
  by { have h := X.to_RingedSpace.is_unit_res_basic_open r,
  rw ← to_Γ_Spec_opens_map_obj_basic_open_eq at h, exact h }

def to_Γ_Spec_sheaf_app (r : Γ' X) := by {
  let l := is_localization.away.lift r (X.is_unit_res_opens_map_basic_open r),
  swap 5, exact localization.is_localization,
  exact (basic_open_iso _ r).hom ≫ l }

/- characterization of the sheaf morphism on basic opens,
   direction → used in proving naturality of the morphism,
   direction ← ... -/
lemma to_Γ_Spec_sheaf_app_prop (r : Γ' X) :
  ∀ f, to_open _ (basic_open r) ≫ f = X.to_opens_map_basic_open r
  ↔ f = X.to_Γ_Spec_sheaf_app r :=
λ f, begin
  unfold to_Γ_Spec_sheaf_app, rw ← iso.inv_comp_eq,
  rw ← (is_localization.away.away_map.lift_comp r
    (X.is_unit_res_opens_map_basic_open r) : _ = X.to_opens_map_basic_open r),
  swap 5, exact localization.is_localization,
  rw ← localization_to_basic_open _ r,
  change f.comp _ = _ ↔ _, rw ← ring_hom.comp_assoc,
  split, { intro h, apply is_localization.ring_hom_ext _ h,
  swap, exact localization.is_localization },
  { intro h, rw ← h, refl },
end

def to_Γ_Spec_sheaf_basic_opens : idfo _ ⋙ (Spec' (Γ' X)).presheaf
                               ⟶ idfo _ ⋙ X.to_Γ_Spec_Top _* X.presheaf :=
{ app := X.to_Γ_Spec_sheaf_app,
  naturality' := λ r s f, by {
    apply (to_basic_open_epi _ r).1,
    simp only [←category.assoc],
    rw (X.to_Γ_Spec_sheaf_app_prop r _).2 rfl,
    convert (X.to_Γ_Spec_sheaf_app_prop s _).2 rfl,
    apply eq.symm, apply X.presheaf.map_comp } }


end LocallyRingedSpace

end algebraic_geometry
