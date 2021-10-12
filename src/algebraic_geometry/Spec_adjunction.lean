/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
import algebraic_geometry.Scheme
import ring_theory.ideal.operations

/-!

# Adjunction between `Spec` and `Γ`

We construct the adjunction between `Spec.to_LocallyRingedSpace` and `LocallyRingedSpace.Γ`.

We do this by giving unit and counit and proving the triangle identities.

-/

noncomputable theory

open category_theory
open topological_space
open opposite
open prime_spectrum

namespace algebraic_geometry

namespace LocallyRingedSpace

variables (X : LocallyRingedSpace)

def to_prime_spectrum_fun : X → prime_spectrum (Γ.obj (op X)) := λ x,
⟨ideal.comap (X.presheaf.germ (⟨x, trivial⟩ : (⊤ : opens X)))
  (local_ring.maximal_ideal (X.stalk x)),
begin
  haveI : ideal.is_prime (local_ring.maximal_ideal (X.stalk x)), apply_instance,
  apply ideal.is_prime.comap,
end⟩

@[simp]
lemma mem_to_prime_spectrum_fun (f : Γ.obj (op X)) (x : X) :
  f ∈ (X.to_prime_spectrum_fun x).as_ideal ↔
  ¬is_unit (X.presheaf.germ (⟨x, trivial⟩ : (⊤ : opens X)) f) :=
iff.rfl

lemma to_prime_spectrum_preim_basic_open_eq (f : Γ.obj (op X)) :
  X.to_prime_spectrum_fun ⁻¹' (basic_open f) =
  (X.to_RingedSpace.basic_open f).1 :=
set.ext $ λ x,
begin
  rw [set.mem_preimage, opens.mem_coe, mem_basic_open, mem_to_prime_spectrum_fun, not_not],
  refl,
end

lemma continuous_to_prime_spectrum_fun : continuous X.to_prime_spectrum_fun :=
begin
  apply is_topological_basis_basic_opens.continuous,
  rintros s ⟨f, rfl⟩,
  rw to_prime_spectrum_preim_basic_open_eq,
  exact (X.to_RingedSpace.basic_open f).2,
end

@[simps]
def to_Spec_Top : X.to_Top ⟶ Spec.Top_obj (Γ.obj (op X)) :=
{ to_fun := X.to_prime_spectrum_fun,
  continuous_to_fun := X.continuous_to_prime_spectrum_fun }

lemma to_Spec_Top_preim_basic_open_eq (f : Γ.obj (op X))  :
  (opens.map X.to_Spec_Top).obj (basic_open f) =
  X.to_RingedSpace.basic_open f :=
opens.ext (X.to_prime_spectrum_preim_basic_open_eq f)

/--
The components of the sheaf homomorphism to the map $X ⟶ Spec(Γ(X))$ on basic opens.
This should be made to a proper sheaf homomorphism by some means of extension.
-/
def to_Spec_c_basic_open (f : Γ.obj (op X)) :
  (structure_sheaf (Γ.obj (op X))).1.obj (op (basic_open f)) ⟶
  X.presheaf.obj (op ((opens.map X.to_Spec_Top).obj (basic_open f))) :=
(structure_sheaf.basic_open_iso (Γ.obj (op X)) f).hom ≫
  CommRing.of_hom (is_localization.away.lift f (X.to_RingedSpace.is_unit_res_basic_open f)) ≫
  X.presheaf.map (eq_to_hom (X.to_Spec_Top_preim_basic_open_eq f)).op

-- Naturality of the sheaf homomorphism, on basic opens.
lemma to_Spec_c_basic_open_naturality (f g : Γ.obj (op X)) (i : basic_open f ⟶ basic_open g) :
  X.to_Spec_c_basic_open g ≫ X.presheaf.map ((opens.map X.to_Spec_Top).map i).op =
  (structure_sheaf (Γ.obj (op X))).1.map i.op ≫ X.to_Spec_c_basic_open f :=
sorry

def to_Spec_SheafedSpace : X.to_SheafedSpace ⟶ Spec.SheafedSpace_obj (Γ.obj (op X)) :=
{ base := X.to_Spec_Top, c := sorry }

-- No matter how the extension of the sheaf homomorphism works, this compatibility lemma should be
-- satisfied.
lemma to_Spec_SheafedSpace_c_basic_open_eq (f : Γ.obj (op X)) :
  X.to_Spec_SheafedSpace.c.app (op (basic_open f)) = X.to_Spec_c_basic_open f :=
sorry

-- TODO: Show that the induced stalk maps are local.
def to_Spec_LocallyRingedSpace : X ⟶ Spec.LocallyRingedSpace_obj (Γ.obj (op X)) :=
begin
  refine ⟨X.to_Spec_SheafedSpace, _⟩,
  sorry
end

end LocallyRingedSpace

def Spec.LocallyRingedSpace_adjunction :
  Spec.to_LocallyRingedSpace.right_op ⊣ LocallyRingedSpace.Γ :=
adjunction.mk_of_unit_counit $
{ unit := Spec_Γ_identity.inv,
  counit :=
  { app := λ X, (unop X).to_Spec_LocallyRingedSpace.op,
    naturality' := sorry },
  left_triangle' := sorry,
  right_triangle' := sorry }


end algebraic_geometry
