/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import representation_theory.Rep
import algebra.category.fgModule.limits
import category_theory.preadditive.schur
import representation_theory.basic

/-!
# `fdRep k G` is the category of finite dimensional `k`-linear representations of `G`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

If `V : fdRep k G`, there is a coercion that allows you to treat `V` as a type,
and this type comes equipped with `module k V` and `finite_dimensional k V` instances.
Also `V.ρ` gives the homomorphism `G →* (V →ₗ[k] V)`.

Conversely, given a homomorphism `ρ : G →* (V →ₗ[k] V)`,
you can construct the bundled representation as `Rep.of ρ`.

We verify that `fdRep k G` is a `k`-linear monoidal category, and rigid when `G` is a group.

`fdRep k G` has all finite limits.

## TODO
* `fdRep k G ≌ full_subcategory (finite_dimensional k)`
* Upgrade the right rigid structure to a rigid structure
  (this just needs to be done for `fgModule`).
* `fdRep k G` has all finite colimits.
* `fdRep k G` is abelian.
* `fdRep k G ≌ fgModule (monoid_algebra k G)`.

-/

universes u

open category_theory
open category_theory.limits

/-- The category of finite dimensional `k`-linear representations of a monoid `G`. -/
@[derive [large_category, concrete_category, preadditive, has_finite_limits]]
abbreviation fdRep (k G : Type u) [field k] [monoid G] :=
Action (fgModule.{u} k) (Mon.of G)

namespace fdRep

variables {k G : Type u} [field k] [monoid G]

instance : linear k (fdRep k G) := by apply_instance

instance : has_coe_to_sort (fdRep k G) (Type u) := concrete_category.has_coe_to_sort _

instance (V : fdRep k G) : add_comm_group V :=
by { change add_comm_group ((forget₂ (fdRep k G) (fgModule k)).obj V).obj, apply_instance, }

instance (V : fdRep k G) : module k V :=
by { change module k ((forget₂ (fdRep k G) (fgModule k)).obj V).obj, apply_instance, }

instance (V : fdRep k G) : finite_dimensional k V :=
by { change finite_dimensional k ((forget₂ (fdRep k G) (fgModule k)).obj V).obj, apply_instance, }

/-- All hom spaces are finite dimensional. -/
instance (V W : fdRep k G) : finite_dimensional k (V ⟶ W) :=
finite_dimensional.of_injective
  ((forget₂ (fdRep k G) (fgModule k)).map_linear_map k) (functor.map_injective _)

/-- The monoid homomorphism corresponding to the action of `G` onto `V : fdRep k G`. -/
def ρ (V : fdRep k G) : G →* (V →ₗ[k] V) := V.ρ

/-- The underlying `linear_equiv` of an isomorphism of representations. -/
def iso_to_linear_equiv {V W : fdRep k G} (i : V ≅ W) : V ≃ₗ[k] W :=
  fgModule.iso_to_linear_equiv ((Action.forget (fgModule k) (Mon.of G)).map_iso i)

lemma iso.conj_ρ {V W : fdRep k G} (i : V ≅ W) (g : G) :
   W.ρ g = (fdRep.iso_to_linear_equiv i).conj (V.ρ g) :=
begin
  rw [fdRep.iso_to_linear_equiv, ←fgModule.iso.conj_eq_conj, iso.conj_apply],
  rw [iso.eq_inv_comp ((Action.forget (fgModule k) (Mon.of G)).map_iso i)],
  exact (i.hom.comm g).symm,
end

/-- Lift an unbundled representation to `fdRep`. -/
@[simps ρ]
def of {V : Type u} [add_comm_group V] [module k V] [finite_dimensional k V]
  (ρ : representation k G V) : fdRep k G :=
⟨fgModule.of k V, ρ⟩

instance : has_forget₂ (fdRep k G) (Rep k G) :=
{ forget₂ := (forget₂ (fgModule k) (Module k)).map_Action (Mon.of G), }

lemma forget₂_ρ (V : fdRep k G) : ((forget₂ (fdRep k G) (Rep k G)).obj V).ρ = V.ρ :=
by { ext g v, refl }

-- Verify that the monoidal structure is available.
example : monoidal_category (fdRep k G) := by apply_instance
example : monoidal_preadditive (fdRep k G) := by apply_instance
example : monoidal_linear k (fdRep k G) := by apply_instance

open finite_dimensional
open_locale classical

-- We need to provide this instance explicitely as otherwise `finrank_hom_simple_simple` gives a
-- deterministic timeout.
instance : has_kernels (fdRep k G) := by apply_instance

-- Verify that Schur's lemma applies out of the box.
lemma finrank_hom_simple_simple [is_alg_closed k] (V W : fdRep k G) [simple V] [simple W] :
  finrank k (V ⟶ W) = if nonempty (V ≅ W) then 1 else 0 :=
category_theory.finrank_hom_simple_simple k V W

/-- The forgetful functor to `Rep k G` preserves hom-sets and their vector space structure -/
def forget₂_hom_linear_equiv (X Y : fdRep k G) :
  (((forget₂ (fdRep k G) (Rep k G)).obj X) ⟶ ((forget₂ (fdRep k G) (Rep k G)).obj Y)) ≃ₗ[k]
  (X ⟶ Y) :=
{ to_fun := λ f, ⟨f.hom, f.comm⟩,
  map_add' := λ _ _, rfl,
  map_smul' := λ _ _, rfl,
  inv_fun := λ f, ⟨(forget₂ (fgModule k) (Module k)).map f.hom, f.comm⟩,
  left_inv := λ _, by { ext, refl },
  right_inv := λ _, by { ext, refl } }

end fdRep

namespace fdRep
variables {k G : Type u} [field k] [group G]

-- Verify that the right rigid structure is available when the monoid is a group.
noncomputable instance : right_rigid_category (fdRep k G) :=
by { change right_rigid_category (Action (fgModule k) (Group.of G)), apply_instance, }

end fdRep

namespace fdRep

-- The variables in this section are slightly weird, living half in `representation` and half in
-- `fdRep`. When we have a better API for general monoidal closed and rigid categories and these
-- structures on `fdRep`, we should remove the dependancy of statements about `fdRep` on
-- `representation.lin_hom` and `representation.dual`. The isomorphism `dual_tensor_iso_lin_hom`
-- below should then just be obtained from general results about rigid categories.

 open representation

variables {k G V : Type u} [field k] [group G]
variables [add_comm_group V] [module k V]
variables [finite_dimensional k V]
variables (ρV : representation k G V) (W : fdRep k G)

/-- Auxiliary definition for `fdRep.dual_tensor_iso_lin_hom`. -/
noncomputable def dual_tensor_iso_lin_hom_aux :
  ((fdRep.of ρV.dual) ⊗ W).V ≅ (fdRep.of (lin_hom ρV W.ρ)).V :=
(dual_tensor_hom_equiv k V W).to_fgModule_iso

/-- When `V` and `W` are finite dimensional representations of a group `G`, the isomorphism
`dual_tensor_hom_equiv k V W` of vector spaces induces an isomorphism of representations. -/
noncomputable def dual_tensor_iso_lin_hom :
  (fdRep.of ρV.dual) ⊗ W ≅ fdRep.of (lin_hom ρV W.ρ) :=
begin
  apply Action.mk_iso (dual_tensor_iso_lin_hom_aux ρV W),
  convert (dual_tensor_hom_comm ρV W.ρ),
end

@[simp] lemma dual_tensor_iso_lin_hom_hom_hom :
  (dual_tensor_iso_lin_hom ρV W).hom.hom = dual_tensor_hom k V W := rfl

end fdRep
