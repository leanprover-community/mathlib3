/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import representation_theory.basic
import representation_theory.Action
import algebra.category.Module.abelian
import algebra.category.Module.colimits
import algebra.category.Module.monoidal
import algebra.category.Module.adjunctions
import category_theory.closed.functor_category

/-!
# `Rep k G` is the category of `k`-linear representations of `G`.

If `V : Rep k G`, there is a coercion that allows you to treat `V` as a type,
and this type comes equipped with a `module k V` instance.
Also `V.ρ` gives the homomorphism `G →* (V →ₗ[k] V)`.

Conversely, given a homomorphism `ρ : G →* (V →ₗ[k] V)`,
you can construct the bundled representation as `Rep.of ρ`.

We construct the categorical equivalence `Rep k G ≌ Module (monoid_algebra k G)`.
We verify that `Rep k G` is a `k`-linear abelian symmetric monoidal category with all (co)limits.
-/

universes u

open category_theory
open category_theory.limits

/-- The category of `k`-linear representations of a monoid `G`. -/
@[derive [large_category, concrete_category, has_limits, has_colimits,
  preadditive, abelian]]
abbreviation Rep (k G : Type u) [ring k] [monoid G] :=
Action (Module.{u} k) (Mon.of G)

instance (k G : Type u) [comm_ring k] [monoid G] : linear k (Rep k G) :=
by apply_instance

namespace Rep
variables {k G : Type u} [comm_ring k]
section
variables [monoid G]

instance : has_coe_to_sort (Rep k G) (Type u) := concrete_category.has_coe_to_sort _

instance (V : Rep k G) : add_comm_group V :=
by { change add_comm_group ((forget₂ (Rep k G) (Module k)).obj V), apply_instance, }

instance (V : Rep k G) : module k V :=
by { change module k ((forget₂ (Rep k G) (Module k)).obj V), apply_instance, }

/--
Specialize the existing `Action.ρ`, changing the type to `representation k G V`.
-/
def ρ (V : Rep k G) : representation k G V := V.ρ

/-- Lift an unbundled representation to `Rep`. -/
def of {V : Type u} [add_comm_group V] [module k V] (ρ : G →* (V →ₗ[k] V)) : Rep k G :=
⟨Module.of k V, ρ⟩

@[simp]
lemma coe_of {V : Type u} [add_comm_group V] [module k V] (ρ : G →* (V →ₗ[k] V)) :
  (of ρ : Type u) = V := rfl

@[simp] lemma of_ρ {V : Type u} [add_comm_group V] [module k V] (ρ : G →* (V →ₗ[k] V)) :
  (of ρ).ρ = ρ := rfl

-- Verify that limits are calculated correctly.
noncomputable example : preserves_limits (forget₂ (Rep k G) (Module.{u} k)) :=
by apply_instance
noncomputable example : preserves_colimits (forget₂ (Rep k G) (Module.{u} k)) :=
by apply_instance

section linearization

variables (k G)

/-- The monoidal functor sending a type `H` with a `G`-action to the induced `k`-linear
`G`-representation on `k[H].` -/
noncomputable def linearization :
  monoidal_functor (Action (Type u) (Mon.of G)) (Rep k G) :=
(Module.monoidal_free k).map_Action (Mon.of G)

variables {k G}

@[simp] lemma linearization_obj_ρ (X : Action (Type u) (Mon.of G)) (g : G) (x : X.V →₀ k) :
  ((linearization k G).1.1.obj X).ρ g x = finsupp.lmap_domain k k (X.ρ g) x := rfl

@[simp] lemma linearization_of (X : Action (Type u) (Mon.of G)) (g : G) (x : X.V) :
  ((linearization k G).1.1.obj X).ρ g (finsupp.single x (1 : k))
    = finsupp.single (X.ρ g x) (1 : k) :=
by rw [linearization_obj_ρ, finsupp.lmap_domain_apply, finsupp.map_domain_single]

variables (X Y : Action (Type u) (Mon.of G)) (f : X ⟶ Y)

@[simp] lemma linearization_map_hom :
  ((linearization k G).1.1.map f).hom = finsupp.lmap_domain k k f.hom := rfl

lemma linearization_map_hom_of (x : X.V) :
  ((linearization k G).1.1.map f).hom (finsupp.single x (1 : k))
    = finsupp.single (f.hom x) (1 : k) :=
by rw [linearization_map_hom, finsupp.lmap_domain_apply, finsupp.map_domain_single]

variables (k G)

/-- Given a `G`-action on `H`, this is `k[H]` bundled with the natural representation
`G →* End(k[H])` as a term of type `Rep k G`. -/
noncomputable abbreviation of_mul_action (H : Type u) [mul_action G H] : Rep k G :=
of $ representation.of_mul_action k G H

/-- The linearization of a type `H` with a `G`-action is definitionally isomorphic to the
`k`-linear `G`-representation on `k[H]` induced by the `G`-action on `H`. -/
noncomputable def linearization_of_mul_action_iso (n : ℕ) :
  (linearization k G).1.1.obj (Action.of_mul_action G (fin n → G))
    ≅ of_mul_action k G (fin n → G) := iso.refl _

end linearization
end
section
open Action
variables [group G] (A B C : Rep k G)

noncomputable instance : monoidal_closed (Rep k G) :=
monoidal_closed.of_equiv (functor_category_monoidal_equivalence _ _)

lemma ihom_obj_ρ_def :
  ((ihom A).obj B).ρ = (functor_category_equivalence.inverse.obj
  ((functor_category_equivalence.functor.obj A).closed_ihom.obj
  (functor_category_equivalence.functor.obj B))).ρ := rfl

@[simp] lemma ihom_obj_ρ :
  ((ihom A).obj B).ρ = A.ρ.lin_hom B.ρ :=
begin
  refine monoid_hom.ext (λ g, _),
  rw [ihom_obj_ρ_def, functor_category_equivalence.inverse_obj_ρ_apply,
    functor.closed_ihom_obj_map, ←functor.map_inv],
  dsimp only [functor_category_equivalence.functor_obj_obj,
    functor_category_equivalence.functor_obj_map, functor.closed_ihom_obj_map],
  simpa only [Module.monoidal_closed_pre_app, single_obj.inv_as_inv],
end

lemma ihom_map_def {B C : Rep k G} (f : B ⟶ C) :
  ((ihom A).map f) = (functor_category_equivalence.inverse.map
  ((functor_category_equivalence.functor.obj A).closed_ihom.map
  (functor_category_equivalence.functor.map f))) := rfl

@[simp] lemma ihom_map_hom {B C : Rep k G} (f : B ⟶ C) :
  ((ihom A).map f).hom = linear_map.llcomp k A B C f.hom :=
rfl

lemma ihom_coev_app_def :
  (ihom.coev A).app B = functor_category_equivalence.unit_iso.hom.app B ≫
  functor_category_equivalence.inverse.map
  ((functor_category_equivalence.functor.obj A).closed_unit.app _ ≫
  (functor_category_equivalence.functor.obj A).closed_ihom.map
  ((functor_category_monoidal_equivalence (Module.{u} k) (Mon.of G)).μ A B)) :=
rfl

@[simp] lemma ihom_coev_app_hom :
  Action.hom.hom ((ihom.coev A).app B) =
    (tensor_product.mk _ _ _).flip :=
begin
  refine linear_map.ext (λ x, linear_map.ext (λ y, _)),
  simpa only [ihom_coev_app_def, functor_category_equivalence_unit_iso, iso.app_hom,
    functor.map_comp, ihom_coev_app_def, functor_category_equivalence_unit_iso, iso.app_hom,
    functor.map_comp, comp_hom, functor_category_equivalence.unit_iso_hom_app_hom,
    functor_category_equivalence.inverse_map_hom, functor.closed_unit_app_app,
    functor.closed_ihom_map_app, Module.ihom_coev_app, Module.coe_comp,
    function.comp_app, tensor_product.curry_apply, linear_map.flip_apply,
    Module.ihom_map_apply, Module.monoidal_category.braiding_hom_apply,
    functor_category_monoidal_equivalence.μ_app, id_apply, linear_map.id_apply],
end

variables {A B C}

@[simp] lemma monoidal_closed_curry_hom (f : A ⊗ B ⟶ C) :
  (monoidal_closed.curry f).hom = (tensor_product.curry f.hom).flip :=
begin
  rw [monoidal_closed.curry_eq, comp_hom, ihom_coev_app_hom],
  refl,
end

@[simp] lemma monoidal_closed_uncurry_hom (f : B ⟶ (ihom A).obj C) :
  (monoidal_closed.uncurry f).hom = tensor_product.uncurry _ _ _ _ f.hom.flip :=
begin
  simp only [monoidal_closed.of_equiv_uncurry_def, comp_inv_iso_inv_app,
    monoidal_functor.comm_tensor_left_inv_app, adjunction.hom_equiv_counit,
    category.assoc, comp_hom, functor_category_monoidal_equivalence.inv_counit_app_hom,
    functor_category_monoidal_equivalence.counit_app],
  simp only [monoidal_closed.uncurry_eq, category_theory.functor.ihom_ev_app, functor.map_comp,
    Action.comp_hom, category.assoc, functor_category_monoidal_equivalence.inverse_map,
    functor_category_monoidal_equivalence.functor_map, functor_category_equivalence.inverse_map_hom,
    functor_category_equivalence.functor_map_app, monoidal_category.id_tensor_comp,
    nat_trans.comp_app, monoidal.tensor_hom_app, nat_trans.id_app, functor.closed_counit_app_app,
    Module.ihom_ev_app, functor_category_monoidal_equivalence.μ_iso_inv_app,
    functor_category_monoidal_equivalence.counit_app],
  ext,
  refl,
end

@[simp] lemma ihom_ev_app_hom : Action.hom.hom ((ihom.ev A).app B) =
  tensor_product.uncurry _ _ _ _ linear_map.id.flip :=
monoidal_closed_uncurry_hom _

end
end Rep

/-!
# The categorical equivalence `Rep k G ≌ Module.{u} (monoid_algebra k G)`.
-/
namespace Rep
variables {k G : Type u} [comm_ring k] [monoid G]

-- Verify that the symmetric monoidal structure is available.
example : symmetric_category (Rep k G) := by apply_instance
example : monoidal_preadditive (Rep k G) := by apply_instance
example : monoidal_linear k (Rep k G) := by apply_instance

noncomputable theory

/-- Auxilliary lemma for `to_Module_monoid_algebra`. -/
lemma to_Module_monoid_algebra_map_aux {k G : Type*} [comm_ring k] [monoid G]
  (V W : Type*) [add_comm_group V] [add_comm_group W] [module k V] [module k W]
  (ρ : G →* V →ₗ[k] V) (σ : G →* W →ₗ[k] W)
  (f : V →ₗ[k] W) (w : ∀ (g : G), f.comp (ρ g) = (σ g).comp f)
  (r : monoid_algebra k G) (x : V) :
  f ((((monoid_algebra.lift k G (V →ₗ[k] V)) ρ) r) x) =
    (((monoid_algebra.lift k G (W →ₗ[k] W)) σ) r) (f x) :=
begin
  apply monoid_algebra.induction_on r,
  { intro g,
    simp only [one_smul, monoid_algebra.lift_single, monoid_algebra.of_apply],
    exact linear_map.congr_fun (w g) x, },
  { intros g h gw hw, simp only [map_add, add_left_inj, linear_map.add_apply, hw, gw], },
  { intros r g w,
    simp only [alg_hom.map_smul, w, ring_hom.id_apply,
      linear_map.smul_apply, linear_map.map_smulₛₗ], }
end

/-- Auxilliary definition for `to_Module_monoid_algebra`. -/
def to_Module_monoid_algebra_map {V W : Rep k G} (f : V ⟶ W) :
  Module.of (monoid_algebra k G) V.ρ.as_module ⟶ Module.of (monoid_algebra k G) W.ρ.as_module :=
{ map_smul' := λ r x, to_Module_monoid_algebra_map_aux V.V W.V V.ρ W.ρ f.hom f.comm r x,
  ..f.hom, }

/-- Functorially convert a representation of `G` into a module over `monoid_algebra k G`. -/
def to_Module_monoid_algebra : Rep k G ⥤ Module.{u} (monoid_algebra k G) :=
{ obj := λ V, Module.of _ V.ρ.as_module ,
  map := λ V W f, to_Module_monoid_algebra_map f, }

/-- Functorially convert a module over `monoid_algebra k G` into a representation of `G`. -/
def of_Module_monoid_algebra : Module.{u} (monoid_algebra k G) ⥤ Rep k G :=
{ obj := λ M, Rep.of (representation.of_module k G M),
  map := λ M N f,
  { hom :=
    { map_smul' := λ r x, f.map_smul (algebra_map k _ r) x,
      ..f },
    comm' := λ g, by { ext, apply f.map_smul, }, }, }.

lemma of_Module_monoid_algebra_obj_coe (M : Module.{u} (monoid_algebra k G)) :
  (of_Module_monoid_algebra.obj M : Type u) = restrict_scalars k (monoid_algebra k G) M := rfl

lemma of_Module_monoid_algebra_obj_ρ (M : Module.{u} (monoid_algebra k G)) :
  (of_Module_monoid_algebra.obj M).ρ = representation.of_module k G M := rfl

/-- Auxilliary definition for `equivalence_Module_monoid_algebra`. -/
def counit_iso_add_equiv {M : Module.{u} (monoid_algebra k G)} :
  ((of_Module_monoid_algebra ⋙ to_Module_monoid_algebra).obj M) ≃+ M :=
begin
  dsimp [of_Module_monoid_algebra, to_Module_monoid_algebra],
  refine (representation.of_module k G ↥M).as_module_equiv.trans (restrict_scalars.add_equiv _ _ _),
end

/-- Auxilliary definition for `equivalence_Module_monoid_algebra`. -/
def unit_iso_add_equiv {V : Rep k G} :
  V ≃+ ((to_Module_monoid_algebra ⋙ of_Module_monoid_algebra).obj V) :=
begin
  dsimp [of_Module_monoid_algebra, to_Module_monoid_algebra],
  refine V.ρ.as_module_equiv.symm.trans _,
  exact (restrict_scalars.add_equiv _ _ _).symm,
end

/-- Auxilliary definition for `equivalence_Module_monoid_algebra`. -/
def counit_iso (M : Module.{u} (monoid_algebra k G)) :
  (of_Module_monoid_algebra ⋙ to_Module_monoid_algebra).obj M ≅ M :=
linear_equiv.to_Module_iso'
{ map_smul' := λ r x, begin
    dsimp [counit_iso_add_equiv],
    simp,
  end,
  ..counit_iso_add_equiv, }

lemma unit_iso_comm (V : Rep k G) (g : G) (x : V) :
  unit_iso_add_equiv (((V.ρ) g).to_fun x) =
    (((of_Module_monoid_algebra.obj (to_Module_monoid_algebra.obj V)).ρ) g).to_fun
      (unit_iso_add_equiv x) :=
begin
  dsimp [unit_iso_add_equiv, of_Module_monoid_algebra, to_Module_monoid_algebra],
  simp only [add_equiv.apply_eq_iff_eq, add_equiv.apply_symm_apply,
    representation.as_module_equiv_symm_map_rho, representation.of_module_as_module_act],
end

/-- Auxilliary definition for `equivalence_Module_monoid_algebra`. -/
def unit_iso (V : Rep k G) :
  V ≅ ((to_Module_monoid_algebra ⋙ of_Module_monoid_algebra).obj V) :=
Action.mk_iso (linear_equiv.to_Module_iso'
{ map_smul' := λ r x, begin
    dsimp [unit_iso_add_equiv],
    simp only [representation.as_module_equiv_symm_map_smul,
      restrict_scalars.add_equiv_symm_map_algebra_map_smul],
  end,
  ..unit_iso_add_equiv, })
  (λ g, by { ext, apply unit_iso_comm, })

/-- The categorical equivalence `Rep k G ≌ Module (monoid_algebra k G)`. -/
def equivalence_Module_monoid_algebra : Rep k G ≌ Module.{u} (monoid_algebra k G) :=
{ functor := to_Module_monoid_algebra,
  inverse := of_Module_monoid_algebra,
  unit_iso := nat_iso.of_components (λ V, unit_iso V) (by tidy),
  counit_iso := nat_iso.of_components (λ M, counit_iso M) (by tidy), }

-- TODO Verify that the equivalence with `Module (monoid_algebra k G)` is a monoidal functor.

end Rep
