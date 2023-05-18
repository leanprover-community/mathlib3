/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import representation_theory.basic
import representation_theory.Action
import algebra.category.Module.abelian
import algebra.category.Module.colimits
import algebra.category.Module.monoidal.symmetric
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

@[simp] lemma Action_ρ_eq_ρ {A : Rep k G} : Action.ρ A = A.ρ := rfl

/-- Allows us to apply lemmas about the underlying `ρ`, which would take an element `g : G` rather
than `g : Mon.of G` as an argument. -/
lemma of_ρ_apply {V : Type u} [add_comm_group V] [module k V]
  (ρ : representation k G V) (g : Mon.of G) :
  (Rep.of ρ).ρ g = ρ (g : G) := rfl

variables (k G)

/-- The trivial `k`-linear `G`-representation on a `k`-module `V.` -/
def trivial (V : Type u) [add_comm_group V] [module k V] : Rep k G :=
Rep.of (@representation.trivial k G V _ _ _ _)

variables {k G}

lemma trivial_def {V : Type u} [add_comm_group V] [module k V] (g : G) (v : V) :
  (trivial k G V).ρ g v = v := rfl

-- Verify that limits are calculated correctly.
noncomputable example : preserves_limits (forget₂ (Rep k G) (Module.{u} k)) :=
by apply_instance
noncomputable example : preserves_colimits (forget₂ (Rep k G) (Module.{u} k)) :=
by apply_instance

@[simp] lemma monoidal_category.braiding_hom_apply {A B : Rep k G} (x : A) (y : B) :
  Action.hom.hom (β_ A B).hom (tensor_product.tmul k x y) = tensor_product.tmul k y x := rfl

@[simp] lemma monoidal_category.braiding_inv_apply {A B : Rep k G} (x : A) (y : B) :
  Action.hom.hom (β_ A B).inv (tensor_product.tmul k y x) = tensor_product.tmul k x y := rfl

section linearization

variables (k G)

/-- The monoidal functor sending a type `H` with a `G`-action to the induced `k`-linear
`G`-representation on `k[H].` -/
noncomputable def linearization :
  monoidal_functor (Action (Type u) (Mon.of G)) (Rep k G) :=
(Module.monoidal_free k).map_Action (Mon.of G)

variables {k G}

@[simp] lemma linearization_obj_ρ (X : Action (Type u) (Mon.of G)) (g : G) (x : X.V →₀ k) :
  ((linearization k G).obj X).ρ g x = finsupp.lmap_domain k k (X.ρ g) x := rfl

@[simp] lemma linearization_of (X : Action (Type u) (Mon.of G)) (g : G) (x : X.V) :
  ((linearization k G).obj X).ρ g (finsupp.single x (1 : k))
    = finsupp.single (X.ρ g x) (1 : k) :=
by rw [linearization_obj_ρ, finsupp.lmap_domain_apply, finsupp.map_domain_single]

variables {X Y : Action (Type u) (Mon.of G)} (f : X ⟶ Y)

@[simp] lemma linearization_map_hom :
  ((linearization k G).map f).hom = finsupp.lmap_domain k k f.hom := rfl

lemma linearization_map_hom_single (x : X.V) (r : k) :
  ((linearization k G).map f).hom (finsupp.single x r)
    = finsupp.single (f.hom x) r :=
by rw [linearization_map_hom, finsupp.lmap_domain_apply, finsupp.map_domain_single]

@[simp] lemma linearization_μ_hom (X Y : Action (Type u) (Mon.of G)) :
  ((linearization k G).μ X Y).hom = (finsupp_tensor_finsupp' k X.V Y.V).to_linear_map :=
rfl

@[simp] lemma linearization_μ_inv_hom (X Y : Action (Type u) (Mon.of G)) :
  (inv ((linearization k G).μ X Y)).hom = (finsupp_tensor_finsupp' k X.V Y.V).symm.to_linear_map :=
begin
  simp_rw [←Action.forget_map, functor.map_inv, Action.forget_map, linearization_μ_hom],
  apply is_iso.inv_eq_of_hom_inv_id _,
  exact linear_map.ext (λ x, linear_equiv.symm_apply_apply _ _),
end

@[simp] lemma linearization_ε_hom :
  (linearization k G).ε.hom = finsupp.lsingle punit.star :=
rfl

@[simp] lemma linearization_ε_inv_hom_apply (r : k) :
  (inv (linearization k G).ε).hom (finsupp.single punit.star r) = r :=
begin
  simp_rw [←Action.forget_map, functor.map_inv, Action.forget_map],
  rw [←finsupp.lsingle_apply punit.star r],
  apply is_iso.hom_inv_id_apply _ _,
end

variables (k G)

/-- The linearization of a type `X` on which `G` acts trivially is the trivial `G`-representation
on `k[X]`. -/
@[simps] noncomputable def linearization_trivial_iso (X : Type u) :
  (linearization k G).obj (Action.mk X 1) ≅ trivial k G (X →₀ k) :=
Action.mk_iso (iso.refl _) $ λ g, by { ext1, ext1, exact linearization_of _ _ _ }

variables (k G)

/-- Given a `G`-action on `H`, this is `k[H]` bundled with the natural representation
`G →* End(k[H])` as a term of type `Rep k G`. -/
noncomputable abbreviation of_mul_action (H : Type u) [mul_action G H] : Rep k G :=
of $ representation.of_mul_action k G H

/-- The `k`-linear `G`-representation on `k[G]`, induced by left multiplication. -/
noncomputable def left_regular : Rep k G :=
of_mul_action k G G

/-- The `k`-linear `G`-representation on `k[Gⁿ]`, induced by left multiplication. -/
noncomputable def diagonal (n : ℕ) : Rep k G :=
of_mul_action k G (fin n → G)

/-- The linearization of a type `H` with a `G`-action is definitionally isomorphic to the
`k`-linear `G`-representation on `k[H]` induced by the `G`-action on `H`. -/
noncomputable def linearization_of_mul_action_iso (H : Type u) [mul_action G H] :
  (linearization k G).obj (Action.of_mul_action G H)
    ≅ of_mul_action k G H := iso.refl _

variables {k G}

/-- Given an element `x : A`, there is a natural morphism of representations `k[G] ⟶ A` sending
`g ↦ A.ρ(g)(x).` -/
@[simps] noncomputable def left_regular_hom (A : Rep k G) (x : A) :
  Rep.of_mul_action k G G ⟶ A :=
{ hom := finsupp.lift _ _ _ (λ g, A.ρ g x),
  comm' := λ g,
  begin
    refine finsupp.lhom_ext' (λ y, linear_map.ext_ring _),
    simpa only [linear_map.comp_apply, Module.comp_def, finsupp.lsingle_apply,
      finsupp.lift_apply, Action_ρ_eq_ρ, of_ρ_apply, representation.of_mul_action_single,
      finsupp.sum_single_index, zero_smul, one_smul, smul_eq_mul, A.ρ.map_mul],
  end }

lemma left_regular_hom_apply {A : Rep k G} (x : A) :
  (left_regular_hom A x).hom (finsupp.single 1 1) = x :=
begin
  simpa only [left_regular_hom_hom, finsupp.lift_apply, finsupp.sum_single_index, one_smul,
    A.ρ.map_one, zero_smul],
end

/-- Given a `k`-linear `G`-representation `A`, there is a `k`-linear isomorphism between
representation morphisms `Hom(k[G], A)` and `A`. -/
@[simps] noncomputable def left_regular_hom_equiv (A : Rep k G) :
  (Rep.of_mul_action k G G ⟶ A) ≃ₗ[k] A :=
{ to_fun := λ f, f.hom (finsupp.single 1 1),
  map_add' := λ x y, rfl,
  map_smul' := λ r x, rfl,
  inv_fun := λ x, left_regular_hom A x,
  left_inv := λ f,
  begin
    refine Action.hom.ext _ _ (finsupp.lhom_ext' (λ (x : G), linear_map.ext_ring _)),
    have : f.hom (((of_mul_action k G G).ρ) x (finsupp.single (1 : G) (1 : k)))
      = A.ρ x (f.hom (finsupp.single (1 : G) (1 : k))) :=
      linear_map.ext_iff.1 (f.comm x) (finsupp.single 1 1),
    simp only [linear_map.comp_apply, finsupp.lsingle_apply,
      left_regular_hom_hom, finsupp.lift_apply, finsupp.sum_single_index, one_smul, ←this,
      zero_smul, of_ρ_apply, representation.of_mul_action_single x (1 : G) (1 : k), smul_eq_mul,
      mul_one],
  end,
  right_inv := λ x, left_regular_hom_apply x }

lemma left_regular_hom_equiv_symm_single {A : Rep k G} (x : A) (g : G) :
  ((left_regular_hom_equiv A).symm x).hom (finsupp.single g 1) = A.ρ g x :=
begin
  simp only [left_regular_hom_equiv_symm_apply, left_regular_hom_hom,
    finsupp.lift_apply, finsupp.sum_single_index, zero_smul, one_smul],
end

end linearization
end
section
open Action
variables [group G] (A B C : Rep k G)

noncomputable instance : monoidal_closed (Rep k G) :=
monoidal_closed.of_equiv (functor_category_monoidal_equivalence _ _)

/-- Explicit description of the 'internal Hom' `iHom(A, B)` of two representations `A, B`:
this is `F⁻¹(iHom(F(A), F(B)))`, where `F` is an equivalence
`Rep k G ≌ (single_obj G ⥤ Module k)`. Just used to prove `Rep.ihom_obj_ρ`. -/
lemma ihom_obj_ρ_def :
  ((ihom A).obj B).ρ = (functor_category_equivalence.inverse.obj
  ((functor_category_equivalence.functor.obj A).closed_ihom.obj
  (functor_category_equivalence.functor.obj B))).ρ := rfl

/-- Given `k`-linear `G`-representations `(A, ρ₁), (B, ρ₂)`, the 'internal Hom' is the
representation on `Homₖ(A, B)` sending `g : G` and `f : A →ₗ[k] B` to `(ρ₂ g) ∘ₗ f ∘ₗ (ρ₁ g⁻¹)`. -/
@[simp] lemma ihom_obj_ρ :
  ((ihom A).obj B).ρ = A.ρ.lin_hom B.ρ :=
begin
  refine monoid_hom.ext (λ g, _),
  simpa only [ihom_obj_ρ_def, functor_category_equivalence.inverse_obj_ρ_apply,
    functor.closed_ihom_obj_map, ←functor.map_inv, single_obj.inv_as_inv],
end

@[simp] lemma ihom_map_hom {B C : Rep k G} (f : B ⟶ C) :
  ((ihom A).map f).hom = linear_map.llcomp k A B C f.hom :=
rfl

/-- Unfolds the unit in the adjunction `A ⊗ - ⊣ iHom(A, -)`; just used to prove
`Rep.ihom_coev_app_hom`. -/
lemma ihom_coev_app_def :
  (ihom.coev A).app B = functor_category_equivalence.unit_iso.hom.app B ≫
  functor_category_equivalence.inverse.map
  ((functor_category_equivalence.functor.obj A).closed_unit.app _ ≫
  (functor_category_equivalence.functor.obj A).closed_ihom.map
  ((functor_category_monoidal_equivalence (Module.{u} k) (Mon.of G)).μ A B)) :=
rfl

/-- Describes the unit in the adjunction `A ⊗ - ⊣ iHom(A, -)`; given another `k`-linear
`G`-representation `B,` the `k`-linear map underlying the resulting map `B ⟶ iHom(A, A ⊗ B)` is
given by flipping the arguments in the natural `k`-bilinear map `A →ₗ[k] B →ₗ[k] A ⊗ B`. -/
@[simp] lemma ihom_coev_app_hom :
  Action.hom.hom ((ihom.coev A).app B) = (tensor_product.mk _ _ _).flip :=
begin
  refine linear_map.ext (λ x, linear_map.ext (λ y, _)),
  simpa only [ihom_coev_app_def, functor.map_comp, comp_hom,
    functor_category_equivalence.inverse_map_hom, functor.closed_ihom_map_app,
    functor_category_monoidal_equivalence.μ_app],
end

variables {A B C}

/-- Given a `k`-linear `G`-representation `A`, the adjunction `A ⊗ - ⊣ iHom(A, -)` defines a
bijection `Hom(A ⊗ B, C) ≃ Hom(B, iHom(A, C))` for all `B, C`. Given `f : A ⊗ B ⟶ C`, this lemma
describes the `k`-linear map underlying `f`'s image under the bijection. It is given by currying the
`k`-linear map underlying `f`, giving a map `A →ₗ[k] B →ₗ[k] C`, then flipping the arguments. -/
@[simp] lemma monoidal_closed_curry_hom (f : A ⊗ B ⟶ C) :
  (monoidal_closed.curry f).hom = (tensor_product.curry f.hom).flip :=
begin
  rw [monoidal_closed.curry_eq, comp_hom, ihom_coev_app_hom],
  refl,
end

/-- Given a `k`-linear `G`-representation `A`, the adjunction `A ⊗ - ⊣ iHom(A, -)` defines a
bijection `Hom(A ⊗ B, C) ≃ Hom(B, iHom(A, C))` for all `B, C`. Given `f : B ⟶ iHom(A, C)`, this
lemma describes the `k`-linear map underlying `f`'s image under the bijection. It is given by
flipping the arguments of the `k`-linear map underlying `f`, giving a map `A →ₗ[k] B →ₗ[k] C`, then
uncurrying. -/
@[simp] lemma monoidal_closed_uncurry_hom (f : B ⟶ (ihom A).obj C) :
  (monoidal_closed.uncurry f).hom = tensor_product.uncurry _ _ _ _ f.hom.flip :=
begin
  simp only [monoidal_closed.of_equiv_uncurry_def, comp_inv_iso_inv_app,
    monoidal_functor.comm_tensor_left_inv_app, comp_hom,
    functor_category_monoidal_equivalence.inverse_map, functor_category_equivalence.inverse_map_hom,
    functor_category_monoidal_equivalence.μ_iso_inv_app],
  ext,
  refl,
end

/-- Describes the counit in the adjunction `A ⊗ - ⊣ iHom(A, -)`; given another `k`-linear
`G`-representation `B,` the `k`-linear map underlying the resulting morphism `A ⊗ iHom(A, B) ⟶ B`
is given by uncurrying the map `A →ₗ[k] (A →ₗ[k] B) →ₗ[k] B` defined by flipping the arguments in
the identity map on `Homₖ(A, B).` -/
@[simp] lemma ihom_ev_app_hom : Action.hom.hom ((ihom.ev A).app B) =
  tensor_product.uncurry _ _ _ _ linear_map.id.flip :=
monoidal_closed_uncurry_hom _

variables (A B C)

/-- There is a `k`-linear isomorphism between the sets of representation morphisms`Hom(A ⊗ B, C)`
and `Hom(B, Homₖ(A, C))`. -/
noncomputable def monoidal_closed.linear_hom_equiv :
  (A ⊗ B ⟶ C) ≃ₗ[k] (B ⟶ (A ⟶[Rep k G] C)) :=
{ map_add' := λ f g, rfl,
  map_smul' := λ r f, rfl, ..(ihom.adjunction A).hom_equiv _ _ }

/-- There is a `k`-linear isomorphism between the sets of representation morphisms`Hom(A ⊗ B, C)`
and `Hom(A, Homₖ(B, C))`. -/
noncomputable def monoidal_closed.linear_hom_equiv_comm :
  (A ⊗ B ⟶ C) ≃ₗ[k] (A ⟶ (B ⟶[Rep k G] C)) :=
(linear.hom_congr k (β_ A B) (iso.refl _)) ≪≫ₗ
  monoidal_closed.linear_hom_equiv _ _ _

variables {A B C}

lemma monoidal_closed.linear_hom_equiv_hom (f : A ⊗ B ⟶ C) :
  (monoidal_closed.linear_hom_equiv A B C f).hom =
  (tensor_product.curry f.hom).flip :=
monoidal_closed_curry_hom _

lemma monoidal_closed.linear_hom_equiv_comm_hom (f : A ⊗ B ⟶ C) :
  (monoidal_closed.linear_hom_equiv_comm A B C f).hom =
 tensor_product.curry f.hom :=
begin
  dunfold monoidal_closed.linear_hom_equiv_comm,
  refine linear_map.ext (λ x, linear_map.ext (λ y, _)),
  simp only [linear_equiv.trans_apply, monoidal_closed.linear_hom_equiv_hom,
    linear.hom_congr_apply, iso.refl_hom, iso.symm_hom, linear_map.to_fun_eq_coe,
    linear_map.coe_comp, function.comp_app, linear.left_comp_apply, linear.right_comp_apply,
    category.comp_id, Action.comp_hom, linear_map.flip_apply, tensor_product.curry_apply,
    Module.coe_comp, function.comp_app, monoidal_category.braiding_inv_apply],
end

lemma monoidal_closed.linear_hom_equiv_symm_hom (f : B ⟶ (A ⟶[Rep k G] C)) :
  ((monoidal_closed.linear_hom_equiv A B C).symm f).hom =
  tensor_product.uncurry k A B C f.hom.flip :=
monoidal_closed_uncurry_hom _

lemma monoidal_closed.linear_hom_equiv_comm_symm_hom (f : A ⟶ (B ⟶[Rep k G] C)) :
  ((monoidal_closed.linear_hom_equiv_comm A B C).symm f).hom =
  tensor_product.uncurry k A B C f.hom :=
begin
  dunfold monoidal_closed.linear_hom_equiv_comm,
  refine tensor_product.algebra_tensor_module.curry_injective
    (linear_map.ext (λ x, linear_map.ext (λ y, _))),
  simp only [linear_equiv.trans_symm, linear_equiv.trans_apply, linear.hom_congr_symm_apply,
    iso.refl_inv, linear_map.coe_comp, function.comp_app, category.comp_id, Action.comp_hom,
    monoidal_closed.linear_hom_equiv_symm_hom, tensor_product.algebra_tensor_module.curry_apply,
    linear_map.coe_restrict_scalars, linear_map.to_fun_eq_coe, linear_map.flip_apply,
    tensor_product.curry_apply, Module.coe_comp, function.comp_app,
    monoidal_category.braiding_hom_apply, tensor_product.uncurry_apply],
end

end
end Rep
namespace representation
variables {k G : Type u} [comm_ring k] [monoid G] {V W : Type u}
  [add_comm_group V] [add_comm_group W] [module k V] [module k W]
  (ρ : representation k G V) (τ : representation k G W)

/-- Tautological isomorphism to help Lean in typechecking. -/
def Rep_of_tprod_iso : Rep.of (ρ.tprod τ) ≅ Rep.of ρ ⊗ Rep.of τ := iso.refl _

lemma Rep_of_tprod_iso_apply (x : tensor_product k V W) :
  (Rep_of_tprod_iso ρ τ).hom.hom x = x := rfl

lemma Rep_of_tprod_iso_inv_apply (x : tensor_product k V W) :
  (Rep_of_tprod_iso ρ τ).inv.hom x = x := rfl

end representation
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
