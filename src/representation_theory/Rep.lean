/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import representation_theory.basic
import representation_theory.Action
import algebra.category.Module.limits
import algebra.category.Module.colimits
import algebra.category.Module.monoidal

/-!
# `Rep k G` is the category of `k`-linear representations of `G`.

If `V : Rep k G`, there is a coercion that allows you to treat `V` as a type,
and this type comes equipped with a `module k V` instance.
Also `V.ρ` gives the homomorphism `G →* (V →ₗ[k] V)`.

Conversely, given a homomorphism `ρ : G →* (V →ₗ[k] V)`,
you can construct the bundled representation as `Rep.of ρ`.

We verify that `Rep k G` has all limits and colimits, and is a monoidal category.
-/

universes u

open category_theory
open category_theory.limits

/-- The category of `k`-linear representations of a monoid `G`. -/
@[derive [large_category, concrete_category, has_limits, has_colimits]]
abbreviation Rep (k G : Type u) [ring k] [monoid G] :=
Action (Module.{u} k) (Mon.of G)

namespace Rep

variables {k G : Type u} [ring k] [monoid G]

instance : has_coe_to_sort (Rep k G) (Type u) := concrete_category.has_coe_to_sort _

instance (V : Rep k G) : add_comm_group V :=
by { change add_comm_group ((forget₂ (Rep k G) (Module k)).obj V), apply_instance, }

instance (V : Rep k G) : module k V :=
by { change module k ((forget₂ (Rep k G) (Module k)).obj V), apply_instance, }

-- This works well with the new design for representations:
def ρ' (V : Rep k G) : G →* (V →ₗ[k] V) := V.ρ

/-- Lift an unbundled representation to `Rep`. -/
@[simps]
def of {V : Type u} [add_comm_group V] [module k V] (ρ : G →* (V →ₗ[k] V)) : Rep k G :=
⟨Module.of k V, ρ⟩

@[simp] lemma of_ρ' {V : Type u} [add_comm_group V] [module k V] (ρ : G →* (V →ₗ[k] V)) :
  (of ρ).ρ' = ρ := rfl

-- Verify that limits are calculated correctly.
noncomputable example : preserves_limits (forget₂ (Rep k G) (Module.{u} k)) :=
by apply_instance
noncomputable example : preserves_colimits (forget₂ (Rep k G) (Module.{u} k)) :=
by apply_instance

end Rep

namespace Rep
variables {k G : Type u} [comm_ring k] [monoid G]

noncomputable theory

def module_monoid_algebra (V : Rep k G) : module (monoid_algebra k G) V :=
representation.as_module V.ρ

local attribute [instance] module_monoid_algebra

@[simp]
lemma turkle {V : Rep k G} (r : monoid_algebra k G) (x : V) :
  r • x = (monoid_algebra.lift k G _) V.ρ' r x :=
rfl

lemma algebra_map_smul' {V : Rep k G} {r : k} {v : V} :
  algebra_map k (monoid_algebra k G) r • v = r • v :=
begin
  simp,
end

-- local attribute [-instance] Rep.module

lemma quux {V : Rep k G} {g : G} {v : V} : monoid_algebra.of k G g • v = (V.ρ g).to_fun v :=
begin
  simp,
  refl,
end

lemma aux {k G : Type*} [comm_ring k] [monoid G]
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

def to_Module_monoid_algebra_map {V W : Rep k G} (f : V ⟶ W) :
  Module.of (monoid_algebra k G) V ⟶ Module.of (monoid_algebra k G) W :=
{ map_smul' := λ r x, aux V.V W.V V.ρ W.ρ f.hom f.comm r x,
  ..f.hom, }

def to_Module_monoid_algebra : Rep k G ⥤ Module.{u} (monoid_algebra k G) :=
{ obj := λ V, Module.of _ V,
  map := λ V W f, to_Module_monoid_algebra_map f, }

-- attribute [simps] to_Module_monoid_algebra

def representation_of_module_monoid_algebra (V : Module.{u} (monoid_algebra k G)) :
  G →* restrict_scalars k (monoid_algebra k G) V →ₗ[k] restrict_scalars k (monoid_algebra k G) V :=
(monoid_algebra.lift k G
  ((restrict_scalars k (monoid_algebra k G) V) →ₗ[k] restrict_scalars k (monoid_algebra k G) V)).symm
  (restrict_scalars.lsmul k (monoid_algebra k G) (restrict_scalars k (monoid_algebra k G) V))

-- @[simps]
-- @[irreducible]
def of_Module_monoid_algebra : Module.{u} (monoid_algebra k G) ⥤ Rep k G :=
{ obj := λ V, Rep.of (representation_of_module_monoid_algebra V), -- inline?
  map := λ V W f,
  { hom :=
    { map_smul' := λ r x, f.map_smul (algebra_map k _ r) x,
      ..f },
    comm' := λ g, by { ext, apply f.map_smul, }, }, }.

lemma of_Module_monoid_algebra_obj_coe (M : Module.{u} (monoid_algebra k G)) :
  (of_Module_monoid_algebra.obj M : Type u) = restrict_scalars k (monoid_algebra k G) M := rfl

lemma of_Module_monoid_algebra_obj_ρ' (M : Module.{u} (monoid_algebra k G)) :
  (of_Module_monoid_algebra.obj M).ρ' = representation_of_module_monoid_algebra M := rfl

def step1 (M : Module.{u} (monoid_algebra k G)) : of_Module_monoid_algebra.obj M ≃+ M :=
restrict_scalars.add_equiv k (monoid_algebra k G) M

def step2 (V : Rep k G) : to_Module_monoid_algebra.obj V ≃+ V :=
add_equiv.refl _

lemma step2_smul (V : Rep k G) (r : monoid_algebra k G) (x : to_Module_monoid_algebra.obj V) :
  step2 V (r • x) = monoid_algebra.lift k G _ V.ρ' r (step2 V x) := sorry

lemma smul_step1 (M : Module.{u} (monoid_algebra k G)) (r : monoid_algebra k G) (x : of_Module_monoid_algebra.obj M) :
  r • step1 M x = step1 M (monoid_algebra.lift k G _ (representation_of_module_monoid_algebra M) r x) :=
sorry

lemma smul_step1_symm (M : Module.{u} (monoid_algebra k G)) (r : k) (x : M) :
  r • (step1 M).symm x = (step1 M).symm (algebra_map k (monoid_algebra k G) r • x) :=
rfl

lemma step2_symm_smul (V : Rep k G) (r : k) (x : V) :
  (step2 V).symm (r • x) = algebra_map k (monoid_algebra k G) r • ((step2 V).symm x) :=
sorry

attribute [irreducible] of_Module_monoid_algebra to_Module_monoid_algebra

@[simps?]
def counit_iso_add_equiv {M : Module.{u} (monoid_algebra k G)}
  : ((of_Module_monoid_algebra ⋙ to_Module_monoid_algebra).obj M) ≃+ M :=
(step2 _).trans (step1 _)

@[simps?]
def unit_iso_add_equiv {V : Rep k G}
  : V ≃+ ((to_Module_monoid_algebra ⋙ of_Module_monoid_algebra).obj V) :=
(step2 _).symm.trans (step1 _).symm

-- lemma counit_iso_map_smul {M : Module.{u} (monoid_algebra k G)} (r : monoid_algebra k G)
--   (x : ((of_Module_monoid_algebra ⋙ to_Module_monoid_algebra).obj M)) :
--   counit_iso_to_fun ((((monoid_algebra.lift k G
--     ((of_Module_monoid_algebra.obj M) →ₗ[k] (of_Module_monoid_algebra.obj M)))
--     (of_Module_monoid_algebra.obj M).ρ') r) x) =
--       r • counit_iso_to_fun x :=
-- begin
--   dsimp [representation_of_module_monoid_algebra, counit_iso_to_fun],
--   apply monoid_algebra.induction_on r,
--   { intros, dsimp,
--     simp only [monoid_algebra.lift_symm_apply, monoid_algebra.lift_single, one_smul,
--       algebra.lsmul_coe], sorry, },
--   { intros f g fw gw, simp only [fw, gw, map_add, add_smul, linear_map.add_apply], },
--   { intros r' f w,
--     simp only [w, alg_hom.map_smul, linear_map.smul_apply],
--     clear w,
--     change algebra_map k (monoid_algebra k G) r' • _ = _,
--     rw ←mul_smul,
--     rw algebra.smul_def, },
-- end

#print add_equiv.trans_apply
attribute [simp] add_equiv.trans_apply

@[simps?]
def counit_iso (M : Module.{u} (monoid_algebra k G)) :
  (of_Module_monoid_algebra ⋙ to_Module_monoid_algebra).obj M ≅ M :=
linear_equiv.to_Module_iso'
{ map_smul' := λ r x, begin
    dsimp [counit_iso_add_equiv],
    rw step2_smul, rw smul_step1,
    --dsimp only [of_Module_monoid_algebra_obj_coe, of_Module_monoid_algebra_obj_ρ'],
    dsimp [of_Module_monoid_algebra, to_Module_monoid_algebra],
    refl,
  end,
  ..counit_iso_add_equiv, } --counit_iso_map_smul r x, }

attribute [simp] add_equiv.refl_apply

#print restrict_scalars.add_equiv_symm_apply

def unit_iso (V : Rep k G) :
  V ≅ ((to_Module_monoid_algebra ⋙ of_Module_monoid_algebra).obj V) :=
Action.mk_iso (linear_equiv.to_Module_iso'
{ map_smul' := λ r x, begin

    dsimp only [unit_iso_add_equiv],
    dsimp,
    rw step2_symm_smul,
    rw smul_step1_symm,
  end,
  ..unit_iso_add_equiv,
}) (λ g, begin ext, dsimp only [unit_iso_add_equiv], dsimp [step1, step2], dsimp [of_Module_monoid_algebra, to_Module_monoid_algebra],refl, simp, end

-- @[simps]
-- def foo (V : Rep k G) : Module.of k (restrict_scalars k (monoid_algebra k G) V) ≅ V.V :=
-- { hom :=
--   { to_fun := λ x, x,
--     map_add' := λ x y, rfl,
--     map_smul' := λ r x, algebra_map_smul', },
--   inv :=
--   { to_fun := λ x, x,
--     map_add' := λ x y, rfl,
--     map_smul' := λ r x, algebra_map_smul'.symm, }, }.

/-- The categorical equivalence `Rep k G ≌ Module (monoid_algebra k G)`. -/
def equivalence_Module_monoid_algebra : Rep k G ≌ Module.{u} (monoid_algebra k G) :=
{ functor := to_Module_monoid_algebra,
  inverse := of_Module_monoid_algebra,
  unit_iso := nat_iso.of_components (λ V, unit_iso V) sorry,
  counit_iso := nat_iso.of_components (λ M, counit_iso M) (sorry), }

-- Verify that the monoidal structure is available.
example : monoidal_category (Rep k G) := by apply_instance

-- TODO Verify that the equivalence with `Module (monoid_algebra k G)` is a monoidal functor.

end Rep
