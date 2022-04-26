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

local attribute [-instance] Rep.module

lemma quux {V : Rep k G} {g : G} {v : V} : monoid_algebra.of k G g • v = (V.ρ g).to_fun v :=
begin
  simp,
  refl,
end

def to_Module_monoid_algebra_map {V W : Rep k G} (f : V ⟶ W) :
  Module.of (monoid_algebra k G) V ⟶ Module.of (monoid_algebra k G) W :=
{ map_smul' := λ r x, begin
    dsimp,
    apply monoid_algebra.induction_on r,
    { intro g,
      simp only [one_smul, monoid_algebra.lift_single, monoid_algebra.of_apply],
      exact congr_hom (f.comm g) x, },
    { intros g h gw hw, simp only [map_add, add_left_inj, linear_map.add_apply, hw, gw], },
    { intros r g w,
      simp only [alg_hom.map_smul, w, ring_hom.id_apply,
        linear_map.smul_apply, linear_map.map_smulₛₗ], },
  end,
  ..f.hom, }

def to_Module_monoid_algebra : Rep k G ⥤ Module.{u} (monoid_algebra k G) :=
{ obj := λ V, Module.of _ V,
  map := λ V W f, to_Module_monoid_algebra_map f, }

attribute [simps] to_Module_monoid_algebra

@[simps]
def of_Module_monoid_algebra : Module.{u} (monoid_algebra k G) ⥤ Rep k G :=
{ obj := λ V,
  begin
    refine Rep.of
      ((monoid_algebra.lift k G ((restrict_scalars k (monoid_algebra k G) V) →ₗ[k] _)).symm _),
    apply algebra.lsmul k,
  end,
  map := λ V W f,
  { hom :=
    { map_smul' := λ r x, f.map_smul (algebra_map k _ r) x,
      ..f },
    comm' := λ g, by { ext, apply f.map_smul, }, }, }.

def counit_iso (M : Module.{u} (monoid_algebra k G)) :
  (of_Module_monoid_algebra ⋙ to_Module_monoid_algebra).obj M ≅ M :=
linear_equiv.to_Module_iso'
{ to_fun := λ m, m,
  inv_fun := λ m, m,
  left_inv := λ m, rfl,
  right_inv := λ m, rfl,
  map_add' := λ x y, rfl,
  map_smul' := λ r x, begin
    dsimp,
    apply monoid_algebra.induction_on r,
    { intros, dsimp, simp, },
    { intros f g fw gw, simp only [fw, gw, map_add, add_smul, linear_map.add_apply], },
    { intros r f w,
      simp only [w, alg_hom.map_smul, linear_map.smul_apply],
      clear w,
      change algebra_map k (monoid_algebra k G) r • _ = _,
      rw ←mul_smul,
      rw algebra.smul_def, },
  end, }

@[simps]
def foo (V : Rep k G) : Module.of k (restrict_scalars k (monoid_algebra k G) V) ≅ V.V :=
{ hom :=
  { to_fun := λ x, x,
    map_add' := λ x y, rfl,
    map_smul' := λ r x, algebra_map_smul', },
  inv :=
  { to_fun := λ x, x,
    map_add' := λ x y, rfl,
    map_smul' := λ r x, algebra_map_smul'.symm, }, }.

/-- The categorical equivalence `Rep k G ≌ Module (monoid_algebra k G)`. -/
def equivalence_Module_monoid_algebra : Rep k G ≌ Module.{u} (monoid_algebra k G) :=
{ functor := to_Module_monoid_algebra,
  inverse := of_Module_monoid_algebra,
  unit_iso := nat_iso.of_components
    (λ V, Action.mk_iso (foo V).symm (by { intros, ext, exact quux.symm, })) (by tidy),
  counit_iso := nat_iso.of_components (λ M, counit_iso M) (by tidy), }

-- Verify that the monoidal structure is available.
example : monoidal_category (Rep k G) := by apply_instance

-- TODO Verify that the equivalence with `Module (monoid_algebra k G)` is a monoidal functor.

end Rep
