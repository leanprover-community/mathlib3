/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.CommRing.basic
import algebra.category.Module.basic
import group_theory.Action
import ring_theory.algebra
import data.monoid_algebra

noncomputable theory

universes u

open category_theory

@[derive [large_category, concrete_category]]
def Rep (R : CommRing.{u}) (G : Group.{u}) := Action (Module R) (Mon.of G)

namespace Rep
variables (R : CommRing.{u}) (G : Group.{u})

instance : has_forget₂ (Rep.{u} R G) (Module.{u} R) :=
by { dsimp [Rep], apply_instance }

local attribute [instance] concrete_category.has_coe_to_sort

variables {R G}

instance add_comm_group (V : Rep R G) : add_comm_group V :=
begin
  change add_comm_group V.V,
  apply_instance,
end
instance module (V : Rep R G) : module R V :=
begin
  change module R V.V,
  apply_instance,
end

-- So far it's all been boilerplate; the tiny bit of content starts here.

-- TODO: it would be nice to be able to use the coercion here,
-- rather than the terefah `.to_fun`.
instance has_scalar_monoid_algebra (V : Rep R G) : has_scalar (monoid_algebra R G) V :=
{ smul := λ f v, f.sum (λ g r, r • (((V.ρ g).to_fun) v)) }

namespace monoid_algebra_module
variables (V : Rep R G)

lemma one_smul (v : V) : (1 : monoid_algebra R G) • v = v :=
begin
  dsimp [(•)],
  change finsupp.sum (finsupp.single _ _) _ = _,
  rw finsupp.sum_single_index,
  { simp,
    rw Action.ρ_1, -- FIXME why can't simp do this?
    simp, },
  { simp, }
end

lemma mul_smul (x y : monoid_algebra R G) (v : V) : (x * y) • v = x • y • v :=
begin
  dsimp [(•)],
  simp [monoid_algebra.mul_def],
  sorry,
end

lemma add_smul (x y : monoid_algebra R G) (v : V) : (x + y) • v = x • v + y • v :=
begin
  dsimp [(•)],
  rw [finsupp.sum_add_index],
  { simp, },
  { intros g r₁ r₂, simp [add_smul], }
end

lemma smul_add (x : monoid_algebra R G) (v w : V) : x • (v + w) = x • v + x • w :=
begin
  dsimp [(•)],
  simp [smul_add],
end

lemma zero_smul (v : V) : (0 : monoid_algebra R G) • v = 0 :=
begin
  dsimp [(•)],
  simp,
end

lemma smul_zero (x : monoid_algebra R G) : x • (0 : V) = 0 :=
begin
  dsimp [(•)],
  simp,
end

end monoid_algebra_module

open monoid_algebra_module

instance monoid_algebra_module (V : Rep R G) : module (monoid_algebra R G) V :=
{ one_smul := λ v, one_smul V v,
  mul_smul := λ x y v, mul_smul V x y v,
  add_smul := λ x y v, add_smul V x y v,
  smul_add := λ x v w, smul_add V x v w,
  zero_smul := λ v, zero_smul V v,
  smul_zero := λ x, smul_zero V x, }

namespace monoid_algebra_equivalence

section
instance module_of_monoid_algebra_module
  (V : Type*) [add_comm_group V] [module (monoid_algebra R G) V] : module R V :=
module.restrict_scalars R (monoid_algebra R G) V.

-- instance distrib_mul_action_of_monoid_algebra_module
--   (V : Type*) [add_comm_group V] [module (monoid_algebra R G) V] : distrib_mul_action G V :=
-- { smul := λ g v, (g • (1 : monoid_algebra R G)) • v,
--   one_smul := λ v, by { dsimp, rw [mul_action.one_smul (1 : monoid_algebra R G), mul_action.one_smul v], },
--   mul_smul := λ g g' v, by { sorry },
--   smul_zero := λ g, by { dsimp, erw [distrib_mul_action.smul_zero (g • (1 : monoid_algebra R G))], refl, },
--   smul_add := λ g v w, by { dsimp, erw [distrib_mul_action.smul_add], refl, }, }

def mas (g : G) (r : R) : monoid_algebra R G := finsupp.single g r

instance distrib_mul_action_of_monoid_algebra_module
  (V : Type*) [add_comm_group V] [module (monoid_algebra R G) V] : distrib_mul_action G V :=
{ smul := λ g v, (mas g 1) • v,
  one_smul := λ v, sorry,
  mul_smul := λ g g' v, sorry,
  smul_zero := λ g, sorry,
  smul_add := λ g v w, sorry, }.

#exit

@[simp]
lemma group_action (V : Type*) [add_comm_group V] [module (monoid_algebra R G) V] (g : G) (v : V) :
  g • v = (mas g (1 : R)) • v :=
rfl

def action_of_monoid_algebra_module (M : Module (monoid_algebra R G)) : Mon.of G ⟶ Mon.of (End (Module.of R M)) :=
{ to_fun := λ g, linear_map.of_add_monoid_hom
    (by { dsimp, change (G : Type u) at g, exact smul.add_monoid_hom g M, })
    (λ r m,
    begin
      dsimp, change (G : Type u) at g,
      dsimp [(•)],
    -- change (g • (1 : monoid_algebra R G)) • ((r • m) : M) = r • (g • (1 : monoid_algebra R G)) • m, simp,
    end),
  map_one' := sorry,
  map_mul' := λ g h, sorry, }

@[simp]
lemma action_of_monoid_algebra_module_apply_apply (M : Module (monoid_algebra R G)) (g : G) (m : M) :
  action_of_monoid_algebra_module M g m = (g • (1 : monoid_algebra R G)) • m :=
rfl

-- Do we need more simp lemmas about the action of `G` on `monoid_algebra R G`? e.g.
-- `g • single g' r = single (g * g') r`
-- `(g • f) h = f (g⁻¹ * h)`

def functor : Rep R G ⥤ Module (monoid_algebra R G) :=
{ obj := λ V, Module.of _ V,
  map := λ V W f, linear_map.of_add_monoid_hom f.hom.to_add_monoid_hom
  begin
    sorry,
  end, }

def inverse : Module (monoid_algebra R G) ⥤ Rep R G :=
{ obj := λ V,
  { V := Module.of R V,
    ρ := action_of_monoid_algebra_module V },
  map := λ V W f,
  { hom := linear_map.restrict_scalars R f,
    comm' := sorry, }, }

end monoid_algebra_equivalence

def monoid_algebra_equivalence : Rep R G ≌ Module (monoid_algebra R G) :=
{ functor := monoid_algebra_equivalence.functor,
  inverse := monoid_algebra_equivalence.inverse,
  unit_iso := sorry,
  counit_iso := sorry,
  functor_unit_iso_comp' := sorry, }

end Rep

-- TODO the projection onto the trivial isotypic component, given by 1/|G| Σ g
-- TODO regular representation, induction functors (adjoint to `res`)
