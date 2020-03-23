import algebra.category.CommRing.basic
import algebra.category.Module.basic
import algebra.group.Action
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
  sorry
end

lemma mul_smul (x y : monoid_algebra R G) (v : V) : (x * y) • v = x • y • v :=
begin
  sorry
end

lemma add_smul (x y : monoid_algebra R G) (v : V) : (x + y) • v = x • v + y • v :=
begin
  sorry
end

lemma smul_add (x : monoid_algebra R G) (v w : V) : x • (v + w) = x • v + x • w :=
begin
  sorry
end

lemma zero_smul (v : V) : (0 : monoid_algebra R G) • v = 0 :=
begin
  sorry
end

lemma smul_zero (x : monoid_algebra R G) : x • (0 : V) = 0 :=
begin
  admit
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
module.restrict_scalars R (monoid_algebra R G) V

def action_of_monoid_algebra_module (M : Module (monoid_algebra R G)) : Mon.of G ⟶ Mon.of (End (Module.of R M)) :=
{ to_fun := λ g, sorry,
  map_one' := sorry,
  map_mul' := λ g h, sorry, }
end

def functor : Rep R G ⥤ Module (monoid_algebra R G) :=
{ obj := λ V, Module.of _ V,
  map := sorry,
  map_id' := sorry,
  map_comp' := sorry, }

def inverse : Module (monoid_algebra R G) ⥤ Rep R G :=
{ obj := λ V,
  { V := Module.of R V,
    ρ := action_of_monoid_algebra_module V },
  map := sorry,
  map_id' := sorry,
  map_comp' := sorry, }

end monoid_algebra_equivalence

def monoid_algebra_equivalence : Rep R G ≌ Module (monoid_algebra R G) :=
{ functor := monoid_algebra_equivalence.functor,
  inverse := monoid_algebra_equivalence.inverse,
  unit_iso := sorry,
  counit_iso := sorry,
  functor_unit_iso_comp' := sorry, }

end Rep
