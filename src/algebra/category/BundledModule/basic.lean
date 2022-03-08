/-
Copyright (c) 2021 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import algebra.category.Module.basic
import algebra.category.CommRing.basic
import category_theory.category.basic
import algebra.category.Module.change_of_rings
import algebra.algebra.restrict_scalars

/-!
# The category of bundled module

`BundledModule.{u}` is the category of pairs of the shape `(R, M)` where `R` is
a ring in universe u and `M` is an `R`-module. A morphism between `M1 = (R, M)`
and `M2 = (S, N)` is a pair of morphism `(f, g)` where `f : R ⟶ S` is a ring
homomorphism and `g : M ⟶ f* N` is a module homomorphism (linear map).
-/

open category_theory change_of_rings

-- section restriction_of_scalars

-- universe u

-- variables {R S : CommRing.{u}} (f : R ⟶ S)
-- include f

-- -- /--Definition of scalar multiplication in restriction of scalars-/
-- -- def restriction_of_scalar.has_scalar (N : Module S) : has_scalar R N :=
-- -- { smul := λ r n,  f r • n}

-- -- local attribute [instance] restriction_of_scalar.has_scalar

-- /--
-- Given a ring homomorphism `f : R ⟶ S`, and an `S`-module `N`, we can turn `N` into an `R`-module.
-- This is called restriction_of_scalar
-- -/
-- @[reducible] def restriction_of_scalar.module (N : Module S) :
--   Module R :=
-- { carrier := N,
--   is_module := module.comp_hom _ f, }

-- local notation f `^*` N := restriction_of_scalar.module f N

-- @[simp] lemma restriction_of_scalar.smul_def (r : R) (N : Module S) (n : N) :
--   @has_scalar.smul R N (by { haveI := (f ^* N).is_module, apply_instance }) r n = f r • n := rfl

-- instance restriction_of_scalar.has_scalar' (N : Module S) :
--   has_scalar S (f ^* N) :=
-- { smul := λ r n, r • n }

-- @[simp] lemma restriction_of_scalar.smul_def' (r : R) (N : Module S)
--   (n : f ^* N) :
--   (r • n) = (f r • n) := rfl

-- /--restriction of scalar is a functor from `S`-modules to `R`-modules.-/
-- def restriction_of_scalar.functor : Module S ⥤ Module R :=
-- { obj := restriction_of_scalar.module f,
--   map := λ N₁ N₂ l,
--     { to_fun := l,
--       map_add' := λ x y, by rw [linear_map.map_add],
--       map_smul' := λ r y, begin
--         simp only [restriction_of_scalar.smul_def', ring_hom.id_apply],
--         convert linear_map.map_smul l (f r) y,
--       end } }

-- end restriction_of_scalars

section BundledModule

universe u

/--
A bundled module is a pair `(R, M)` such that `R : Ring` and `M` is an `R`-module.
-/
@[nolint has_inhabited_instance]
structure RingModulePair : Type (u+1) :=
(R : CommRing.{u})
(M : Module.{u} R.α)

variables {M1 M2 : RingModulePair} (f : M1.R ⟶ M2.R)
include f

/--
Given bundled modules `(R, M)` and `(S, N)` and a ring homomorphism `f : R ⟶ S`, there is
a bundled module `(R, N)` given by restriction of scalars.
-/
@[reducible] def restriction_of_scalars.bundled : RingModulePair :=
{ R := M1.R,
  M := restriction_of_scalars.module f M2.M }

local notation f `^*` M2 := restriction_of_scalars.bundled f

@[simp] lemma restriction_of_scalars.R :
  (f^* M2).R = M1.R := rfl

@[simp] lemma restriction_of_scalars.M :
  (f^* M2).M = restriction_of_scalars.module f M2.M := rfl

omit f
/--
A morphism between two bundled module `M1, M2` is a pair of morphism `(f, g)` such that
`f` is a ring homomorphism from `M1.R` to `M2.R` and `g` is a linear map from `M1.M` to `(f* M2).M`
-/
@[nolint has_inhabited_instance]
def bundledMap (M1 M2 : RingModulePair) : Type u :=
Σ (f : M1.R ⟶ M2.R), M1.M ⟶ (f^* M2).M

@[ext] lemma bundledMap.ext {M1 M2 : RingModulePair} (f1 f2 : bundledMap M1 M2) :
  f1 = f2 ↔ (f1.1 = f2.1 ∧ (∀ (m : M1.M), f1.2 m = f2.2 m)) :=
⟨λ eq1, ⟨eq1 ▸ rfl, λ m, eq1 ▸ rfl⟩, λ EQ, begin
  obtain ⟨eq1, eq2⟩ := EQ,
  ext,
  { rw eq1, },
  { rcases f1 with ⟨f1, m1⟩,
    rcases f2 with ⟨f2, m2⟩,
    dsimp only at eq1 eq2 ⊢,
    subst eq1,
    rw heq_iff_eq,
    ext,
    exact eq2 x, },
end⟩

@[simp] def bundledMap.id (M) : bundledMap M M :=
⟨𝟙 M.R, { to_fun := λ m, m,
          map_add' := λ _ _, rfl,
          map_smul' := λ _ _, rfl }⟩

def bundledMap.comp (M1 M2 M3) (f : bundledMap M1 M2) (g : bundledMap M2 M3) : bundledMap M1 M3 :=
⟨f.1 ≫ g.1,
 { to_fun := λ m, g.2 (f.2 m),
   map_add' := by simp,
   map_smul' := λ r m, begin
    convert linear_map.map_smul _ _ _,
    simpa only [restriction_of_scalars.smul_def', ring_hom.id_apply, linear_map.map_smulₛₗ],
   end }⟩

instance RingModulePair.is_cat : category RingModulePair :=
{ hom := λ M1 M2, bundledMap M1 M2,
  id := bundledMap.id,
  comp := bundledMap.comp }.

lemma bundledMap.comp_fst {M1 M2 M3 : RingModulePair} (f : M1 ⟶ M2) (g : M2 ⟶ M3) :
  (f ≫ g).1 = f.1 ≫ g.1 := rfl

lemma bundledMap.comp_snd {M1 M2 M3 : RingModulePair} (f : M1 ⟶ M2) (g : M2 ⟶ M3) :
  (f ≫ g).2 =
  { to_fun := λ m, g.2 (f.2 m),
    map_add' := by simp,
    map_smul' := λ r m,
    by { convert linear_map.map_smul _ _ _,
      simpa only [restriction_of_scalars.smul_def', ring_hom.id_apply, linear_map.map_smulₛₗ], } } :=
rfl

/-- the forgetful functor from `BundledModule` to `Ring`-/
@[simp] def RingModulePair.forget_to_Ring : RingModulePair ⥤ CommRing :=
{ obj := λ M, M.R,
  map := λ M1 M2 f, f.1 }

/-- the forgetful functor from `BundledModyle` to `Ab`-/
@[simp] def RingModulePair.forget_to_Ab : RingModulePair ⥤ Ab :=
{ obj := λ M, ⟨M.2⟩,
  map := λ X Y f, { to_fun := f.2,
    map_zero' := map_zero _,
    map_add' := map_add _ },
  map_id' := λ X, begin
    ext,
    simpa only [add_monoid_hom.coe_mk, id_apply],
  end,
  map_comp' := λ X Y Z f g, begin
    ext,
    simpa only [add_monoid_hom.coe_mk, comp_apply],
  end }

lemma RingModulePair.forget_to_Ab.map_def {M1 M2 : RingModulePair} (f : M1 ⟶ M2) :
  (RingModulePair.forget_to_Ab.map f).to_fun = f.2 := rfl

end BundledModule

section composition

universe u
variables {M1 M2 M3 : RingModulePair.{u}} (f : M1.R ⟶ M2.R) (g : M2.R ⟶ M3.R)
include f g

/--
If `Mᵢ = (Rᵢ, Nᵢ)` and `f : R₁ ⟶ R₂` and `g : R₂ ⟶ R₃` then
`(f ≫ g)^* N₃ ≅ g^* (f^* N₃)`
-/
def restriction_of_scalars.restrict_comp :
  restriction_of_scalars.bundled (f ≫ g) ≅
  @restriction_of_scalars.bundled M1 (@restriction_of_scalars.bundled M2 M3 g) f :=
{ hom := ⟨𝟙 _, 𝟙 _⟩,
  inv := ⟨𝟙 _, 𝟙 _⟩ }

end composition

section Module'

universe u
variable (A : CommRing.{u})

structure Module' :=
(pair : RingModulePair.{u})
(e : pair.R ≅ A)

namespace Module'

variable {A}
def M (M : Module' A) := M.pair.M
def R (M : Module' A) := M.pair.R


instance (A : CommRing.{u}) : has_coe_to_sort (Module' A) (Type u) :=
⟨λ M, M.M⟩

instance (M : Module' A) : module A M :=
begin
  haveI : algebra A M.R := M.e.inv.to_algebra,
  change module A (restrict_scalars A M.R M),
  apply_instance,
end

def morphism (M1 M2 : Module' A) := bundledMap M1.pair M2.pair

def morphism.id (M1 : Module' A) : bundledMap M1.pair M1.pair :=
⟨𝟙 M1.R, { to_fun := id, map_add' := λ _ _, rfl, map_smul' := λ _ _, rfl }⟩

def morphism.comp (M1 M2 M3 : Module' A) (f : morphism M1 M2) (g : morphism M2 M3) :
  morphism M1 M3 := bundledMap.comp _ _ _ f g

variable (A)
instance : category (Module' A) :=
{ hom := morphism,
  id := morphism.id,
  comp := λ M1 M2 M3 f g, morphism.comp M1 M2 M3 f g }.

end Module'

end Module'
