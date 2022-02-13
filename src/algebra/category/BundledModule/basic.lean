/-
Copyright (c) 2021 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import algebra.category.Module.basic
import algebra.category.CommRing.basic
import category_theory.category.basic

/-!
# The category of bundled module

`BundledModule.{u}` is the category of pairs of the shape `(R, M)` where `R` is
a ring in universe u and `M` is an `R`-module. A morphism between `M1 = (R, M)`
and `M2 = (S, N)` is a pair of morphism `(f, g)` where `f : R ⟶ S` is a ring
homomorphism and `g : M ⟶ f* N` is a module homomorphism (linear map).
-/

open category_theory

section restriction_of_scalars

universe u

variables {R S : Ring.{u}} (f : R ⟶ S)
include f

/--Definition of scalar multiplication in restriction of scalars-/
@[reducible] def restriction_of_scalar.has_scalar (N : Module S) : has_scalar R N :=
{ smul := λ r n,  f r • n}

local attribute [instance] restriction_of_scalar.has_scalar

/--
Given a ring homomorphism `f : R ⟶ S`, and an `S`-module `N`, we can turn `N` into an `R`-module.
This is called restriction_of_scalar
-/
@[reducible] def restriction_of_scalar.module (N : Module S) :
  Module R :=
{ carrier := N,
  is_module :=
  { one_smul := λ b, begin
      unfold has_scalar.smul,
      rw [ring_hom.map_one, one_smul],
    end,
    mul_smul := λ _ _ _, begin
      unfold has_scalar.smul,
      rw [ring_hom.map_mul, mul_smul],
    end,
    smul_add := λ _ _ _,by { unfold has_scalar.smul, rw [smul_add] },
    smul_zero := λ _, by { unfold has_scalar.smul, rw [smul_zero] },
    add_smul := λ _ _ _, begin
      unfold has_scalar.smul,
      rw [ring_hom.map_add, add_smul],
    end,
    zero_smul := λ _, begin
      unfold has_scalar.smul,
      rw [ring_hom.map_zero, zero_smul],
    end,
    ..(restriction_of_scalar.has_scalar f N) } }

instance restriction_of_scalar.has_scalar' (N : Module S) :
  has_scalar S (restriction_of_scalar.module f N) :=
{ smul := λ r n, r • n }

@[simp] lemma restriction_of_scalar.smul_def' (r : R) (N : Module S)
  (n : restriction_of_scalar.module f N) :
  (r • n) = (f r • n) := rfl

/--restrictino of scalar is a functor from `S`-modules to `R`-modules.-/
def restriction_of_scalar.functor : Module S ⥤ Module R :=
{ obj := restriction_of_scalar.module f,
  map := λ N₁ N₂ l,
    { to_fun := l,
      map_add' := λ x y, by rw [linear_map.map_add],
      map_smul' := λ r y, begin
        simp only [restriction_of_scalar.smul_def', ring_hom.id_apply],
        convert linear_map.map_smul l (f r) y,
      end } }

end restriction_of_scalars

section BundledModule

universe u

/--
A bundled module is a pair `(R, M)` such that `R : Ring` and `M` is an `R`-module.
-/
@[nolint has_inhabited_instance]
structure BundledModule : Type (u+1) :=
(R : Ring.{u})
(M : Module.{u} R.α)

variables {M1 M2 : BundledModule} (f : M1.R ⟶ M2.R)
include f

/--
Given bundled modules `(R, M)` and `(S, N)` and a ring homomorphism `f : R ⟶ S`, there is
a bundled module `(R, N)` given by restriction of scalars.
-/
def restriction_of_scalar.bundled : BundledModule :=
{ R := M1.R,
  M := restriction_of_scalar.module f M2.M }

local notation f `*` M2 := restriction_of_scalar.bundled f

@[simp] lemma restriction_of_scalar.R :
  (f* M2).R = M1.R := rfl

@[simp] lemma restriction_of_scalar.M :
  (f* M2).M = restriction_of_scalar.module f M2.M := rfl

omit f
/--
A morphism between two bundled module `M1, M2` is a pair of morphism `(f, g)` such that
`f` is a ring homomorphism from `M1.R` to `M2.R` and `g` is a linear map from `M1.M` to `(f* M2).M`
-/
@[nolint has_inhabited_instance]
def bundledMap (M1 M2 : BundledModule) : Type u :=
Σ (f : M1.R ⟶ M2.R), M1.M ⟶ (f* M2).M

@[ext] lemma bundledMap.ext {M1 M2 : BundledModule} (f1 f2 : bundledMap M1 M2) :
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

instance BundledModule.is_cat : category BundledModule :=
{ hom := λ M1 M2, bundledMap M1 M2,
  id := λ M, ⟨𝟙 M.R, { to_fun := λ m, m,
                       map_add' := λ _ _, rfl,
                       map_smul' := λ _ _, rfl }⟩,
  comp := λ M1 M2 M3 f g,
    ⟨f.1 ≫ g.1,
     { to_fun := λ m, g.2 (f.2 m),
       map_add' := λ m1 m2, by simp only [linear_map.map_add],
       map_smul' := λ r m, begin
        rcases f with ⟨f, f'⟩,
        rcases g with ⟨g, g'⟩,
        dsimp only,
        rw [ring_hom.id_apply, linear_map.map_smulₛₗ, ring_hom.id_apply,
          restriction_of_scalar.smul_def', restriction_of_scalar.smul_def', comp_apply],
        convert linear_map.map_smul g' (f r) (f' m),
      end }⟩,
  comp_id' := λ M1 M2 f, begin
    ext, refl, rw heq_iff_eq, ext, refl,
  end,
  id_comp' := λ M1 M2 f, begin
    ext, refl, rw heq_iff_eq, ext, refl,
  end }

/-- the forgetful functor from `BundledModule` to `Ring`-/
def BundledModule.forget : BundledModule ⥤ Ring :=
{ obj := λ M, M.R,
  map := λ M1 M2 f, f.1 }

end BundledModule

section composition

universe u
variables {M1 M2 M3 : BundledModule.{u}} (f : M1.R ⟶ M2.R) (g : M2.R ⟶ M3.R)
include f g

/--
If `Mᵢ = (Rᵢ, Nᵢ)` and `f : R₁ ⟶ R₂` and `g : R₂ ⟶ R₃` then
`(f ≫ g)* N₃ ≅ g* (f* N₃)`
-/
def restriction_of_scalar.restrict_comp :
  restriction_of_scalar.bundled (f ≫ g) ≅
  @restriction_of_scalar.bundled M1 (@restriction_of_scalar.bundled M2 M3 g) f :=
{ hom := ⟨𝟙 _, 𝟙 _⟩,
  inv := ⟨𝟙 _, 𝟙 _⟩ }

end composition
