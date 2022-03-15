/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Scott Morrison
-/
import category_theory.preadditive.injective_resolution
import category_theory.abelian.exact
import algebra.homology.homotopy_category

/-!
# Main result

When the underlying category is abelian:
* `category_theory.InjectiveResolution.desc`: Given `I : InjectiveResolution X` and
  `J : InjectiveResolution Y`, any morphism `X ⟶ Y` admits a descent to a chain map
  `J.cocomplex ⟶ I.cocomplex`. It is a descent in the sense that `I.ι` intertwine the descent and
  the original morphism, see `category_theory.InjectiveResolution.desc_commutes`.
* `category_theory.InjectiveResolution.desc_homotopy`: Any two such descents are homotopic.
* `category_theory.InjectiveResolution.homotopy_equiv`: Any two injective resolutions of the same
  object are homotopy equivalent.
* `category_theory.injective_resolutions`: If every object admits an injective resolution, we can
  construct a functor `injective_resolutions C : C ⥤ homotopy_category C`.

* `category_theory.injective.exact_d_f`: `f` and `injective.d f` are exact.
* `category_theory.InjectiveResolution.of`: Hence, starting from a monomorphism `X ⟶ J`, where `J`
  is injective, we can apply `injective.d` repeatedly to obtain an injective resolution of `X`.
-/

noncomputable theory

open category_theory
open category_theory.limits

universes v u

namespace category_theory
variables {C : Type u} [category.{v} C]

open injective

namespace InjectiveResolution
section
variables [has_zero_morphisms C] [has_zero_object C] [has_equalizers C] [has_images C]
/-- Auxiliary construction for `desc`. -/
def desc_f_zero {Y Z : C} (f : Z ⟶ Y) (I : InjectiveResolution Y) (J : InjectiveResolution Z) :
  J.cocomplex.X 0 ⟶ I.cocomplex.X 0 :=
factor_thru (f ≫ I.ι.f 0) (J.ι.f 0)

end

section abelian
variables [abelian C]
/-- Auxiliary construction for `desc`. -/
def desc_f_one {Y Z : C}
  (f : Z ⟶ Y) (I : InjectiveResolution Y) (J : InjectiveResolution Z) :
  J.cocomplex.X 1 ⟶ I.cocomplex.X 1 :=
exact.desc (desc_f_zero f I J ≫ I.cocomplex.d 0 1) (J.ι.f 0) (J.cocomplex.d 0 1)
  (by simp [←category.assoc, desc_f_zero])

@[simp] lemma desc_f_one_zero_comm {Y Z : C}
  (f : Z ⟶ Y) (I : InjectiveResolution Y) (J : InjectiveResolution Z) :
  J.cocomplex.d 0 1 ≫ desc_f_one f I J = desc_f_zero f I J ≫ I.cocomplex.d 0 1 :=
by simp [desc_f_zero, desc_f_one]

/-- Auxiliary construction for `desc`. -/
def desc_f_succ {Y Z : C}
  (I : InjectiveResolution Y) (J : InjectiveResolution Z)
  (n : ℕ) (g : J.cocomplex.X n ⟶ I.cocomplex.X n) (g' : J.cocomplex.X (n+1) ⟶ I.cocomplex.X (n+1))
  (w : J.cocomplex.d n (n+1) ≫ g' = g ≫ I.cocomplex.d n (n+1)) :
  Σ' g'' : J.cocomplex.X (n+2) ⟶ I.cocomplex.X (n+2),
    J.cocomplex.d (n+1) (n+2) ≫ g'' = g' ≫ I.cocomplex.d (n+1) (n+2) :=
⟨@exact.desc C _ _ _ _ _ _ _ _ _
  (g' ≫ I.cocomplex.d (n+1) (n+2))
  (J.cocomplex.d n (n+1))
  (J.cocomplex.d (n+1) (n+2)) _
  (by simp [←category.assoc, w]), (by simp)⟩

/-- A morphism in `C` descents to a chain map between injective resolutions. -/
def desc {Y Z : C}
  (f : Z ⟶ Y) (I : InjectiveResolution Y) (J : InjectiveResolution Z) :
  J.cocomplex ⟶ I.cocomplex :=
begin
  fapply cochain_complex.mk_hom,
  apply desc_f_zero f,
  apply desc_f_one f,
  symmetry,
  apply desc_f_one_zero_comm f,
  rintro n ⟨g, g', w⟩,
  obtain ⟨g'', eq1⟩ := desc_f_succ I J n g g' w.symm,
  refine ⟨g'', eq1.symm⟩,
end

/-- The resolution maps intertwine the descent of a morphism and that morphism. -/
@[simp, reassoc]
lemma desc_commutes {Y Z : C}
  (f : Z ⟶ Y) (I : InjectiveResolution Y) (J : InjectiveResolution Z) :
  J.ι ≫ desc f I J = (cochain_complex.single₀ C).map f ≫ I.ι :=
begin
  ext n,
  rcases n with (_|_|n),
  { dsimp [desc, desc_f_zero], simp, },
  { dsimp [desc, desc_f_one], simp, },
  { dsimp, simp, },
end

-- Now that we've checked this property of the descent,
-- we can seal away the actual definition.
attribute [irreducible] desc

end abelian

end InjectiveResolution

end category_theory
