/-
Copyright (c) 2021 Luke Kershaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Kershaw
-/
import category_theory.additive.basic
import category_theory.shift
import category_theory.preadditive.additive_functor
import category_theory.triangulated.basic
import category_theory.triangulated.rotate

/-!
# Pretriangulated Categories

This file contains the definition of pretriangulated categories and triangulated functors
between them.

TODO: generalise this to n-angulated categories as in https://arxiv.org/abs/1006.4592
-/

noncomputable theory

open category_theory
open category_theory.preadditive

universes v v₀ v₁ v₂ u u₀ u₁ u₂

namespace category_theory.triangulated
open category_theory.category

/-
We work in an additive category `C` equipped with an additive shift.
-/
variables (C : Type u) [category.{v} C] [has_shift C] [additive_category C]
[functor.additive (shift C).functor] [functor.additive (shift C).inverse]

/--
An additive category `C` with an additive shift, and a class of "distinguished triangles"
relative to that shift is called pretriangulated if the following hold:
* Any triangle that is isomorphic to a distinguished triangle is also distinguished.
* Any triangle of the form `(X,X,0,id,0,0)` is distinguished.
* For any morphism `f : X ⟶ Y` there exists a distinguished triangle of the form `(X,Y,Z,f,g,h)`.
* The triangle `(X,Y,Z,f,g,h)` is distinguished if and only if `(Y,Z,X⟦1⟧,g,h,-f⟦1⟧)` is.
* Given a diagram:
  ```
        f       g       h
    X  ───> Y  ───> Z  ───> X⟦1⟧
    │       │                │
    │a      │b               │a⟦1⟧'
    V       V                V
    X' ───> Y' ───> Z' ───> X'⟦1⟧
        f'      g'      h'
  ```
  where the left square commutes, and whose rows are distinguished triangles,
  there exists a morphism `c : Z ⟶ Z'` such that `(a,b,c)` is a triangle morphism.
See https://stacks.math.columbia.edu/tag/0145
-/
class pretriangulated :=
(distinguished_triangles [] : set (triangle C))
(isomorphic_distinguished : Π (T₁ ∈ distinguished_triangles) (T₂ : triangle C) (T₁ ≅ T₂),
  T₂ ∈ distinguished_triangles)
(contractible_distinguished : Π (X : C), (contractible_triangle C X) ∈ distinguished_triangles)
(distinguished_cocone_triangle : Π (X Y : C) (f: X ⟶ Y), (∃ (Z : C) (g : Y ⟶ Z) (h : Z ⟶ X⟦1⟧),
  triangle.mk _ f g h ∈ distinguished_triangles))
(rotate_distinguished_triangle : Π (T : triangle C),
  T ∈ distinguished_triangles ↔ T.rotate ∈ distinguished_triangles)
(complete_distinguished_triangle_morphism : Π (T₁ T₂ : triangle C)
  (h₁ : T₁ ∈ distinguished_triangles) (h₂ : T₂ ∈ distinguished_triangles) (a : T₁.obj₁ ⟶ T₂.obj₁)
  (b : T₁.obj₂ ⟶ T₂.obj₂) (comm₁ : T₁.mor₁ ≫ b = a ≫ T₂.mor₁),
  (∃ (c : T₁.obj₃ ⟶ T₂.obj₃), (T₁.mor₂ ≫ c = b ≫ T₂.mor₂) ∧ (T₁.mor₃ ≫ a⟦1⟧' = c ≫ T₂.mor₃) ))

namespace pretriangulated
variables [pretriangulated C]

notation `dist_triang`:20 C := distinguished_triangles C
/--
Given any distinguished triangle `T`, then we know `T.rotate` is also distinguished.
-/
lemma rot_of_dist_triangle (T ∈ dist_triang C) : (T.rotate ∈ dist_triang C) :=
(rotate_distinguished_triangle T).mp H

/--
Given any distinguished triangle `T`, then we know `T.inv_rotate` is also distinguished.
-/
lemma inv_rot_of_dist_triangle (T ∈ dist_triang C) : (T.inv_rotate ∈ dist_triang C) :=
(rotate_distinguished_triangle (T.inv_rotate)).mpr
  (isomorphic_distinguished T H (T.inv_rotate.rotate) T (inv_rot_comp_rot.symm.app T))

/--
Given any distinguished triangle
```
      f       g       h
  X  ───> Y  ───> Z  ───> X⟦1⟧
```
the composition `f ≫ g = 0`.
See https://stacks.math.columbia.edu/tag/0146
-/
lemma comp_dist_triangle_mor_zero₁₂ (T ∈ dist_triang C) : T.mor₁ ≫ T.mor₂ = 0 :=
begin
  have h := contractible_distinguished T.obj₁,
  have f := complete_distinguished_triangle_morphism,
  specialize f (contractible_triangle C T.obj₁) T h H (𝟙 T.obj₁) T.mor₁,
  have t : (contractible_triangle C T.obj₁).mor₁ ≫ T.mor₁ = 𝟙 T.obj₁ ≫ T.mor₁,
    by refl,
  specialize f t,
  cases f with c f,
  rw ← f.left,
  simp only [limits.zero_comp, contractible_triangle_mor₂],
end -- TODO : tidy this proof up

/--
Given any distinguished triangle
```
      f       g       h
  X  ───> Y  ───> Z  ───> X⟦1⟧
```
the composition `g ≫ h = 0`.
See https://stacks.math.columbia.edu/tag/0146
-/
lemma comp_dist_triangle_mor_zero₂₃  (T ∈ dist_triang C) : T.mor₂ ≫ T.mor₃ = 0 :=
comp_dist_triangle_mor_zero₁₂ C T.rotate (rot_of_dist_triangle C T H)

/--
Given any distinguished triangle
```
      f       g       h
  X  ───> Y  ───> Z  ───> X⟦1⟧
```
the composition `h ≫ f⟦1⟧ = 0`.
See https://stacks.math.columbia.edu/tag/0146
-/
lemma comp_dist_triangle_mor_zero₃₁ (T ∈ dist_triang C) :
  T.mor₃ ≫ ((shift C).functor.map T.mor₁) = 0 :=
have H₂ : _ := rot_of_dist_triangle C T.rotate (rot_of_dist_triangle C T H),
by simpa using comp_dist_triangle_mor_zero₁₂ C (T.rotate.rotate) H₂

/-
TODO: If `C` is pretriangulated with respect to a shift,
then `Cᵒᵖ` is pretriangulated with respect to the inverse shift.
-/
end pretriangulated
end category_theory.triangulated

namespace category_theory.triangulated
namespace pretriangulated

variables (C : Type u₁) [category.{v₁} C] [has_shift C] [additive_category C]
[functor.additive (shift C).functor] [functor.additive (shift C).inverse]
variables (D : Type u₂) [category.{v₂} D] [has_shift D] [additive_category D]
[functor.additive (shift D).functor] [functor.additive (shift D).inverse]

/--
A triangulated functor between pretriangulated categories `C` and `D` is a functor `F : C ⥤ D`
together with given functorial isomorphisms `ξ X : F(X⟦1⟧) ⟶ F(X)⟦1⟧` with extra conditions
involving images of triangles.
-/
structure triangulated_functor_struct extends (C ⥤ D) :=
(nat_iso : (shift C).functor ⋙ to_functor ≅ to_functor ⋙ (shift D).functor)

instance : inhabited (triangulated_functor_struct C C) :=
⟨{ obj := λ X, X,
  map := λ _ _ f, f,
  nat_iso := by refl }⟩

variables {C D}
/--
Given a `triangulated_functor_struct` we can define a function from triangles of `C` to
triangles of `D`.
-/
@[simp]
def triangulated_functor_struct.map_triangle (F : triangulated_functor_struct C D)
  (T : triangle C) : triangle D :=
{ obj₁ := F.obj T.obj₁,
  obj₂ := F.obj T.obj₂,
  obj₃ := F.obj T.obj₃,
  mor₁ := F.map T.mor₁,
  mor₂ := F.map T.mor₂,
  mor₃ := F.map T.mor₃ ≫ F.nat_iso.hom.app T.obj₁ }

variables (C D)
/--
A triangulated functor between pretriangulated categories `C` and `D` is a functor `F : C ⥤ D`
together with given functorial isomorphisms `ξ X : F(X⟦1⟧) ⟶ F(X)⟦1⟧` such that for every
distinguished triangle `(X,Y,Z,f,g,h)` of `C`, the triangle
`(F(X), F(Y), F(Z), F(f), F(g), F(h) ≫ (ξ X))` is a distinguished triangle of `D`.
See https://stacks.math.columbia.edu/tag/014V
-/
structure triangulated_functor [pretriangulated C] [pretriangulated D] extends
  triangulated_functor_struct C D :=
(map_distinguished : Π (T: triangle C), (T ∈ dist_triang C) →
  (to_triangulated_functor_struct.map_triangle T ∈ dist_triang D) )

instance [pretriangulated C] : inhabited (triangulated_functor C C) :=
⟨{obj := λ X, X,
  map := λ _ _ f, f,
  nat_iso := by refl ,
  map_distinguished := begin
    rintros ⟨_,_,_,_⟩ Tdt,
    dsimp at *,
    rwa category.comp_id,
  end }⟩

end pretriangulated
end category_theory.triangulated
