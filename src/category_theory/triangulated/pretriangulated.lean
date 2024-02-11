/-
Copyright (c) 2021 Luke Kershaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Kershaw
-/
import category_theory.preadditive.additive_functor
import category_theory.shift.basic
import category_theory.triangulated.rotate

/-!
# Pretriangulated Categories

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains the definition of pretriangulated categories and triangulated functors
between them.

## Implementation Notes

We work under the assumption that pretriangulated categories are preadditive categories,
but not necessarily additive categories, as is assumed in some sources.

TODO: generalise this to n-angulated categories as in https://arxiv.org/abs/1006.4592
-/

noncomputable theory

open category_theory
open category_theory.preadditive
open category_theory.limits

universes v v₀ v₁ v₂ u u₀ u₁ u₂

namespace category_theory
open category pretriangulated

/-
We work in a preadditive category `C` equipped with an additive shift.
-/
variables (C : Type u) [category.{v} C] [has_zero_object C] [has_shift C ℤ] [preadditive C]
  [∀ n : ℤ, functor.additive (shift_functor C n)]
variables (D : Type u₂) [category.{v₂} D] [has_zero_object D] [has_shift D ℤ] [preadditive D]
  [∀ n : ℤ, functor.additive (shift_functor D n)]

/--
A preadditive category `C` with an additive shift, and a class of "distinguished triangles"
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

See <https://stacks.math.columbia.edu/tag/0145>
-/
class pretriangulated :=
(distinguished_triangles [] : set (triangle C))
(isomorphic_distinguished : Π (T₁ ∈ distinguished_triangles) (T₂ ≅ T₁),
  T₂ ∈ distinguished_triangles)
(contractible_distinguished : Π (X : C), (contractible_triangle X) ∈ distinguished_triangles)
(distinguished_cocone_triangle : Π (X Y : C) (f : X ⟶ Y), (∃ (Z : C) (g : Y ⟶ Z)
  (h : Z ⟶ X⟦(1:ℤ)⟧),
  triangle.mk f g h ∈ distinguished_triangles))
(rotate_distinguished_triangle : Π (T : triangle C),
  T ∈ distinguished_triangles ↔ T.rotate ∈ distinguished_triangles)
(complete_distinguished_triangle_morphism : Π (T₁ T₂ : triangle C)
  (h₁ : T₁ ∈ distinguished_triangles) (h₂ : T₂ ∈ distinguished_triangles) (a : T₁.obj₁ ⟶ T₂.obj₁)
  (b : T₁.obj₂ ⟶ T₂.obj₂) (comm₁ : T₁.mor₁ ≫ b = a ≫ T₂.mor₁),
  (∃ (c : T₁.obj₃ ⟶ T₂.obj₃), (T₁.mor₂ ≫ c = b ≫ T₂.mor₂) ∧ (T₁.mor₃ ≫ a⟦1⟧' = c ≫ T₂.mor₃) ))

namespace pretriangulated
variables [hC : pretriangulated C]

include hC

notation `dist_triang `:20 C := distinguished_triangles C
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
  (isomorphic_distinguished T H T.inv_rotate.rotate (inv_rot_comp_rot.app T))

/--
Given any distinguished triangle
```
      f       g       h
  X  ───> Y  ───> Z  ───> X⟦1⟧
```
the composition `f ≫ g = 0`.
See <https://stacks.math.columbia.edu/tag/0146>
-/
lemma comp_dist_triangle_mor_zero₁₂ (T ∈ dist_triang C) : T.mor₁ ≫ T.mor₂ = 0 :=
begin
  obtain ⟨c, hc⟩ := complete_distinguished_triangle_morphism _ _
    (contractible_distinguished T.obj₁) H (𝟙 T.obj₁) T.mor₁ rfl,
  simpa only [contractible_triangle_mor₂, zero_comp] using hc.left.symm,
end

/--
Given any distinguished triangle
```
      f       g       h
  X  ───> Y  ───> Z  ───> X⟦1⟧
```
the composition `g ≫ h = 0`.
See <https://stacks.math.columbia.edu/tag/0146>
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
See <https://stacks.math.columbia.edu/tag/0146>
-/
lemma comp_dist_triangle_mor_zero₃₁ (T ∈ dist_triang C) :
  T.mor₃ ≫ ((shift_equiv C 1).functor.map T.mor₁) = 0 :=
have H₂ : _ := rot_of_dist_triangle C T.rotate (rot_of_dist_triangle C T H),
by simpa using comp_dist_triangle_mor_zero₁₂ C (T.rotate.rotate) H₂

/-
TODO: If `C` is pretriangulated with respect to a shift,
then `Cᵒᵖ` is pretriangulated with respect to the inverse shift.
-/

end pretriangulated
end category_theory
