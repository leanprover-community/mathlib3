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
  `J.cocomplex ⟶ I.cocomplex`. It is a descent in the sense that `I.ι` intertwines the descent and
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

/-- A morphism in `C` descends to a chain map between injective resolutions. -/
def desc {Y Z : C}
  (f : Z ⟶ Y) (I : InjectiveResolution Y) (J : InjectiveResolution Z) :
  J.cocomplex ⟶ I.cocomplex :=
cochain_complex.mk_hom _ _ (desc_f_zero f _ _) (desc_f_one f _ _)
  (desc_f_one_zero_comm f I J).symm
  (λ n ⟨g, g', w⟩, ⟨(desc_f_succ I J n g g' w.symm).1, (desc_f_succ I J n g g' w.symm).2.symm⟩)

/-- The resolution maps intertwine the descent of a morphism and that morphism. -/
@[simp, reassoc]
lemma desc_commutes {Y Z : C}
  (f : Z ⟶ Y) (I : InjectiveResolution Y) (J : InjectiveResolution Z) :
  J.ι ≫ desc f I J = (cochain_complex.single₀ C).map f ≫ I.ι :=
begin
  ext n,
  rcases n with (_|_|n);
  { dsimp [desc, desc_f_one, desc_f_zero], simp, },
end

-- Now that we've checked this property of the descent,
-- we can seal away the actual definition.
attribute [irreducible] desc

/-- An auxiliary definition for `desc_homotopy_zero`. -/
def desc_homotopy_zero_zero {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
  (f : I.cocomplex ⟶ J.cocomplex)
  (comm : I.ι ≫ f = 0) : I.cocomplex.X 1 ⟶ J.cocomplex.X 0 :=
exact.desc (f.f 0) (I.ι.f 0) (I.cocomplex.d 0 1)
  (congr_fun (congr_arg homological_complex.hom.f comm) 0)

/-- An auxiliary definition for `desc_homotopy_zero`. -/
def desc_homotopy_zero_one {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
  (f : I.cocomplex ⟶ J.cocomplex)
  (comm : I.ι ≫ f = (0 : _ ⟶ J.cocomplex)) : I.cocomplex.X 2 ⟶ J.cocomplex.X 1 :=
exact.desc (f.f 1 - desc_homotopy_zero_zero f comm ≫ J.cocomplex.d 0 1)
  (I.cocomplex.d 0 1) (I.cocomplex.d 1 2)
  (by simp [desc_homotopy_zero_zero, ←category.assoc])

/-- An auxiliary definition for `desc_homotopy_zero`. -/
def desc_homotopy_zero_succ {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
  (f : I.cocomplex ⟶ J.cocomplex) (n : ℕ)
  (g : I.cocomplex.X (n + 1) ⟶ J.cocomplex.X n)
  (g' : I.cocomplex.X (n + 2) ⟶ J.cocomplex.X (n + 1))
  (w : f.f (n + 1) = I.cocomplex.d (n+1) (n+2) ≫ g' + g ≫ J.cocomplex.d n (n+1)) :
  I.cocomplex.X (n + 3) ⟶ J.cocomplex.X (n + 2) :=
exact.desc (f.f (n+2) - g' ≫ J.cocomplex.d _ _) (I.cocomplex.d (n+1) (n+2))
  (I.cocomplex.d (n+2) (n+3))
  (by simp [preadditive.comp_sub, ←category.assoc, preadditive.sub_comp,
        show I.cocomplex.d (n+1) (n+2) ≫ g' = f.f (n + 1) - g ≫ J.cocomplex.d n (n+1),
        by {rw w, simp only [add_sub_cancel] } ])

/-- Any descent of the zero morphism is homotopic to zero. -/
def desc_homotopy_zero {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
  (f : I.cocomplex ⟶ J.cocomplex)
  (comm : I.ι ≫ f = 0) :
  homotopy f 0 :=
homotopy.mk_coinductive _ (desc_homotopy_zero_zero f comm) (by simp [desc_homotopy_zero_zero])
  (desc_homotopy_zero_one f comm) (by simp [desc_homotopy_zero_one])
  (λ n ⟨g, g', w⟩, ⟨desc_homotopy_zero_succ f n g g' (by simp only [w, add_comm]),
    by simp [desc_homotopy_zero_succ, w]⟩)

/-- Two descents of the same morphism are homotopic. -/
def desc_homotopy {Y Z : C} (f : Y ⟶ Z) {I : InjectiveResolution Y} {J : InjectiveResolution Z}
  (g h : I.cocomplex ⟶ J.cocomplex)
  (g_comm : I.ι ≫ g = (cochain_complex.single₀ C).map f ≫ J.ι)
  (h_comm : I.ι ≫ h = (cochain_complex.single₀ C).map f ≫ J.ι) :
  homotopy g h :=
homotopy.equiv_sub_zero.inv_fun (desc_homotopy_zero _ (by simp [g_comm, h_comm]))

/-- The descent of the identity morphism is homotopic to the identity cochain map. -/
def desc_id_homotopy (X : C) (I : InjectiveResolution X) :
  homotopy (desc (𝟙 X) I I) (𝟙 I.cocomplex) :=
by { apply desc_homotopy (𝟙 X); simp, }

/-- The descent of a composition is homotopic to the composition of the descents. -/
def desc_comp_homotopy {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  (I : InjectiveResolution X) (J : InjectiveResolution Y) (K : InjectiveResolution Z) :
  homotopy (desc (f ≫ g) K I) (desc f J I ≫ desc g K J)  :=
by apply desc_homotopy (f ≫ g); simp

-- We don't care about the actual definitions of these homotopies.
attribute [irreducible] desc_homotopy_zero desc_homotopy desc_id_homotopy desc_comp_homotopy

/-- Any two injective resolutions are homotopy equivalent. -/
def homotopy_equiv {X : C} (I J : InjectiveResolution X) :
  homotopy_equiv I.cocomplex J.cocomplex :=
{ hom := desc (𝟙 X) J I,
  inv := desc (𝟙 X) I J,
  homotopy_hom_inv_id := (desc_comp_homotopy (𝟙 X) (𝟙 X) I J I).symm.trans $
    by simpa [category.id_comp] using desc_id_homotopy _ _,
  homotopy_inv_hom_id := (desc_comp_homotopy (𝟙 X) (𝟙 X) J I J).symm.trans $
    by simpa [category.id_comp] using desc_id_homotopy _ _ }

@[simp, reassoc] lemma homotopy_equiv_hom_ι {X : C} (I J : InjectiveResolution X) :
  I.ι ≫ (homotopy_equiv I J).hom = J.ι :=
by simp [homotopy_equiv]

@[simp, reassoc] lemma homotopy_equiv_inv_ι {X : C} (I J : InjectiveResolution X) :
  J.ι ≫ (homotopy_equiv I J).inv = I.ι :=
by simp [homotopy_equiv]

end abelian

end InjectiveResolution

end category_theory
