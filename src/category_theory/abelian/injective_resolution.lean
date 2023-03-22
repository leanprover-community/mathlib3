/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Scott Morrison
-/
import algebra.homology.quasi_iso
import category_theory.preadditive.injective_resolution
import category_theory.abelian.homology
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

* `category_theory.exact_f_d`: `f` and `injective.d f` are exact.
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
  (abelian.exact.op _ _ J.exact₀) (by simp [←category.assoc, desc_f_zero])

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
  (J.cocomplex.d (n+1) (n+2)) (abelian.exact.op _ _ (J.exact _))
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
exact.desc (f.f 0) (I.ι.f 0) (I.cocomplex.d 0 1) (abelian.exact.op _ _ I.exact₀)
  (congr_fun (congr_arg homological_complex.hom.f comm) 0)

/-- An auxiliary definition for `desc_homotopy_zero`. -/
def desc_homotopy_zero_one {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
  (f : I.cocomplex ⟶ J.cocomplex)
  (comm : I.ι ≫ f = (0 : _ ⟶ J.cocomplex)) : I.cocomplex.X 2 ⟶ J.cocomplex.X 1 :=
exact.desc (f.f 1 - desc_homotopy_zero_zero f comm ≫ J.cocomplex.d 0 1)
  (I.cocomplex.d 0 1) (I.cocomplex.d 1 2) (abelian.exact.op _ _ (I.exact _))
  (by simp [desc_homotopy_zero_zero, ←category.assoc])

/-- An auxiliary definition for `desc_homotopy_zero`. -/
def desc_homotopy_zero_succ {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
  (f : I.cocomplex ⟶ J.cocomplex) (n : ℕ)
  (g : I.cocomplex.X (n + 1) ⟶ J.cocomplex.X n)
  (g' : I.cocomplex.X (n + 2) ⟶ J.cocomplex.X (n + 1))
  (w : f.f (n + 1) = I.cocomplex.d (n+1) (n+2) ≫ g' + g ≫ J.cocomplex.d n (n+1)) :
  I.cocomplex.X (n + 3) ⟶ J.cocomplex.X (n + 2) :=
exact.desc (f.f (n+2) - g' ≫ J.cocomplex.d _ _) (I.cocomplex.d (n+1) (n+2))
  (I.cocomplex.d (n+2) (n+3)) (abelian.exact.op _ _ (I.exact _))
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
by apply desc_homotopy (𝟙 X); simp

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

section
variables [abelian C]

/-- An arbitrarily chosen injective resolution of an object. -/
abbreviation injective_resolution (Z : C) [has_injective_resolution Z] : cochain_complex C ℕ :=
(has_injective_resolution.out Z).some.cocomplex

/-- The cochain map from cochain complex consisting of `Z` supported in degree `0`
back to the arbitrarily chosen injective resolution `injective_resolution Z`. -/
abbreviation injective_resolution.ι (Z : C) [has_injective_resolution Z] :
  (cochain_complex.single₀ C).obj Z ⟶ injective_resolution Z :=
(has_injective_resolution.out Z).some.ι

/-- The descent of a morphism to a cochain map between the arbitrarily chosen injective resolutions.
-/
abbreviation injective_resolution.desc {X Y : C} (f : X ⟶ Y)
  [has_injective_resolution X] [has_injective_resolution Y] :
  injective_resolution X ⟶ injective_resolution Y :=
InjectiveResolution.desc f _ _

variables (C) [has_injective_resolutions C]

/--
Taking injective resolutions is functorial,
if considered with target the homotopy category
(`ℕ`-indexed cochain complexes and chain maps up to homotopy).
-/
def injective_resolutions : C ⥤ homotopy_category C (complex_shape.up ℕ) :=
{ obj := λ X, (homotopy_category.quotient _ _).obj (injective_resolution X),
  map := λ X Y f, (homotopy_category.quotient _ _).map (injective_resolution.desc f),
  map_id' := λ X, begin
    rw ←(homotopy_category.quotient _ _).map_id,
    apply homotopy_category.eq_of_homotopy,
    apply InjectiveResolution.desc_id_homotopy,
  end,
  map_comp' := λ X Y Z f g, begin
    rw ←(homotopy_category.quotient _ _).map_comp,
    apply homotopy_category.eq_of_homotopy,
    apply InjectiveResolution.desc_comp_homotopy,
  end, }

end

section

variables [abelian C] [enough_injectives C]

lemma exact_f_d {X Y : C} (f : X ⟶ Y) : exact f (d f) :=
(abelian.exact_iff _ _).2 $
  ⟨by simp, zero_of_comp_mono (ι _) $ by rw [category.assoc, kernel.condition]⟩

end

namespace InjectiveResolution
/-!
Our goal is to define `InjectiveResolution.of Z : InjectiveResolution Z`.
The `0`-th object in this resolution will just be `injective.under Z`,
i.e. an arbitrarily chosen injective object with a map from `Z`.
After that, we build the `n+1`-st object as `injective.syzygies`
applied to the previously constructed morphism,
and the map from the `n`-th object as `injective.d`.
-/

variables [abelian C] [enough_injectives C]

/-- Auxiliary definition for `InjectiveResolution.of`. -/
@[simps]
def of_cocomplex (Z : C) : cochain_complex C ℕ :=
cochain_complex.mk'
  (injective.under Z) (injective.syzygies (injective.ι Z)) (injective.d (injective.ι Z))
  (λ ⟨X, Y, f⟩, ⟨injective.syzygies f, injective.d f, (exact_f_d f).w⟩)

/--
In any abelian category with enough injectives,
`InjectiveResolution.of Z` constructs an injective resolution of the object `Z`.
-/
@[irreducible] def of (Z : C) : InjectiveResolution Z :=
{ cocomplex := of_cocomplex Z,
  ι := cochain_complex.mk_hom _ _ (injective.ι Z) 0
    (by { simp only [of_cocomplex_d, eq_self_iff_true, eq_to_hom_refl, category.comp_id,
      dite_eq_ite, if_true, comp_zero],
      exact (exact_f_d (injective.ι Z)).w, } ) (λ n _, ⟨0, by ext⟩),
  injective := by { rintros (_|_|_|n); { apply injective.injective_under, } },
  exact₀ := by simpa using exact_f_d (injective.ι Z),
  exact := by { rintros (_|n); { simp, apply exact_f_d } },
  mono := injective.ι_mono Z }

@[priority 100]
instance (Z : C) : has_injective_resolution Z :=
{ out := ⟨of Z⟩ }

@[priority 100]
instance : has_injective_resolutions C :=
{ out := λ _, infer_instance }

end InjectiveResolution
end category_theory
namespace homological_complex.hom

variables {C : Type u} [category.{v} C] [abelian C]

/-- If `X` is a cochain complex of injective objects and we have a quasi-isomorphism
`f : Y[0] ⟶ X`, then `X` is an injective resolution of `Y.` -/
def homological_complex.hom.from_single₀_InjectiveResolution (X : cochain_complex C ℕ) (Y : C)
  (f : (cochain_complex.single₀ C).obj Y ⟶ X) [quasi_iso f]
  (H : ∀ n, injective (X.X n)) :
  InjectiveResolution Y :=
{ cocomplex := X,
  ι := f,
  injective := H,
  exact₀ := f.from_single₀_exact_f_d_at_zero,
  exact := f.from_single₀_exact_at_succ,
  mono := f.from_single₀_mono_at_zero }

end homological_complex.hom
