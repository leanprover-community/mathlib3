/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Scott Morrison
-/
import category_theory.abelian.injective_resolution
import algebra.homology.additive
import category_theory.limits.constructions.epi_mono
import category_theory.abelian.homology
import category_theory.abelian.exact

/-!
# Right-derived functors

We define the right-derived functors `F.right_derived n : C ⥤ D` for any additive functor `F`
out of a category with injective resolutions.

The definition is
```
injective_resolutions C ⋙ F.map_homotopy_category _ ⋙ homotopy_category.homology_functor D _ n
```
that is, we pick an injective resolution (thought of as an object of the homotopy category),
we apply `F` objectwise, and compute `n`-th homology.

We show that these right-derived functors can be calculated
on objects using any choice of injective resolution,
and on morphisms by any choice of lift to a cochain map between chosen injective resolutions.

Similarly we define natural transformations between right-derived functors coming from
natural transformations between the original additive functors,
and show how to compute the components.

## Main results
* `category_theory.functor.right_derived_obj_injective_zero`: the `0`-th derived functor of `F` on
  an injective object `X` is isomorphic to `F.obj X`.
* `category_theory.functor.right_derived_obj_injective_succ`: injective objects have no higher
  right derived functor.
* `category_theory.nat_trans.right_derived`: the natural isomorphism between right derived functors
  induced by natural transformation.

Now, we assume `preserves_finite_limits F`, then
* `category_theory.abelian.functor.preserves_exact_of_preserves_finite_limits_of_mono`: if `f` is
  mono and `exact f g`, then `exact (F.map f) (F.map g)`.
* `category_theory.abelian.functor.right_derived_zero_iso_self`: if there are enough injectives,
  then there is a natural isomorphism `(F.right_derived 0) ≅ F`.
-/

noncomputable theory

open category_theory
open category_theory.limits


namespace category_theory
universes v u
variables {C : Type u} [category.{v} C] {D : Type*} [category D]
variables [abelian C] [has_injective_resolutions C] [abelian D]

/-- The right derived functors of an additive functor. -/
def functor.right_derived (F : C ⥤ D) [F.additive] (n : ℕ) : C ⥤ D :=
injective_resolutions C ⋙ F.map_homotopy_category _ ⋙ homotopy_category.homology_functor D _ n

/-- We can compute a right derived functor using a chosen injective resolution. -/
@[simps]
def functor.right_derived_obj_iso (F : C ⥤ D) [F.additive] (n : ℕ)
  {X : C} (P : InjectiveResolution X) :
  (F.right_derived n).obj X ≅
    (homology_functor D _ n).obj ((F.map_homological_complex _).obj P.cocomplex) :=
(homotopy_category.homology_functor D _ n).map_iso
  (homotopy_category.iso_of_homotopy_equiv
    (F.map_homotopy_equiv (InjectiveResolution.homotopy_equiv _ P)))
  ≪≫ (homotopy_category.homology_factors D _ n).app _

/-- The 0-th derived functor of `F` on an injective object `X` is just `F.obj X`. -/
@[simps]
def functor.right_derived_obj_injective_zero (F : C ⥤ D) [F.additive]
  (X : C) [injective X] :
  (F.right_derived 0).obj X ≅ F.obj X :=
F.right_derived_obj_iso 0 (InjectiveResolution.self X) ≪≫
  (homology_functor _ _ _).map_iso ((cochain_complex.single₀_map_homological_complex F).app X) ≪≫
  (cochain_complex.homology_functor_0_single₀ D).app (F.obj X)

open_locale zero_object

/-- The higher derived functors vanish on injective objects. -/
@[simps]
def functor.right_derived_obj_injective_succ (F : C ⥤ D) [F.additive] (n : ℕ)
  (X : C) [injective X] :
  (F.right_derived (n+1)).obj X ≅ 0 :=
F.right_derived_obj_iso (n+1) (InjectiveResolution.self X) ≪≫
  (homology_functor _ _ _).map_iso ((cochain_complex.single₀_map_homological_complex F).app X) ≪≫
  (cochain_complex.homology_functor_succ_single₀ D n).app (F.obj X)
/--
We can compute a right derived functor on a morphism using a descent of that morphism
to a cochain map between chosen injective resolutions.
-/
lemma functor.right_derived_map_eq (F : C ⥤ D) [F.additive] (n : ℕ) {X Y : C} (f : Y ⟶ X)
  {P : InjectiveResolution X} {Q : InjectiveResolution Y} (g : Q.cocomplex ⟶ P.cocomplex)
  (w : Q.ι ≫ g = (cochain_complex.single₀ C).map f ≫ P.ι) :
  (F.right_derived n).map f =
  (F.right_derived_obj_iso n Q).hom ≫
    (homology_functor D _ n).map ((F.map_homological_complex _).map g) ≫
    (F.right_derived_obj_iso n P).inv :=
begin
  dsimp only [functor.right_derived, functor.right_derived_obj_iso],
  dsimp, simp only [category.comp_id, category.id_comp],
  rw [←homology_functor_map, homotopy_category.homology_functor_map_factors],
  simp only [←functor.map_comp],
  congr' 1,
  apply homotopy_category.eq_of_homotopy,
  apply functor.map_homotopy,
  apply homotopy.trans,
  exact homotopy_category.homotopy_out_map _,
  apply InjectiveResolution.desc_homotopy f,
  { simp, },
  { simp only [InjectiveResolution.homotopy_equiv_hom_ι_assoc],
    rw [←category.assoc, w, category.assoc],
    simp only [InjectiveResolution.homotopy_equiv_inv_ι], },
end

/-- The natural transformation between right-derived functors induced by a natural transformation.-/
@[simps]
def nat_trans.right_derived {F G : C ⥤ D} [F.additive] [G.additive] (α : F ⟶ G) (n : ℕ) :
  F.right_derived n ⟶ G.right_derived n :=
whisker_left (injective_resolutions C)
  (whisker_right (nat_trans.map_homotopy_category α _)
    (homotopy_category.homology_functor D _ n))

@[simp] lemma nat_trans.right_derived_id (F : C ⥤ D) [F.additive] (n : ℕ) :
  nat_trans.right_derived (𝟙 F) n = 𝟙 (F.right_derived n) :=
by { simp [nat_trans.right_derived], refl, }

@[simp, nolint simp_nf] lemma nat_trans.right_derived_comp
  {F G H : C ⥤ D} [F.additive] [G.additive] [H.additive]
  (α : F ⟶ G) (β : G ⟶ H) (n : ℕ) :
  nat_trans.right_derived (α ≫ β) n = nat_trans.right_derived α n ≫ nat_trans.right_derived β n :=
by simp [nat_trans.right_derived]

/--
A component of the natural transformation between right-derived functors can be computed
using a chosen injective resolution.
-/
lemma nat_trans.right_derived_eq {F G : C ⥤ D} [F.additive] [G.additive] (α : F ⟶ G) (n : ℕ)
  {X : C} (P : InjectiveResolution X) :
  (nat_trans.right_derived α n).app X =
    (F.right_derived_obj_iso n P).hom ≫
      (homology_functor D _ n).map ((nat_trans.map_homological_complex α _).app P.cocomplex) ≫
        (G.right_derived_obj_iso n P).inv :=
begin
  symmetry,
  dsimp [nat_trans.right_derived, functor.right_derived_obj_iso],
  simp only [category.comp_id, category.id_comp],
  rw [←homology_functor_map, homotopy_category.homology_functor_map_factors],
  simp only [←functor.map_comp],
  congr' 1,
  apply homotopy_category.eq_of_homotopy,
  simp only [nat_trans.map_homological_complex_naturality_assoc,
    ←functor.map_comp],
  apply homotopy.comp_left_id,
  rw [←functor.map_id],
  apply functor.map_homotopy,
  apply homotopy_equiv.homotopy_hom_inv_id,
end

end category_theory
