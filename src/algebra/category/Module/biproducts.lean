/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.group.pi
import category_theory.limits.shapes.biproducts
import algebra.category.Module.limits
import algebra.category.Module.abelian
import algebra.homology.short_exact.abelian

/-!
# The category of `R`-modules has finite biproducts
-/

open category_theory
open category_theory.limits

open_locale big_operators

universes w v u

namespace Module

variables {R : Type u} [ring R]

-- As `Module R` is preadditive, and has all limits, it automatically has biproducts.
instance : has_binary_biproducts (Module.{v} R) :=
has_binary_biproducts.of_has_binary_products

instance : has_finite_biproducts (Module.{v} R) :=
has_finite_biproducts.of_has_finite_products

-- We now construct explicit limit data,
-- so we can compare the biproducts to the usual unbundled constructions.

/--
Construct limit data for a binary product in `Module R`, using `Module.of R (M × N)`.
-/
@[simps cone_X is_limit_lift]
def binary_product_limit_cone (M N : Module.{v} R) : limits.limit_cone (pair M N) :=
{ cone :=
  { X := Module.of R (M × N),
    π :=
    { app := λ j, discrete.cases_on j
        (λ j, walking_pair.cases_on j (linear_map.fst R M N) (linear_map.snd R M N)),
      naturality' := by rintros ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟨⟨⟩⟩⟩; refl,  }},
  is_limit :=
  { lift := λ s, linear_map.prod (s.π.app ⟨walking_pair.left⟩) (s.π.app ⟨walking_pair.right⟩),
    fac' := by { rintros s (⟨⟩|⟨⟩); { ext x, simp only
      [binary_fan.π_app_right, binary_fan.π_app_left, Module.coe_comp, function.comp_app,
        linear_map.fst_apply, linear_map.snd_apply, linear_map.prod_apply, pi.prod], }, },
    uniq' := λ s m w,
    begin
      ext; [rw ← w ⟨walking_pair.left⟩, rw ← w ⟨walking_pair.right⟩]; refl,
    end, } }

@[simp] lemma binary_product_limit_cone_cone_π_app_left (M N : Module.{v} R) :
  (binary_product_limit_cone M N).cone.π.app ⟨walking_pair.left⟩ = linear_map.fst R M N := rfl

@[simp] lemma binary_product_limit_cone_cone_π_app_right (M N : Module.{v} R) :
  (binary_product_limit_cone M N).cone.π.app ⟨walking_pair.right⟩ = linear_map.snd R M N := rfl

/--
We verify that the biproduct in `Module R` is isomorphic to
the cartesian product of the underlying types:
-/
@[simps hom_apply] noncomputable
def biprod_iso_prod (M N : Module.{v} R) : (M ⊞ N : Module.{v} R) ≅ Module.of R (M × N) :=
is_limit.cone_point_unique_up_to_iso
  (binary_biproduct.is_limit M N)
  (binary_product_limit_cone M N).is_limit

@[simp, elementwise] lemma biprod_iso_prod_inv_comp_fst (M N : Module.{v} R) :
  (biprod_iso_prod M N).inv ≫ biprod.fst = linear_map.fst R M N :=
is_limit.cone_point_unique_up_to_iso_inv_comp _ _ (discrete.mk walking_pair.left)

@[simp, elementwise] lemma biprod_iso_prod_inv_comp_snd (M N : Module.{v} R) :
  (biprod_iso_prod M N).inv ≫ biprod.snd = linear_map.snd R M N :=
is_limit.cone_point_unique_up_to_iso_inv_comp _ _ (discrete.mk walking_pair.right)

namespace has_limit

variables {J : Type w} (f : J → Module.{max w v} R)

/--
The map from an arbitrary cone over a indexed family of abelian groups
to the cartesian product of those groups.
-/
@[simps]
def lift (s : fan f) :
  s.X ⟶ Module.of R (Π j, f j) :=
{ to_fun := λ x j, s.π.app ⟨j⟩ x,
  map_add' := λ x y, by { ext, simp, },
  map_smul' := λ r x, by { ext, simp, }, }

/--
Construct limit data for a product in `Module R`, using `Module.of R (Π j, F.obj j)`.
-/
@[simps] def product_limit_cone : limits.limit_cone (discrete.functor f) :=
{ cone :=
  { X := Module.of R (Π j, f j),
    π := discrete.nat_trans (λ j, (linear_map.proj j.as : (Π j, f j) →ₗ[R] f j.as)), },
  is_limit :=
  { lift := lift f,
    fac' := λ s j, by { cases j, ext, simp, },
    uniq' := λ s m w,
    begin
      ext x j,
      dsimp only [has_limit.lift],
      simp only [linear_map.coe_mk],
      exact congr_arg (λ g : s.X ⟶ f j, (g : s.X → f j) x) (w ⟨j⟩),
    end, }, }

end has_limit

open has_limit

variables {J : Type} (f : J → Module.{v} R)

/--
We verify that the biproduct we've just defined is isomorphic to the `Module R` structure
on the dependent function type
-/
@[simps hom_apply] noncomputable
def biproduct_iso_pi [fintype J] (f : J → Module.{v} R) :
  (⨁ f : Module.{v} R) ≅ Module.of R (Π j, f j) :=
is_limit.cone_point_unique_up_to_iso
  (biproduct.is_limit f)
  (product_limit_cone f).is_limit

@[simp, elementwise] lemma biproduct_iso_pi_inv_comp_π [fintype J]
  (f : J → Module.{v} R) (j : J) :
  (biproduct_iso_pi f).inv ≫ biproduct.π f j = (linear_map.proj j : (Π j, f j) →ₗ[R] f j) :=
is_limit.cone_point_unique_up_to_iso_inv_comp _ _ (discrete.mk j)

end Module

section split_exact

variables {R : Type u} {A M B : Type v} [ring R] [add_comm_group A] [module R A]
  [add_comm_group B] [module R B] [add_comm_group M] [module R M]
variables {j : A →ₗ[R] M} {g : M →ₗ[R] B}
open Module

/--The isomorphism `A × B ≃ₗ[R] M` coming from a right split exact sequence `0 ⟶ A ⟶ M ⟶ B ⟶ 0`
of modules.-/
noncomputable def lequiv_prod_of_right_split_exact {f : B →ₗ[R] M}
  (hj : function.injective j) (exac : j.range = g.ker) (h : g.comp f = linear_map.id) :
  (A × B) ≃ₗ[R] M :=
(({ right_split := ⟨as_hom f, h⟩,
    mono := (Module.mono_iff_injective $ as_hom j).mpr hj,
    exact := (exact_iff _ _).mpr exac } : right_split _ _).splitting.iso.trans $
  biprod_iso_prod _ _).to_linear_equiv.symm

/--The isomorphism `A × B ≃ₗ[R] M` coming from a left split exact sequence `0 ⟶ A ⟶ M ⟶ B ⟶ 0`
of modules.-/
noncomputable def lequiv_prod_of_left_split_exact {f : M →ₗ[R] A}
  (hg : function.surjective g) (exac : j.range = g.ker) (h : f.comp j = linear_map.id) :
  (A × B) ≃ₗ[R] M :=
(({ left_split := ⟨as_hom f, h⟩,
    epi := (Module.epi_iff_surjective $ as_hom g).mpr hg,
    exact := (exact_iff _ _).mpr exac } : left_split _ _).splitting.iso.trans $
  biprod_iso_prod _ _).to_linear_equiv.symm

end split_exact
