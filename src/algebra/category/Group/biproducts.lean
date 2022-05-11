/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.group.pi
import algebra.category.Group.preadditive
import category_theory.limits.shapes.biproducts
import algebra.category.Group.limits

/-!
# The category of abelian groups has finite biproducts
-/

open category_theory
open category_theory.limits

open_locale big_operators

universe u

namespace AddCommGroup

-- As `AddCommGroup` is preadditive, and has all limits, it automatically has biproducts.
instance : has_binary_biproducts AddCommGroup :=
has_binary_biproducts.of_has_binary_products

instance : has_finite_biproducts AddCommGroup :=
has_finite_biproducts.of_has_finite_products

-- We now construct explicit limit data,
-- so we can compare the biproducts to the usual unbundled constructions.

/--
Construct limit data for a binary product in `AddCommGroup`, using `AddCommGroup.of (G × H)`.
-/
@[simps cone_X is_limit_lift]
def binary_product_limit_cone (G H : AddCommGroup.{u}) : limits.limit_cone (pair G H) :=
{ cone :=
  { X := AddCommGroup.of (G × H),
    π := { app := λ j, walking_pair.cases_on j (add_monoid_hom.fst G H) (add_monoid_hom.snd G H) }},
  is_limit :=
  { lift := λ s, add_monoid_hom.prod (s.π.app walking_pair.left) (s.π.app walking_pair.right),
    fac' := begin rintros s (⟨⟩|⟨⟩); { ext x, simp, }, end,
    uniq' := λ s m w,
    begin
      ext; [rw ← w walking_pair.left, rw ← w walking_pair.right]; refl,
    end, } }

@[simp] lemma binary_product_limit_cone_cone_π_app_left (G H : AddCommGroup.{u}) :
  (binary_product_limit_cone G H).cone.π.app walking_pair.left = add_monoid_hom.fst G H := rfl

@[simp] lemma binary_product_limit_cone_cone_π_app_right (G H : AddCommGroup.{u}) :
  (binary_product_limit_cone G H).cone.π.app walking_pair.right = add_monoid_hom.snd G H := rfl

/--
We verify that the biproduct in AddCommGroup is isomorphic to
the cartesian product of the underlying types:
-/
@[simps] noncomputable
def biprod_iso_prod (G H : AddCommGroup.{u}) : (G ⊞ H : AddCommGroup) ≅ AddCommGroup.of (G × H) :=
is_limit.cone_point_unique_up_to_iso
  (binary_biproduct.is_limit G H)
  (binary_product_limit_cone G H).is_limit

-- Furthermore, our biproduct will automatically function as a coproduct.
example (G H : AddCommGroup.{u}) : has_colimit (pair G H) := by apply_instance

variables {J : Type u} (F : (discrete J) ⥤ AddCommGroup.{u})

namespace has_limit

/--
The map from an arbitrary cone over a indexed family of abelian groups
to the cartesian product of those groups.
-/
def lift (s : cone F) :
  s.X ⟶ AddCommGroup.of (Π j, F.obj j) :=
{ to_fun := λ x j, s.π.app j x,
  map_zero' := by { ext, simp },
  map_add' := λ x y, by { ext, simp }, }

@[simp] lemma lift_apply (s : cone F) (x : s.X) (j : J) : (lift F s) x j = s.π.app j x := rfl

/--
Construct limit data for a product in `AddCommGroup`, using `AddCommGroup.of (Π j, F.obj j)`.
-/
@[simps] def product_limit_cone : limits.limit_cone F :=
{ cone :=
  { X := AddCommGroup.of (Π j, F.obj j),
    π := discrete.nat_trans (λ j, pi.eval_add_monoid_hom (λ j, F.obj j) j), },
  is_limit :=
  { lift := lift F,
    fac' := λ s j, by { ext, simp, },
    uniq' := λ s m w,
    begin
      ext x j,
      dsimp only [has_limit.lift],
      simp only [add_monoid_hom.coe_mk],
      exact congr_arg (λ f : s.X ⟶ F.obj j, (f : s.X → F.obj j) x) (w j),
    end, }, }

end has_limit

open has_limit

/--
We verify that the biproduct we've just defined is isomorphic to the AddCommGroup structure
on the dependent function type
-/
@[simps hom_apply] noncomputable
def biproduct_iso_pi [decidable_eq J] [fintype J] (f : J → AddCommGroup.{u}) :
  (⨁ f : AddCommGroup) ≅ AddCommGroup.of (Π j, f j) :=
is_limit.cone_point_unique_up_to_iso
  (biproduct.is_limit f)
  (product_limit_cone (discrete.functor f)).is_limit

@[simp, elementwise] lemma biproduct_iso_pi_inv_comp_π [decidable_eq J] [fintype J]
  (f : J → AddCommGroup.{u}) (j : J) :
  (biproduct_iso_pi f).inv ≫ biproduct.π f j = pi.eval_add_monoid_hom (λ j, f j) j :=
is_limit.cone_point_unique_up_to_iso_inv_comp _ _ _

end AddCommGroup
