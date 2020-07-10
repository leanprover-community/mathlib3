/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Group.basic
import algebra.category.Group.preadditive
import category_theory.limits.shapes.biproducts
import algebra.pi_instances

/-!
# The category of abelian groups has finite biproducts
-/

open category_theory
open category_theory.limits

open_locale big_operators

universe u

namespace AddCommGroup

instance has_binary_product (G H : AddCommGroup.{u}) : has_binary_product G H :=
{ cone :=
  { X := AddCommGroup.of (G × H),
    π := { app := λ j, walking_pair.cases_on j (add_monoid_hom.fst G H) (add_monoid_hom.snd G H) }},
  is_limit :=
  { lift := λ s, add_monoid_hom.prod (s.π.app walking_pair.left) (s.π.app walking_pair.right),
    fac' := begin rintros s (⟨⟩|⟨⟩); { ext x, dsimp, simp, }, end,
    uniq' := λ s m w,
    begin
      ext; [rw ← w walking_pair.left, rw ← w walking_pair.right]; refl,
    end, } }

instance (G H : AddCommGroup.{u}) : has_binary_biproduct G H :=
has_binary_biproduct.of_has_binary_product _ _

-- We verify that the underlying type of the biproduct we've just defined is definitionally
-- the cartesian product of the underlying types:
example (G H : AddCommGroup.{u}) : ((G ⊞ H : AddCommGroup) : Type u) = (G × H) := rfl

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

instance has_limit_discrete : has_limit F :=
{ cone :=
  { X := AddCommGroup.of (Π j, F.obj j),
    π := discrete.nat_trans (λ j, add_monoid_hom.apply (λ j, F.obj j) j), },
  is_limit :=
  { lift := lift F,
    fac' := λ s j, by { ext, dsimp, simp, },
    uniq' := λ s m w,
    begin
      ext x j,
      dsimp only [has_limit.lift],
      simp only [add_monoid_hom.coe_mk],
      exact congr_arg (λ f : s.X ⟶ F.obj j, (f : s.X → F.obj j) x) (w j),
    end, }, }

end has_limit

section

open has_limit

variables [decidable_eq J] [fintype J]

instance (f : J → AddCommGroup.{u}) : has_biproduct f :=
has_biproduct.of_has_product _

-- We verify that the underlying type of the biproduct we've just defined is definitionally
-- the dependent function type:
example (f : J → AddCommGroup.{u}) : ((⨁ f : AddCommGroup) : Type u) = (Π j, f j) := rfl

end

instance : has_finite_biproducts AddCommGroup :=
⟨λ J _ _, { has_biproduct := λ f, by exactI infer_instance }⟩

end AddCommGroup
