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

instance has_limit_pair (G H : AddCommGroup.{u}) : has_limit.{u} (pair G H) :=
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

instance (G H : AddCommGroup.{u}) : has_binary_biproduct.{u} G H :=
has_binary_biproduct.of_has_binary_product _ _

-- We verify that the underlying type of the biproduct we've just defined is definitionally
-- the cartesian product of the underlying types:
example (G H : AddCommGroup.{u}) : ((G ⊞ H : AddCommGroup.{u}) : Type u) = (G × H) := rfl

-- Furthermore, our biproduct will automatically function as a coproduct.
example (G H : AddCommGroup.{u}) : has_colimit.{u} (pair G H) := by apply_instance

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

namespace has_colimit
variables [fintype J]

/--
The map from the cartesian product of a finite family of abelian groups
to any cocone over that family.
-/
def desc (s : cocone F) :
  AddCommGroup.of (Π j, F.obj j) ⟶ s.X :=
{ to_fun := λ f, ∑ j, s.ι.app j (f j),
  map_zero' :=
  begin
    conv_lhs { apply_congr, skip, simp [@pi.zero_apply _ (λ j, F.obj j) x _], },
    simp,
  end,
  map_add' := λ x y,
  begin
    conv_lhs { apply_congr, skip, simp [pi.add_apply x y _], },
    simp [finset.sum_add_distrib],
  end, }

@[simp] lemma desc_apply (s : cocone F) (f : Π j, F.obj j) :
  (desc F s) f = ∑ j, s.ι.app j (f j) := rfl

variables [decidable_eq J]

instance has_colimit_discrete : has_colimit F :=
{ cocone :=
  { X := AddCommGroup.of (Π j, F.obj j),
    ι := discrete.nat_trans (λ j, add_monoid_hom.single (λ j, F.obj j) j), },
  is_colimit :=
  { desc := desc F,
    fac' := λ s j,
    begin
      dsimp, ext,
      dsimp [add_monoid_hom.single],
      simp only [pi.single, add_monoid_hom.coe_mk, desc_apply, coe_comp],
      rw finset.sum_eq_single j,
      { simp, },
      { intros b _ h, simp only [dif_neg h, add_monoid_hom.map_zero], },
      { simp, },
    end,
    uniq' := λ s m w,
    begin
      dsimp at *,
      convert @add_monoid_hom.functions_ext
        (discrete J) _ (λ j, F.obj j) _ _ s.X _ m (eq_to_hom rfl ≫ desc F s) _,
      intros j x,
      dsimp [desc],
      simp,
      rw finset.sum_eq_single j,
      { -- FIXME what prevents either of these `erw`s working by `simp`?
        erw [pi.single_eq_same], rw ←w, simp,
        erw add_monoid_hom.single_apply, },
      { intros j' _ h, simp only [pi.single_eq_of_ne h, add_monoid_hom.map_zero], },
      { intros h, exfalso, simpa using h, },
    end, }, }.

end has_colimit

open has_limit has_colimit

variables [decidable_eq J] [fintype J]

instance (f : J → AddCommGroup.{u}) : has_biproduct f :=
{ bicone :=
  { X := AddCommGroup.of (Π j, f j),
    ι := λ j, add_monoid_hom.single (λ j, f j) j,
    π := λ j, add_monoid_hom.apply (λ j, f j) j,
    ι_π := λ j j',
    begin
      ext, split_ifs,
      { subst h, simp, },
      { rw [eq_comm] at h, simp [h], },
    end, },
  is_limit := limit.is_limit (discrete.functor f),
  is_colimit := colimit.is_colimit (discrete.functor f), }.

-- We verify that the underlying type of the biproduct we've just defined is definitionally
-- the dependent function type:
example (f : J → AddCommGroup.{u}) : ((⨁ f : AddCommGroup.{u}) : Type u) = (Π j, f j) := rfl

end AddCommGroup
