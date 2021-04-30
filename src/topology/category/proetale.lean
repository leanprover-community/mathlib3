/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import topology.category.Profinite
import category_theory.sites.pretopology
import category_theory.sites.sheaf_of_types
import category_theory.sites.sheaf
import algebra.category.Group
import algebra.category.CommRing

open category_theory category_theory.limits

universes v u

variables {C : Type u} [category.{v} C]

/-- A terminal Profinite type, which has the important property that morphisms to `X` are the same
thing as elements of `X`. -/
def point : Profinite.{u} := ⟨⟨punit⟩⟩

/-- There is a (natural) bijection between morphisms `* ⟶ X` and elements of `X`.  -/
def from_point {X : Profinite.{u}} :
  (point ⟶ X) ≃ X :=
{ to_fun := λ f, f punit.star,
  inv_fun := λ x, ⟨λ _, x⟩,
  left_inv := λ x, by { ext ⟨⟩, refl },
  right_inv := λ x, rfl}

lemma from_point_apply {X Y : Profinite} (f : point ⟶ X) (g : X ⟶ Y) :
  g (from_point f) = from_point (f ≫ g) :=
rfl

noncomputable def mk_pullback {X Y Z : Profinite.{u}} {f : X ⟶ Z} {g : Y ⟶ Z} {x : X} {y : Y}
  (h : f x = g y) :
  (pullback f g : Profinite) :=
from_point (pullback.lift (from_point.symm x) (from_point.symm y) (by { ext ⟨⟩, exact h }))

lemma mk_pullback_fst {X Y Z : Profinite} {f : X ⟶ Z} {g : Y ⟶ Z} {x : X} {y : Y}
  {h : f x = g y} : (pullback.fst : pullback f g ⟶ _) (mk_pullback h) = x :=
begin
  rw [mk_pullback, from_point_apply],
  simp
end

lemma mk_pullback_snd {X Y Z : Profinite.{u}} {f : X ⟶ Z} {g : Y ⟶ Z} {x : X} {y : Y}
  {h : f x = g y} : (pullback.snd : pullback f g ⟶ _) (mk_pullback h) = y :=
begin
  rw [mk_pullback, from_point_apply],
  simp
end

/-- The proetale pretopology on Profinites. -/
def proetale_pretopology : pretopology.{u} Profinite.{u} :=
{ coverings := λ X S, ∃ (ι : Type u) [fintype ι] (Y : ι → Profinite) (f : Π (i : ι), Y i ⟶ X),
      (∀ (x : X), ∃ i (y : Y i), f i y = x) ∧ S = presieve.of_arrows Y f,
  has_isos := λ X Y f i,
  begin
    refine ⟨punit, infer_instance, λ _, Y, λ _, f, _, _⟩,
    { introI x,
      refine ⟨punit.star, inv f x, _⟩,
      change (inv f ≫ f) x = x,
      rw is_iso.inv_hom_id,
      simp },
    { rw presieve.of_arrows_punit },
  end,
  pullbacks := λ X Y f S,
  begin
    rintro ⟨ι, hι, Z, g, hg, rfl⟩,
    refine ⟨ι, hι, λ i, pullback (g i) f, λ i, pullback.snd, _, _⟩,
    { intro y,
      rcases hg (f y) with ⟨i, z, hz⟩,
      exact ⟨i, mk_pullback hz, mk_pullback_snd⟩ },
    { rw presieve.of_arrows_pullback }
  end,
  transitive := λ X S Ti,
  begin
    rintro ⟨ι, hι, Z, g, hY, rfl⟩ hTi,
    choose j hj W k hk₁ hk₂ using hTi,
    resetI,
    refine ⟨Σ (i : ι), j (g i) (presieve.of_arrows.mk _), infer_instance, λ i, W _ _ i.2, _, _, _⟩,
    { intro ij,
      exact k _ _ ij.2 ≫ g ij.1 },
    { intro x,
      obtain ⟨i, y, rfl⟩ := hY x,
      obtain ⟨i', z, rfl⟩ := hk₁ (g i) (presieve.of_arrows.mk _) y,
      refine ⟨⟨i, i'⟩, z, rfl⟩ },
    { have : Ti = λ Y f H, presieve.of_arrows (W f H) (k f H),
      { ext Y f H : 3,
        apply hk₂ },
      rw this,
      apply presieve.of_arrows_bind },
  end }

def proetale_topology : grothendieck_topology.{u} Profinite.{u} :=
proetale_pretopology.to_grothendieck _

@[derive category]
def CondensedSet : Type (u+1) := SheafOfTypes.{u} proetale_topology.{u}

@[derive category]
def Condensed (A : Type (u+1)) [large_category A] : Type (u+1) := Sheaf.{u} proetale_topology A

example : category.{u+1} (Condensed Ab.{u}) := infer_instance
example : category.{u+1} (Condensed Ring.{u}) := infer_instance
