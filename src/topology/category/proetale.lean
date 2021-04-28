/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import topology.category.Profinite
import category_theory.sites.pretopology

open category_theory category_theory.limits

universes v u

variables {C : Type u} [category.{v} C]

section MOVE_TO_PRESIEVE

inductive presieve_of_arrows {X : C} {ι : Type*} (Y : ι → C) (f : Π i, Y i ⟶ X) :
  presieve X
| mk (i : ι) : presieve_of_arrows (f i)

lemma presieve_of_arrows_punit {X Y : C} (f : Y ⟶ X) :
  presieve_of_arrows _ (λ _ : punit, f) = presieve.singleton f :=
begin
  ext Y g,
  split,
  { rintro ⟨_⟩,
    apply presieve.singleton.mk },
  { rintro ⟨_⟩,
    exact presieve_of_arrows.mk punit.star },
end

lemma presieve_of_arrows_pullback [has_pullbacks C] {X Y : C} {ι : Type*}
  (f : Y ⟶ X) (Y : ι → C) (g : Π (i : ι), Y i ⟶ X) :
  presieve_of_arrows (λ i, pullback (g i) f) (λ i, pullback.snd) =
    pullback_arrows f (presieve_of_arrows Y g) :=
begin
  ext Z h,
  split,
  { rintro ⟨hk⟩,
   exact pullback_arrows.mk _ _ (presieve_of_arrows.mk hk) },
  { rintro ⟨W, k, hk₁⟩,
    cases hk₁ with i hi,
    apply presieve_of_arrows.mk },
end

lemma presieve_of_arrows_bind (X : C) (ι : Type*)
  (Z : ι → C)
  (g : Π (i : ι), Z i ⟶ X)
  (j : Π ⦃Y : C⦄ (f : Y ⟶ X),
         presieve_of_arrows Z g f → Type*)
  (W : Π ⦃Y : C⦄ (f : Y ⟶ X) (H : presieve_of_arrows Z g f),
         j f H → C)
  (k : Π ⦃Y : C⦄ (f : Y ⟶ X) (H : presieve_of_arrows Z g f)
       (i : j f H), W f H i ⟶ Y) :
  (presieve_of_arrows Z g).bind (λ Y f H, presieve_of_arrows (W f H) (k f H)) =
    presieve_of_arrows (λ (i : Σ (i : ι), j (g i) (presieve_of_arrows.mk _)), W (g i.1) _ i.2)
      (λ ij, k (g ij.1) _ ij.2 ≫ g ij.1) :=
begin
  ext Y f,
  split,
  { rintro ⟨_, _, _, ⟨i⟩, ⟨i'⟩, rfl⟩,
    refine presieve_of_arrows.mk (sigma.mk _ _) },
  { rintro ⟨⟨i, i'⟩⟩,
    refine presieve.bind_comp _ _ _,
    { apply presieve_of_arrows.mk },
    { apply presieve_of_arrows.mk } }
end

end MOVE_TO_PRESIEVE

section MOVE_TO_PROFINITE
@[simp] lemma id_app (X : Profinite) (x : X) :
  (𝟙 X : X → X) x = x := rfl

@[simp] lemma comp_app {X Y Z : Profinite} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
  (f ≫ g : X → Z) x = g (f x) := rfl

def point : Profinite.{u} := ⟨⟨punit⟩⟩
end MOVE_TO_PROFINITE

section MAYBEMOVE
def from_point {X : Profinite} :
  (point ⟶ X) ≃ X :=
{ to_fun := λ f, f punit.star,
  inv_fun := λ x, ⟨λ _, x⟩,
  left_inv := λ x, by { ext ⟨⟩, refl },
  right_inv := λ x, rfl}

lemma from_point_apply {X Y : Profinite} (f : point ⟶ X) (g : X ⟶ Y) :
  g (from_point f) = from_point (f ≫ g) :=
rfl

noncomputable def mk_pullback {X Y Z : Profinite} {f : X ⟶ Z} {g : Y ⟶ Z} {x : X} {y : Y}
  (h : f x = g y) :
  (pullback f g : Profinite) :=
from_point (pullback.lift (from_point.symm x) (from_point.symm y) (by { ext ⟨⟩, exact h }))

lemma mk_pullback_fst {X Y Z : Profinite} {f : X ⟶ Z} {g : Y ⟶ Z} {x : X} {y : Y}
  {h : f x = g y} : (pullback.fst : pullback f g ⟶ _) (mk_pullback h) = x :=
begin
  rw [mk_pullback, from_point_apply],
  simp
end

lemma mk_pullback_snd {X Y Z : Profinite} {f : X ⟶ Z} {g : Y ⟶ Z} {x : X} {y : Y}
  {h : f x = g y} : (pullback.snd : pullback f g ⟶ _) (mk_pullback h) = y :=
begin
  rw [mk_pullback, from_point_apply],
  simp
end
end MAYBEMOVE

def proetale_pretopology : pretopology Profinite :=
{ coverings := λ X S, ∃ (ι : Type*) [fintype ι] (Y : ι → Profinite) (f : Π (i : ι), Y i ⟶ X),
      (∀ (x : X), ∃ i (y : Y i), f i y = x) ∧ S = presieve_of_arrows Y f,
  has_isos := λ X Y f i,
  begin
    refine ⟨punit, infer_instance, λ _, Y, λ _, f, _, _⟩,
    { introI x,
      refine ⟨punit.star, inv f x, _⟩,
      change (inv f ≫ f) x = x,
      rw is_iso.inv_hom_id,
      simp },
    { rw presieve_of_arrows_punit },
  end,
  pullbacks := λ X Y f S,
  begin
    rintro ⟨ι, hι, Z, g, hg, rfl⟩,
    refine ⟨ι, hι, λ i, pullback (g i) f, λ i, pullback.snd, _, _⟩,
    { intro y,
      rcases hg (f y) with ⟨i, z, hz⟩,
      exact ⟨i, mk_pullback hz, mk_pullback_snd⟩ },
    { rw presieve_of_arrows_pullback }
  end,
  transitive := λ X S Ti,
  begin
    rintro ⟨ι, hι, Z, g, hY, rfl⟩ hTi,
    choose j hj W k hk₁ hk₂ using hTi,
    resetI,
    refine ⟨Σ (i : ι), j (g i) (presieve_of_arrows.mk _), infer_instance, λ i, W _ _ i.2, _, _, _⟩,
    { intro ij,
      exact k _ _ ij.2 ≫ g ij.1 },
    { intro x,
      obtain ⟨i, y, rfl⟩ := hY x,
      obtain ⟨i', z, rfl⟩ := hk₁ (g i) (presieve_of_arrows.mk _) y,
      refine ⟨⟨i, i'⟩, z, rfl⟩ },
    { have : Ti = λ Y f H, presieve_of_arrows (W f H) (k f H),
      { ext Y f H : 3,
        apply hk₂ },
      rw this,
      apply presieve_of_arrows_bind },
  end }
