/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import category_theory.sites.grothendieck

universes v u
noncomputable theory

namespace category_theory

open category_theory category

variables {C : Type u} [category.{v} C]

structure family_with_target (U : C) :=
(ι : Type u)
(obj : ι → C)
(hom : Π i, obj i ⟶ U)

@[simps]
def family_to_sieve {X : C} (R : family_with_target X) : sieve X :=
{ arrows := λ Y k, ∃ (i : R.ι) (g : Y ⟶ R.obj i), g ≫ R.hom i = k,
  downward_closed := λ Y Z f,
  begin
    rintro ⟨i, g, rfl⟩ f,
    exact ⟨i, f ≫ g, assoc _ _ _⟩,
  end }


@[simps]
def arrow_to_family {X Y : C} (f : Y ⟶ X) : family_with_target X :=
{ ι := punit,
  obj := λ _, Y,
  hom := λ _, f }

@[simps]
def pullback_family {X Y : C} (f : Y ⟶ X) (S : family_with_target X)
  [limits.has_pullbacks C] :
  family_with_target Y :=
{ ι := S.ι,
  obj := λ i, limits.pullback (S.hom i) f,
  hom := λ i, limits.pullback.snd }

@[simps]
def bind_family {X : C} (S : family_with_target X) (Ti : Π i, family_with_target (S.obj i)) :
  family_with_target X :=
{ ι := Σ (i : S.ι), (Ti i).ι,
  obj := λ i, (Ti i.1).obj i.2,
  hom := λ i, (Ti i.1).hom i.2 ≫ S.hom i.1 }

lemma family_to_sieve_comm [limits.has_pullbacks C] {X Y : C}
  (f : Y ⟶ X) (R : family_with_target X) :
  family_to_sieve (pullback_family f R) = sieve.pullback f (family_to_sieve R) :=
begin
  ext Z g,
  apply exists_congr,
  intro i,
  split,
  { rintro ⟨g, rfl⟩,
    refine ⟨g ≫ limits.pullback.fst, _⟩,
    rw [assoc, limits.pullback.condition, assoc], refl },
  { simp only [pullback_family_hom, exists_imp_distrib],
    intros k hk,
    exact ⟨limits.pullback.lift k g hk, by simp⟩ }
end

variables (C) [limits.has_pullbacks C]

structure pretopology :=
(coverings : Π (X : C), set (family_with_target X))
(has_isos : ∀ ⦃X Y⦄ (f : Y ⟶ X) [is_iso f], arrow_to_family f ∈ coverings X)
(pullbacks : ∀ ⦃X Y⦄ (f : Y ⟶ X) S, S ∈ coverings X → pullback_family f S ∈ coverings Y)
(transitive : ∀ ⦃X : C⦄ (S : family_with_target X) (Ti : Π i, family_with_target (S.obj i)),
               S ∈ coverings X → (∀ i, Ti i ∈ coverings (S.obj i)) → bind_family S Ti ∈ coverings X)

instance : has_coe_to_fun (pretopology C) :=
⟨_, λ J, J.coverings⟩

namespace pretopology

def to_grothendieck (K : pretopology C) : grothendieck_topology C :=
{ sieves := λ X S, ∃ (R : family_with_target X) (h : R ∈ K X), ∀ (i : R.ι), S.arrows (R.hom i),
  top_mem' := λ X, ⟨arrow_to_family (𝟙 _), K.has_isos (𝟙 X), λ i, by simp⟩,
  pullback_stable' := λ X Y S g ⟨R, hR, RS⟩,
    ⟨pullback_family g R, K.pullbacks g R hR, λ i, by simp [← limits.pullback.condition, RS i]⟩,
  transitive' :=
  begin
    rintro X S ⟨R', hR', RS⟩ R t,
    choose t₁ t₂ t₃ using t,
    refine ⟨bind_family R' (λ i, t₁ (RS i)), K.transitive _ _ hR' (λ i, t₂ _), λ i, t₃ _ i.2⟩,
  end }

def of_grothendieck (J : grothendieck_topology C) : pretopology C :=
{ coverings := λ X R, J X (family_to_sieve R),
  has_isos := λ X Y f i,
  begin
    apply J.covering_of_eq_top,
    rw ← sieve.id_mem_iff_eq_top,
    exactI ⟨⟨⟩, inv f, by simp⟩,
  end,
  pullbacks := λ X Y f R hR,
  begin
    rw set.mem_def at hR ⊢,
    rw family_to_sieve_comm,
    apply J.pullback_stable _ hR,
  end,
  transitive := λ X S Ti hS hTi,
  begin
    simp_rw set.mem_def at *,

  end }


end pretopology


end category_theory
