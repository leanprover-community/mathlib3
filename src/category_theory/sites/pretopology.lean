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

def pullback_arrows [limits.has_pullbacks C] {X Y : C} (f : Y ⟶ X) (S : arrows_with_codomain X) :
  arrows_with_codomain Y :=
λ Z g, ∃ Z' (h : Z' ⟶ X), S h ∧ ∃ (H : limits.pullback h f = Z), eq_to_hom H.symm ≫ limits.pullback.snd = g

lemma pullback_arrows_comm [limits.has_pullbacks C] {X Y : C} (f : Y ⟶ X)
  (R : arrows_with_codomain X) :
  sieve.generate (pullback_arrows f R) = sieve.pullback f (sieve.generate R) :=
begin
  ext Z g,
  split,
  { rintro ⟨W, k, l, ⟨T, g, hg, rfl, rfl⟩, rfl⟩,
    refine ⟨_, k ≫ limits.pullback.fst, g, hg, _⟩,
    rw [assoc, limits.pullback.condition, eq_to_hom_refl, id_comp, assoc] },
  { rintro ⟨W, k, h, hh, comm⟩,
    exact ⟨_, limits.pullback.lift _ _ comm, _, ⟨_, h, hh, rfl, rfl⟩, by simp⟩ },
end

variables (C) [limits.has_pullbacks C]

@[ext]
structure pretopology' :=
(coverings : Π (X : C), set (arrows_with_codomain X))
(has_isos : ∀ ⦃X Y⦄ (f : Y ⟶ X) [is_iso f], arrows_with_codomain.singleton_arrow f ∈ coverings X)
(pullbacks : ∀ ⦃X Y⦄ (f : Y ⟶ X) S, S ∈ coverings X → pullback_arrows f S ∈ coverings Y)
(transitive : ∀ ⦃X : C⦄ (S : arrows_with_codomain X)
               (Ti : Π ⦃Y⦄ (f : Y ⟶ X), S f → arrows_with_codomain Y),
               S ∈ coverings X → (∀ ⦃Y⦄ f (H : S f), Ti f H ∈ coverings Y) → S.bind Ti ∈ coverings X)

namespace pretopology'

instance : has_coe_to_fun (pretopology' C) :=
⟨_, λ J, J.coverings⟩

instance : partial_order (pretopology' C) :=
{ le := λ K₁ K₂, (K₁ : Π (X : C), set _) ≤ K₂,
  le_refl := λ K, le_refl _,
  le_trans := λ K₁ K₂ K₃ h₁₂ h₂₃, le_trans h₁₂ h₂₃,
  le_antisymm := λ K₁ K₂ h₁₂ h₂₁, pretopology'.ext _ _ (le_antisymm h₁₂ h₂₁) }

/--
A pretopology `K` can be completed to a Grothendieck topology `J` by declaring a sieve to be
`J`-covering if it contains a family in `K`.
-/
def to_grothendieck (K : pretopology' C) : grothendieck_topology C :=
{ sieves := λ X S, ∃ R ∈ K X, R ≤ S.arrows,
  top_mem' := λ X, ⟨arrows_with_codomain.singleton_arrow (𝟙 _), K.has_isos _, λ _ _ _, ⟨⟩⟩,
  pullback_stable' := λ X Y S g,
  begin
    rintro ⟨R, hR, RS⟩,
    refine ⟨_, K.pullbacks g _ hR, _⟩,
    rw [← sieve.gi_generate.gc, pullback_arrows_comm],
    apply sieve.pullback_monotone,
    rwa sieve.gi_generate.gc,
  end,
  transitive' :=
  begin
    rintro X S ⟨R', hR', RS⟩ R t,
    choose t₁ t₂ t₃ using t,
    refine ⟨_, K.transitive _ _ hR' (λ _ f hf, t₂ (RS _ hf)), _⟩,
    rintro Y _ ⟨Z, g, f, hg, hf, rfl⟩,
    apply t₃ (RS _ hg) _ hf,
  end }

/-- The largest pretopology generating the given Grothendieck topology. -/
def of_grothendieck (J : grothendieck_topology C) : pretopology' C :=
{ coverings := λ X R, J X (sieve.generate R),
  has_isos := λ X Y f i,
  begin
    apply J.covering_of_eq_top,
    rw [← sieve.id_mem_iff_eq_top],
    exactI ⟨_, inv f, f, by simp⟩,
  end,
  pullbacks := λ X Y f R hR,
  begin
    rw [set.mem_def, pullback_arrows_comm],
    apply J.pullback_stable f hR,
  end,
  transitive := λ X S Ti hS hTi,
  begin
    apply J.transitive hS,
    intros Y f,
    rintros ⟨Z, g, f, hf, rfl⟩,
    rw sieve.pullback_comp,
    apply J.pullback_stable g,
    apply J.superset_covering _ (hTi _ hf),
    clear' Y g,
    rintro Y g ⟨W, h, g, hg, rfl⟩,
    exact ⟨_, h, _, ⟨_, _, _, hf, hg, rfl⟩, by simp⟩,
  end }

end pretopology'

end category_theory
