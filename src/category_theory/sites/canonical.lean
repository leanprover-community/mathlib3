/-
Copyright (c) 2020 Bhavik Mehta, E. W. Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, E. W. Ayers
-/

import category_theory.sites.grothendieck
import category_theory.sites.pretopology
import category_theory.sites.sheaf
import category_theory.full_subcategory
import category_theory.types

universes v u
namespace category_theory

open category_theory category limits sieve classical

variables {C : Type u} [category.{v} C]

namespace sheaf

variables {P : Cᵒᵖ ⥤ Type v}
variables {X Y : C} {S : sieve X} {R : presieve X}
variables (J J₂ : grothendieck_topology C)

lemma is_sheaf_for_bind (P : Cᵒᵖ ⥤ Type v) (U : sieve X)
  (B : Π ⦃Y⦄ ⦃f : Y ⟶ X⦄, U f → sieve Y)
  (hU : is_sheaf_for P U)
  (hB : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : U f), is_sheaf_for P (B hf))
  (hB' : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : U f) ⦃Z⦄ (g : Z ⟶ Y), is_separated_for P ((B hf).pullback g)) :
  is_sheaf_for P (sieve.bind U B) :=
begin
  intros s hs,
  let y : Π ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : U f), family_of_elements P (B hf) :=
    λ Y f hf Z g hg, s _ (presieve.bind_comp _ _ hg),
  have hy : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : U f), (y hf).consistent,
  { intros Y f H Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ comm,
    apply hs,
    apply reassoc_of comm },
  let t : family_of_elements P U,
  { intros Y f hf,
    apply (hB hf).amalgamate (y hf) (hy hf) },
  have ht : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : U f), is_amalgamation_for (y hf) (t f hf),
  { intros Y f hf,
    apply (hB hf).is_amalgamation_for _ },
  have hT : t.consistent,
  { rw is_sieve_consistent_iff,
    intros Z W f h hf,
    apply (hB (U.downward_closed hf h)).is_separated_for.ext,
    intros Y l hl,
    apply (hB' hf (l ≫ h)).ext,
    intros M m hm,
    have : (bind ⇑U B) (m ≫ l ≫ h ≫ f),
    { have : bind U B _ := presieve.bind_comp f hf hm,
      simpa using this },
    transitivity s (m ≫ l ≫ h ≫ f) this,
    { have := ht (U.downward_closed hf h) _ ((B _).downward_closed hl m),
      rw [op_comp, functor_to_types.map_comp_apply] at this,
      rw this,
      change s _ _ = s _ _,
      simp },
    { have : s _ _ = _ := (ht hf _ hm).symm,
      simp only [assoc] at this,
      rw this,
      simp } },
  refine ⟨hU.amalgamate t hT, _, _⟩,
  { rintro Z _ ⟨Y, f, g, hg, hf, rfl⟩,
    rw [op_comp, functor_to_types.map_comp_apply, is_sheaf_for.valid_glue _ _ _ hg],
    apply ht hg _ hf },
  { intros y hy,
    apply hU.is_separated_for.ext,
    intros Y f hf,
    apply (hB hf).is_separated_for.ext,
    intros Z g hg,
    rw [←functor_to_types.map_comp_apply, ←op_comp, hy _ (presieve.bind_comp _ _ hg),
        hU.valid_glue _ _ hf, ht hf _ hg] }
end

lemma is_sheaf_for_trans (P : Cᵒᵖ ⥤ Type v) (R S : sieve X)
  (hR : is_sheaf_for P R)
  (hR' : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : S f), is_separated_for P (R.pullback f))
  (hS : Π ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : R f), is_sheaf_for P (S.pullback f)) :
  is_sheaf_for P S :=
begin
  have : (bind ⇑R (λ (Y : C) (f : Y ⟶ X) (hf : R f), pullback f S) : presieve X) ≤ S,
  { rintros Z f ⟨W, f, g, hg, (hf : S _), rfl⟩,
    apply hf },
  apply is_sheaf_for_subsieve_aux P this,
  apply is_sheaf_for_bind _ _ _ hR hS,
  { intros Y f hf Z g,
    dsimp,
    rw ← pullback_comp,
    apply (hS (R.downward_closed hf _)).is_separated_for },
  { intros Y f hf,
    have : (sieve.pullback f (bind R (λ T (k : T ⟶ X) (hf : R k), pullback k S))) = R.pullback f,
    { ext Z g,
      split,
      { rintro ⟨W, k, l, hl, _, comm⟩,
        rw [mem_pullback, ← comm],
        simp [hl] },
      { intro a,
        refine ⟨Z, 𝟙 Z, _, a, _⟩,
        simp [hf] } },
    rw this,
    apply hR' hf },
end

/-- Construct the finest Grothendieck topology for which the given presheaf is a sheaf. -/
def finest_topology_single (P : Cᵒᵖ ⥤ Type v) : grothendieck_topology C :=
{ sieves := λ X S, ∀ Y (f : Y ⟶ X), is_sheaf_for P (S.pullback f),
  top_mem' := λ X Y f,
  begin
    rw sieve.pullback_top,
    exact is_sheaf_for_top_sieve P,
  end,
  pullback_stable' := λ X Y S f hS Z g,
  begin
    rw ← pullback_comp,
    apply hS,
  end,
  transitive' := λ X S hS R hR Z g,
  begin
    refine is_sheaf_for_trans P (pullback g S) _ (hS Z g) _ _,
    { intros Y f hf,
      rw ← pullback_comp,
      apply (hS _ _).is_separated_for },
    { intros Y f hf,
      have := hR hf _ (𝟙 _),
      rw [pullback_id, pullback_comp] at this,
      apply this },
  end }

/-- Construct the finest Grothendieck topology for which the given presheaves are sheaves. -/
def finest_topology (Ps : set (Cᵒᵖ ⥤ Type v)) : grothendieck_topology C :=
Inf (finest_topology_single '' Ps)

lemma sheaf_for_finest_topology (Ps : set (Cᵒᵖ ⥤ Type v)) :
  P ∈ Ps → is_sheaf (finest_topology Ps) P :=
begin
  intros h X S hS,
  simpa using hS _ ⟨⟨_, _, ⟨_, h, rfl⟩, rfl⟩, rfl⟩ _ (𝟙 _),
end

lemma is_finest_topology (Ps : set (Cᵒᵖ ⥤ Type v)) (J : grothendieck_topology C)
  (hJ : ∀ P ∈ Ps, is_sheaf J P) : J ≤ finest_topology Ps :=
begin
  intros X S hS,
  rintro _ ⟨⟨_, _, ⟨P, hP, rfl⟩, rfl⟩, rfl⟩,
  intros Y f,
  exact hJ P hP (S.pullback f) (J.pullback_stable f hS),
end

def canonical_topology : grothendieck_topology C :=
finest_topology (set.range yoneda.obj)

end sheaf

end category_theory
