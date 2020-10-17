/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import category_theory.sites.grothendieck

/-!
# Grothendieck pretopologies

Definition and lemmas about Grothendieck pretopologies.
A Grothendieck pretopology for a category `C` is a set of families of morphisms with fixed codomain,
satisfying certain closure conditions.

We show that a pretopology generates a genuine Grothendieck topology, and every topology has
a maximal pretopology which generates it.

## Todo

Define sheaves on a pretopology, and show they are the same as the sheaves for the topology
generated by the pretopology.

## Tags

coverage, pretopology, site

## References

* [https://ncatlab.org/nlab/show/Grothendieck+pretopology][nlab]
* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]
* [https://stacks.math.columbia.edu/tag/00VG][Stacks]
-/

universes v u
noncomputable theory

namespace category_theory

open category_theory category limits arrows_with_codomain

variables {C : Type u} [category.{v} C] [has_pullbacks C]

/--
Pullback a set of arrows with given codomain along a fixed map, by taking the pullback in the
category.
This is not the same as the arrow set of `sieve.pullback`, but there is a relation between them
in `pullback_arrows_comm`.
-/
def pullback_arrows {X Y : C} (f : Y ⟶ X) (S : arrows_with_codomain X) :
  arrows_with_codomain Y :=
λ Z g, ∃ Z' (h : Z' ⟶ X), S h ∧ ∃ (H : Z = pullback h f),
  eq_to_hom H ≫ pullback.snd = g

lemma pullback_arrows_comm {X Y : C} (f : Y ⟶ X)
  (R : arrows_with_codomain X) :
  sieve.generate (pullback_arrows f R) = (sieve.generate R).pullback f :=
begin
  ext Z g,
  split,
  { rintro ⟨W, k, l, ⟨T, g, hg, rfl, rfl⟩, rfl⟩,
    refine ⟨_, k ≫ pullback.fst, g, hg, _⟩,
    rw [assoc, pullback.condition, eq_to_hom_refl, id_comp, assoc] },
  { rintro ⟨W, k, h, hh, comm⟩,
    exact ⟨_, pullback.lift _ _ comm, _, ⟨_, h, hh, rfl, rfl⟩, by simp⟩ },
end

set_option pp.proofs true
set_option pp.implicit false

lemma pullback_singleton {X Y Z : C} (f : Y ⟶ X) (g : Z ⟶ X) :
 ∃ (W : C) (k : W ⟶ Y), pullback_arrows f (singleton_arrow g) = singleton_arrow k :=
begin
  refine ⟨pullback (eq_to_hom (eq.refl _) ≫ g) f, pullback.snd, _⟩,
  ext W k,
  split,
  { rintro ⟨W, k, ⟨rfl, rfl⟩, rfl, rfl⟩,
    rw [eq_to_hom_refl (pullback (eq_to_hom (eq.refl W) ≫ g) f) (eq.refl _), id_comp],
    apply singleton_arrow_self },
  { rintro ⟨rfl, rfl⟩,
    exact ⟨_, _, by simp, _, rfl⟩ }
end

variables (C)

/--
A (Grothendieck) pretopology on `C` is a collection of morphisms with fixed target for each object,
satisfying three axioms:
1. Every family consisting of a single isomorphism is a covering family.
2. The collection of covering families is stable under pullback.
3. Given a covering family, and a covering family on each domain of the former, the composition
   is a covering family.

In some sense, a pretopology can be seen as Grothendieck topology with weaker saturation conditions,
in that each covering is not necessarily downward closed.

See: https://ncatlab.org/nlab/show/Grothendieck+pretopology, or
https://stacks.math.columbia.edu/tag/00VH, or [MM92] Chapter III, Section 2, Definition 2.
Note that Stacks calls a category together with a pretopology a site, and [MM92] calls this
a basis for a topology.
-/
@[ext]
structure pretopology :=
(coverings : Π (X : C), set (arrows_with_codomain X))
(has_isos : ∀ ⦃X Y⦄ (f : Y ⟶ X) [is_iso f], arrows_with_codomain.singleton_arrow f ∈ coverings X)
(pullbacks : ∀ ⦃X Y⦄ (f : Y ⟶ X) S, S ∈ coverings X → pullback_arrows f S ∈ coverings Y)
(transitive : ∀ ⦃X : C⦄ (S : arrows_with_codomain X)
               (Ti : Π ⦃Y⦄ (f : Y ⟶ X), S f → arrows_with_codomain Y), S ∈ coverings X →
               (∀ ⦃Y⦄ f (H : S f), Ti f H ∈ coverings Y) → S.bind Ti ∈ coverings X)

namespace pretopology

instance : has_coe_to_fun (pretopology C) :=
⟨_, λ J, J.coverings⟩

instance : partial_order (pretopology C) :=
{ le := λ K₁ K₂, (K₁ : Π (X : C), set _) ≤ K₂,
  le_refl := λ K, le_refl _,
  le_trans := λ K₁ K₂ K₃ h₁₂ h₂₃, le_trans h₁₂ h₂₃,
  le_antisymm := λ K₁ K₂ h₁₂ h₂₁, pretopology.ext _ _ (le_antisymm h₁₂ h₂₁) }

/--
A pretopology `K` can be completed to a Grothendieck topology `J` by declaring a sieve to be
`J`-covering if it contains a family in `K`.
-/
def to_grothendieck (K : pretopology C) : grothendieck_topology C :=
{ sieves := λ X S, ∃ R ∈ K X, R ≤ (S : arrows_with_codomain _),
  top_mem' := λ X, ⟨arrows_with_codomain.singleton_arrow (𝟙 _), K.has_isos _, λ _ _ _, ⟨⟩⟩,
  pullback_stable' := λ X Y S g,
  begin
    rintro ⟨R, hR, RS⟩,
    refine ⟨_, K.pullbacks g _ hR, _⟩,
    rw [← sieve.sets_iff_generate, pullback_arrows_comm],
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
def of_grothendieck (J : grothendieck_topology C) : pretopology C :=
{ coverings := λ X R, sieve.generate R ∈ J X,
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
    rintro Y g ⟨W, h, g, hg, rfl⟩,
    exact ⟨_, h, _, ⟨_, _, _, hf, hg, rfl⟩, by simp⟩,
  end }

lemma insert : galois_insertion (to_grothendieck C) (of_grothendieck C) :=
{ gc :=
  λ K J,
  begin
    split,
    { intros h X R hR,
      apply h,
      refine ⟨_, hR, _⟩,
      apply sieve.gi_generate.gc.le_u_l },
    { rintro h X S ⟨R, hR, RS⟩,
      apply J.superset_covering _ (h _ hR),
      rwa sieve.gi_generate.gc }
  end,
  le_l_u := λ J X S hS, ⟨S, J.superset_covering (sieve.gi_generate.gc.le_u_l _) hS, le_refl _⟩,
  choice := λ x hx, to_grothendieck C x,
  choice_eq := λ _ _, rfl }

-- galois_insertion.monotone_intro _ _ _ _

-- def discrete : pretopology C :=
-- { coverings := λ X S, ∃ Y (f : Y ⟶ X) (h : is_iso f), S = arrows_with_codomain.singleton_arrow f,
--   has_isos := λ X Y f i, ⟨_, _, i, rfl⟩,
--   pullbacks := λ X Y f S,
--   begin
--     rintro ⟨Z, g, i, rfl⟩,
--     rw set.mem_def,
--     obtain ⟨W, k, hk⟩ := pullback_singleton f g,

--     refine ⟨_, _, _, _⟩,
--   end

-- }

end pretopology

end category_theory
