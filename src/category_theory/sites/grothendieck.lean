/-
Copyright (c) 2020 Bhavik Mehta, E. W. Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, E. W. Ayers
-/

import category_theory.sites.sieves
import category_theory.full_subcategory
import category_theory.types

universes v u
namespace category_theory

open category_theory category sieve

-- /-- A set of sieves for every object in the category: a candidate to be a Grothendieck topology. -/
-- @[derive complete_lattice]
-- def sieve_set (C : Type u) [category.{v} C] := Π (X : C), set (sieve X)

/-- The trivial sieve set, containing only the maximal sieve on each object. -/
def sieve_set.trivial (C : Type u) [category.{v} C] : Π (X : C), set (sieve X) := λ X, {⊤}

/--
A sieve on `X` is dense if for any arrow `f : Y ⟶ X`, there is a `g : Z ⟶ Y` with `g ≫ f ∈ S`.
-/
def sieve_set.dense (C : Type u) [category.{v} C] : Π (X : C), set (sieve X) :=
λ X, {S | ∀ {Y : C} (f : Y ⟶ X), ∃ Z (g : Z ⟶ Y), S.arrows (g ≫ f)}

/-- The atomic sieve_set just contains all of the non-empty sieves. -/
def sieve_set.atomic (C : Type u) [category.{v} C] : Π (X : C), set (sieve X) :=
λ X, {S | ∃ {Y} (f : Y ⟶ X), S.arrows f}

variables {C : Type u} [category.{v} C]

@[simp]
lemma mem_trivial {C : Type u} [category.{v} C] {X : C} (S : sieve X) :
  S ∈ sieve_set.trivial C X ↔ S = ⊤ :=
set.mem_singleton_iff

/--
The definition of a Grothendieck topology: a set of sieves `J X` on each object `X` satisfying
three axioms:
1. For every object `X`, the maximal sieve is in `J X`.
2. If `S ∈ J X` then its pullback along any `h : Y ⟶ X` is in `J Y`.
3. If `S ∈ J X` and `R` is a sieve on `X`, then provided that the pullback of `R` along any arrow
   `f : Y ⟶ X` in `S` is in `J Y`, we have that `R` itself is in `J X`.

A sieve `S` on `X` is referred to as `J`-covering, (or just covering), if `S ∈ J X`.
-/
class grothendieck_topology (J : Π (X : C), set (sieve X)) : Prop :=
(max : ∀ X, ⊤ ∈ J X)
(stab : ∀ ⦃X Y : C⦄ ⦃S : sieve X⦄ (h₁ : S ∈ J X) (f : Y ⟶ X), S.pullback f ∈ J Y)
(trans : ∀ ⦃X⦄ ⦃S : sieve X⦄ (hS : S ∈ J X) (R : sieve X),
         (∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, S.arrows f → R.pullback f ∈ J Y) → R ∈ J X)

/-- A site is a category equipped with a Grothendieck topology. -/
structure Site :=
(C : Type u)
[𝒞 : category.{v} C]
(J : Π (X : C), set (sieve X))
[g : grothendieck_topology J]

namespace grothendieck_topology
variables {X Y : C} {S R : sieve X}
variables {J : Π (X : C), set (sieve X)} [grothendieck_topology J]

@[simp] lemma top_covering : ⊤ ∈ J X := grothendieck_topology.max _

lemma covering_of_max : S = ⊤ → S ∈ J X := λ h, h.symm ▸ grothendieck_topology.max X

lemma superset_covering (Hss : S ≤ R) (sjx : S ∈ J X) : R ∈ J X :=
begin
  apply grothendieck_topology.trans sjx,
  intros Y h hh,
  rw pullback_eq_top_iff_mem at hh,
  apply covering_of_max,
  rw [← top_le_iff, ← hh],
  apply pullback_monotone _ Hss,
end

/-- The sieve `S` on `X` `J`-covers an arrow `f` to `X` if `S.pullback f ∈ J Y`. -/
def covers (J : Π (X : C), set (sieve X)) (S : sieve X) (f : Y ⟶ X) : Prop := S.pullback f ∈ J Y

lemma covers_iff {J : Π (X : C), set (sieve X)} (S : sieve X) (f : Y ⟶ X) :
  covers J S f ↔ S.pullback f ∈ J Y :=
iff.rfl

lemma covering_iff_covers_id {J : Π (X : C), set (sieve X)} (S : sieve X) :
  S ∈ J X ↔ covers J S (𝟙 X) :=
by simp [covers_iff]

lemma intersection_covering (rj : R ∈ J X) (sj : S ∈ J X) : R ⊓ S ∈ J X :=
begin
  apply grothendieck_topology.trans rj,
  intros Y f Hf,
  have : S.pullback f ≤ (R ⊓ S).pullback f,
    intros Z g hg,
    exact ⟨downward_closed _ Hf _, hg⟩,
  exact superset_covering this (stab sj f),
end

lemma arrow_max (f : Y ⟶ X) (S : sieve X) (hf : S.arrows f) : covers J S f :=
begin
  rw [covers, (pullback_eq_top_iff_mem f).1 hf],
  apply max,
end
lemma arrow_stab (f : Y ⟶ X) (S : sieve X) (h : covers J S f) {Z : C} (g : Z ⟶ Y) : covers J S (g ≫ f) :=
begin
  rw [covers, pullback_comp],
  apply stab,
  apply h,
end
lemma arrow_trans (f : Y ⟶ X) (S R : sieve X) (h : covers J S f) :
  (∀ {Z : C} (g : Z ⟶ X), S.arrows g → covers J R g) → covers J R f :=
begin
  intro k,
  apply trans h,
  intros Z g hg,
  rw ← pullback_comp,
  apply k (g ≫ f) hg,
end

lemma arrow_intersect (f : Y ⟶ X) (S R : sieve X) (hS : covers J S f) (hR : covers J R f) :
  covers J (S ⊓ R) f :=
begin
  rw [covers, pullback_inter],
  apply intersection_covering;
  assumption
end

open sieve_set

/-- The trivial topology is always a Grothendieck topology. -/
instance trivial.grothendieck_topology: grothendieck_topology (sieve_set.trivial C) :=
{ max := λ X, set.mem_singleton _,
  stab := λ X Y S HS h,
  begin
    rw mem_trivial at *,
    rw [HS, pullback_top],
  end,
  trans := λ X S HS R HR,
  begin
    rw [mem_trivial, ← id_mem_iff_eq_top, pullback_eq_top_iff_mem],
    simp only [mem_trivial] at HR,
    apply HR,
    rwa [id_mem_iff_eq_top, ← mem_trivial],
  end }

/-- The dense topology is always a Grothendieck topology. -/
instance dense.grothendieck_topology: grothendieck_topology (dense C) :=
{ max := λ X Y f, ⟨Y, 𝟙 Y, ⟨⟩⟩,
  stab :=
    begin
      intros X Y S H h Z f,
      rcases H (f ≫ h) with ⟨W, g, H⟩,
      exact ⟨W, g, by simpa⟩,
    end,
  trans :=
    begin
      intros X S H₁ R H₂ Y f,
      rcases H₁ f with ⟨Z, g, H₃⟩,
      rcases H₂ H₃ (𝟙 Z) with ⟨W, h, H₄⟩,
      exact ⟨W, (h ≫ g), by simpa using H₄⟩,
    end }

instance : inhabited Site := ⟨{ C := Type u, J := sieve_set.dense _ }⟩

/--
A category satisfies the right Ore condition if any span can be completed to a
commutative square.
NB. Any category with pullbacks obviously satisfies the right Ore condition.
-/
def right_ore_condition (C : Type u) [category.{v} C] : Prop :=
∀ {X Y Z : C} (yx : Y ⟶ X) (zx : Z ⟶ X), ∃ W (wy : W ⟶ Y) (wz : W ⟶ Z), wy ≫ yx = wz ≫ zx

/--
The atomic sieveset is a Grothendieck topology when it satisfies the right ore condition.
-/
lemma atomic.grothendieck_topology (hro : right_ore_condition C) : grothendieck_topology (atomic C) :=
{ max := λ X, ⟨_, 𝟙 _, ⟨⟩⟩,
  stab :=
  begin
    rintros X Y S ⟨Z, f, hf⟩ h,
    rcases hro h f with ⟨W, g, k, comm⟩,
    refine ⟨_, g, _⟩,
    simp [mem_pullback, comm, hf],
  end,
  trans :=
  begin
    rintros X S ⟨Y, f, hf⟩ R h,
    rcases h hf with ⟨Z, g, hg⟩,
    exact ⟨_, _, hg⟩,
  end }

open opposite

instance : partial_order { J : Π (X : C), set (sieve X) // grothendieck_topology J } :=
subtype.partial_order _

lemma intersect (Js : set (Π (X : C), set (sieve X))) (hJs : Π J ∈ Js, grothendieck_topology J) :
  grothendieck_topology (Inf Js) :=
{ max :=
  begin
    rintro X S ⟨⟨J, hJ⟩, rfl⟩,
    apply (hJs _ hJ).max,
  end,
  stab :=
  begin
    rintro X Y S hS f _ ⟨J, rfl⟩,
    apply (hJs _ J.2).stab,
    apply hS _ ⟨J, rfl⟩,
  end,
  trans :=
  begin
    rintro X S hS R t _ ⟨J, rfl⟩,
    apply (hJs _ J.2).trans,
    apply hS _ ⟨J, rfl⟩,
    intros Y f hf,
    apply t hf _ ⟨_, rfl⟩,
  end }

instance : has_Inf { J : Π (X : C), set (sieve X) // grothendieck_topology J } :=
{ Inf := λ T, ⟨Inf (subtype.val '' T), intersect _ (by { rintro _ ⟨⟨_, q⟩, _, rfl⟩, apply q })⟩}

instance : complete_lattice { J : Π (X : C), set (sieve X) // grothendieck_topology J } :=
complete_lattice_of_Inf _
begin
  intro T,
  refine @is_glb.of_image _ _ _ _ subtype.val _ _ _ _,
  intros, refl,
  exact is_glb_Inf (subtype.val '' T),
end

end grothendieck_topology

end category_theory
