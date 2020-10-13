/-
Copyright (c) 2020 Bhavik Mehta, E. W. Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, E. W. Ayers
-/

import category_theory.sites.sieves
import category_theory.full_subcategory
import category_theory.types
import category_theory.limits.shapes.pullbacks

/-!
# Grothendieck topologies

Definition and lemmas about Grothendieck topologies.
A Grothendieck topology for a category `C` is a set of sieves on each object `X` satisfying
certain closure conditions.

Alternate versions of the axioms (in arrow form) are also described.
Two explicit examples of Grothendieck topologies are given:
* The dense topology
* The atomic topology
as well as the complete lattice structure on Grothendieck topologies (which gives two additional
explicit topologies: the discrete and trivial topologies.)

## Tags

Grothendieck topology, coverage, pretopology, site
-/

universes v u
namespace category_theory

open category_theory category

variables (C : Type u) [category.{v} C]

/--
The definition of a Grothendieck topology: a set of sieves `J X` on each object `X` satisfying
three axioms:
1. For every object `X`, the maximal sieve is in `J X`.
2. If `S ∈ J X` then its pullback along any `h : Y ⟶ X` is in `J Y`.
3. If `S ∈ J X` and `R` is a sieve on `X`, then provided that the pullback of `R` along any arrow
   `f : Y ⟶ X` in `S` is in `J Y`, we have that `R` itself is in `J X`.

A sieve `S` on `X` is referred to as `J`-covering, (or just covering), if `S ∈ J X`.
-/
@[ext]
structure grothendieck_topology :=
(sieves : Π (X : C), set (sieve X))
(top_mem' : ∀ X, ⊤ ∈ sieves X)
(pullback_stable' : ∀ ⦃X Y : C⦄ ⦃S : sieve X⦄ (f : Y ⟶ X), S ∈ sieves X → S.pullback f ∈ sieves Y)
(transitive' : ∀ ⦃X⦄ ⦃S : sieve X⦄ (hS : S ∈ sieves X) (R : sieve X),
              (∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, S.arrows f → R.pullback f ∈ sieves Y) → R ∈ sieves X)

namespace grothendieck_topology

instance : has_coe_to_fun (grothendieck_topology C) :=
⟨_, λ J, J.sieves⟩

variables {C} {X Y : C} {S R : sieve X}
variables (J : grothendieck_topology C)

@[simp] lemma mem_sieves_iff_coe : S ∈ J.sieves X ↔ S ∈ J X := iff.rfl

-- Also known as the maximality axiom.
@[simp] lemma top_mem (X : C) : ⊤ ∈ J X := J.top_mem' X
-- Also known as the stability axiom.
@[simp] lemma pullback_stable (f : Y ⟶ X) (hS : S ∈ J X) : S.pullback f ∈ J Y :=
J.pullback_stable' f hS
lemma transitive (hS : S ∈ J X) (R : sieve X)
  (h : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, S.arrows f → R.pullback f ∈ J Y) :
  R ∈ J X :=
J.transitive' hS R h

lemma covering_of_eq_top : S = ⊤ → S ∈ J X := λ h, h.symm ▸ J.top_mem X

lemma superset_covering (Hss : S ≤ R) (sjx : S ∈ J X) : R ∈ J X :=
begin
  apply J.transitive sjx R (λ Y f hf, _),
  apply covering_of_eq_top,
  rw [← top_le_iff, ← S.pullback_eq_top_of_mem hf],
  apply sieve.pullback_monotone _ Hss,
end

lemma intersection_covering (rj : R ∈ J X) (sj : S ∈ J X) : R ⊓ S ∈ J X :=
begin
  apply J.transitive rj _ (λ Y f Hf, _),
  rw [sieve.pullback_inter, R.pullback_eq_top_of_mem Hf],
  simp [sj],
end

@[simp]
lemma intersection_covering_iff : R ⊓ S ∈ J X ↔ R ∈ J X ∧ S ∈ J X :=
⟨λ h, ⟨J.superset_covering inf_le_left h, J.superset_covering inf_le_right h⟩,
 λ t, intersection_covering _ t.1 t.2⟩

/--
The sieve `S` on `X` `J`-covers an arrow `f` to `X` if `S.pullback f ∈ J Y`.
This definition is an alternate way of presenting a Grothendieck topology.
-/
def covers (S : sieve X) (f : Y ⟶ X) : Prop := S.pullback f ∈ J Y

lemma covers_iff (S : sieve X) (f : Y ⟶ X) : J.covers S f ↔ S.pullback f ∈ J Y :=
iff.rfl

lemma covering_iff_covers_id (S : sieve X) : S ∈ J X ↔ J.covers S (𝟙 X) :=
by simp [covers_iff]

/-- The maximality axiom in 'arrow' form: Any arrow `f` in `S` is covered by `S`. -/
lemma arrow_max (f : Y ⟶ X) (S : sieve X) (hf : S.arrows f) : J.covers S f :=
begin
  rw [covers, (sieve.pullback_eq_top_iff_mem f).1 hf],
  apply J.top_mem,
end

/-- The stability axiom in 'arrow' form: If `S` covers `f` then `S` covers `g ≫ f` for any `g`. -/
lemma arrow_stab (f : Y ⟶ X) (S : sieve X) (h : J.covers S f) {Z : C} (g : Z ⟶ Y) :
  J.covers S (g ≫ f) :=
begin
  rw covers_iff at h ⊢,
  simp [h, sieve.pullback_comp],
end

/--
The transitivity axiom in 'arrow' form: If `S` covers `f` and every arrow in `S` is covered by
`R`, then `R` covers `f`.
-/
lemma arrow_trans (f : Y ⟶ X) (S R : sieve X) (h : J.covers S f) :
  (∀ {Z : C} (g : Z ⟶ X), S.arrows g → J.covers R g) → J.covers R f :=
begin
  intro k,
  apply J.transitive h,
  intros Z g hg,
  rw ← sieve.pullback_comp,
  apply k (g ≫ f) hg,
end

lemma arrow_intersect (f : Y ⟶ X) (S R : sieve X) (hS : J.covers S f) (hR : J.covers R f) :
  J.covers (S ⊓ R) f :=
by simpa [covers_iff] using and.intro hS hR

instance : partial_order (grothendieck_topology C) :=
{ le := λ J₁ J₂, (J₁ : Π (X : C), set (sieve X)) ≤ (J₂ : Π (X : C), set (sieve X)),
  le_refl := λ J₁, le_refl _,
  le_trans := λ J₁ J₂ J₃ h₁₂ h₂₃, le_trans h₁₂ h₂₃,
  le_antisymm := λ J₁ J₂ h₁₂ h₂₁, grothendieck_topology.ext _ _ (le_antisymm h₁₂ h₂₁) }

instance : has_Inf (grothendieck_topology C) :=
{ Inf := λ T,
  { sieves := Inf (sieves '' T),
    top_mem' :=
    begin
      rintro X S ⟨⟨_, J, hJ, rfl⟩, rfl⟩,
      simp,
    end,
    pullback_stable' :=
    begin
      rintro X Y S hS f _ ⟨⟨_, J, hJ, rfl⟩, rfl⟩,
      apply J.pullback_stable _ (f _ ⟨⟨_, _, hJ, rfl⟩, rfl⟩),
    end,
    transitive' :=
    begin
      rintro X S hS R h _ ⟨⟨_, J, hJ, rfl⟩, rfl⟩,
      apply J.transitive (hS _ ⟨⟨_, _, hJ, rfl⟩, rfl⟩) _ (λ Y f hf, h hf _ ⟨⟨_, _, hJ, rfl⟩, rfl⟩),
    end } }

instance : complete_lattice (grothendieck_topology C) :=
complete_lattice_of_Inf _
begin
  intro T,
  refine @is_glb.of_image _ _ _ _ sieves _ _ _ _,
  { intros, refl },
  { exact is_glb_Inf _ },
end

variable (C)
def trivial : grothendieck_topology C :=
{ sieves := λ X, {⊤},
  top_mem' := λ X, rfl,
  pullback_stable' := λ X Y S f hf,
  begin
    rw set.mem_singleton_iff at ⊢ hf,
    simp [hf],
  end,
  transitive' := λ X S hS R hR,
  begin
    rw [set.mem_singleton_iff, ← sieve.id_mem_iff_eq_top] at hS,
    simpa using hR hS,
  end }
variable {C}

lemma trivial_covering : S ∈ trivial C X ↔ S = ⊤ := set.mem_singleton_iff

lemma trivial_covers (S : sieve X) (f : Y ⟶ X) : (trivial C).covers S f ↔ S.arrows f :=
by rw [covers_iff, trivial_covering, ← sieve.pullback_eq_top_iff_mem]

lemma trivial_eq_bot : trivial C = ⊥ :=
begin
  rw ← le_bot_iff,
  intros X S hS,
  rw trivial_covering at hS,
  apply covering_of_eq_top _ hS,
end

def discrete : grothendieck_topology C :=
{ sieves := λ X, set.univ,
  top_mem' := by simp,
  pullback_stable' := λ X Y f, by simp,
  transitive' := by simp }

lemma discrete_eq_top : discrete C = ⊤ := top_unique (λ S hS, set.mem_univ _)

/-- The dense Grothendieck topology. -/
def dense : grothendieck_topology C :=
{ sieves := λ X S, ∀ {Y : C} (f : Y ⟶ X), ∃ Z (g : Z ⟶ Y), S.arrows (g ≫ f),
  top_mem' := λ X Y f, ⟨Y, 𝟙 Y, ⟨⟩⟩,
  pullback_stable' :=
  begin
    intros X Y S h H Z f,
    rcases H (f ≫ h) with ⟨W, g, H'⟩,
    exact ⟨W, g, by simpa⟩,
  end,
  transitive' :=
  begin
    intros X S H₁ R H₂ Y f,
    rcases H₁ f with ⟨Z, g, H₃⟩,
    rcases H₂ H₃ (𝟙 Z) with ⟨W, h, H₄⟩,
    exact ⟨W, (h ≫ g), by simpa using H₄⟩,
  end }

instance : inhabited (grothendieck_topology C) := ⟨dense⟩

/--
A category satisfies the right Ore condition if any span can be completed to a
commutative square.
NB. Any category with pullbacks obviously satisfies the right Ore condition.
-/
def right_ore_condition (C : Type u) [category.{v} C] : Prop :=
∀ {X Y Z : C} (yx : Y ⟶ X) (zx : Z ⟶ X), ∃ W (wy : W ⟶ Y) (wz : W ⟶ Z), wy ≫ yx = wz ≫ zx

lemma right_ore_of_pullbacks [limits.has_pullbacks C] : right_ore_condition C :=
λ X Y Z yx zx, ⟨_, _, _, limits.pullback.condition⟩

/--
The atomic Grothendieck topology: a sieve is covering iff it is nonempty.
For the pullback stability condition, we need the right Ore condition to hold.
-/
def atomic (hro : right_ore_condition C) : grothendieck_topology C :=
{ sieves := λ X S, ∃ Y (f : Y ⟶ X), S.arrows f,
  top_mem' := λ X, ⟨_, 𝟙 _, ⟨⟩⟩,
  pullback_stable' :=
  begin
    rintros X Y S h ⟨Z, f, hf⟩,
    rcases hro h f with ⟨W, g, k, comm⟩,
    refine ⟨_, g, _⟩,
    simp [comm, hf],
  end,
  transitive' :=
  begin
    rintros X S ⟨Y, f, hf⟩ R h,
    rcases h hf with ⟨Z, g, hg⟩,
    exact ⟨_, _, hg⟩,
  end }

lemma dense_covering : S ∈ dense X ↔ ∀ {Y} (f : Y ⟶ X), ∃ Z (g : Z ⟶ Y), S.arrows (g ≫ f) :=
iff.rfl

end grothendieck_topology

end category_theory
