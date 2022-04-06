/-
Copyright (c) 2020 Bhavik Mehta, E. W. Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, E. W. Ayers
-/

import category_theory.sites.sieves
import category_theory.limits.shapes.pullbacks
import category_theory.limits.shapes.multiequalizer
import category_theory.category.preorder
import order.copy

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

A pretopology, or a basis for a topology is defined in `pretopology.lean`. The topology associated
to a topological space is defined in `spaces.lean`.

## Tags

Grothendieck topology, coverage, pretopology, site

## References

* [nLab, *Grothendieck topology*](https://ncatlab.org/nlab/show/Grothendieck+topology)
* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]

## Implementation notes

We use the definition of [nlab] and [MM92][] (Chapter III, Section 2), where Grothendieck topologies
are saturated collections of morphisms, rather than the notions of the Stacks project (00VG) and
the Elephant, in which topologies are allowed to be unsaturated, and are then completed.
TODO (BM): Add the definition from Stacks, as a pretopology, and complete to a topology.

This is so that we can produce a bijective correspondence between Grothendieck topologies on a
small category and Lawvere-Tierney topologies on its presheaf topos, as well as the equivalence
between Grothendieck topoi and left exact reflective subcategories of presheaf toposes.
-/

universes w v u
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

See https://stacks.math.columbia.edu/tag/00Z4, or [nlab], or [MM92][] Chapter III, Section 2,
Definition 1.
-/
structure grothendieck_topology :=
(sieves : Π (X : C), set (sieve X))
(top_mem' : ∀ X, ⊤ ∈ sieves X)
(pullback_stable' : ∀ ⦃X Y : C⦄ ⦃S : sieve X⦄ (f : Y ⟶ X), S ∈ sieves X → S.pullback f ∈ sieves Y)
(transitive' : ∀ ⦃X⦄ ⦃S : sieve X⦄ (hS : S ∈ sieves X) (R : sieve X),
              (∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f → R.pullback f ∈ sieves Y) → R ∈ sieves X)

namespace grothendieck_topology

instance : has_coe_to_fun (grothendieck_topology C) (λ _, Π X : C, set (sieve X)) := ⟨sieves⟩

variables {C} {X Y : C} {S R : sieve X}
variables (J : grothendieck_topology C)

/--
An extensionality lemma in terms of the coercion to a pi-type.
We prove this explicitly rather than deriving it so that it is in terms of the coercion rather than
the projection `.sieves`.
-/
@[ext]
lemma ext {J₁ J₂ : grothendieck_topology C} (h : (J₁ : Π (X : C), set (sieve X)) = J₂) : J₁ = J₂ :=
by { cases J₁, cases J₂, congr, apply h }

@[simp] lemma mem_sieves_iff_coe : S ∈ J.sieves X ↔ S ∈ J X := iff.rfl

-- Also known as the maximality axiom.
@[simp] lemma top_mem (X : C) : ⊤ ∈ J X := J.top_mem' X
-- Also known as the stability axiom.
@[simp] lemma pullback_stable (f : Y ⟶ X) (hS : S ∈ J X) : S.pullback f ∈ J Y :=
J.pullback_stable' f hS
lemma transitive (hS : S ∈ J X) (R : sieve X)
  (h : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f → R.pullback f ∈ J Y) :
  R ∈ J X :=
J.transitive' hS R h

lemma covering_of_eq_top : S = ⊤ → S ∈ J X := λ h, h.symm ▸ J.top_mem X

/--
If `S` is a subset of `R`, and `S` is covering, then `R` is covering as well.

See https://stacks.math.columbia.edu/tag/00Z5 (2), or discussion after [MM92] Chapter III,
Section 2, Definition 1.
-/
lemma superset_covering (Hss : S ≤ R) (sjx : S ∈ J X) : R ∈ J X :=
begin
  apply J.transitive sjx R (λ Y f hf, _),
  apply covering_of_eq_top,
  rw [← top_le_iff, ← S.pullback_eq_top_of_mem hf],
  apply sieve.pullback_monotone _ Hss,
end

/--
The intersection of two covering sieves is covering.

See https://stacks.math.columbia.edu/tag/00Z5 (1), or [MM92] Chapter III,
Section 2, Definition 1 (iv).
-/
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

lemma bind_covering {S : sieve X} {R : Π ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → sieve Y} (hS : S ∈ J X)
  (hR : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (H : S f), R H ∈ J Y) :
sieve.bind S R ∈ J X :=
J.transitive hS _ (λ Y f hf, superset_covering J (sieve.le_pullback_bind S R f hf) (hR hf))

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
lemma arrow_max (f : Y ⟶ X) (S : sieve X) (hf : S f) : J.covers S f :=
begin
  rw [covers, (sieve.pullback_eq_top_iff_mem f).1 hf],
  apply J.top_mem,
end

/-- The stability axiom in 'arrow' form: If `S` covers `f` then `S` covers `g ≫ f` for any `g`. -/
lemma arrow_stable (f : Y ⟶ X) (S : sieve X) (h : J.covers S f) {Z : C} (g : Z ⟶ Y) :
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
  (∀ {Z : C} (g : Z ⟶ X), S g → J.covers R g) → J.covers R f :=
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

variable (C)
/--
The trivial Grothendieck topology, in which only the maximal sieve is covering. This topology is
also known as the indiscrete, coarse, or chaotic topology.

See [MM92] Chapter III, Section 2, example (a), or
https://en.wikipedia.org/wiki/Grothendieck_topology#The_discrete_and_indiscrete_topologies
-/
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

/--
The discrete Grothendieck topology, in which every sieve is covering.

See https://en.wikipedia.org/wiki/Grothendieck_topology#The_discrete_and_indiscrete_topologies.
-/
def discrete : grothendieck_topology C :=
{ sieves := λ X, set.univ,
  top_mem' := by simp,
  pullback_stable' := λ X Y f, by simp,
  transitive' := by simp }
variable {C}

lemma trivial_covering : S ∈ trivial C X ↔ S = ⊤ := set.mem_singleton_iff

/-- See https://stacks.math.columbia.edu/tag/00Z6 -/
instance : has_le (grothendieck_topology C) :=
{ le := λ J₁ J₂, (J₁ : Π (X : C), set (sieve X)) ≤ (J₂ : Π (X : C), set (sieve X)) }

lemma le_def {J₁ J₂ : grothendieck_topology C} :
  J₁ ≤ J₂ ↔ (J₁ : Π (X : C), set (sieve X)) ≤ J₂ := iff.rfl

/-- See https://stacks.math.columbia.edu/tag/00Z6 -/
instance : partial_order (grothendieck_topology C) :=
{ le_refl := λ J₁, le_def.mpr le_rfl,
  le_trans := λ J₁ J₂ J₃ h₁₂ h₂₃, le_def.mpr (le_trans h₁₂ h₂₃),
  le_antisymm := λ J₁ J₂ h₁₂ h₂₁, grothendieck_topology.ext (le_antisymm h₁₂ h₂₁),
  ..grothendieck_topology.has_le }

/-- See https://stacks.math.columbia.edu/tag/00Z7 -/
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

/-- See https://stacks.math.columbia.edu/tag/00Z7 -/
lemma is_glb_Inf (s : set (grothendieck_topology C)) : is_glb s (Inf s) :=
begin
  refine @is_glb.of_image _ _ _ _ sieves _ _ _ _,
  { intros, refl },
  { exact is_glb_Inf _ },
end

/--
Construct a complete lattice from the `Inf`, but make the trivial and discrete topologies
definitionally equal to the bottom and top respectively.
-/
instance : complete_lattice (grothendieck_topology C) :=
complete_lattice.copy
(complete_lattice_of_Inf _ is_glb_Inf)
_ rfl
(discrete C)
(begin
  apply le_antisymm,
  { exact @complete_lattice.le_top _ (complete_lattice_of_Inf _ is_glb_Inf) (discrete C) },
  { intros X S hS,
    apply set.mem_univ },
end)
(trivial C)
(begin
  apply le_antisymm,
  { intros X S hS,
    rw trivial_covering at hS,
    apply covering_of_eq_top _ hS },
  { refine @complete_lattice.bot_le _ (complete_lattice_of_Inf _ is_glb_Inf) (trivial C) },
end)
_ rfl
_ rfl
_ rfl
Inf rfl

instance : inhabited (grothendieck_topology C) := ⟨⊤⟩

@[simp] lemma trivial_eq_bot : trivial C = ⊥ := rfl
@[simp] lemma discrete_eq_top : discrete C = ⊤ := rfl

@[simp] lemma bot_covering : S ∈ (⊥ : grothendieck_topology C) X ↔ S = ⊤ := trivial_covering
@[simp] lemma top_covering : S ∈ (⊤ : grothendieck_topology C) X := ⟨⟩

lemma bot_covers (S : sieve X) (f : Y ⟶ X) :
  (⊥ : grothendieck_topology C).covers S f ↔ S f :=
by rw [covers_iff, bot_covering, ← sieve.pullback_eq_top_iff_mem]

@[simp] lemma top_covers (S : sieve X) (f : Y ⟶ X) : (⊤ : grothendieck_topology C).covers S f :=
by simp [covers_iff]

/--
The dense Grothendieck topology.

See https://ncatlab.org/nlab/show/dense+topology, or [MM92] Chapter III, Section 2, example (e).
-/
def dense : grothendieck_topology C :=
{ sieves := λ X S, ∀ {Y : C} (f : Y ⟶ X), ∃ Z (g : Z ⟶ Y), S (g ≫ f),
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

lemma dense_covering : S ∈ dense X ↔ ∀ {Y} (f : Y ⟶ X), ∃ Z (g : Z ⟶ Y), S (g ≫ f) :=
iff.rfl

/--
A category satisfies the right Ore condition if any span can be completed to a commutative square.
NB. Any category with pullbacks obviously satisfies the right Ore condition, see
`right_ore_of_pullbacks`.
-/
def right_ore_condition (C : Type u) [category.{v} C] : Prop :=
∀ {X Y Z : C} (yx : Y ⟶ X) (zx : Z ⟶ X), ∃ W (wy : W ⟶ Y) (wz : W ⟶ Z), wy ≫ yx = wz ≫ zx

lemma right_ore_of_pullbacks [limits.has_pullbacks C] : right_ore_condition C :=
λ X Y Z yx zx, ⟨_, _, _, limits.pullback.condition⟩

/--
The atomic Grothendieck topology: a sieve is covering iff it is nonempty.
For the pullback stability condition, we need the right Ore condition to hold.

See https://ncatlab.org/nlab/show/atomic+site, or [MM92] Chapter III, Section 2, example (f).
-/
def atomic (hro : right_ore_condition C) : grothendieck_topology C :=
{ sieves := λ X S, ∃ Y (f : Y ⟶ X), S f,
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

/-- `J.cover X` denotes the poset of covers of `X` with respect to the
Grothendieck topology `J`. -/
@[derive preorder]
def cover (X : C) := { S : sieve X // S ∈ J X }

namespace cover

variables {J}

instance : has_coe (J.cover X) (sieve X) := ⟨λ S, S.1⟩

instance : has_coe_to_fun (J.cover X) (λ S, Π ⦃Y⦄ (f : Y ⟶ X), Prop) :=
⟨λ S Y f, (S : sieve X) f⟩

@[simp]
lemma coe_fun_coe (S : J.cover X) (f : Y ⟶ X) : (S : sieve X) f = S f := rfl

lemma condition (S : J.cover X) : (S : sieve X) ∈ J X := S.2

@[ext]
lemma ext (S T : J.cover X) (h : ∀ ⦃Y⦄ (f : Y ⟶ X), S f ↔ T f) : S = T :=
subtype.ext $ sieve.ext h

instance : order_top (J.cover X) :=
{ top := ⟨⊤, J.top_mem _⟩,
  le_top := λ S Y f h, by tauto,
  ..(infer_instance : preorder _) }

instance : semilattice_inf (J.cover X) :=
{ inf := λ S T, ⟨S ⊓ T, J.intersection_covering S.condition T.condition⟩,
  le_antisymm := λ S T h1 h2, ext _ _ $ λ Y f, ⟨h1 _, h2 _⟩,
  inf_le_left := λ S T Y f hf, hf.1,
  inf_le_right := λ S T Y f hf, hf.2,
  le_inf := λ S T W h1 h2 Y f h, ⟨h1 _ h, h2 _ h⟩,
  ..(infer_instance : preorder _) }

instance : inhabited (J.cover X) := ⟨⊤⟩

/-- An auxiliary structure, used to define `S.index` in `plus.lean`. -/
@[nolint has_inhabited_instance, ext]
structure arrow (S : J.cover X) :=
(Y : C)
(f : Y ⟶ X)
(hf : S f)

/-- An auxiliary structure, used to define `S.index` in `plus.lean`. -/
@[nolint has_inhabited_instance, ext]
structure relation (S : J.cover X) :=
(Y₁ Y₂ Z : C)
(g₁ : Z ⟶ Y₁)
(g₂ : Z ⟶ Y₂)
(f₁ : Y₁ ⟶ X)
(f₂ : Y₂ ⟶ X)
(h₁ : S f₁)
(h₂ : S f₂)
(w : g₁ ≫ f₁ = g₂ ≫ f₂)

/-- Map a `arrow` along a refinement `S ⟶ T`. -/
@[simps]
def arrow.map {S T : J.cover X} (I : S.arrow) (f : S ⟶ T) : T.arrow :=
⟨I.Y, I.f, f.le _ I.hf⟩

/-- Map a `relation` along a refinement `S ⟶ T`. -/
@[simps]
def relation.map {S T : J.cover X} (I : S.relation) (f : S ⟶ T) : T.relation :=
⟨_, _, _, I.g₁, I.g₂, I.f₁, I.f₂, f.le _ I.h₁, f.le _ I.h₂, I.w⟩

/-- The first `arrow` associated to a `relation`.
Used in defining `index` in `plus.lean`. -/
@[simps]
def relation.fst {S : J.cover X} (I : S.relation) : S.arrow :=
⟨I.Y₁, I.f₁, I.h₁⟩

/-- The second `arrow` associated to a `relation`.
Used in defining `index` in `plus.lean`. -/
@[simps]
def relation.snd {S : J.cover X} (I : S.relation) : S.arrow :=
⟨I.Y₂, I.f₂, I.h₂⟩

@[simp]
lemma relation.map_fst {S T : J.cover X} (I : S.relation) (f : S ⟶ T) :
   I.fst.map f = (I.map f).fst := rfl

@[simp]
lemma relation.map_snd {S T : J.cover X} (I : S.relation) (f : S ⟶ T) :
  I.snd.map f = (I.map f).snd := rfl

/-- Pull back a cover along a morphism. -/
def pullback (S : J.cover X) (f : Y ⟶ X) : J.cover Y :=
⟨sieve.pullback f S, J.pullback_stable _ S.condition⟩

/-- An arrow of `S.pullback f` gives rise to an arrow of `S`. -/
@[simps]
def arrow.base {f : Y ⟶ X} {S : J.cover X} (I : (S.pullback f).arrow) : S.arrow :=
⟨I.Y, I.f ≫ f, I.hf⟩

/-- A relation of `S.pullback f` gives rise to a relation of `S`. -/
@[simps]
def relation.base {f : Y ⟶ X} {S : J.cover X} (I : (S.pullback f).relation) : S.relation :=
⟨_, _, _, I.g₁, I.g₂, I.f₁ ≫ f, I.f₂≫ f, I.h₁, I.h₂, by simp [reassoc_of I.w]⟩

@[simp]
lemma relation.base_fst {f : Y ⟶ X} {S : J.cover X} (I : (S.pullback f).relation) :
 I.fst.base = I.base.fst := rfl

@[simp]
lemma relation.base_snd {f : Y ⟶ X} {S : J.cover X} (I : (S.pullback f).relation) :
 I.snd.base = I.base.snd := rfl

@[simp]
lemma coe_pullback {Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) (S : J.cover X) :
  (S.pullback f) g ↔ S (g ≫ f) := iff.rfl

/-- The isomorphism between `S` and the pullback of `S` w.r.t. the identity. -/
def pullback_id (S : J.cover X) : S.pullback (𝟙 X) ≅ S :=
eq_to_iso $ cover.ext _ _ $ λ Y f, by simp

/-- Pulling back with respect to a composition is the composition of the pullbacks. -/
def pullback_comp {X Y Z : C} (S : J.cover X) (f : Z ⟶ Y) (g : Y ⟶ X) :
  S.pullback (f ≫ g) ≅ (S.pullback g).pullback f :=
eq_to_iso $ cover.ext _ _ $ λ Y f, by simp

/-- Combine a family of covers over a cover. -/
def bind {X : C} (S : J.cover X) (T : Π (I : S.arrow), J.cover I.Y) : J.cover X :=
⟨sieve.bind S (λ Y f hf, T ⟨Y, f, hf⟩), J.bind_covering S.condition (λ _ _ _, (T _).condition)⟩

/-- The canonical moprhism from `S.bind T` to `T`. -/
def bind_to_base {X : C} (S : J.cover X) (T : Π (I : S.arrow), J.cover I.Y) : S.bind T ⟶ S :=
hom_of_le $ by { rintro Y f ⟨Z,e1,e2,h1,h2,h3⟩, rw ← h3, apply sieve.downward_closed, exact h1 }

/-- An arrow in bind has the form `A ⟶ B ⟶ X` where `A ⟶ B` is an arrow in `T I` for some `I`.
 and `B ⟶ X` is an arrow of `S`. This is the object `B`. -/
noncomputable def arrow.middle {X : C} {S : J.cover X} {T : Π (I : S.arrow), J.cover I.Y}
  (I : (S.bind T).arrow) : C :=
I.hf.some

/-- An arrow in bind has the form `A ⟶ B ⟶ X` where `A ⟶ B` is an arrow in `T I` for some `I`.
 and `B ⟶ X` is an arrow of `S`. This is the hom `A ⟶ B`. -/
noncomputable def arrow.to_middle_hom {X : C} {S : J.cover X} {T : Π (I : S.arrow), J.cover I.Y}
  (I : (S.bind T).arrow) : I.Y ⟶ I.middle :=
I.hf.some_spec.some

/-- An arrow in bind has the form `A ⟶ B ⟶ X` where `A ⟶ B` is an arrow in `T I` for some `I`.
 and `B ⟶ X` is an arrow of `S`. This is the hom `B ⟶ X`. -/
noncomputable def arrow.from_middle_hom {X : C} {S : J.cover X} {T : Π (I : S.arrow), J.cover I.Y}
  (I : (S.bind T).arrow) : I.middle ⟶ X :=
I.hf.some_spec.some_spec.some

lemma arrow.from_middle_condition {X : C} {S : J.cover X} {T : Π (I : S.arrow), J.cover I.Y}
  (I : (S.bind T).arrow) : S I.from_middle_hom :=
I.hf.some_spec.some_spec.some_spec.some

/-- An arrow in bind has the form `A ⟶ B ⟶ X` where `A ⟶ B` is an arrow in `T I` for some `I`.
 and `B ⟶ X` is an arrow of `S`. This is the hom `B ⟶ X`, as an arrow. -/
noncomputable
def arrow.from_middle {X : C} {S : J.cover X} {T : Π (I : S.arrow), J.cover I.Y}
  (I : (S.bind T).arrow) : S.arrow := ⟨_, I.from_middle_hom, I.from_middle_condition⟩

lemma arrow.to_middle_condition {X : C} {S : J.cover X} {T : Π (I : S.arrow), J.cover I.Y}
  (I : (S.bind T).arrow) : (T I.from_middle) I.to_middle_hom :=
I.hf.some_spec.some_spec.some_spec.some_spec.1

/-- An arrow in bind has the form `A ⟶ B ⟶ X` where `A ⟶ B` is an arrow in `T I` for some `I`.
 and `B ⟶ X` is an arrow of `S`. This is the hom `A ⟶ B`, as an arrow. -/
noncomputable
def arrow.to_middle {X : C} {S : J.cover X} {T : Π (I : S.arrow), J.cover I.Y}
  (I : (S.bind T).arrow) : (T I.from_middle).arrow := ⟨_, I.to_middle_hom, I.to_middle_condition⟩

lemma arrow.middle_spec {X : C} {S : J.cover X} {T : Π (I : S.arrow), J.cover I.Y}
  (I : (S.bind T).arrow) : I.to_middle_hom ≫ I.from_middle_hom = I.f :=
I.hf.some_spec.some_spec.some_spec.some_spec.2

-- This is used extensively in `plus.lean`, etc.
-- We place this definition here as it will be used in `sheaf.lean` as well.
/-- To every `S : J.cover X` and presheaf `P`, associate a `multicospan_index`. -/
def index {D : Type w} [category.{max v u} D] (S : J.cover X) (P : Cᵒᵖ ⥤ D) :
  limits.multicospan_index D :=
{ L := S.arrow,
  R := S.relation,
  fst_to := λ I, I.fst,
  snd_to := λ I, I.snd,
  left := λ I, P.obj (opposite.op I.Y),
  right := λ I, P.obj (opposite.op I.Z),
  fst := λ I, P.map I.g₁.op,
  snd := λ I, P.map I.g₂.op }

/-- The natural multifork associated to `S : J.cover X` for a presheaf `P`.
Saying that this multifork is a limit is essentially equivalent to the sheaf condition at the
given object for the given covering sieve. See `sheaf.lean` for an equivalent sheaf condition
using this.
-/
abbreviation multifork {D : Type w} [category.{max v u} D] (S : J.cover X) (P : Cᵒᵖ ⥤ D) :
  limits.multifork (S.index P) :=
limits.multifork.of_ι _ (P.obj (opposite.op X)) (λ I, P.map I.f.op) begin
  intros I,
  dsimp [index],
  simp only [← P.map_comp, ← op_comp, I.w]
end

/-- The canonical map from `P.obj (op X)` to the multiequalizer associated to a covering sieve,
assuming such a multiequalizer exists. This will be used in `sheaf.lean` to provide an equivalent
sheaf condition in terms of multiequalizers. -/
noncomputable
abbreviation to_multiequalizer {D : Type w} [category.{max v u} D] (S : J.cover X) (P : Cᵒᵖ ⥤ D)
  [limits.has_multiequalizer (S.index P)] :
P.obj (opposite.op X) ⟶ limits.multiequalizer (S.index P) :=
limits.multiequalizer.lift _ _ (λ I, P.map I.f.op) begin
  intros I,
  dsimp only [index, relation.fst, relation.snd],
  simp only [← P.map_comp, ← op_comp, I.w],
end

end cover

/-- Pull back a cover along a morphism. -/
@[simps obj]
def pullback (f : Y ⟶ X) : J.cover X ⥤ J.cover Y :=
{ obj := λ S, S.pullback f,
  map := λ S T f, (sieve.pullback_monotone _ f.le).hom }

/-- Pulling back along the identity is naturally isomorphic to the identity functor. -/
def pullback_id (X : C) : J.pullback (𝟙 X) ≅ 𝟭 _ :=
nat_iso.of_components (λ S, S.pullback_id) $ by tidy

/-- Pulling back along a composition is naturally isomorphic to
the composition of the pullbacks. -/
def pullback_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  J.pullback (f ≫ g) ≅ J.pullback g ⋙ J.pullback f :=
nat_iso.of_components (λ S, S.pullback_comp f g) $ by tidy

end grothendieck_topology

end category_theory
