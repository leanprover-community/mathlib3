/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.limits
import category_theory.punit
import category_theory.comma
import category_theory.is_connected

/-!
# Cofinal functors

A functor `F : C ⥤ D` is cofinal if for every `d : D`,
the comma category of morphisms `d ⟶ F.obj c` is connected.

We prove that when `F : C ⥤ D` is cofinal,
a functor `G : D ⥤ E` has a colimit if and only if `F ⋙ D` does
(and in either case, the colimits are isomorphic).

There is a converse which we don't prove here.

## Naming
There is some discrepancy in the literature about naming; some say 'final' instead of 'cofinal'.
The explanation for this is that the 'co' prefix here is *not* the usual category-theoretic one
indicating duality, but rather indicating the sense of "along with".

While the trend seems to be towards using 'final', for now we go with the bulk of the literature
and use 'cofinal'.

## References
* https://stacks.math.columbia.edu/tag/09WN
* https://ncatlab.org/nlab/show/final+functor
* Borceux, Handbook of Categorical Algebra I, Section 2.11.
  (Note he reverses the roles of definition and main result relative to here!)
-/

noncomputable theory

universes v u

namespace category_theory
open category_theory.limits

variables {C : Type v} [small_category C]
variables {D : Type v} [small_category D]

/--
A functor `F : C ⥤ D` is cofinal if for every `d : D`, the comma category of morphisms `d ⟶ F.obj c`
is connected.

See https://stacks.math.columbia.edu/tag/04E6
-/
def cofinal (F : C ⥤ D) : Prop :=
∀ (d : D), is_connected (comma (functor.from_punit d) F)

attribute [class] cofinal

instance (F : C ⥤ D) [ℱ : cofinal F] (d : D) : is_connected (comma (functor.from_punit d) F) :=
ℱ d

namespace cofinal

variables (F : C ⥤ D) [ℱ : cofinal F]
include ℱ

instance (d : D) : nonempty (comma (functor.from_punit d) F) := (‹cofinal F› d).is_nonempty

variables {E : Type u} [category.{v} E] (G : D ⥤ E)

/--
When `F : C ⥤ D` is cofinal, we denote by `lift F d` an arbitrary choice of object in `C` such that
there exists a morphism `d ⟶ F.obj (lift F d)`.
-/
def lift (d : D) : C :=
(classical.arbitrary (comma (functor.from_punit d) F)).right

/--
When `F : C ⥤ D` is cofinal, we denote by `hom_to_lift` an arbitrary choice of morphism
`d ⟶ F.obj (lift F d)`.
-/
def hom_to_lift (d : D) : d ⟶ F.obj (lift F d) :=
(classical.arbitrary (comma (functor.from_punit d) F)).hom

/--
We provide an induction principle for reasoning about `lift` and `hom_to_lift`.
We want to perform some construction (usually just a proof) about
the particular choices `lift F d` and `hom_to_lift F d`,
it suffices to perform that construction for some other pair of choices
(denoted `X₀ : C` and `k₀ : d ⟶ F.obj X₀` below),
and to show that how to transport such a construction
*both* directions along a morphism between such choices.
-/
def induction {d : D} (Z : Π (X : C) (k : d ⟶ F.obj X), Sort*)
  (h₁ : Π X₁ X₂ (k₁ : d ⟶ F.obj X₁) (k₂ : d ⟶ F.obj X₂) (f : X₁ ⟶ X₂), (k₁ ≫ F.map f = k₂) → Z X₁ k₁ → Z X₂ k₂)
  (h₂ : Π X₁ X₂ (k₁ : d ⟶ F.obj X₁) (k₂ : d ⟶ F.obj X₂) (f : X₁ ⟶ X₂), (k₁ ≫ F.map f = k₂) → Z X₂ k₂ → Z X₁ k₁)
  {X₀ : C} {k₀ : d ⟶ F.obj X₀} (z : Z X₀ k₀) : Z (lift F d) (hom_to_lift F d) :=
begin
  apply @is_preconnected_induction _ _ _
    (λ (Y : comma (functor.from_punit d) F), Z Y.right Y.hom) _ _ { right := X₀, hom := k₀, } z,
  { intros, fapply h₁ _ _ _ _ f.right _ a, convert f.w.symm, dsimp, simp, },
  { intros, fapply h₂ _ _ _ _ f.right _ a, convert f.w.symm, dsimp, simp, },
end

variables {F G}

/--
Given a cocone over `F ⋙ G`, we can construct a `cocone G` with the same cocone point.
-/
@[simps]
def extend_cocone (c : cocone (F ⋙ G)) : cocone G :=
{ X := c.X,
  ι :=
  { app := λ X, G.map (hom_to_lift F X) ≫ c.ι.app (lift F X),
    naturality' := λ X Y f,
    begin
      dsimp, simp,
      -- This would be true if we'd chosen `lift F X` to be `lift F Y`
      -- and `hom_to_lift F X` to be `f ≫ hom_to_lift F Y`.
      apply induction F (λ Z k, G.map f ≫ G.map (hom_to_lift F Y) ≫ c.ι.app (lift F Y) = G.map k ≫ c.ι.app Z),
      { intros Z₁ Z₂ k₁ k₂ g a z,
       rw [←a, functor.map_comp, category.assoc, ←functor.comp_map, c.w, z], },
      { intros Z₁ Z₂ k₁ k₂ g a z,
       rw [←a, functor.map_comp, category.assoc, ←functor.comp_map, c.w] at z,
       rw z, },
      { rw [←functor.map_comp_assoc], },
    end }}

variables (F)

@[simp]
lemma colimit_cocone_comp_aux (s : cocone (F ⋙ G)) (j : C) :
  G.map (hom_to_lift F (F.obj j)) ≫ s.ι.app (lift F (F.obj j)) =
    s.ι.app j :=
begin
  -- This point is that this would be true if we took `lift (F.obj j)` to just be `j`
  -- and `hom_to_lift (F.obj j)` to be `𝟙 (F.obj j)`.
  apply induction F (λ X k, G.map k ≫ s.ι.app X = (s.ι.app j : _)),
  { intros j₁ j₂ k₁ k₂ f w h, rw ←w, rw ← s.w f at h, simpa using h, },
  { intros j₁ j₂ k₁ k₂ f w h, rw ←w at h, rw ← s.w f, simpa using h, },
  { exact s.w (𝟙 _), },
end

/-- Given a colimit cocone over `G` we can construct a colimit cocone over `F ⋙ G`. -/
@[simps]
def colimit_cocone_comp (t : colimit_cocone G) :
  colimit_cocone (F ⋙ G) :=
{ cocone := t.cocone.whisker F,
  is_colimit :=
  { desc := λ s, t.is_colimit.desc (extend_cocone s),
    uniq' := λ s m w,
    begin
      apply t.is_colimit.hom_ext,
      intro d,
      simp [(w _).symm],
    end, }, }.

@[priority 100]
instance comp_has_colimit [has_colimit G] :
  has_colimit (F ⋙ G) :=
has_colimit.mk (colimit_cocone_comp F (get_colimit_cocone G))

lemma colimit_pre_is_iso_aux (t : colimit_cocone G) :
  (colimit_cocone_comp F t).is_colimit.desc (t.cocone.whisker F) = 𝟙 t.cocone.X :=
begin
  apply t.is_colimit.hom_ext,
  tidy,
end

instance colimit_pre_is_iso [has_colimit G] :
  is_iso (colimit.pre G F) :=
begin
  rw colimit.pre_eq (colimit_cocone_comp F (get_colimit_cocone G)) (get_colimit_cocone G),
  rw colimit_pre_is_iso_aux,
  dsimp,
  apply_instance,
end

/--
When `F` is cofinal, and `G` has a colimit, then `F ⋙ G` has a colimit also and
`colimit (F ⋙ G) ≅ colimit G`

https://stacks.math.columbia.edu/tag/04E7
-/
def colimit_iso [has_colimit G] : colimit (F ⋙ G) ≅ colimit G := as_iso (colimit.pre G F)

/-- Given a colimit cocone over `F ⋙ G` we can construct a colimit cocone over `G`. -/
@[simps]
def colimit_cocone_of_comp (t : colimit_cocone (F ⋙ G)) :
  colimit_cocone G :=
{ cocone := extend_cocone t.cocone,
  is_colimit :=
  { desc := λ s, t.is_colimit.desc (s.whisker F),
    uniq' := λ s m w,
    begin
      apply t.is_colimit.hom_ext,
      intro X,
      simp [(w _).symm],
    end, }, }

/--
When `F` is cofinal, and `F ⋙ G` has a colimit, then `G` has a colimit also.

We can't make this an instance.
-/
lemma has_colimit_of_comp [has_colimit (F ⋙ G)] :
  has_colimit G :=
has_colimit.mk (colimit_cocone_of_comp F (get_colimit_cocone (F ⋙ G)))

section
local attribute [instance] has_colimit_of_comp

/--
When `F` is cofinal, and `F ⋙ G` has a colimit, then `G` has a colimit also and
`colimit (F ⋙ G) ≅ colimit G`

https://stacks.math.columbia.edu/tag/04E7
-/
def colimit_iso' [has_colimit (F ⋙ G)] : colimit (F ⋙ G) ≅ colimit G := as_iso (colimit.pre G F)

end

end cofinal

end category_theory
