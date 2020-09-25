/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.punit
import category_theory.comma
import category_theory.is_connected
import category_theory.limits.yoneda
import category_theory.limits.types

/-!
# Cofinal functors

A functor `F : C ⥤ D` is cofinal if for every `d : D`,
the comma category of morphisms `d ⟶ F.obj c` is connected.

We prove the following three statements are equivalent:
1. `F : C ⥤ D` is cofinal.
2. A functor `G : D ⥤ E` has a colimit if and only if `F ⋙ G` does,
   and these colimits are isomorphic via `colimit.pre G F`.
3. `colimit (F ⋙ coyoneda.obj (op d)) ≅ punit`

Starting at 1. we show (in `cocones_equiv`) that
the categories of cocones over `G : D ⥤ E` and over `F ⋙ G` are equivalent.
(In fact, via an equivalence which does not change the cocone point.)
This readily implies 2, as `comp_has_colimit`, `has_colimit_of_comp`, and `colimit_iso`.

From 2. we can specialize to `G = coyoneda.obj (op d)` to obtain 3., as `colimit_comp_coyoneda_iso`.

From 3., we prove 1. directly in `cofinal_of_colimit_comp_coyoneda_iso_punit`.

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

open opposite
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

variables (F : C ⥤ D) [cofinal F]

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
lemma induction {d : D} (Z : Π (X : C) (k : d ⟶ F.obj X), Prop)
  (h₁ : Π X₁ X₂ (k₁ : d ⟶ F.obj X₁) (k₂ : d ⟶ F.obj X₂) (f : X₁ ⟶ X₂),
    (k₁ ≫ F.map f = k₂) → Z X₁ k₁ → Z X₂ k₂)
  (h₂ : Π X₁ X₂ (k₁ : d ⟶ F.obj X₁) (k₂ : d ⟶ F.obj X₂) (f : X₁ ⟶ X₂),
    (k₁ ≫ F.map f = k₂) → Z X₂ k₂ → Z X₁ k₁)
  {X₀ : C} {k₀ : d ⟶ F.obj X₀} (z : Z X₀ k₀) : Z (lift F d) (hom_to_lift F d) :=
begin
  apply nonempty.some,
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
def extend_cocone : cocone (F ⋙ G) ⥤ cocone G :=
{ obj := λ c,
  { X := c.X,
    ι :=
    { app := λ X, G.map (hom_to_lift F X) ≫ c.ι.app (lift F X),
      naturality' := λ X Y f,
      begin
        dsimp, simp,
        -- This would be true if we'd chosen `lift F X` to be `lift F Y`
        -- and `hom_to_lift F X` to be `f ≫ hom_to_lift F Y`.
        apply induction F
          (λ Z k, G.map f ≫ G.map (hom_to_lift F Y) ≫ c.ι.app (lift F Y) = G.map k ≫ c.ι.app Z),
        { intros Z₁ Z₂ k₁ k₂ g a z,
        rw [←a, functor.map_comp, category.assoc, ←functor.comp_map, c.w, z], },
        { intros Z₁ Z₂ k₁ k₂ g a z,
        rw [←a, functor.map_comp, category.assoc, ←functor.comp_map, c.w] at z,
        rw z, },
        { rw [←functor.map_comp_assoc], },
      end } },
  map := λ X Y f,
  { hom := f.hom, } }

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

variables (F G)

/--
If `F` is cofinal,
the category of cocones on `F ⋙ G` is equivalent to the category of cocones on `G`.
-/
@[simps]
def cocones_equiv : cocone (F ⋙ G) ≌ cocone G :=
{ functor := extend_cocone,
  inverse := cocones.whiskering F,
  unit_iso := nat_iso.of_components (λ c, cocones.ext (iso.refl _) (by tidy)) (by tidy),
  counit_iso := nat_iso.of_components (λ c, cocones.ext (iso.refl _) (by tidy)) (by tidy), }.

def cones_equiv (H : Dᵒᵖ ⥤ E) : cone (F.op ⋙ H) ≌ cone H :=
begin
  have := cocones_equiv F (unop_unop ⋙ H.op),
end

variables {G}

/--
When `F` is cofinal, and `t : cocone G`,
`t.whisker F` is a colimit coconne exactly when `t` is.
-/
def is_colimit_whisker_equiv (t : cocone G) : is_colimit (t.whisker F) ≃ is_colimit t :=
is_colimit.of_cocone_equiv (cocones_equiv F G).symm

/--
When `F` is cofinal, and `t : cocone (F ⋙ G)`,
`extend_cocone.obj t` is a colimit coconne exactly when `t` is.
-/
def is_colimit_extend_cocone_equiv (t : cocone (F ⋙ G)) :
  is_colimit (extend_cocone.obj t) ≃ is_colimit t :=
is_colimit.of_cocone_equiv (cocones_equiv F G)

/-- Given a colimit cocone over `G` we can construct a colimit cocone over `F ⋙ G`. -/
@[simps]
def colimit_cocone_comp (t : colimit_cocone G) :
  colimit_cocone (F ⋙ G) :=
{ cocone := _,
  is_colimit := (is_colimit_whisker_equiv F _).symm (t.is_colimit) }

@[priority 100]
instance comp_has_colimit [has_colimit G] :
  has_colimit (F ⋙ G) :=
has_colimit.mk (colimit_cocone_comp F (get_colimit_cocone G))

lemma colimit_pre_is_iso_aux {t : cocone G} (P : is_colimit t) :
  ((is_colimit_whisker_equiv F _).symm P).desc (t.whisker F) = 𝟙 t.X :=
begin
  dsimp [is_colimit_whisker_equiv],
  apply P.hom_ext,
  tidy,
end

instance colimit_pre_is_iso [has_colimit G] :
  is_iso (colimit.pre G F) :=
begin
  rw colimit.pre_eq (colimit_cocone_comp F (get_colimit_cocone G)) (get_colimit_cocone G),
  erw colimit_pre_is_iso_aux,
  dsimp,
  apply_instance,
end

section
variables (G)

/--
When `F` is cofinal, and `G` has a colimit, then `F ⋙ G` has a colimit also and
`colimit (F ⋙ G) ≅ colimit G`

https://stacks.math.columbia.edu/tag/04E7
-/
def colimit_iso [has_colimit G] : colimit (F ⋙ G) ≅ colimit G := as_iso (colimit.pre G F)

end

/--
If the universal morphism `colimit (F ⋙ coyoneda.obj (op d)) ⟶ colimit (coyoneda.obj (op d))`
is an isomorphism (as it always is when `F` is cofinal),
then `colimit (F ⋙ coyoneda.obj (op d)) ≅ punit`
(simply because `colimit (coyoneda.obj (op d)) ≅ punit`).
-/
def colimit_comp_coyoneda_iso (d : D) [is_iso (colimit.pre (coyoneda.obj (op d)) F)] :
  colimit (F ⋙ coyoneda.obj (op d)) ≅ punit :=
as_iso (colimit.pre (coyoneda.obj (op d)) F) ≪≫ coyoneda.colimit_coyoneda_iso (op d)

/-- Given a colimit cocone over `F ⋙ G` we can construct a colimit cocone over `G`. -/
@[simps]
def colimit_cocone_of_comp (t : colimit_cocone (F ⋙ G)) :
  colimit_cocone G :=
{ cocone := extend_cocone.obj t.cocone,
  is_colimit := (is_colimit_extend_cocone_equiv F _).symm (t.is_colimit), }

/--
When `F` is cofinal, and `F ⋙ G` has a colimit, then `G` has a colimit also.

We can't make this an instance, because `F` is not determined by the goal.
(Even if this weren't a problem, it would cause a loop with `comp_has_colimit`.)
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

lemma zigzag_of_eqv_gen_quot_rel {d : D} {f₁ f₂ : Σ X, d ⟶ F.obj X}
  (t : eqv_gen (types.quot.rel (F ⋙ coyoneda.obj (op d))) f₁ f₂) :
  zigzag
    ({left := punit.star, right := f₁.1, hom := f₁.2} : comma (functor.from_punit d) F)
    {left := punit.star, right := f₂.1, hom := f₂.2} :=
begin
  induction t,
  case eqv_gen.rel : x y r
  { obtain ⟨f, w⟩ := r,
    fconstructor,
    swap 2, fconstructor,
    left, fsplit,
    exact { right := f, } },
  case eqv_gen.refl
  { fconstructor, },
  case eqv_gen.symm : x y h ih
  { apply zigzag_symmetric,
    exact ih, },
  case eqv_gen.trans : x y z h₁ h₂ ih₁ ih₂
  { apply relation.refl_trans_gen.trans,
    exact ih₁, exact ih₂, }
end

/--
If `colimit (F ⋙ coyoneda.obj (op d)) ≅ punit` for all `d : D`, then `F` is cofinal.
-/
def cofinal_of_colimit_comp_coyoneda_iso_punit
  (I : Π d, colimit (F ⋙ coyoneda.obj (op d)) ≅ punit) : cofinal F :=
λ d,
begin
  haveI : nonempty (comma (functor.from_punit d) F) := by
  { have := (I d).inv punit.star,
    obtain ⟨j, y, rfl⟩ := limits.types.jointly_surjective' this,
    exact ⟨{right := j, hom := y}⟩, },
  apply zigzag_is_connected,
  rintros ⟨⟨⟩,X₁,f₁⟩ ⟨⟨⟩,X₂,f₂⟩,
  dsimp at *,
  let y₁ := colimit.ι (F ⋙ coyoneda.obj (op d)) X₁ f₁,
  let y₂ := colimit.ι (F ⋙ coyoneda.obj (op d)) X₂ f₂,
  have e : y₁ = y₂,
  { apply (I d).to_equiv.injective, ext, },
  have t := types.colimit_eq e,
  clear e y₁ y₂,
  exact zigzag_of_eqv_gen_quot_rel F t,
end

end cofinal

end category_theory
