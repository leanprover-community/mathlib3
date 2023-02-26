/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import category_theory.functor.const
import category_theory.discrete_category

/-!
# The category `discrete punit`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define `star : C ⥤ discrete punit` sending everything to `punit.star`,
show that any two functors to `discrete punit` are naturally isomorphic,
and construct the equivalence `(discrete punit ⥤ C) ≌ C`.
-/

universes v u -- morphism levels before object levels. See note [category_theory universes].

namespace category_theory
variables (C : Type u) [category.{v} C]

namespace functor

/-- The constant functor sending everything to `punit.star`. -/
@[simps]
def star : C ⥤ discrete punit :=
(functor.const _).obj ⟨⟨⟩⟩

variable {C}
/-- Any two functors to `discrete punit` are isomorphic. -/
@[simps]
def punit_ext (F G : C ⥤ discrete punit) : F ≅ G :=
nat_iso.of_components (λ _, eq_to_iso dec_trivial) (λ _ _ _, dec_trivial)

/--
Any two functors to `discrete punit` are *equal*.
You probably want to use `punit_ext` instead of this.
-/
lemma punit_ext' (F G : C ⥤ discrete punit) : F = G :=
functor.ext (λ _, dec_trivial) (λ _ _ _, dec_trivial)

/-- The functor from `discrete punit` sending everything to the given object. -/
abbreviation from_punit (X : C) : discrete punit.{v+1} ⥤ C :=
(functor.const _).obj X

/-- Functors from `discrete punit` are equivalent to the category itself. -/
@[simps]
def equiv : (discrete punit ⥤ C) ≌ C :=
{ functor :=
  { obj := λ F, F.obj ⟨⟨⟩⟩,
    map := λ F G θ, θ.app ⟨⟨⟩⟩ },
  inverse := functor.const _,
  unit_iso :=
  begin
    apply nat_iso.of_components _ _,
    intro X,
    apply discrete.nat_iso,
    rintro ⟨⟨⟩⟩,
    apply iso.refl _,
    intros,
    ext ⟨⟨⟩⟩,
    simp,
  end,
  counit_iso :=
  begin
    refine nat_iso.of_components iso.refl _,
    intros X Y f,
    dsimp, simp,  -- See note [dsimp, simp].
  end }

end functor

/-- A category being equivalent to `punit` is equivalent to it having a unique morphism between
  any two objects. (In fact, such a category is also a groupoid; see `groupoid.of_hom_unique`) -/
theorem equiv_punit_iff_unique :
  nonempty (C ≌ discrete punit) ↔ (nonempty C) ∧ (∀ x y : C, nonempty $ unique (x ⟶ y)) :=
begin
  split,
  { rintro ⟨h⟩,
    refine ⟨⟨h.inverse.obj ⟨⟨⟩⟩⟩, λ x y, nonempty.intro _⟩,
    apply (unique_of_subsingleton _), swap,
    { have hx : x ⟶ h.inverse.obj ⟨⟨⟩⟩ := by convert h.unit.app x,
      have hy : h.inverse.obj ⟨⟨⟩⟩ ⟶ y := by convert h.unit_inv.app y,
      exact hx ≫ hy, },
    have : ∀ z, z = h.unit.app x ≫ (h.functor ⋙ h.inverse).map z ≫ h.unit_inv.app y,
    { intro z, simpa using congr_arg (≫ (h.unit_inv.app y)) (h.unit.naturality z), },
    apply subsingleton.intro,
    intros a b,
    rw [this a, this b],
    simp only [functor.comp_map], congr, },
  { rintro ⟨⟨p⟩, h⟩,
    haveI := λ x y, (h x y).some,
    refine nonempty.intro (category_theory.equivalence.mk
      ((functor.const _).obj ⟨⟨⟩⟩) ((functor.const _).obj p) _ (by apply functor.punit_ext)),
    exact nat_iso.of_components (λ _, { hom := default, inv := default }) (λ _ _ _, by tidy), },
end

end category_theory
