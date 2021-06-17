/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.adjunction.basic
import category_theory.limits.shapes.wide_equalizers
import category_theory.limits.shapes
import category_theory.limits.preserves.basic
import category_theory.limits.creates
import category_theory.limits.comma
import category_theory.punit

/-!
# Adjoint functor theorem

This file proves the (general) adjoint functor theorem, in the form:
* If `G : D ⥤ C` preserves limits and `D` has limits, and satisfies the solution set condition,
  then it has a left adjoint.

We show that the converse holds, i.e. that if `G` has a left adjoint then it satisfies the solution
set condition (`category_theroy/adjunction/limits` already shows it preserves limits).

We define the solution set condition for the functor `G : D ⥤ C` to mean, for every object `A : C`,
there is a set-indexed family ${f_i : A ⟶ G (B_i)}$ such that any morphism `A ⟶ G X` factors
through one of the `f_i`.

-/
universes v u

namespace category_theory
open limits

variables {J : Type v}
variables {C : Type u} [category.{v} C]

/--
If `C` has (small) products and a small weakly initial set of objects, then it has a weakly initial
object.
-/
lemma has_weakly_initial_of_weakly_initial_set_and_has_products (C : Type u) [category.{v} C]
  [has_products C]
  {ι : Type v} (B : ι → C) (hB : ∀ (A : C), ∃ i, nonempty (B i ⟶ A)) :
  ∃ (T : C), ∀ X, nonempty (T ⟶ X) :=
⟨∏ B, λ X, ⟨pi.π _ _ ≫ (hB X).some_spec.some⟩⟩

/--
If `C` has (small) wide equalizers and a weakly initial object, then it has an initial object.

The initial object is constructed as the wide equalizer of all endomorphisms on the given weakly
initial object.
-/
lemma has_initial_of_weakly_initial_and_has_wide_equalizers (C : Type u) [category.{v} C]
  [has_wide_equalizers C] (T : C) (hT : ∀ X, nonempty (T ⟶ X)) :
  has_initial C :=
begin
  let endos := T ⟶ T,
  let i := wide_equalizer.ι (id : endos → endos),
  haveI : nonempty endos := ⟨𝟙 _⟩,
  have : ∀ (X : C), unique (wide_equalizer (id : endos → endos) ⟶ X),
  { intro X,
    refine ⟨⟨i ≫ classical.choice (hT X)⟩, λ a, _⟩,
    let E := equalizer a (i ≫ classical.choice (hT _)),
    let e : E ⟶ wide_equalizer id := equalizer.ι _ _,
    let h : T ⟶ E := classical.choice (hT E),
    have : ((i ≫ h) ≫ e) ≫ i = i ≫ 𝟙 _,
    { rw [category.assoc, category.assoc],
      apply wide_equalizer.condition (id : endos → endos) (h ≫ e ≫ i) },
    rw [category.comp_id, cancel_mono_id i] at this,
    haveI : split_epi e := ⟨i ≫ h, this⟩,
    rw ←cancel_epi e,
    apply equalizer.condition },
  exactI has_initial_of_unique (wide_equalizer (id : endos → endos)),
end

/--
The functor `G : D ⥤ C` satisfies the *solution set condition* if for every `A : C`, there is a
family of morphisms `{f_i : A ⟶ G (B_i) // i ∈ ι}` such that given any morphism `h : A ⟶ G X`,
there is some `i ∈ ι` such that `h` factors through `f_i`.

The key part of this definition is that the indexing set `ι` lives in `Type v`, where `v` is the
universe of morphisms of the category: this is the "smallness" condition which allows the general
adjoint functor theorem to go through.
-/
def solution_set_condition {D : Type u} [category.{v} D] (G : D ⥤ C) : Prop :=
  ∀ (A : C), ∃ (ι : Type v) (B : ι → D) (f : Π (i : ι), A ⟶ G.obj (B i)),
  ∀ X (h : A ⟶ G.obj X), ∃ (i : ι) (g : B i ⟶ X), f i ≫ G.map g = h

variables {D : Type u} [category.{v} D]

-- TODO: move this section somewhere.
-- TODO: consider showing the converse
-- TODO: dualise
-- This section proves that if each comma category (A ↓ G) has an initial object then `G` has a
-- left adjoint

section initials
noncomputable theory

variables (G : D ⥤ C)
variables [∀ A, has_initial (structured_arrow A G)]

def F : C → D := λ A, (⊥_ (structured_arrow A G)).right
def η (A : C) : A ⟶ G.obj (F G A) := (⊥_ (structured_arrow A G)).hom

@[simps]
def init_equivalence (A : C) (B : D) :
  (F G A ⟶ B) ≃ (A ⟶ G.obj B) :=
{ to_fun := λ g, η G A ≫ G.map g,
  inv_fun := λ f, comma_morphism.right (initial.to (structured_arrow.mk f)),
  left_inv := λ g,
  begin
    let B' : structured_arrow A G := structured_arrow.mk (η G A ≫ G.map g),
    let g' : (⊥_ (structured_arrow A G)) ⟶ B' :=
      ⟨eq_to_hom (subsingleton.elim _ _), g, category.id_comp _⟩,
    have : initial.to _ = g',
    { apply colimit.hom_ext, rintro ⟨⟩ },
    change comma_morphism.right (initial.to B') = _,
    rw this,
  end,
  right_inv := λ f,
  begin
    let B' : structured_arrow A G := { right := B, hom := f },
    apply (comma_morphism.w (initial.to B')).symm.trans (category.id_comp _),
  end }

def init_to_adj := adjunction.left_adjoint_of_equiv (init_equivalence G) (λ _ _, by simp)

def is_right_adjoint_of_initials : is_right_adjoint G :=
{ left := init_to_adj G,
  adj := adjunction.adjunction_of_equiv_left _ _ }
end initials

section gaft

variables (G : D ⥤ C) [has_limits D]

/--
The general adjoint functor theorem says that if `G : D ⥤ C` preserves limits and `D` has them,
then `G` is a right adjoint.
-/
noncomputable def is_right_adjoint_of_preserves_limits_of_solution_set_condition
  [preserves_limits G] (hG : solution_set_condition G) :
  is_right_adjoint G :=
begin
  apply is_right_adjoint_of_initials _,
  intro A,
  specialize hG A,
  choose ι B f g using hG,
  let B' : ι → structured_arrow A G := λ i, structured_arrow.mk (f i),
  have hB' : ∀ (A' : structured_arrow A G), ∃ i, nonempty (B' i ⟶ A'),
  { intros A',
    obtain ⟨i, _, t⟩ := g _ A'.hom,
    exact ⟨i, ⟨structured_arrow.hom_mk _ t⟩⟩ },
  obtain ⟨T, hT⟩ := has_weakly_initial_of_weakly_initial_set_and_has_products _ B' hB',
  apply has_initial_of_weakly_initial_and_has_wide_equalizers _ _ hT,
end

/-- If `G : D ⥤ C` is a right adjoint it satisfies the solution set condition.  -/
lemma solution_set_condition_of_is_right_adjoint [is_right_adjoint G] :
  solution_set_condition G :=
begin
  intros A,
  refine ⟨punit, λ _, (left_adjoint G).obj A, λ _, (adjunction.of_right_adjoint G).unit.app A, _⟩,
  intros B h,
  refine ⟨punit.star, ((adjunction.of_right_adjoint G).hom_equiv _ _).symm h, _⟩,
  rw [←adjunction.hom_equiv_unit, equiv.apply_symm_apply],
end

end gaft

end category_theory
