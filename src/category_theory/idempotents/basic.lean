/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.abelian.basic

/-!
# Idempotent complete categories

In this file, we define the notion of idempotent complete categories
(also known as Karoubian categories, or pseudoabelian in the case of
preadditive categories).

## Main definitions

- `is_idempotent_complete C` expresses that `C` is idempotent complete, i.e.
all idempotents in `C` split. Other characterisations of idempotent completeness are given
by `is_idempotent_complete_iff_has_equalizer_of_id_and_idempotent` and
`is_idempotent_complete_iff_idempotents_have_kernels`.
- `is_idempotent_complete_of_abelian` expresses that abelian categories are
idempotent complete.
- `is_idempotent_complete_iff_of_equivalence` expresses that if two categories `C` and `D`
are equivalent, then `C` is idempotent complete iff `D` is.
- `is_idempotent_complete_iff_opposite` expresses that `Cᵒᵖ` is idempotent complete
iff `C` is.

## References
* [Stacks: Karoubian categories] https://stacks.math.columbia.edu/tag/09SF

-/

open category_theory
open category_theory.category
open category_theory.limits
open category_theory.preadditive
open opposite

namespace category_theory

variables (C : Type*) [category C]

/-- A category is idempotent complete iff all idempotent endomorphisms `p`
split as a composition `p = e ≫ i` with `i ≫ e = 𝟙 _` -/
class is_idempotent_complete : Prop :=
(idempotents_split : ∀ (X : C) (p : X ⟶ X), p ≫ p = p →
  ∃ (Y : C) (i : Y ⟶ X) (e : X ⟶ Y), i ≫ e = 𝟙 Y ∧ e ≫ i = p)

namespace idempotents

/-- A category is idempotent complete iff for all idempotent endomorphisms,
the equalizer of the identity and this idempotent exists. -/
lemma is_idempotent_complete_iff_has_equalizer_of_id_and_idempotent :
  is_idempotent_complete C ↔ ∀ (X : C) (p : X ⟶ X), p ≫ p = p → has_equalizer (𝟙 X) p :=
begin
  split,
  { introI,
    intros X p hp,
    rcases is_idempotent_complete.idempotents_split X p hp with ⟨Y, i, e, ⟨h₁, h₂⟩⟩,
    exact ⟨nonempty.intro
      { cone := fork.of_ι i
          (show i ≫ 𝟙 X = i ≫ p, by rw [comp_id, ← h₂, ← assoc, h₁, id_comp]),
        is_limit := begin
          apply fork.is_limit.mk',
          intro s,
          refine ⟨s.ι ≫ e, _⟩,
          split,
          { erw [assoc, h₂, ← limits.fork.condition s, comp_id], },
          { intros m hm,
            rw fork.ι_of_ι at hm,
            rw [← hm],
            simp only [← hm, assoc, h₁],
            exact (comp_id m).symm }
        end }⟩, },
  { intro h,
    refine ⟨_⟩,
    intros X p hp,
    haveI := h X p hp,
    use equalizer (𝟙 X) p,
    use equalizer.ι (𝟙 X) p,
    use equalizer.lift p (show p ≫ 𝟙 X = p ≫ p, by rw [hp, comp_id]),
    split,
    { ext,
      rw [assoc, equalizer.lift_ι, id_comp],
      conv { to_rhs, erw [← comp_id (equalizer.ι (𝟙 X) p)], },
      exact (limits.fork.condition (equalizer.fork (𝟙 X) p)).symm, },
    { rw [equalizer.lift_ι], }, }
end

variables {C}

/-- In a preadditive category, when `p : X ⟶ X` is idempotent,
then `𝟙 X - p` is also idempotent. -/
lemma idem_of_id_sub_idem [preadditive C]
  {X : C} (p : X ⟶ X) (hp : p ≫ p = p) :
  (𝟙 _ - p) ≫ (𝟙 _ - p) = (𝟙 _ - p) :=
by simp only [comp_sub, sub_comp, id_comp, comp_id, hp, sub_self, sub_zero]

variables (C)

/-- A preadditive category is pseudoabelian iff all idempotent endomorphisms have a kernel. -/
lemma is_idempotent_complete_iff_idempotents_have_kernels [preadditive C] :
  is_idempotent_complete C ↔ ∀ (X : C) (p : X ⟶ X), p ≫ p = p → has_kernel p :=
begin
  rw is_idempotent_complete_iff_has_equalizer_of_id_and_idempotent,
  split,
  { intros h X p hp,
    haveI := h X (𝟙 _ - p) (idem_of_id_sub_idem p hp),
    convert has_kernel_of_has_equalizer (𝟙 X) (𝟙 X - p),
    rw [sub_sub_cancel], },
  { intros h X p hp,
    haveI : has_kernel (𝟙 _ - p) := h X (𝟙 _ - p) (idem_of_id_sub_idem p hp),
    apply preadditive.has_equalizer_of_has_kernel, },
end

/-- An abelian category is idempotent complete. -/
@[priority 100]
instance is_idempotent_complete_of_abelian (D : Type*) [category D] [abelian D] :
  is_idempotent_complete D :=
by { rw is_idempotent_complete_iff_idempotents_have_kernels, intros, apply_instance, }

variables {C}

lemma split_imp_of_iso {X X' : C} (φ : X ≅ X') (p : X ⟶ X) (p' : X' ⟶ X')
  (hpp' : p ≫ φ.hom = φ.hom ≫ p')
  (h : ∃ (Y : C) (i : Y ⟶ X) (e : X ⟶ Y), i ≫ e = 𝟙 Y ∧ e ≫ i = p) :
  (∃ (Y' : C) (i' : Y' ⟶ X') (e' : X' ⟶ Y'), i' ≫ e' = 𝟙 Y' ∧ e' ≫ i' = p') :=
begin
  rcases h with ⟨Y, i, e, ⟨h₁, h₂⟩⟩,
  use [Y, i ≫ φ.hom, φ.inv ≫ e],
  split,
  { slice_lhs 2 3 { rw φ.hom_inv_id, },
    rw [id_comp, h₁], },
  { slice_lhs 2 3 { rw h₂, },
    rw [hpp', ← assoc, φ.inv_hom_id, id_comp], }
end

lemma split_iff_of_iso {X X' : C} (φ : X ≅ X') (p : X ⟶ X) (p' : X' ⟶ X')
  (hpp' : p ≫ φ.hom = φ.hom ≫ p') :
  (∃ (Y : C) (i : Y ⟶ X) (e : X ⟶ Y), i ≫ e = 𝟙 Y ∧ e ≫ i = p) ↔
  (∃ (Y' : C) (i' : Y' ⟶ X') (e' : X' ⟶ Y'), i' ≫ e' = 𝟙 Y' ∧ e' ≫ i' = p') :=
begin
  split,
  { exact split_imp_of_iso φ p p' hpp', },
  { apply split_imp_of_iso φ.symm p' p,
    rw [← comp_id p, ← φ.hom_inv_id],
    slice_rhs 2 3 { rw hpp', },
    slice_rhs 1 2 { erw φ.inv_hom_id, },
    simpa only [id_comp], },
end

lemma equivalence.is_idempotent_complete {D : Type*} [category D] (ε : C ≌ D)
  (h : is_idempotent_complete C) : is_idempotent_complete D :=
begin
  refine ⟨_⟩,
  intros X' p hp,
  let φ := ε.counit_iso.symm.app X',
  erw split_iff_of_iso φ p (φ.inv ≫ p ≫ φ.hom)
    (by { slice_rhs 1 2 { rw φ.hom_inv_id, }, rw id_comp,}),
  rcases is_idempotent_complete.idempotents_split (ε.inverse.obj X') (ε.inverse.map p)
    (by rw [← ε.inverse.map_comp, hp]) with ⟨Y, i, e, ⟨h₁,h₂⟩⟩,
  use [ε.functor.obj Y, ε.functor.map i, ε.functor.map e],
  split,
  { rw [← ε.functor.map_comp, h₁, ε.functor.map_id], },
  { simpa only [← ε.functor.map_comp, h₂, equivalence.fun_inv_map], },
end

/-- If `C` and `D` are equivalent categories, that `C` is idempotent complete iff `D` is. -/
lemma is_idempotent_complete_iff_of_equivalence {D : Type*} [category D] (ε : C ≌ D) :
  is_idempotent_complete C ↔ is_idempotent_complete D :=
begin
  split,
  { exact equivalence.is_idempotent_complete ε, },
  { exact equivalence.is_idempotent_complete ε.symm, },
end

lemma is_idempotent_complete_of_is_idempotent_complete_opposite
  (h : is_idempotent_complete Cᵒᵖ) : is_idempotent_complete C :=
begin
  refine ⟨_⟩,
  intros X p hp,
  rcases is_idempotent_complete.idempotents_split (op X) p.op
    (by rw [← op_comp, hp]) with ⟨Y, i, e, ⟨h₁, h₂⟩⟩,
  use [Y.unop, e.unop, i.unop],
  split,
  { simpa only [← unop_comp, h₁], },
  { simpa only [← unop_comp, h₂], },
end

lemma is_idempotent_complete_iff_opposite :
  is_idempotent_complete Cᵒᵖ ↔ is_idempotent_complete C :=
begin
  split,
  { exact is_idempotent_complete_of_is_idempotent_complete_opposite, },
  { intro h,
    apply is_idempotent_complete_of_is_idempotent_complete_opposite,
    rw is_idempotent_complete_iff_of_equivalence (op_op_equivalence C),
    exact h, },
end

instance [is_idempotent_complete C] : is_idempotent_complete (Cᵒᵖ) :=
by rwa is_idempotent_complete_iff_opposite

end idempotents

end category_theory
