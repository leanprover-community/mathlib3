/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.abelian.basic

/-!
# Idempotent complete categories

In this file, we define the notion of idempotent complete categories
(also known as Karoubian categories).

## Main constructions and definitions

- `is_idempotent_complete C` expresses that `C` is idempotent complete, i.e.
all idempotents in `C` split.
- `is_idempotent_complete_of_abelian` expresses that abelian categories are
idempotent complete.

## References
* [Stacks: Karoubian categories] https://stacks.math.columbia.edu/tag/09SF

-/

open category_theory
open category_theory.category
open category_theory.limits
open category_theory.preadditive

namespace category_theory

variables (C : Type*) [category C]

class is_idempotent_complete : Prop :=
(idempotents_split : ∀ (X : C) (p : X ⟶ X), p ≫ p = p →
  ∃ (Y : C) (i : Y ⟶ X) (e : X ⟶ Y), i ≫ e = 𝟙 Y ∧ p = e ≫ i)

/-- A category is idempotent complete iff for all idempotents endomorphisms,
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
          (show i ≫ 𝟙 X = i ≫ p, by rw [comp_id, h₂, ← assoc, h₁, id_comp]),
        is_limit := begin
          apply fork.is_limit.mk',
          intro s,
          refine ⟨s.ι ≫ e, _⟩,
          split,
          { erw [assoc, ← h₂, ← limits.fork.condition s, comp_id], },
          { intros m hm,
            erw [← hm],
            simp only [← hm, assoc, fork.ι_eq_app_zero,
              fork.of_ι_π_app, h₁],
            erw comp_id m, }
        end
      }⟩, },
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
lemma idempotence_of_id_sub_idempotent [preadditive C]
  {X : C} (p : X ⟶ X) (hp : p ≫ p = p) :
  (𝟙 _ - p) ≫ (𝟙 _ - p) = (𝟙 _ - p) :=
by simp only [comp_sub, sub_comp, id_comp, comp_id, hp, sub_self, sub_zero]

/-- for preadditive/default.lean -/
lemma has_kernel_of_has_equalizer [preadditive C] {X Y : C} (f g : X ⟶ Y)
  [has_equalizer f g] : has_kernel (f - g) :=
has_limit.mk
  { cone := fork.of_ι (equalizer.ι f g)
      (by erw [comp_zero, comp_sub, equalizer.condition f g, sub_self]),
  is_limit := fork.is_limit.mk _
    (λ s, equalizer.lift s.ι (by simpa only [comp_sub, comp_zero, sub_eq_zero] using s.condition))
    (λ s, by simp only [fork.ι_eq_app_zero, fork.of_ι_π_app, equalizer.lift_ι])
    (λ s m h, by { ext, simpa only [equalizer.lift_ι] using h walking_parallel_pair.zero, }), }

variables (C)

/-- A preadditive category is pseudoabelian iff all idempotent endomorphisms have a kernel. -/
lemma is_idempotent_complete_iff_idempotents_have_kernels [preadditive C] :
  is_idempotent_complete C ↔ ∀ (X : C) (p : X ⟶ X), p ≫ p = p → has_kernel p :=
begin
  rw is_idempotent_complete_iff_has_equalizer_of_id_and_idempotent,
  split,
  { intros h X p hp,
    haveI := h X (𝟙 _ - p) (idempotence_of_id_sub_idempotent p hp),
    convert has_kernel_of_has_equalizer (𝟙 X) (𝟙 X - p),
    rw [sub_sub_cancel], },
  { intros h X p hp,
    haveI : has_kernel (𝟙 _ - p) := h X (𝟙 _ - p) (idempotence_of_id_sub_idempotent p hp),
    apply preadditive.has_limit_parallel_pair, },
end

/-- An abelian category is idempotent complete. -/
@[priority 100]
instance is_idempotent_complete_of_abelian (D : Type*) [category D] [abelian D] :
  is_idempotent_complete D :=
begin
  rw is_idempotent_complete_iff_idempotents_have_kernels,
  intros X p hp,
  apply_instance,
end

end category_theory
