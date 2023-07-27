/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
import order.conditionally_complete_lattice.basic

/-!
# Extension of a monotone function from a set to the whole space

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove that if a function is monotone and is bounded on a set `s`, then it admits a
monotone extension to the whole space.
-/

open set

variables {α β : Type*} [linear_order α] [conditionally_complete_linear_order β]
  {f : α → β} {s : set α} {a b : α}

/-- If a function is monotone and is bounded on a set `s`, then it admits a monotone extension to
the whole space. -/
lemma monotone_on.exists_monotone_extension (h : monotone_on f s) (hl : bdd_below (f '' s))
  (hu : bdd_above (f '' s)) :
  ∃ g : α → β, monotone g ∧ eq_on f g s :=
begin
  /- The extension is defined by `f x = f a` for `x ≤ a`, and `f x` is the supremum of the values
  of `f`  to the left of `x` for `x ≥ a`. -/
  classical,
  rcases hl with ⟨a, ha⟩,
  have hu' : ∀ x, bdd_above (f '' (Iic x ∩ s)),
    from λ x, hu.mono (image_subset _ (inter_subset_right _ _)),
  set g : α → β := λ x, if disjoint (Iic x) s then a else Sup (f '' (Iic x ∩ s)),
  have hgs : eq_on f g s,
  { intros x hx,
    simp only [g],
    have : is_greatest (Iic x ∩ s) x, from ⟨⟨right_mem_Iic, hx⟩, λ y hy, hy.1⟩,
    rw [if_neg this.nonempty.not_disjoint,
      ((h.mono $ inter_subset_right _ _).map_is_greatest this).cSup_eq] },
  refine ⟨g, λ x y hxy, _, hgs⟩,
  by_cases hx : disjoint (Iic x) s; by_cases hy : disjoint (Iic y) s;
    simp only [g, if_pos, if_neg, not_false_iff, *],
  { rcases not_disjoint_iff_nonempty_inter.1 hy with ⟨z, hz⟩,
    exact le_cSup_of_le (hu' _) (mem_image_of_mem _ hz) (ha $ mem_image_of_mem _ hz.2) },
  { exact (hx $ hy.mono_left $ Iic_subset_Iic.2 hxy).elim },
  { rw [not_disjoint_iff_nonempty_inter] at hx hy,
    refine cSup_le_cSup (hu' _) (hx.image _) (image_subset _ _),
    exact inter_subset_inter_left _ (Iic_subset_Iic.2 hxy) },
end

/-- If a function is antitone and is bounded on a set `s`, then it admits an antitone extension to
the whole space. -/
lemma antitone_on.exists_antitone_extension (h : antitone_on f s) (hl : bdd_below (f '' s))
  (hu : bdd_above (f '' s)) :
  ∃ g : α → β, antitone g ∧ eq_on f g s :=
h.dual_right.exists_monotone_extension hu hl
