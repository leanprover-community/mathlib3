/-
Copyright (c) Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.adjunction.limits
import category_theory.limits.shapes.terminal

/-!
# Transporting existence of specific limits across equivalences

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

For now, we only treat the case of initial and terminal objects, but other special shapes can be
added in the future.
-/

open category_theory category_theory.limits

namespace category_theory
universes v₁ v₂ u₁ u₂
variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]

lemma has_initial_of_equivalence (e : D ⥤ C) [is_equivalence e] [has_initial C] : has_initial D :=
adjunction.has_colimits_of_shape_of_equivalence e

lemma equivalence.has_initial_iff (e : C ≌ D) : has_initial C ↔ has_initial D :=
⟨λ h, by exactI has_initial_of_equivalence e.inverse,
 λ h, by exactI has_initial_of_equivalence e.functor⟩

lemma has_terminal_of_equivalence (e : D ⥤ C) [is_equivalence e] [has_terminal C] :
  has_terminal D :=
adjunction.has_limits_of_shape_of_equivalence e

lemma equivalence.has_terminal_iff (e : C ≌ D) : has_terminal C ↔ has_terminal D :=
⟨λ h, by exactI has_terminal_of_equivalence e.inverse,
 λ h, by exactI has_terminal_of_equivalence e.functor⟩

end category_theory
