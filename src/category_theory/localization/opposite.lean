/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.localization.predicate

/-!

# Localization of the opposite category

If a functor `L : C ⥤ D` is a localization functor for `W : morphism_property C`, it
is shown in this file that `L.op : Cᵒᵖ ⥤ Dᵒᵖ` is also a localization functor.

-/

noncomputable theory

open category_theory category_theory.category

namespace category_theory

variables {C D : Type*} [category C] [category D] {L : C ⥤ D} {W : morphism_property C}

namespace localization

/-- If `L : C ⥤ D` satisfies the universal property of the localisation
for `W : morphism_property C`, then `L.op` also does. -/
def strict_universal_property_fixed_target.op {E : Type*} [category E]
  (h : strict_universal_property_fixed_target L W Eᵒᵖ):
  strict_universal_property_fixed_target L.op W.op E :=
{ inverts := h.inverts.op,
  lift := λ F hF, (h.lift F.right_op hF.right_op).left_op,
  fac := λ F hF, begin
    convert congr_arg functor.left_op (h.fac F.right_op hF.right_op),
    exact F.right_op_left_op_eq.symm,
  end,
  uniq := λ F₁ F₂ eq, begin
    suffices : F₁.right_op = F₂.right_op,
    { rw [← F₁.right_op_left_op_eq, ← F₂.right_op_left_op_eq, this], },
    have eq' := congr_arg functor.right_op eq,
    exact h.uniq _ _ eq',
  end, }

instance is_localization_op : W.Q.op.is_localization W.op :=
functor.is_localization.mk' W.Q.op W.op
  (strict_universal_property_fixed_target_Q W _).op
  (strict_universal_property_fixed_target_Q W _).op

end localization

namespace functor

instance is_localization.op [h : L.is_localization W] : L.op.is_localization W.op :=
is_localization.of_equivalence_target W.Q.op W.op L.op
  (localization.equivalence_from_model L W).op
  (nat_iso.op (localization.Q_comp_equivalence_from_model_functor_iso L W).symm)

end functor

end category_theory
