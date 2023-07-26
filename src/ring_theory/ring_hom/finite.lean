/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import ring_theory.ring_hom_properties

/-!

# The meta properties of finite ring homomorphisms.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/

namespace ring_hom

open_locale tensor_product

open tensor_product algebra.tensor_product

lemma finite_stable_under_composition :
  stable_under_composition @finite :=
by { introv R hf hg, exactI hg.comp hf }

lemma finite_respects_iso :
  respects_iso @finite :=
begin
  apply finite_stable_under_composition.respects_iso,
  introsI,
  exact finite.of_surjective _ e.to_equiv.surjective,
end

lemma finite_stable_under_base_change :
  stable_under_base_change @finite :=
begin
  refine stable_under_base_change.mk _ finite_respects_iso _,
  classical,
  introv h,
  resetI,
  replace h : module.finite R T := by { convert h, ext, rw algebra.smul_def, refl },
  suffices : module.finite S (S ⊗[R] T),
  { change module.finite _ _, convert this, ext, rw algebra.smul_def, refl },
  exactI infer_instance
end

end ring_hom
