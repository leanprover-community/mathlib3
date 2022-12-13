/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import ring_theory.ring_hom_properties

/-!

# The meta properties of integral ring homomorphisms.

-/

namespace ring_hom

open_locale tensor_product

open tensor_product algebra.tensor_product

lemma is_integral_stable_under_composition :
  stable_under_composition (λ R S _ _ f, by exactI f.is_integral) :=
by { introv R hf hg, exactI ring_hom.is_integral_trans _ _ hf hg }

lemma is_integral_respects_iso :
  respects_iso (λ R S _ _ f, by exactI f.is_integral) :=
begin
  apply is_integral_stable_under_composition.respects_iso,
  introv x,
  resetI,
  rw ← e.apply_symm_apply x,
  apply ring_hom.is_integral_map
end

lemma is_integral_stable_under_base_change :
  stable_under_base_change (λ R S _ _ f, by exactI f.is_integral) :=
begin
  refine stable_under_base_change.mk _ is_integral_respects_iso _,
  introv h x,
  resetI,
  apply tensor_product.induction_on x,
  { apply is_integral_zero },
  { intros x y, exact is_integral.tmul x (h y) },
  { intros x y hx hy, exact is_integral_add _ hx hy }
end

end ring_hom
