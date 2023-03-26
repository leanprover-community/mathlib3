/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.abelian.subobject
import category_theory.limits.essentially_small
import category_theory.preadditive.injective
import category_theory.preadditive.generator
import category_theory.preadditive.yoneda.limits

/-!
# A complete abelian category with enough injectives and a separator has an injective coseparator

## Future work
* Once we know that Grothendieck categories have enough injectives, we can use this to conclude
  that Grothendieck categories have an injective coseparator.

## References
* [Peter J Freyd, *Abelian Categories* (Theorem 3.37)][freyd1964abelian]

-/

open category_theory category_theory.limits opposite

universes v u

namespace category_theory.abelian
variables {C : Type u} [category.{v} C] [abelian C]

theorem has_injective_coseparator [has_limits C] [enough_injectives C] (G : C)
  (hG : is_separator G) : ∃ G : C, injective G ∧ is_coseparator G :=
begin
  haveI : well_powered C := well_powered_of_is_detector G hG.is_detector,
  haveI : has_products_of_shape (subobject (op G)) C := has_products_of_shape_of_small _ _,
  let T : C := injective.under (pi_obj (λ P : subobject (op G), unop P)),
  refine ⟨T, infer_instance, (preadditive.is_coseparator_iff _).2 (λ X Y f hf, _)⟩,
  refine (preadditive.is_separator_iff _).1 hG _ (λ h, _),
  suffices hh : factor_thru_image (h ≫ f) = 0,
  { rw [← limits.image.fac (h ≫ f), hh, zero_comp] },
  let R := subobject.mk (factor_thru_image (h ≫ f)).op,
  let q₁ : image (h ≫ f) ⟶ unop R :=
    (subobject.underlying_iso (factor_thru_image (h ≫ f)).op).unop.hom,
  let q₂ : unop (R : Cᵒᵖ) ⟶ pi_obj (λ P : subobject (op G), unop P) :=
    section_ (pi.π (λ P : subobject (op G), unop P) R),
  let q : image (h ≫ f) ⟶ T := q₁ ≫ q₂ ≫ injective.ι _,
  exact zero_of_comp_mono q (by rw [← injective.comp_factor_thru q (limits.image.ι (h ≫ f)),
    limits.image.fac_assoc, category.assoc, hf, comp_zero])
end

theorem has_projective_separator [has_colimits C] [enough_projectives C] (G : C)
  (hG : is_coseparator G) : ∃ G : C, projective G ∧ is_separator G :=
begin
  obtain ⟨T, hT₁, hT₂⟩ := has_injective_coseparator (op G) ((is_separator_op_iff _).2 hG),
  exactI ⟨unop T, infer_instance, (is_separator_unop_iff _).2 hT₂⟩
end

end category_theory.abelian
