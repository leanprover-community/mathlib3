/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.set.pointwise.smul
import order.chain
import order.grade
import order.rel_iso.group

/-!
# Additional constructions about flags

This file defines the action of order isomorphisms on flags and grades the elements of a flag.

## TODO

The file structure doesn't seem optimal. Maybe all the `flag` material could move here, or to a
subfolder?
-/

open_locale pointwise

variables {𝕆 α : Type*}

namespace flag

/-!
### Action on flags

Order isomorphisms act on flags.
-/

section preorder
variables [preorder α]

instance : has_smul (α ≃o α) (flag α) :=
⟨λ e s,
  { carrier := e • s,
    chain' := s.chain_le.image _ _ _ e.monotone,
    max_chain' := λ t ht hst, (smul_eq_iff_eq_inv_smul _).2 $ s.max_chain.2
      (ht.image _ _ _ e.symm.monotone) $ set.set_smul_subset_iff.1 hst }⟩

@[simp, norm_cast] lemma coe_smul (e : α ≃o α) (s : flag α) : (↑(e • s) : set α) = e • s := rfl

instance : mul_action (α ≃o α) (flag α) := set_like.coe_injective.mul_action _ coe_smul

end preorder

/-!
### Grading a flag

A flag inherits the grading of its ambient order.
-/

section partial_order
variables [partial_order α] {s : flag α}

@[simp] lemma coe_covby_coe {a b : s} : (a : α) ⋖ b ↔ a ⋖ b :=
begin
  refine and_congr_right' ⟨λ h c hac, h hac, λ h c hac hcb,
    @h ⟨c, mem_iff_forall_le_or_ge.2 $ λ d hd, _⟩ hac hcb⟩,
  classical,
  obtain hda | had := le_or_lt (⟨d, hd⟩ : s) a,
  { exact or.inr ((subtype.coe_le_coe.2 hda).trans hac.le) },
  obtain hbd | hdb := le_or_lt b ⟨d, hd⟩,
  { exact or.inl (hcb.le.trans hbd) },
  { cases h had hdb }
end

@[simp] lemma is_max_coe {a : s} : is_max (a : α) ↔ is_max a :=
⟨λ h b hab, h hab, λ h b hab, @h ⟨b, mem_iff_forall_le_or_ge.2 $ λ c hc,
  by { classical, exact or.inr (hab.trans' $ h.is_top ⟨c, hc⟩) }⟩ hab⟩

@[simp] lemma is_min_coe {a : s} : is_min (a : α) ↔ is_min a :=
⟨λ h b hba, h hba, λ h b hba, @h ⟨b, mem_iff_forall_le_or_ge.2 $ λ c hc,
  by { classical, exact or.inl (hba.trans $ h.is_bot ⟨c, hc⟩) }⟩ hba⟩

variables [preorder 𝕆]

instance [grade_order 𝕆 α] (s : flag α) : grade_order 𝕆 s :=
grade_order.lift_right coe (subtype.strict_mono_coe _) $ λ _ _, coe_covby_coe.2

instance [grade_min_order 𝕆 α] (s : flag α) : grade_min_order 𝕆 s :=
grade_min_order.lift_right coe (subtype.strict_mono_coe _) (λ _ _, coe_covby_coe.2) $
  λ _, is_min_coe.2

instance [grade_max_order 𝕆 α] (s : flag α) : grade_max_order 𝕆 s :=
grade_max_order.lift_right coe (subtype.strict_mono_coe _) (λ _ _, coe_covby_coe.2) $
  λ _, is_max_coe.2

instance [grade_bounded_order 𝕆 α] (s : flag α) : grade_bounded_order 𝕆 s :=
grade_bounded_order.lift_right coe (subtype.strict_mono_coe _) (λ _ _, coe_covby_coe.2)
  (λ _, is_min_coe.2) (λ _, is_max_coe.2)

@[simp, norm_cast] lemma grade_coe [grade_order 𝕆 α] (a : s) : grade 𝕆 (a : α) = grade 𝕆 a := rfl

end partial_order
end flag
