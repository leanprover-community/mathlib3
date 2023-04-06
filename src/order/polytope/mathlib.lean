/-
Copyright (c) 2022 Yaël Dillies, Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Violeta Hernández Palacios, Grayson Burton, Vladimir Ivanov
-/
import algebra.big_operators.finsupp
import algebra.big_operators.order
import data.dfinsupp.order
import data.finsupp.order
import data.nat.succ_pred
import data.sum.order
import order.atoms
import order.locally_finite
import order.grade
import order.rel_iso.group
import order.zorn

/-!
# To move
-/

open finset function order

variables {ι 𝕆 ℙ α β γ : Type*} {σ : ι → Type*}

section order_dual
open order_dual
variables {a b : αᵒᵈ}

variables [preorder α] [locally_finite_order α]

lemma Icc_eq : Icc a b = (Icc (of_dual b) (of_dual a)).map to_dual.to_embedding := Icc_to_dual _ _
lemma Ico_eq : Ico a b = (Ioc (of_dual b) (of_dual a)).map to_dual.to_embedding := Ico_to_dual _ _
lemma Ioc_eq : Ioc a b = (Ico (of_dual b) (of_dual a)).map to_dual.to_embedding := Ioc_to_dual _ _
lemma Ioo_eq : Ioo a b = (Ioo (of_dual b) (of_dual a)).map to_dual.to_embedding := Ioo_to_dual _ _

@[simp] lemma card_Icc : (Icc a b).card = (Icc (of_dual b) (of_dual a)).card :=
by rw [Icc_eq, card_map]

@[simp] lemma card_Ico : (Ico a b).card = (Ioc (of_dual b) (of_dual a)).card :=
by rw [Ico_eq, card_map]

@[simp] lemma card_Ioc : (Ioc a b).card = (Ico (of_dual b) (of_dual a)).card :=
by rw [Ioc_eq, card_map]

@[simp] lemma card_Ioo : (Ioo a b).card = (Ioo (of_dual b) (of_dual a)).card :=
by rw [Ioo_eq, card_map]

end order_dual

section
variables [preorder α]

/-- A constructor for a locally finite order from intervals that are "too big". -/
@[reducible] -- See note [reducible non-instances]
def locally_finite_order.of_decidable_le_lt [decidable_rel ((≤) : α → α → Prop)]
  [decidable_rel ((<) : α → α → Prop)] (Icc Ico Ioc Ioo : α → α → finset α)
  (hIcc : ∀ ⦃a b x⦄, a ≤ x → x ≤ b → x ∈ Icc a b) (hIco : ∀ ⦃a b x⦄, a ≤ x → x < b → x ∈ Ico a b)
  (hIoc : ∀ ⦃a b x⦄, a < x → x ≤ b → x ∈ Ioc a b) (hIoo : ∀ ⦃a b x⦄, a < x → x < b → x ∈ Ioo a b) :
  locally_finite_order α :=
{ finset_Icc := λ a b, (Icc a b).filter (λ x, a ≤ x ∧ x ≤ b),
  finset_Ico := λ a b, (Ico a b).filter (λ x, a ≤ x ∧ x < b),
  finset_Ioc := λ a b, (Ioc a b).filter (λ x, a < x ∧ x ≤ b),
  finset_Ioo := λ a b, (Ioo a b).filter (λ x, a < x ∧ x < b),
  finset_mem_Icc := by simpa using hIcc,
  finset_mem_Ico := by simpa using hIco,
  finset_mem_Ioc := by simpa using hIoc,
  finset_mem_Ioo := by simpa using hIoo }

/-- A constructor for a locally finite order from intervals that are "too big". -/
@[reducible] -- See note [reducible non-instances]
def locally_finite_order_bot.of_decidable_le_lt [decidable_rel ((≤) : α → α → Prop)]
  [decidable_rel ((<) : α → α → Prop)] (Iic Iio : α → finset α)
  (hIic : ∀ ⦃b x⦄, x ≤ b → x ∈ Iic b) (hIio : ∀ ⦃b x⦄, x < b → x ∈ Iio b) :
  locally_finite_order_bot α :=
{ finset_Iic := λ b, (Iic b).filter (λ x, x ≤ b),
  finset_Iio := λ b, (Iio b).filter (λ x, x < b),
  finset_mem_Iic := by simpa using hIic,
  finset_mem_Iio := by simpa using hIio }

/-- A constructor for a locally finite order from intervals that are "too big". -/
@[reducible] -- See note [reducible non-instances]
def locally_finite_order_top.of_decidable_le_lt [decidable_rel ((≤) : α → α → Prop)]
  [decidable_rel ((<) : α → α → Prop)] (Ici Ioi : α → finset α)
  (hIci : ∀ ⦃a x⦄, a ≤ x → x ∈ Ici a) (hIoi : ∀ ⦃a x⦄, a < x → x ∈ Ioi a) :
  locally_finite_order_top α :=
{ finset_Ici := λ a, (Ici a).filter (λ x, a ≤ x),
  finset_Ioi := λ a, (Ioi a).filter (λ x, a < x),
  finset_mem_Ici := by simpa using hIci,
  finset_mem_Ioi := by simpa using hIoi }

end

lemma is_chain_singleton (r : α → α → Prop) (a : α) : is_chain r {a} := set.pairwise_singleton _ _

lemma is_chain_pair (r : α → α → Prop) {a b : α} (h : r a b) : is_chain r {a, b} :=
(is_chain_singleton _ _).insert $ λ _ hb _, or.inl $ (set.eq_of_mem_singleton hb).symm.rec_on ‹_›

section
variables [preorder α] {a b c : α}

lemma ne_bot_of_lt [order_bot α] {a b : α} (h : a < b) : b ≠ ⊥ := (bot_le.trans_lt h).ne'

lemma ne_top_of_gt [order_top α] {a b : α} (h : a < b) : a ≠ ⊤ := (h.trans_le le_top).ne

lemma not_covby_of_lt_lt {c : α} (hab : a < b) (hbc : b < c) : ¬ a ⋖ c := λ h, h.2 hab hbc

alias not_covby_of_lt_lt ← has_lt.lt.not_covby_of_lt

section
variables {p : α → Prop}

open subtype

lemma subtype.coe_strict_mono : strict_mono (coe : subtype p → α) := λ _ _, coe_lt_coe.1

end
end

section preorder
variables [preorder α] [preorder β]

@[simp] lemma is_min_map (e : α ≃o β) {a : α} : is_min (e a) ↔ is_min a :=
e.forall_congr_left.symm.trans $ by simp [is_min]

@[simp] lemma is_max_map (e : α ≃o β) {a : α} : is_max (e a) ↔ is_max a :=
e.forall_congr_left.symm.trans $ by simp [is_max]

end preorder

namespace order_iso

/-- The tautological action by `α ≃o α` on `α`. -/
instance apply_mul_action (α : Type*) [preorder α] : mul_action (α ≃o α) α :=
{ smul := coe_fn,
  one_smul := λ _, rfl,
  mul_smul := λ _ _ _, rfl }

@[simp] lemma smul_def {α : Type*} [preorder α] (f : α ≃o α) (a : α) : f • a = f a := rfl

end order_iso

namespace flag
section preorder
variables [preorder α] {s : flag α} {c : set α} {a b : α}

/-- Reinterpret a maximal chain as a flag. -/
@[simps] protected def _root_.is_max_chain.flag (hc : is_max_chain (≤) c) : flag α :=
⟨c, hc.is_chain, hc.2⟩

lemma _root_.is_chain.exists_subset_flag (hc : is_chain (≤) c) : ∃ s : flag α, c ⊆ s :=
let ⟨s, hs, hcs⟩ := hc.exists_max_chain in ⟨hs.flag, hcs⟩

lemma exists_mem (a : α) : ∃ s : flag α, a ∈ s :=
let ⟨s, hs⟩ := set.subsingleton_singleton.is_chain.exists_subset_flag in ⟨s, hs rfl⟩

lemma exists_mem_mem (hab : a ≤ b) : ∃ s : flag α, a ∈ s ∧ b ∈ s :=
by simpa [set.insert_subset] using (is_chain_pair _ hab).exists_subset_flag

instance : nonempty (flag α) := ⟨max_chain_spec.flag⟩

lemma mem_iff_forall_le_or_ge : a ∈ s ↔ ∀ ⦃b⦄, b ∈ s → a ≤ b ∨ b ≤ a :=
⟨λ ha b, s.le_or_le ha, λ hb, of_not_not $ λ ha, set.ne_insert_of_not_mem _ ‹_› $ s.max_chain.2
  (s.chain_le.insert $ λ c hc _, hb hc) $ set.subset_insert _ _⟩

end preorder

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

instance [preorder 𝕆] [grade_order 𝕆 α] (s : flag α) : grade_order 𝕆 s :=
grade_order.lift_right coe subtype.coe_strict_mono $ λ _ _, coe_covby_coe.2

instance [preorder 𝕆] [grade_min_order 𝕆 α] (s : flag α) : grade_min_order 𝕆 s :=
grade_min_order.lift_right coe subtype.coe_strict_mono (λ _ _, coe_covby_coe.2) $ λ _, is_min_coe.2

instance [preorder 𝕆] [grade_max_order 𝕆 α] (s : flag α) : grade_max_order 𝕆 s :=
grade_max_order.lift_right coe subtype.coe_strict_mono (λ _ _, coe_covby_coe.2) $ λ _, is_max_coe.2

instance [preorder 𝕆] [grade_bounded_order 𝕆 α] (s : flag α) : grade_bounded_order 𝕆 s :=
grade_bounded_order.lift_right coe subtype.coe_strict_mono (λ _ _, coe_covby_coe.2)
  (λ _, is_min_coe.2) (λ _, is_max_coe.2)

@[simp, norm_cast] lemma grade_coe [preorder 𝕆] [grade_order 𝕆 α] (a : s) :
  grade 𝕆 (a : α) = grade 𝕆 a := rfl

end partial_order
end flag

namespace flag
variables [preorder α] [preorder β]
open_locale pointwise

instance : has_smul (α ≃o α) (flag α) :=
⟨λ e s,
  { carrier := e • s,
    chain' := s.chain_le.image _ _ _ e.monotone,
    max_chain' := λ t ht hst, (smul_eq_iff_eq_inv_smul _).2 $ s.max_chain.2
      (ht.image _ _ _ e.symm.monotone) $ set.set_smul_subset_iff.1 hst }⟩

@[simp, norm_cast] lemma coe_smul (e : α ≃o α) (s : flag α) : (↑(e • s) : set α) = e • s := rfl

instance : mul_action (α ≃o α) (flag α) := set_like.coe_injective.mul_action _ coe_smul

end flag

section
variables [preorder α] [comm_group α] [covariant_class α α (*) (≤)] {a b c : α}

open order_dual

/-- `equiv.div_left` as an `order_iso`. -/
@[to_additive "`equiv.sub_left` as an `order_iso`.", simps to_equiv apply {simp_rhs := tt}]
def order_iso.div_left (a : α) : α ≃o αᵒᵈ :=
{ map_rel_iff' := λ b c, div_le_div_iff_left _, to_equiv := (equiv.div_left a).trans to_dual }

/-- `equiv.div_right` as an `order_iso`. -/
@[to_additive "`equiv.sub_right` as an `order_iso`.", simps to_equiv apply {simp_rhs := tt}]
def order_iso.div_right (a : α) : α ≃o α :=
{ map_rel_iff' := λ b c, div_le_div_iff_right _, to_equiv := equiv.div_right a }

end

section
variables [preorder α] [comm_group α] [covariant_class α α (*) (≤)] {a b c : α}

@[simp, to_additive] lemma mul_covby_mul_left : a * b ⋖ a * c ↔ b ⋖ c :=
apply_covby_apply_iff $ order_iso.mul_left a

@[simp, to_additive] lemma mul_covby_mul_right : a * c ⋖ b * c ↔ a ⋖ b :=
apply_covby_apply_iff $ order_iso.mul_right c

alias mul_covby_mul_left ↔ covby.of_mul_left covby.mul_left
alias mul_covby_mul_right ↔ covby.of_mul_right covby.mul_right

@[simp, to_additive] lemma div_covby_div_left : a / b ⋖ a / c ↔ c ⋖ b :=
to_dual_covby_to_dual_iff.symm.trans $ apply_covby_apply_iff $ order_iso.div_left a

@[simp, to_additive] lemma div_covby_div_right : a / c ⋖ b / c ↔ a ⋖ b :=
apply_covby_apply_iff $ order_iso.div_right c

alias div_covby_div_left ↔ covby.of_div_left covby.div_left
alias div_covby_div_right ↔ covby.of_div_right covby.div_right

end

section
variables [canonically_linear_ordered_add_monoid α] [has_sub α] [has_ordered_sub α]
 [covariant_class α α (+) (<)] [contravariant_class α α (+) (≤)] {a b c : α}

lemma covby.add_left' (h : b ⋖ c) (a : α) : a + b ⋖ a + c :=
⟨add_lt_add_left h.lt _, λ d hb hc,
  h.2 (lt_tsub_iff_left.2 hb) ((tsub_lt_iff_left $ le_self_add.trans hb.le).2 hc)⟩

lemma covby.add_right' (h : b ⋖ c) (a : α) : b + a ⋖ c + a :=
⟨add_lt_add_right h.lt _, λ d hb hc,
  h.2 (lt_tsub_iff_right.2 hb) ((tsub_lt_iff_right $ le_add_self.trans hb.le).2 hc)⟩

lemma covby.tsub_left (hca : c ≤ a) (h : b ⋖ c) : a - c ⋖ a - b :=
⟨(tsub_lt_tsub_iff_left_of_le hca).2 h.lt, λ d hb hc, h.2 (lt_tsub_comm.1 hc) $
  (tsub_lt_iff_left $ hc.le.trans tsub_le_self).2 $ lt_add_of_tsub_lt_right hb⟩

lemma covby.tsub_right (hab : a ≤ b) (h : b ⋖ c) : b - a ⋖ c - a :=
⟨tsub_lt_tsub_right_of_le hab h.lt, λ d hb hc,
  h.2 ((tsub_lt_iff_left $ hab).1 hb) (lt_tsub_iff_left.1 hc)⟩

end

namespace pi
variables [Π i, preorder (σ i)] {a : Π i, σ i}

lemma _root_.is_min.apply' (ha : is_min a) (i : ι) : is_min (a i) :=
λ c hc,
  by { classical, exact (ha (update_le_iff.2 ⟨hc, λ j _, le_rfl⟩) i).trans_eq (update_same _ _ _) }

lemma is_min_iff : is_min a ↔ ∀ i, is_min (a i) :=
⟨is_min.apply', λ h b hb i, h _ $ hb i⟩

end pi

namespace sum
variables [preorder α] [preorder β] {a : α} {b : β}

@[simp] lemma is_min_inl_iff : is_min (inl a : α ⊕ β) ↔ is_min a :=
begin
  refine ⟨λ h b hb, inl_le_inl_iff.1 $ h $ inl_le_inl_iff.2 hb, λ h b hb, _⟩,
  cases b,
  { exact inl_le_inl_iff.2 (h $ inl_le_inl_iff.1 hb) },
  { cases hb }
end

@[simp] lemma is_min_inr_iff : is_min (inr b : α ⊕ β) ↔ is_min b :=
begin
  refine ⟨λ h b hb, inr_le_inr_iff.1 $ h $ inr_le_inr_iff.2 hb, λ h b hb, _⟩,
  cases b,
  { cases hb },
  { exact inr_le_inr_iff.2 (h $ inr_le_inr_iff.1 hb) }
end

@[simp] lemma is_max_inl_iff : is_max (inl a : α ⊕ β) ↔ is_max a :=
begin
  refine ⟨λ h b hb, inl_le_inl_iff.1 $ h $ inl_le_inl_iff.2 hb, λ h b hb, _⟩,
  cases b,
  { exact inl_le_inl_iff.2 (h $ inl_le_inl_iff.1 hb) },
  { cases hb }
end

@[simp] lemma is_max_inr_iff : is_max (inr b : α ⊕ β) ↔ is_max b :=
begin
  refine ⟨λ h b hb, inr_le_inr_iff.1 $ h $ inr_le_inr_iff.2 hb, λ h b hb, _⟩,
  cases b,
  { cases hb },
  { exact inr_le_inr_iff.2 (h $ inr_le_inr_iff.1 hb) }
end

end sum

section
variables [preorder α] [preorder β] [preorder γ] {f : α → γ} {g : β → γ}

open sum

lemma strict_mono.sum_elim (hf : strict_mono f) (hg : strict_mono g) : strict_mono (sum.elim f g)
| (inl a) (inl b) (lift_rel.inl h) := hf h
| (inr a) (inr b) (lift_rel.inr h) := hg h

lemma strict_anti.sum_elim (hf : strict_anti f) (hg : strict_anti g) : strict_anti (sum.elim f g)
| (inl a) (inl b) (lift_rel.inl h) := hf h
| (inr a) (inr b) (lift_rel.inr h) := hg h

end

/-! #### Lifting a graded order -/

section grade_order
variables [preorder 𝕆] [preorder ℙ] [preorder α] [preorder β]

/-- Transfer a graded order across an order isomorphism. -/
@[reducible] -- See note [reducible non-instances]
def order_iso.grade_order_left [grade_order 𝕆 α] (f : 𝕆 ≃o ℙ) : grade_order ℙ α :=
grade_order.lift_left _ f.strict_mono $ λ _ _, (apply_covby_apply_iff f).2

/-- Transfer a graded order across an order isomorphism. -/
@[reducible] -- See note [reducible non-instances]
def order_iso.grade_min_order_left [grade_min_order 𝕆 α] (f : 𝕆 ≃o ℙ) : grade_min_order ℙ α :=
grade_min_order.lift_left _ f.strict_mono (λ _ _, (apply_covby_apply_iff f).2) $ λ _,
  (is_min_map f).2

/-- Transfer a graded order across an order isomorphism. -/
@[reducible] -- See note [reducible non-instances]
def order_iso.grade_max_order_left [grade_max_order 𝕆 α] (f : 𝕆 ≃o ℙ) : grade_max_order ℙ α :=
grade_max_order.lift_left _ f.strict_mono (λ _ _, (apply_covby_apply_iff f).2) $ λ _,
  (is_max_map f).2

/-- Transfer a graded order across an order isomorphism. -/
@[reducible] -- See note [reducible non-instances]
def order_iso.grade_bounded_order_left [grade_bounded_order 𝕆 α] (f : 𝕆 ≃o ℙ) :
  grade_bounded_order ℙ α :=
grade_bounded_order.lift_left _ f.strict_mono (λ _ _, (apply_covby_apply_iff f).2)
  (λ _, (is_min_map f).2) $ λ _, (is_max_map f).2

/-- Transfer a graded order across an order isomorphism. -/
@[reducible] -- See note [reducible non-instances]
def order_iso.grade_order_right [grade_order 𝕆 β] (f : α ≃o β) : grade_order 𝕆 α :=
grade_order.lift_right _ f.strict_mono $ λ _ _, (apply_covby_apply_iff f).2

/-- Transfer a graded order across an order isomorphism. -/
@[reducible] -- See note [reducible non-instances]
def order_iso.grade_min_order_right [grade_min_order 𝕆 β] (f : α ≃o β) : grade_min_order 𝕆 α :=
grade_min_order.lift_right _ f.strict_mono (λ _ _, (apply_covby_apply_iff f).2) $ λ _,
  (is_min_map f).2

/-- Transfer a graded order across an order isomorphism. -/
@[reducible] -- See note [reducible non-instances]
def order_iso.grade_max_order_right [grade_max_order 𝕆 β] (f : α ≃o β) : grade_max_order 𝕆 α :=
grade_max_order.lift_right _ f.strict_mono (λ _ _, (apply_covby_apply_iff f).2) $ λ _,
  (is_max_map f).2

/-- Transfer a graded order across an order isomorphism. -/
@[reducible] -- See note [reducible non-instances]
def order_iso.grade_bounded_order_right [grade_bounded_order 𝕆 β] (f : α ≃o β) :
  grade_bounded_order 𝕆 α :=
grade_bounded_order.lift_right _ f.strict_mono (λ _ _, (apply_covby_apply_iff f).2)
  (λ _, (is_min_map f).2) $ λ _, (is_max_map f).2

end grade_order

namespace list
variables {l : list α} {a : α}

lemma sublist.rfl : l <+ l := sublist.refl _

lemma sublist_singleton : Π {l} {a : α}, l <+ [a] → l = [] ∨ l = [a]
| _ _ (sublist.cons  _ _  _ _ ) := or.inl $ by rwa ←sublist_nil_iff_eq_nil
| _ _ (sublist.cons2 l [] a hl) := or.inr $ by rw sublist_nil_iff_eq_nil.1 hl

lemma sublist_singleton_iff : l <+ [a] ↔ l = [] ∨ l = [a] :=
⟨sublist_singleton, begin
  rintro (rfl | rfl),
  { exact nil_sublist _ },
  { exact sublist.rfl }
end⟩

lemma subperm.rfl : l <+~ l := subperm.refl _

lemma subperm_singleton : l <+~ [a] → l = nil ∨ l = [a] :=
begin
  rintro ⟨l', hl, hl'⟩,
  obtain rfl | rfl := sublist_singleton hl',
  { exact or.inl hl.symm.eq_nil },
  { exact or.inr hl.symm.eq_singleton }
end

lemma subperm_singleton_iff' : l <+~ [a] ↔ l = nil ∨ l = [a] :=
⟨subperm_singleton, begin
  rintro (rfl | rfl),
  { exact nil_subperm },
  { exact subperm.rfl }
end⟩

end list

namespace multiset
variables {s t : multiset α} {a : α}

@[simp] lemma cons_lt_cons_iff : a ::ₘ s < a ::ₘ t ↔ s < t :=
lt_iff_lt_of_le_iff_le' (cons_le_cons_iff _) (cons_le_cons_iff _)

lemma cons_lt_cons (a : α) (h : s < t) : a ::ₘ s < a ::ₘ t := cons_lt_cons_iff.2 h

lemma le_singleton_iff : s ≤ {a} ↔ s = 0 ∨ s = {a} :=
quot.induction_on s $ λ l, by simp only [cons_zero, ←coe_singleton, quot_mk_to_coe'', coe_le,
  coe_eq_zero, coe_eq_coe, list.perm_singleton, list.subperm_singleton_iff']

lemma lt_singleton_iff : s < {a} ↔ s = 0 :=
begin
  simp [lt_iff_le_and_ne, le_singleton_iff, or_and_distrib_right, or_iff_left (and_not_self _).1,
    and_iff_left_of_imp],
  rintro rfl,
  exact (singleton_ne_zero _).symm,
end

lemma covby_cons (m : multiset α) (a : α) : m ⋖ a ::ₘ m :=
⟨lt_cons_self _ _, begin
  simp_rw lt_iff_cons_le,
  rintros m' ⟨b, hbm'⟩ ⟨c, hcm'⟩,
  apply @irrefl _ (<) _ m,
  have h := lt_of_le_of_lt hbm' (lt_cons_self _ c),
  replace h := lt_of_lt_of_le h hcm',
  clear hbm' hcm',
  induction m using multiset.induction with d m hm,
  { rw [cons_zero a, lt_singleton_iff] at h,
    exact (cons_ne_zero h).elim },
  { simp_rw cons_swap _ d at h,
    rw cons_lt_cons_iff at h ⊢,
    exact hm h }
end⟩

lemma _root_.covby.exists_multiset_cons (h : s ⋖ t) : ∃ a, t = a ::ₘ s :=
(lt_iff_cons_le.1 h.lt).imp $ λ a ha, ha.eq_of_not_gt $ h.2 $ lt_cons_self _ _

lemma covby_iff : s ⋖ t ↔ ∃ a, t = a ::ₘ s :=
⟨covby.exists_multiset_cons, by { rintro ⟨a, rfl⟩, exact covby_cons _ _ }⟩

lemma _root_.covby.card_multiset (h : s ⋖ t) : s.card ⋖ t.card :=
by { obtain ⟨a, rfl⟩ := h.exists_multiset_cons, rw card_cons, exact covby_succ _ }

lemma card_strict_mono : strict_mono (card : multiset α → ℕ) := λ _ _, card_lt_of_lt

end multiset

namespace finset
variables {s t : finset α}

-- golf using `image_covby_iff`
@[simp] lemma val_covby_iff : s.1 ⋖ t.1 ↔ s ⋖ t :=
begin
  split;
  rintro ⟨hlt, no_intermediate⟩;
  split;
  simp at *;
  rwa [←val_lt_iff] at *;
  intros c hsc hct;
  simp at *;
  rw [←val_lt_iff] at *,
  { apply @no_intermediate c.val; assumption },
  { apply @no_intermediate ⟨c, multiset.nodup_of_le hct.1 t.nodup⟩;
    rw ←val_lt_iff;
    assumption }
end

alias val_covby_iff ↔ _ covby.finset_val

lemma _root_.covby.card_finset (h : s ⋖ t) : s.card ⋖ t.card := (val_covby_iff.2 h).card_multiset

lemma _root_.is_min.eq_empty : is_min s → s = ∅ := is_min.eq_bot

lemma val_strict_mono : strict_mono (val : finset α → multiset α) := λ _ _, val_lt_iff.2

lemma card_strict_mono : strict_mono (card : finset α → ℕ) := λ _ _, card_lt_card

end finset

namespace finsupp
variables [canonically_ordered_add_monoid α] [canonically_ordered_add_monoid β] {f g : ι →₀ α}
  {m : ι → α → β}

lemma support_mono : monotone (support : (ι →₀ β) → finset ι) :=
λ f g h i hi, by { rw [mem_support_iff, ←bot_eq_zero] at ⊢ hi, exact ne_bot_of_le_ne_bot hi (h i) }

lemma sum_le_sum (h : f ≤ g) (hm : ∀ i, monotone (m i)) : f.sum m ≤ g.sum m :=
(finset.sum_le_sum_of_subset_of_nonneg (support_mono h) $ λ _ _ _, zero_le _).trans $
  sum_le_sum $ λ i _, hm i $ h i

end finsupp

namespace dfinsupp
variables [decidable_eq ι] [Π i, canonically_ordered_add_monoid (σ i)]
  [Π i (x : σ i), decidable (x ≠ 0)] [canonically_ordered_add_monoid α] {f g : Π₀ i, σ i}
  {m : Π i, σ i → α}

lemma support_mono : monotone (support : (Π₀ i, σ i) → finset ι) :=
λ f g h i hi, by { rw [mem_support_iff, ←bot_eq_zero] at ⊢ hi, exact ne_bot_of_le_ne_bot hi (h i) }

lemma sum_le_sum (h : f ≤ g) (hm : ∀ i, monotone (m i)) : f.sum m ≤ g.sum m :=
(finset.sum_le_sum_of_subset_of_nonneg (support_mono h) $ λ _ _ _, zero_le _).trans $
  sum_le_sum $ λ i _, hm i $ h i

end dfinsupp

namespace fin
variables {n : ℕ} {a b : fin n}

@[simp] lemma coe_inj : (a : ℕ) = b ↔ a = b := coe_eq_coe _ _

end fin

namespace nat

/-- A set of nats without gaps is an interval. The sizes of the gaps and intervals we consider are
bounded by `n`, so that we may induct on it. -/
private lemma all_ioo_of_ex_ioo {S : set ℕ} (n : ℕ) {a b c}
  (hS : ∀ {a b c} (hle : b ≤ a + n) (ha : a ∈ S) (hb : b ∈ S) (hac : a < c) (hcb : c < b),
    (S ∩ set.Ioo a b).nonempty)
  (hle : b ≤ a + n) (ha : a ∈ S) (hb : b ∈ S) (hac : a < c) (hcb : c < b) : c ∈ S :=
begin
  revert a b c,
  induction n with n hS',
  { exact λ a b c hle ha hb hac hcb, (not_lt_of_ge hle (lt_trans hac hcb)).elim },
  intros a b c hle ha hb hac hcb,
  rcases hS hle ha hb hac hcb with ⟨d, hd, had, hdb⟩,
  cases eq_or_ne c d with hcd hcd, { rwa hcd },
  have hxy : ∃ x y, y ≤ x + n ∧ x ∈ S ∧ y ∈ S ∧ x < c ∧ c < y := begin
    cases ne.lt_or_lt hcd with hcd hdc,
    { refine ⟨a, d, nat.le_of_lt_succ _, ha, hd, hac, hcd⟩,
      rw ←nat.add_succ,
      exact lt_of_lt_of_le hdb hle },
    { refine ⟨d, b, nat.le_of_lt_succ _, hd, hb, hdc, hcb⟩,
      rw ←nat.add_succ,
      exact lt_of_le_of_lt hle (add_lt_add_right had _) }
  end,
  rcases hxy with ⟨x, y, hle, hx, hy, hxc, hcy⟩,
  exact hS' (λ a b c hle ha hb hac hcb, hS (hle.trans (le_succ _)) ha hb hac hcb) hle hx hy hxc hcy
end

/-- A set of nats without gaps is an interval. -/
lemma all_icc_of_ex_ioo {S : set ℕ}
  (H : ∀ {a b c} (ha : a ∈ S) (hb : b ∈ S) (hac : a < c) (hcb : c < b), (S ∩ set.Ioo a b).nonempty)
  {a b c} (ha : a ∈ S) (hb : b ∈ S) (hac : a ≤ c) (hcb : c ≤ b) : c ∈ S :=
begin
  cases eq_or_lt_of_le hac with hac hac, { rwa ←hac },
  cases eq_or_lt_of_le hcb with hcb hcb, { rwa  hcb },
  exact all_ioo_of_ex_ioo b (λ a b c _ ha hb hac hcb, H ha hb hac hcb) (le_add_self) ha hb hac hcb
end

end nat
