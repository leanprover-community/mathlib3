/-
Copyright (c) 2022 Yaël Dillies, Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Violeta Hernández Palacios, Grayson Burton, Vladimir Ivanov
-/
import algebra.big_operators.order
import data.dfinsupp.order
import data.finsupp.order
import data.nat.succ_pred
import data.sum.order
import order.atoms
import order.locally_finite
import order.chain

/-!
# To move
-/

open finset function

variables {ι α β : Type*} {σ : ι → Type*}

section order_dual
open order_dual
variables {a b : order_dual α}

@[simp] lemma to_dual_top [has_top α] : to_dual (⊤ : α) = ⊥ := rfl
@[simp] lemma to_dual_bot [has_bot α] : to_dual (⊥ : α) = ⊤ := rfl
@[simp] lemma of_dual_top [has_bot α] : of_dual (⊤ : order_dual α) = ⊥ := rfl
@[simp] lemma of_dual_bot [has_top α] : of_dual (⊥ : order_dual α) = ⊤ := rfl

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

lemma is_chain_singleton (r : α → α → Prop) (a : α) : is_chain r {a} := set.pairwise_singleton _ _

/-- A preorder is isomorphic to the section from bottom to top. -/
def set.Icc.self_order_iso_bot_top (α : Type*) [preorder α] [order_bot α] [order_top α] :
  α ≃o set.Icc ⊥ (⊤ : α) :=
{ to_fun := λ x, ⟨x, bot_le, le_top⟩,
  inv_fun := subtype.val,
  left_inv := λ _, rfl,
  right_inv := λ _, subtype.eq rfl,
  map_rel_iff' := by simp }

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

section
variables [has_lt α] [comm_group α] [covariant_class α α (*) (<)] {a b c : α}

@[to_additive] lemma covby.mul_left (h : b ⋖ c) (a : α) : a * b ⋖ a * c :=
⟨mul_lt_mul_left' h.lt _, λ d hb hc,
  h.2 (lt_div_iff_mul_lt.2 $ by rwa mul_comm) (_root_.div_lt_iff_lt_mul'.2 hc)⟩

@[to_additive] lemma covby.mul_right (h : b ⋖ c) (a : α) : b * a ⋖ c * a :=
⟨mul_lt_mul_right' h.lt _, λ d hb hc,
  h.2 (lt_div_iff_mul_lt.2 hb) (_root_.div_lt_iff_lt_mul'.2 $ by rwa mul_comm)⟩

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

namespace prod
variables [partial_order α] [order_bot α] [partial_order β] [order_bot β] {a a' : α} {b b' : β}
  {x y : α × β}

@[simp] lemma swap_le_swap_iff : x.swap ≤ y.swap ↔ x ≤ y := and_comm _ _

@[simp] lemma swap_lt_swap_iff : x.swap < y.swap ↔ x < y :=
lt_iff_lt_of_le_iff_le' swap_le_swap_iff swap_le_swap_iff

@[simp] lemma swap_covby_swap_iff : x.swap ⋖ y.swap ↔ x ⋖ y :=
apply_covby_apply_iff (order_iso.prod_comm : α × β ≃o β × α)

lemma mk_le_mk_iff_left : (a, b) ≤ (a', b) ↔ a ≤ a' := and_iff_left le_rfl
lemma mk_le_mk_iff_right : (a, b) ≤ (a, b') ↔ b ≤ b' := and_iff_right le_rfl

lemma mk_lt_mk_iff_left : (a, b) < (a', b) ↔ a < a' :=
lt_iff_lt_of_le_iff_le' mk_le_mk_iff_left mk_le_mk_iff_left

lemma mk_lt_mk_iff_right : (a, b) < (a, b') ↔ b < b' :=
lt_iff_lt_of_le_iff_le' mk_le_mk_iff_right mk_le_mk_iff_right

lemma fst_eq_or_snd_eq_of_covby : (a, b) ⋖ (a', b') → a = a' ∨ b = b' :=
begin
  contrapose,
  push_neg,
  rintros ⟨ha, hb⟩ hcov,
  have h₁ : (a, b) < (a', b)   := mk_lt_mk.mpr (or.inl ⟨ha.le_iff_lt.mp hcov.1.1.1, le_rfl⟩),
  have h₂ : (a', b) < (a', b') := mk_lt_mk.mpr (or.inr ⟨le_rfl, hb.le_iff_lt.mp hcov.1.1.2⟩),
  exact hcov.2 h₁ h₂
end

lemma mk_covby_mk_iff_left : (a, b) ⋖ (a', b) ↔ a ⋖ a' :=
begin
  split;
  rintro ⟨hcov_left, hcov_right⟩;
  split;
  [ { skip },
    { intros c hac hca',
      apply @hcov_right (c, b) },
    { skip },
    { rintros ⟨c₁, c₂⟩ h h',
      apply @hcov_right c₁;
      have : c₂ = b := le_antisymm h'.1.2 h.1.2;
      rw this at *, } ];
  rw mk_lt_mk_iff_left at *;
  assumption,
end

lemma mk_covby_mk_iff_right : (a, b) ⋖ (a, b') ↔ b ⋖ b' :=
swap_covby_swap_iff.trans mk_covby_mk_iff_left

lemma mk_covby_mk_iff : (a, b) ⋖ (a', b') ↔ a ⋖ a' ∧ b = b' ∨ a = a' ∧ b ⋖ b' :=
begin
  split,
  { intro hcov,
    cases fst_eq_or_snd_eq_of_covby hcov with heq heq;
    rw [heq, eq_self_iff_true] at *,
    { rw [mk_covby_mk_iff_right] at *,
      tauto },
    { rw mk_covby_mk_iff_left at *,
      tauto } },
  { intro h,
    rcases h with ⟨acov, beq⟩ | ⟨aeq, bcov⟩,
    { rw beq at *,
      exact mk_covby_mk_iff_left.mpr acov },
    { rw aeq at *,
      exact mk_covby_mk_iff_right.mpr bcov } }
end

lemma _root_.is_min.prod_mk (ha : is_min a) (hb : is_min b) : is_min (a, b) :=
λ c hc, ⟨ha hc.1, hb hc.2⟩

lemma _root_.is_min.fst (hx : is_min x) : is_min x.1 :=
λ c hc, (hx ((and_iff_left le_rfl).2 hc : (c, x.2) ≤ x)).1

lemma _root_.is_min.snd (hx : is_min x) : is_min x.2 :=
λ c hc, (hx ((and_iff_right le_rfl).2 hc : (x.1, c) ≤ x)).2

lemma is_min_iff : is_min x ↔ is_min x.1 ∧ is_min x.2 :=
⟨λ hx, ⟨hx.fst, hx.snd⟩, λ h, h.1.prod_mk h.2⟩

end prod

namespace pi
variables [Π i, preorder (σ i)] {a : Π i, σ i}

lemma _root_.is_min.apply' (ha : is_min a) (i : ι) : is_min (a i) :=
λ c hc,
  by { classical, exact (ha (update_le_iff.2 ⟨hc, λ j _, le_rfl⟩) i).trans_eq (update_same _ _ _) }

lemma is_min_iff : is_min a ↔ ∀ i, is_min (a i) :=
⟨is_min.apply', λ h b hb i, h _ $ hb i⟩

end pi

namespace sum
variables [preorder α] [preorder β]

@[simp] lemma is_min_inl_iff {a : α} : is_min (inl a : α ⊕ β) ↔ is_min a := sorry
@[simp] lemma is_min_inr_iff {b : β} : is_min (inr b : α ⊕ β) ↔ is_min b := sorry
@[simp] lemma is_max_inl_iff {a : α} : is_max (inl a : α ⊕ β) ↔ is_max a := sorry
@[simp] lemma is_max_inr_iff {b : β} : is_max (inr b : α ⊕ β) ↔ is_max b := sorry

end sum

section
variables {γ : Type*}
variables [preorder α] [preorder β] [preorder γ] {f : α → γ} {g : β → γ}

open sum

lemma strict_mono.sum_elim (hf : strict_mono f) (hg : strict_mono g) : strict_mono (sum.elim f g)
| (inl a) (inl b) (lift_rel.inl h) := hf h
| (inr a) (inr b) (lift_rel.inr h) := hg h

end

namespace list
variables {l : list α} {a : α}

lemma sublist.rfl : l <+ l := sublist.refl _

lemma sublist_singleton : Π {l : list α} {a : α}, l <+ [a] → l = nil ∨ l = [a]
| _ _ (sublist.cons  _ _  _ _ ) := by apply or.inl; rwa ←sublist_nil_iff_eq_nil
| _ _ (sublist.cons2 a [] _ hl) := begin
  rw sublist_nil_iff_eq_nil at hl,
  rw hl,
  exact or.inr rfl
end

lemma sublist_singleton_iff : l <+ [a] ↔ l = nil ∨ l = [a] :=
⟨sublist_singleton, begin
  rintro (rfl | rfl),
  { exact nil_sublist _ },
  { exact sublist.rfl }
end⟩


end list

namespace multiset
variables {s t : multiset α} {a : α}

@[simp] lemma cons_zero (a : α) : a ::ₘ 0 = {a} := rfl

lemma cons_lt_cons_iff : a ::ₘ s < a ::ₘ t ↔ s < t :=
lt_iff_lt_of_le_iff_le' (cons_le_cons_iff _) (cons_le_cons_iff _)

lemma cons_lt_cons (a : α) (h : s < t) : a ::ₘ s < a ::ₘ t := cons_lt_cons_iff.2 h

lemma lt_singleton : s < {a} ↔ s = 0 :=
begin
  rcases s with ⟨s⟩,
  change (↑s < ↑[a]) ↔ ↑s = _,
  simp_rw [coe_eq_zero, lt_iff_cons_le, cons_coe, coe_le],
  refine ⟨λ h, _, λ h, _⟩,
  { rcases h with ⟨w, w', hw'w, hw'a⟩,
    rw list.sublist_singleton_iff at hw'a,
    obtain rfl | rfl := hw'a,
    { rw list.nil_perm at hw'w, contradiction },
    { rw [list.singleton_perm, list.cons.inj_eq] at hw'w,
      rw hw'w.right } },
  { use a,
    induction h,
    refl }
end

lemma covby_cons (m : multiset α) (a : α) : m ⋖ a ::ₘ m := ⟨lt_cons_self _ _, begin
  simp_rw lt_iff_cons_le,
  rintros m' ⟨b, hbm'⟩ ⟨c, hcm'⟩,
  apply @irrefl _ (<) _ m,
  have h := lt_of_le_of_lt hbm' (lt_cons_self _ c),
  replace h := lt_of_lt_of_le h hcm',
  clear hbm' hcm',
  induction m using multiset.induction with d m hm,
  { rw [cons_zero a, lt_singleton] at h,
    exact (cons_ne_zero h).elim },
  { simp_rw cons_swap _ d at h,
    rw cons_lt_cons_iff at h ⊢,
    exact hm h }
end⟩

lemma _root_.covby.exists_cons_multiset (h : s ⋖ t) : ∃ a, t = a ::ₘ s :=
(lt_iff_cons_le.1 h.lt).imp $ λ a ha, ha.eq_of_not_gt $ h.2 $ lt_cons_self _ _

lemma _root_.covby.card_multiset (h : s ⋖ t) : s.card ⋖ t.card :=
begin
  obtain ⟨a, rfl⟩ := h.exists_cons_multiset,
  rw card_cons,
  exact order.covby_succ _,
end

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
