/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import data.set.intervals.disjoint
import order.succ_pred.basic
import tactic.field_simp

/-!
# Monotonicity on intervals

In this file we prove that a function is (strictly) monotone (or antitone) on a linear order `α`
provided that it is (strictly) monotone on `(-∞, a]` and on `[a, +∞)`. We also provide an order
isomorphism `order_iso_Ioo_neg_one_one` between the open interval `(-1, 1)` in a linear ordered
field and the whole field.
-/

open set

section

variables {α β : Type*} [linear_order α] [preorder β] {a : α} {f : α → β}

/-- If `f` is strictly monotone both on `(-∞, a]` and `[a, ∞)`, then it is strictly monotone on the
whole line. -/
protected lemma strict_mono_on.Iic_union_Ici (h₁ : strict_mono_on f (Iic a))
  (h₂ : strict_mono_on f (Ici a)) : strict_mono f :=
begin
  intros x y hxy,
  cases lt_or_le a x with hax hxa; [skip, cases le_or_lt y a with hya hay],
  exacts [h₂ hax.le (hax.trans hxy).le hxy, h₁ hxa hya hxy,
    (h₁.monotone_on hxa le_rfl hxa).trans_lt (h₂ le_rfl hay.le hay)]
end

/-- If `f` is strictly antitone both on `(-∞, a]` and `[a, ∞)`, then it is strictly antitone on the
whole line. -/
protected lemma strict_anti_on.Iic_union_Ici (h₁ : strict_anti_on f (Iic a))
  (h₂ : strict_anti_on f (Ici a)) : strict_anti f :=
(h₁.dual_right.Iic_union_Ici h₂.dual_right).dual_right
protected lemma monotone_on.Iic_union_Ici (h₁ : monotone_on f (Iic a))
  (h₂ : monotone_on f (Ici a)) : monotone f :=
begin
  intros x y hxy,
  cases le_total x a with hxa hax; [cases le_total y a with hya hay, skip],
  exacts [h₁ hxa hya hxy, (h₁ hxa le_rfl hxa).trans (h₂ le_rfl hay hay), h₂ hax (hax.trans hxy) hxy]
end

protected lemma antitone_on.Iic_union_Ici (h₁ : antitone_on f (Iic a))
  (h₂ : antitone_on f (Ici a)) : antitone f :=
(h₁.dual_right.Iic_union_Ici h₂.dual_right).dual_right

end

section ordered_group

variables {G H : Type*} [linear_ordered_add_comm_group G] [ordered_add_comm_group H]

lemma strict_mono_of_odd_strict_mono_on_nonneg {f : G → H} (h₁ : ∀ x, f (-x) = -f x)
  (h₂ : strict_mono_on f (Ici 0)) :
  strict_mono f :=
begin
  refine strict_mono_on.Iic_union_Ici (λ x hx y hy hxy, neg_lt_neg_iff.1 _) h₂,
  rw [← h₁, ← h₁],
  exact h₂ (neg_nonneg.2 hy) (neg_nonneg.2 hx) (neg_lt_neg hxy)
end

lemma monotone_of_odd_of_monotone_on_nonneg {f : G → H} (h₁ : ∀ x, f (-x) = -f x)
  (h₂ : monotone_on f (Ici 0)) : monotone f :=
begin
  refine monotone_on.Iic_union_Ici (λ x hx y hy hxy, neg_le_neg_iff.1 _) h₂,
  rw [← h₁, ← h₁],
  exact h₂ (neg_nonneg.2 hy) (neg_nonneg.2 hx) (neg_le_neg hxy)
end

end ordered_group

/-- In a linear ordered field, the whole field is order isomorphic to the open interval `(-1, 1)`.
We consider the actual implementation to be a "black box", so it is irreducible.
-/
@[irreducible] def order_iso_Ioo_neg_one_one (k : Type*) [linear_ordered_field k] :
  k ≃o Ioo (-1 : k) 1 :=
begin
  refine strict_mono.order_iso_of_right_inverse _ _ (λ x, x / (1 - |x|)) _,
  { refine cod_restrict (λ x, x / (1 + |x|)) _ (λ x, abs_lt.1 _),
    have H : 0 < 1 + |x|, from (abs_nonneg x).trans_lt (lt_one_add _),
    calc |x / (1 + |x|)| = |x| / (1 + |x|) : by rw [abs_div, abs_of_pos H]
                     ... < 1               : (div_lt_one H).2 (lt_one_add _) },
  { refine (strict_mono_of_odd_strict_mono_on_nonneg _ _).cod_restrict _,
    { intro x, simp only [abs_neg, neg_div] },
    { rintros x (hx : 0 ≤ x) y (hy : 0 ≤ y) hxy,
      simp [abs_of_nonneg, mul_add, mul_comm x y, div_lt_div_iff,
        hx.trans_lt (lt_one_add _), hy.trans_lt (lt_one_add _), *] } },
  { refine λ x, subtype.ext _,
    have : 0 < 1 - |(x : k)|, from sub_pos.2 (abs_lt.2 x.2),
    field_simp [abs_div, this.ne', abs_of_pos this] }
end

section Ixx

variables {α β : Type*} [preorder α] [preorder β] {f g : α → β}

lemma antitone_Ici : antitone (Ici : α → set α) := λ _ _, Ici_subset_Ici.2

lemma monotone_Iic : monotone (Iic : α → set α) := λ _ _, Iic_subset_Iic.2

lemma antitone_Ioi : antitone (Ioi : α → set α) := λ _ _, Ioi_subset_Ioi

lemma monotone_Iio : monotone (Iio : α → set α) := λ _ _, Iio_subset_Iio

protected lemma monotone.Ici (hf : monotone f) : antitone (λ x, Ici (f x)) :=
antitone_Ici.comp_monotone hf

protected lemma antitone.Ici (hf : antitone f) : monotone (λ x, Ici (f x)) :=
antitone_Ici.comp hf

protected lemma monotone.Iic (hf : monotone f) : monotone (λ x, Iic (f x)) :=
monotone_Iic.comp hf

protected lemma antitone.Iic (hf : antitone f) : antitone (λ x, Iic (f x)) :=
monotone_Iic.comp_antitone hf

protected lemma monotone.Ioi (hf : monotone f) : antitone (λ x, Ioi (f x)) :=
antitone_Ioi.comp_monotone hf

protected lemma antitone.Ioi (hf : antitone f) : monotone (λ x, Ioi (f x)) :=
antitone_Ioi.comp hf

protected lemma monotone.Iio (hf : monotone f) : monotone (λ x, Iio (f x)) :=
monotone_Iio.comp hf

protected lemma antitone.Iio (hf : antitone f) : antitone (λ x, Iio (f x)) :=
monotone_Iio.comp_antitone hf

protected lemma monotone.Icc (hf : monotone f) (hg : antitone g) :
  antitone (λ x, Icc (f x) (g x)) :=
hf.Ici.inter hg.Iic

protected lemma antitone.Icc (hf : antitone f) (hg : monotone g) :
  monotone (λ x, Icc (f x) (g x)) :=
hf.Ici.inter hg.Iic

protected lemma monotone.Ico (hf : monotone f) (hg : antitone g) :
  antitone (λ x, Ico (f x) (g x)) :=
hf.Ici.inter hg.Iio

protected lemma antitone.Ico (hf : antitone f) (hg : monotone g) :
  monotone (λ x, Ico (f x) (g x)) :=
hf.Ici.inter hg.Iio

protected lemma monotone.Ioc (hf : monotone f) (hg : antitone g) :
  antitone (λ x, Ioc (f x) (g x)) :=
hf.Ioi.inter hg.Iic

protected lemma antitone.Ioc (hf : antitone f) (hg : monotone g) :
  monotone (λ x, Ioc (f x) (g x)) :=
hf.Ioi.inter hg.Iic

protected lemma monotone.Ioo (hf : monotone f) (hg : antitone g) :
  antitone (λ x, Ioo (f x) (g x)) :=
hf.Ioi.inter hg.Iio

protected lemma antitone.Ioo (hf : antitone f) (hg : monotone g) :
  monotone (λ x, Ioo (f x) (g x)) :=
hf.Ioi.inter hg.Iio

end Ixx

section Union

variables {α β : Type*} [semilattice_sup α] [linear_order β] {f g : α → β} {a b : β}

lemma Union_Ioo_of_mono_of_is_glb_of_is_lub (hf : antitone f) (hg : monotone g)
  (ha : is_glb (range f) a) (hb : is_lub (range g) b) :
  (⋃ x, Ioo (f x) (g x)) = Ioo a b :=
calc (⋃ x, Ioo (f x) (g x)) = (⋃ x, Ioi (f x)) ∩ ⋃ x, Iio (g x) :
  Union_inter_of_monotone hf.Ioi hg.Iio
... = Ioi a ∩ Iio b : congr_arg2 (∩) ha.Union_Ioi_eq hb.Union_Iio_eq

end Union

section succ_order

variables {α : Type*} [partial_order α] [order_bot α]
  [succ_order α] [is_succ_archimedean α] [no_max_order α]

lemma strict_mono_on.Icc_id_le {n : α} {φ : α → α} (hφ : strict_mono_on φ (set.Icc ⊥ n)) :
  ∀ m ≤ n, m ≤ φ m :=
begin
  revert hφ,
  refine @succ.rec _ _ _ _ (λ n, strict_mono_on φ (set.Icc ⊥ n) → ∀ m, m ≤ n → m ≤ φ m)
    ⊥ _ _ _ bot_le,
  { simp_rw le_bot_iff,
    rintro _ m rfl,
    exact bot_le },
  { rintro k h ih hφ m (hm : _ ≤ order.succ k),
    have := strict_mono_on.mono hφ (set.Icc_subset_Icc_right (order.le_succ _)),
    obtain (rfl | h) := order.le_succ_iff_eq_or_le.1 hm,
    { specialize ih this k le_rfl,
      exact le_trans (order.succ_mono ih) (order.succ_le_of_lt
        (hφ ⟨bot_le, order.le_succ _⟩ ⟨bot_le, le_refl _⟩ (order.lt_succ _))) },
    { exact ih this _ h } }
end

lemma strict_mono_on_Icc_of_lt_succ {n : α} {φ : α → α}
  (hφ : ∀ m, order.succ m ≤ n → φ m < φ (order.succ m)) :
  strict_mono_on φ (set.Icc ⊥ n) :=
begin
  revert hφ,
  refine @succ.rec _ _ _ _
    (λ n, (∀ m, order.succ m ≤ n → φ m < φ (order.succ m)) → strict_mono_on φ (set.Icc ⊥ n))
    ⊥ _ _ _ bot_le,
  { simp },
  { rintro k h ih hφ i ⟨-, hi⟩ j ⟨-, hj⟩ hij,
    specialize ih (λ m hm, hφ _ (le_trans hm (order.le_succ _))),
    by_cases hj' : j = order.succ k,
    { subst hj',
      rw order.lt_succ_iff at hij,
      exact lt_of_le_of_lt
        (ih.monotone_on ⟨bot_le, hij⟩ ⟨bot_le, le_rfl⟩ hij) (hφ _ le_rfl) },
    { have hj'' : j ≤ k,
      { exact order.lt_succ_iff.1 (lt_of_le_of_ne hj hj') },
      exact ih ⟨bot_le, le_trans hij.le hj''⟩ ⟨bot_le, hj''⟩ hij } }
end

end succ_order
