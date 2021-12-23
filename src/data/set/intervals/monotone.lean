/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import data.set.intervals.basic
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

variables (k : Type*) [linear_ordered_field k]

/-- In a linear ordered field, the whole field is order isomorphic to the open interval `(-1, 1)`.
-/
@[irreducible] def order_iso_Ioo_neg_one_one : k ≃o Ioo (-1 : k) 1 :=
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
