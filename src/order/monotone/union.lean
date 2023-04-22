/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Sébastien Gouëzel
-/
import order.bounds.basic

/-!
# Monotonicity on intervals

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove that a function is (strictly) monotone (or antitone) on a linear order `α`
provided that it is (strictly) monotone on `(-∞, a]` and on `[a, +∞)`. This is a special case
of a more general statement where one deduces monotonicity on a union from monotonicity on each
set.
-/

open set
variables {α β : Type*} [linear_order α] [preorder β] {a : α} {f : α → β}

/-- If `f` is strictly monotone both on `s` and `t`, with `s` to the left of `t` and the center
point belonging to both `s` and `t`, then `f` is strictly monotone on `s ∪ t` -/
protected lemma strict_mono_on.union {s t : set α} {c : α} (h₁ : strict_mono_on f s)
  (h₂ : strict_mono_on f t) (hs : is_greatest s c) (ht : is_least t c) :
  strict_mono_on f (s ∪ t) :=
begin
  have A : ∀ x, x ∈ s ∪ t → x ≤ c → x ∈ s,
  { assume x hx hxc,
    cases hx, { exact hx },
    rcases eq_or_lt_of_le hxc with rfl|h'x, { exact hs.1 },
    exact (lt_irrefl _ (h'x.trans_le (ht.2 hx))).elim },
  have B : ∀ x, x ∈ s ∪ t → c ≤ x → x ∈ t,
  { assume x hx hxc,
    cases hx, swap, { exact hx },
    rcases eq_or_lt_of_le hxc with rfl|h'x, { exact ht.1 },
    exact (lt_irrefl _ (h'x.trans_le (hs.2 hx))).elim },
  assume x hx y hy hxy,
  rcases lt_or_le x c with hxc|hcx,
  { have xs : x ∈ s, from A _ hx hxc.le,
    rcases lt_or_le y c with hyc|hcy,
    { exact h₁ xs (A _ hy hyc.le) hxy },
    { exact (h₁ xs hs.1 hxc).trans_le (h₂.monotone_on ht.1 (B _ hy hcy) hcy) } },
  { have xt : x ∈ t, from B _ hx hcx,
    have yt : y ∈ t, from B _ hy (hcx.trans hxy.le),
    exact h₂ xt yt hxy }
end

/-- If `f` is strictly monotone both on `(-∞, a]` and `[a, ∞)`, then it is strictly monotone on the
whole line. -/
protected lemma strict_mono_on.Iic_union_Ici (h₁ : strict_mono_on f (Iic a))
  (h₂ : strict_mono_on f (Ici a)) : strict_mono f :=
begin
  rw [← strict_mono_on_univ, ← @Iic_union_Ici _ _ a],
  exact strict_mono_on.union h₁ h₂ is_greatest_Iic is_least_Ici,
end

/-- If `f` is strictly antitone both on `s` and `t`, with `s` to the left of `t` and the center
point belonging to both `s` and `t`, then `f` is strictly antitone on `s ∪ t` -/
protected lemma strict_anti_on.union {s t : set α} {c : α} (h₁ : strict_anti_on f s)
  (h₂ : strict_anti_on f t) (hs : is_greatest s c) (ht : is_least t c) :
  strict_anti_on f (s ∪ t) :=
(h₁.dual_right.union h₂.dual_right hs ht).dual_right

/-- If `f` is strictly antitone both on `(-∞, a]` and `[a, ∞)`, then it is strictly antitone on the
whole line. -/
protected lemma strict_anti_on.Iic_union_Ici (h₁ : strict_anti_on f (Iic a))
  (h₂ : strict_anti_on f (Ici a)) : strict_anti f :=
(h₁.dual_right.Iic_union_Ici h₂.dual_right).dual_right

/-- If `f` is monotone both on `s` and `t`, with `s` to the left of `t` and the center
point belonging to both `s` and `t`, then `f` is monotone on `s ∪ t` -/
protected lemma monotone_on.union_right {s t : set α} {c : α} (h₁ : monotone_on f s)
  (h₂ : monotone_on f t) (hs : is_greatest s c) (ht : is_least t c) :
  monotone_on f (s ∪ t) :=
begin
  have A : ∀ x, x ∈ s ∪ t → x ≤ c → x ∈ s,
  { assume x hx hxc,
    cases hx, { exact hx },
    rcases eq_or_lt_of_le hxc with rfl|h'x, { exact hs.1 },
    exact (lt_irrefl _ (h'x.trans_le (ht.2 hx))).elim },
  have B : ∀ x, x ∈ s ∪ t → c ≤ x → x ∈ t,
  { assume x hx hxc,
    cases hx, swap, { exact hx },
    rcases eq_or_lt_of_le hxc with rfl|h'x, { exact ht.1 },
    exact (lt_irrefl _ (h'x.trans_le (hs.2 hx))).elim },
  assume x hx y hy hxy,
  rcases lt_or_le x c with hxc|hcx,
  { have xs : x ∈ s, from A _ hx hxc.le,
    rcases lt_or_le y c with hyc|hcy,
    { exact h₁ xs (A _ hy hyc.le) hxy },
    { exact (h₁ xs hs.1 hxc.le).trans (h₂ ht.1 (B _ hy hcy) hcy) } },
  { have xt : x ∈ t, from B _ hx hcx,
    have yt : y ∈ t, from B _ hy (hcx.trans hxy),
    exact h₂ xt yt hxy }
end

/-- If `f` is monotone both on `(-∞, a]` and `[a, ∞)`, then it is monotone on the whole line. -/
protected lemma monotone_on.Iic_union_Ici (h₁ : monotone_on f (Iic a))
  (h₂ : monotone_on f (Ici a)) : monotone f :=
begin
  rw [← monotone_on_univ, ← @Iic_union_Ici _ _ a],
  exact monotone_on.union_right h₁ h₂ is_greatest_Iic is_least_Ici
end

/-- If `f` is antitone both on `s` and `t`, with `s` to the left of `t` and the center
point belonging to both `s` and `t`, then `f` is antitone on `s ∪ t` -/
protected lemma antitone_on.union_right {s t : set α} {c : α} (h₁ : antitone_on f s)
  (h₂ : antitone_on f t) (hs : is_greatest s c) (ht : is_least t c) :
  antitone_on f (s ∪ t) :=
(h₁.dual_right.union_right h₂.dual_right hs ht).dual_right

/-- If `f` is antitone both on `(-∞, a]` and `[a, ∞)`, then it is antitone on the whole line. -/
protected lemma antitone_on.Iic_union_Ici (h₁ : antitone_on f (Iic a))
  (h₂ : antitone_on f (Ici a)) : antitone f :=
(h₁.dual_right.Iic_union_Ici h₂.dual_right).dual_right
