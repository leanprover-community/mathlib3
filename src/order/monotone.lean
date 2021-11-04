/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Yaël Dillies
-/
import order.compare
import order.order_dual

/-!
# Monotonicity

This file defines (strictly) monotone/antitone functions. Contrary to standard mathematical usage,
"monotone"/"mono" here means "increasing", not "increasing or decreasing". We use "antitone"/"anti"
to mean "decreasing".

## Definitions

* `monotone f`: A function `f` between two preorders is monotone if `a ≤ b` implies `f a ≤ f b`.
* `antitone f`: A function `f` between two preorders is antitone if `a ≤ b` implies `f b ≤ f a`.
* `monotone_on f s`: Same as `monotone f`, but for all `a, b ∈ s`.
* `antitone_on f s`: Same as `antitone f`, but for all `a, b ∈ s`.
* `strict_mono f` : A function `f` between two preorders is strictly monotone if `a < b` implies
  `f a < f b`.
* `strict_anti f` : A function `f` between two preorders is strictly antitone if `a < b` implies
  `f b < f a`.
* `strict_mono_on f s`: Same as `strict_mono f`, but for all `a, b ∈ s`.
* `strict_anti_on f s`: Same as `strict_anti f`, but for all `a, b ∈ s`.

## Main theorems

* `monotone_nat_of_le_succ`: If `f : ℕ → α` and `f n ≤ f (n + 1)` for all `n`, then `f` is
  monotone.
* `antitone_nat_of_succ_le`: If `f : ℕ → α` and `f (n + 1) ≤ f n` for all `n`, then `f` is
  antitone.
* `strict_mono_nat_of_lt_succ`: If `f : ℕ → α` and `f n < f (n + 1)` for all `n`, then `f` is
  strictly monotone.
* `strict_anti_nat_of_succ_lt`: If `f : ℕ → α` and `f (n + 1) < f n` for all `n`, then `f` is
  strictly antitone.

## Implementation notes

Some of these definitions used to only require `has_le α` or `has_lt α`. The advantage of this is
unclear and it led to slight elaboration issues. Now, everything requires `preorder α` and seems to
work fine. Related Zulip discussion:
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Order.20diamond/near/254353352.

## TODO

The above theorems are also true in `ℤ`, `ℕ+`, `fin n`... To make that work, we need `succ_order α`
along with another typeclass we don't yet have roughly stating "everything is reachable using
finitely many `succ`".

## Tags

monotone, strictly monotone, antitone, strictly antitone, increasing, strictly increasing,
decreasing, strictly decreasing
-/

open function

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w} {r : α → α → Prop}

section monotone_def
variables [preorder α] [preorder β]

/-- A function `f` is monotone if `a ≤ b` implies `f a ≤ f b`. -/
def monotone (f : α → β) : Prop := ∀ ⦃a b⦄, a ≤ b → f a ≤ f b

/-- A function `f` is antitone if `a ≤ b` implies `f b ≤ f a`. -/
def antitone (f : α → β) : Prop := ∀ ⦃a b⦄, a ≤ b → f b ≤ f a

/-- A function `f` is monotone on `s` if, for all `a, b ∈ s`, `a ≤ b` implies `f b ≤ f a`. -/
def monotone_on (f : α → β) (s : set α) : Prop :=
∀ ⦃a⦄ (ha : a ∈ s) ⦃b⦄ (hb : b ∈ s), a ≤ b → f a ≤ f b

/-- A function `f` is antitone on `s` if, for all `a, b ∈ s`, `a ≤ b` implies `f a ≤ f b`. -/
def antitone_on (f : α → β) (s : set α) : Prop :=
∀ ⦃a⦄ (ha : a ∈ s) ⦃b⦄ (hb : b ∈ s), a ≤ b → f b ≤ f a

/-- A function `f` is strictly monotone if `a < b` implies `f a < f b`. -/
def strict_mono (f : α → β) : Prop :=
∀ ⦃a b⦄, a < b → f a < f b

/-- A function `f` is strictly antitone if `a < b` implies `f b < f a`. -/
def strict_anti (f : α → β) : Prop :=
∀ ⦃a b⦄, a < b → f b < f a

/-- A function `f` is strictly monotone on `s` if, for all `a, b ∈ s`, `a < b` implies
`f a < f b`. -/
def strict_mono_on (f : α → β) (s : set α) : Prop :=
∀ ⦃a⦄ (ha : a ∈ s) ⦃b⦄ (hb : b ∈ s), a < b → f a < f b

/-- A function `f` is strictly antitone on `s` if, for all `a, b ∈ s`, `a < b` implies
`f b < f a`. -/
def strict_anti_on (f : α → β) (s : set α) : Prop :=
∀ ⦃a⦄ (ha : a ∈ s) ⦃b⦄ (hb : b ∈ s), a < b → f b < f a

end monotone_def

/-! #### Monotonicity on the dual order

Strictly many of the `*_on.dual` lemmas in this section should use `of_dual ⁻¹' s` instead of `s`,
but right now this is not possible as `set.preimage` is not defined yet, and importing it creates
an import cycle.
-/

section order_dual
open order_dual
variables [preorder α] [preorder β] {f : α → β} {s : set α}

protected theorem monotone.dual (hf : monotone f) : monotone (to_dual ∘ f ∘ of_dual) :=
λ a b h, hf h

protected lemma monotone.dual_left (hf : monotone f) : antitone (f ∘ of_dual) :=
λ a b h, hf h

protected lemma monotone.dual_right (hf : monotone f) : antitone (to_dual ∘ f) :=
λ a b h, hf h

protected theorem antitone.dual (hf : antitone f) : antitone (to_dual ∘ f ∘ of_dual) :=
λ a b h, hf h

protected lemma antitone.dual_left (hf : antitone f) : monotone (f ∘ of_dual) :=
λ a b h, hf h

protected lemma antitone.dual_right (hf : antitone f) : monotone (to_dual ∘ f) :=
λ a b h, hf h

protected theorem monotone_on.dual (hf : monotone_on f s) : monotone_on (to_dual ∘ f ∘ of_dual) s :=
λ a ha b hb, hf hb ha

protected lemma monotone_on.dual_left (hf : monotone_on f s) : antitone_on (f ∘ of_dual) s :=
λ a ha b hb, hf hb ha

protected lemma monotone_on.dual_right (hf : monotone_on f s) : antitone_on (to_dual ∘ f) s :=
λ a ha b hb, hf ha hb

protected theorem antitone_on.dual (hf : antitone_on f s) : antitone_on (to_dual ∘ f ∘ of_dual) s :=
λ a ha b hb, hf hb ha

protected lemma antitone_on.dual_left (hf : antitone_on f s) : monotone_on (f ∘ of_dual) s :=
λ a ha b hb, hf hb ha

protected lemma antitone_on.dual_right (hf : antitone_on f s) : monotone_on (to_dual ∘ f) s :=
λ a ha b hb, hf ha hb

protected theorem strict_mono.dual (hf : strict_mono f) : strict_mono (to_dual ∘ f ∘ of_dual) :=
λ a b h, hf h

protected lemma strict_mono.dual_left (hf : strict_mono f) : strict_anti (f ∘ of_dual) :=
λ a b h, hf h

protected lemma strict_mono.dual_right (hf : strict_mono f) : strict_anti (to_dual ∘ f) :=
λ a b h, hf h

protected theorem strict_anti.dual (hf : strict_anti f) : strict_anti (to_dual ∘ f ∘ of_dual) :=
λ a b h, hf h

protected lemma strict_anti.dual_left (hf : strict_anti f) : strict_mono (f ∘ of_dual) :=
λ a b h, hf h

protected lemma strict_anti.dual_right (hf : strict_anti f) : strict_mono (to_dual ∘ f) :=
λ a b h, hf h

protected theorem strict_mono_on.dual (hf : strict_mono_on f s) :
  strict_mono_on (to_dual ∘ f ∘ of_dual) s :=
λ a ha b hb, hf hb ha

protected lemma strict_mono_on.dual_left (hf : strict_mono_on f s) :
  strict_anti_on (f ∘ of_dual) s :=
λ a ha b hb, hf hb ha

protected lemma strict_mono_on.dual_right (hf : strict_mono_on f s) :
  strict_anti_on (to_dual ∘ f) s :=
λ a ha b hb, hf ha hb

protected theorem strict_anti_on.dual (hf : strict_anti_on f s) :
  strict_anti_on (to_dual ∘ f ∘ of_dual) s :=
λ a ha b hb, hf hb ha

protected lemma strict_anti_on.dual_left (hf : strict_anti_on f s) :
  strict_mono_on (f ∘ of_dual) s :=
λ a ha b hb, hf hb ha

protected lemma strict_anti_on.dual_right (hf : strict_anti_on f s) :
  strict_mono_on (to_dual ∘ f) s :=
λ a ha b hb, hf ha hb

end order_dual

/-! #### Monotonicity in function spaces -/

section preorder
variables [preorder α]

theorem monotone.comp_le_comp_left [preorder β]
  {f : β → α} {g h : γ → β} (hf : monotone f) (le_gh : g ≤ h) :
  has_le.le.{max w u} (f ∘ g) (f ∘ h) :=
λ x, hf (le_gh x)

variables [preorder γ]

theorem monotone_lam {f : α → β → γ} (hf : ∀ b, monotone (λ a, f a b)) : monotone f :=
λ a a' h b, hf b h

theorem monotone_app (f : β → α → γ) (b : β) (hf : monotone (λ a b, f b a)) : monotone (f b) :=
λ a a' h, hf h b

theorem antitone_lam {f : α → β → γ} (hf : ∀ b, antitone (λ a, f a b)) : antitone f :=
λ a a' h b, hf b h

theorem antitone_app (f : β → α → γ) (b : β) (hf : antitone (λ a b, f b a)) : antitone (f b) :=
λ a a' h, hf h b

end preorder

lemma function.monotone_eval {ι : Type u} {α : ι → Type v} [∀ i, preorder (α i)] (i : ι) :
  monotone (function.eval i : (Π i, α i) → α i) :=
λ f g H, H i

/-! #### Monotonicity hierarchy -/

section preorder
variables [preorder α]

section preorder
variables [preorder β] {f : α → β}

protected lemma monotone.monotone_on (hf : monotone f) (s : set α) : monotone_on f s :=
λ a _ b _ h, hf h

protected lemma antitone.antitone_on (hf : antitone f) (s : set α) : antitone_on f s :=
λ a _ b _ h, hf h

lemma monotone_on_univ : monotone_on f set.univ ↔ monotone f :=
⟨λ h a b, h trivial trivial, λ h, h.monotone_on _⟩

lemma antitone_on_univ : antitone_on f set.univ ↔ antitone f :=
⟨λ h a b, h trivial trivial, λ h, h.antitone_on _⟩

protected lemma strict_mono.strict_mono_on (hf : strict_mono f) (s : set α) : strict_mono_on f s :=
λ a _ b _ h, hf h

protected lemma strict_anti.strict_anti_on (hf : strict_anti f) (s : set α) : strict_anti_on f s :=
λ a _ b _ h, hf h

lemma strict_mono_on_univ : strict_mono_on f set.univ ↔ strict_mono f :=
⟨λ h a b, h trivial trivial, λ h, h.strict_mono_on _⟩

lemma strict_anti_on_univ : strict_anti_on f set.univ ↔ strict_anti f :=
⟨λ h a b, h trivial trivial, λ h, h.strict_anti_on _⟩

end preorder

section partial_order
variables [partial_order β] {f : α → β}

lemma monotone.strict_mono_of_injective (h₁ : monotone f) (h₂ : injective f) : strict_mono f :=
λ a b h, (h₁ h.le).lt_of_ne (λ H, h.ne $ h₂ H)

lemma antitone.strict_anti_of_injective (h₁ : antitone f) (h₂ : injective f) : strict_anti f :=
λ a b h, (h₁ h.le).lt_of_ne (λ H, h.ne $ h₂ H.symm)

end partial_order
end preorder

section partial_order
variables [partial_order α] [preorder β] {f : α → β}

-- `preorder α` isn't strong enough: if the preorder on `α` is an equivalence relation,
-- then `strict_mono f` is vacuously true.
protected lemma strict_mono.monotone (hf : strict_mono f) : monotone f :=
λ a b h, h.eq_or_lt.rec (by { rintro rfl, refl }) (le_of_lt ∘ (@hf _ _))

protected lemma strict_anti.antitone (hf : strict_anti f) : antitone f :=
λ a b h, h.eq_or_lt.rec (by { rintro rfl, refl }) (le_of_lt ∘ (@hf _ _))

end partial_order

/-! #### Miscellaneous monotonicity results -/

lemma monotone_id [preorder α] : monotone (id : α → α) := λ a b, id

lemma strict_mono_id [preorder α] : strict_mono (id : α → α) := λ a b, id

theorem monotone_const [preorder α] [preorder β] {c : β} : monotone (λ (a : α), c) :=
λ a b _, le_refl c

theorem antitone_const [preorder α] [preorder β] {c : β} : antitone (λ (a : α), c) :=
λ a b _, le_refl c

lemma strict_mono_of_le_iff_le [preorder α] [preorder β] {f : α → β}
  (h : ∀ x y, x ≤ y ↔ f x ≤ f y) : strict_mono f :=
λ a b, by simp [lt_iff_le_not_le, h] {contextual := tt}

lemma injective_of_lt_imp_ne [linear_order α] {f : α → β} (h : ∀ x y, x < y → f x ≠ f y) :
  injective f :=
begin
  intros x y k,
  contrapose k,
  rw [←ne.def, ne_iff_lt_or_gt] at k,
  cases k,
  { exact h _ _ k },
  { exact (h _ _ k).symm }
end

lemma injective_of_le_imp_le [partial_order α] [preorder β] (f : α → β)
  (h : ∀ {x y}, f x ≤ f y → x ≤ y) : injective f :=
λ x y hxy, (h hxy.le).antisymm (h hxy.ge)

section preorder
variables [preorder α] [preorder β] {f g : α → β}

protected lemma strict_mono.ite' (hf : strict_mono f) (hg : strict_mono g) {p : α → Prop}
  [decidable_pred p] (hp : ∀ ⦃x y⦄, x < y → p y → p x)
  (hfg : ∀ ⦃x y⦄, p x → ¬p y → x < y → f x < g y) :
  strict_mono (λ x, if p x then f x else g x) :=
begin
  intros x y h,
  by_cases hy : p y,
  { have hx : p x := hp h hy,
    simpa [hx, hy] using hf h },
  by_cases hx : p x,
  { simpa [hx, hy] using hfg hx hy h },
  { simpa [hx, hy] using hg h}
end

protected lemma strict_mono.ite (hf : strict_mono f) (hg : strict_mono g) {p : α → Prop}
  [decidable_pred p] (hp : ∀ ⦃x y⦄, x < y → p y → p x) (hfg : ∀ x, f x ≤ g x) :
  strict_mono (λ x, if p x then f x else g x) :=
hf.ite' hg hp $ λ x y hx hy h, (hf h).trans_le (hfg y)

protected lemma strict_anti.ite' (hf : strict_anti f) (hg : strict_anti g) {p : α → Prop}
  [decidable_pred p] (hp : ∀ ⦃x y⦄, x < y → p y → p x)
  (hfg : ∀ ⦃x y⦄, p x → ¬p y → x < y → g y < f x) :
  strict_anti (λ x, if p x then f x else g x) :=
(strict_mono.ite' hf.dual_right hg.dual_right hp hfg).dual_right

protected lemma strict_anti.ite (hf : strict_anti f) (hg : strict_anti g) {p : α → Prop}
  [decidable_pred p] (hp : ∀ ⦃x y⦄, x < y → p y → p x) (hfg : ∀ x, g x ≤ f x) :
  strict_anti (λ x, if p x then f x else g x) :=
hf.ite' hg hp $ λ x y hx hy h, (hfg y).trans_lt (hf h)

end preorder

/-! #### Monotonicity under composition -/

section composition
variables [preorder α] [preorder β] [preorder γ] {g : β → γ} {f : α → β} {s : set α}

protected lemma monotone.comp (hg : monotone g) (hf : monotone f) :
  monotone (g ∘ f) :=
λ a b h, hg (hf h)

lemma monotone.comp_antitone (hg : monotone g) (hf : antitone f) :
  antitone (g ∘ f) :=
λ a b h, hg (hf h)

protected lemma antitone.comp (hg : antitone g) (hf : antitone f) :
  monotone (g ∘ f) :=
λ a b h, hg (hf h)

lemma antitone.comp_monotone (hg : antitone g) (hf : monotone f) :
  antitone (g ∘ f) :=
λ a b h, hg (hf h)

protected lemma monotone.iterate {f : α → α} (hf : monotone f) (n : ℕ) : monotone (f^[n]) :=
nat.rec_on n monotone_id (λ n h, h.comp hf)

protected lemma monotone.comp_monotone_on (hg : monotone g) (hf : monotone_on f s) :
  monotone_on (g ∘ f) s :=
λ a ha b hb h, hg (hf ha hb h)

lemma monotone.comp_antitone_on (hg : monotone g) (hf : antitone_on f s) :
  antitone_on (g ∘ f) s :=
λ a ha b hb h, hg (hf ha hb h)

protected lemma antitone.comp_antitone_on (hg : antitone g) (hf : antitone_on f s) :
  monotone_on (g ∘ f) s :=
λ a ha b hb h, hg (hf ha hb h)

lemma antitone.comp_monotone_on (hg : antitone g) (hf : monotone_on f s) :
  antitone_on (g ∘ f) s :=
λ a ha b hb h, hg (hf ha hb h)

protected lemma strict_mono.comp (hg : strict_mono g) (hf : strict_mono f) :
  strict_mono (g ∘ f) :=
λ a b h, hg (hf h)

lemma strict_mono.comp_strict_anti (hg : strict_mono g) (hf : strict_anti f) :
  strict_anti (g ∘ f) :=
λ a b h, hg (hf h)

protected lemma strict_anti.comp (hg : strict_anti g) (hf : strict_anti f) :
  strict_mono (g ∘ f) :=
λ a b h, hg (hf h)

lemma strict_anti.comp_strict_mono (hg : strict_anti g) (hf : strict_mono f) :
  strict_anti (g ∘ f) :=
λ a b h, hg (hf h)

protected lemma strict_mono.iterate {f : α → α} (hf : strict_mono f) (n : ℕ) :
  strict_mono (f^[n]) :=
nat.rec_on n strict_mono_id (λ n h, h.comp hf)

protected lemma strict_mono.comp_strict_mono_on (hg : strict_mono g) (hf : strict_mono_on f s) :
  strict_mono_on (g ∘ f) s :=
λ a ha b hb h, hg (hf ha hb h)

lemma strict_mono.comp_strict_anti_on (hg : strict_mono g) (hf : strict_anti_on f s) :
  strict_anti_on (g ∘ f) s :=
λ a ha b hb h, hg (hf ha hb h)

protected lemma strict_anti.comp_strict_anti_on (hg : strict_anti g) (hf : strict_anti_on f s) :
  strict_mono_on (g ∘ f) s :=
λ a ha b hb h, hg (hf ha hb h)

lemma strict_anti.comp_strict_mono_on (hg : strict_anti g) (hf : strict_mono_on f s) :
  strict_anti_on (g ∘ f) s :=
λ a ha b hb h, hg (hf ha hb h)

end composition

/-! #### Monotonicity in linear orders  -/

section linear_order
variables [linear_order α]

section preorder
variables [preorder β] {f : α → β} {s : set α}

open ordering

lemma monotone.reflect_lt (hf : monotone f) {a b : α} (h : f a < f b) : a < b :=
lt_of_not_ge (λ h', h.not_le (hf h'))

lemma antitone.reflect_lt (hf : antitone f) {a b : α} (h : f a < f b) : b < a :=
lt_of_not_ge (λ h', h.not_le (hf h'))

lemma strict_mono_on.le_iff_le (hf : strict_mono_on f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) :
  f a ≤ f b ↔ a ≤ b :=
⟨λ h, le_of_not_gt $ λ h', (hf hb ha h').not_le h,
 λ h, h.lt_or_eq_dec.elim (λ h', (hf ha hb h').le) (λ h', h' ▸ le_refl _)⟩

lemma strict_anti_on.le_iff_le (hf : strict_anti_on f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) :
  f a ≤ f b ↔ b ≤ a :=
hf.dual_right.le_iff_le hb ha

lemma strict_mono_on.lt_iff_lt (hf : strict_mono_on f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) :
  f a < f b ↔ a < b :=
by rw [lt_iff_le_not_le, lt_iff_le_not_le, hf.le_iff_le ha hb, hf.le_iff_le hb ha]

lemma strict_anti_on.lt_iff_lt (hf : strict_anti_on f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) :
  f a < f b ↔ b < a :=
hf.dual_right.lt_iff_lt hb ha

lemma strict_mono.le_iff_le (hf : strict_mono f) {a b : α} :
  f a ≤ f b ↔ a ≤ b :=
(hf.strict_mono_on set.univ).le_iff_le trivial trivial

lemma strict_anti.le_iff_le (hf : strict_anti f) {a b : α} :
  f a ≤ f b ↔ b ≤ a :=
(hf.strict_anti_on set.univ).le_iff_le trivial trivial

lemma strict_mono.lt_iff_lt (hf : strict_mono f) {a b : α} :
  f a < f b ↔ a < b :=
(hf.strict_mono_on set.univ).lt_iff_lt trivial trivial

lemma strict_anti.lt_iff_lt (hf : strict_anti f) {a b : α} :
  f a < f b ↔ b < a :=
(hf.strict_anti_on set.univ).lt_iff_lt trivial trivial

protected theorem strict_mono_on.compares (hf : strict_mono_on f s) {a b : α} (ha : a ∈ s)
  (hb : b ∈ s) :
  ∀ {o : ordering}, o.compares (f a) (f b) ↔ o.compares a b
| ordering.lt := hf.lt_iff_lt ha hb
| ordering.eq := ⟨λ h, ((hf.le_iff_le ha hb).1 h.le).antisymm ((hf.le_iff_le hb ha).1 h.symm.le),
                   congr_arg _⟩
| ordering.gt := hf.lt_iff_lt hb ha

protected theorem strict_anti_on.compares (hf : strict_anti_on f s) {a b : α} (ha : a ∈ s)
  (hb : b ∈ s) {o : ordering} :
  o.compares (f a) (f b) ↔ o.compares b a :=
order_dual.dual_compares.trans $ hf.dual_right.compares hb ha

protected theorem strict_mono.compares (hf : strict_mono f) {a b : α} {o : ordering} :
  o.compares (f a) (f b) ↔ o.compares a b :=
(hf.strict_mono_on set.univ).compares trivial trivial

protected theorem strict_anti.compares (hf : strict_anti f) {a b : α} {o : ordering} :
  o.compares (f a) (f b) ↔ o.compares b a :=
(hf.strict_anti_on set.univ).compares trivial trivial

lemma strict_mono.injective (hf : strict_mono f) : injective f :=
λ x y h, show compares eq x y, from hf.compares.1 h

lemma strict_anti.injective (hf : strict_anti f) : injective f :=
λ x y h, show compares eq x y, from hf.compares.1 h.symm

lemma strict_mono.maximal_of_maximal_image (hf : strict_mono f) {a} (hmax : ∀ p, p ≤ f a) (x : α) :
  x ≤ a :=
hf.le_iff_le.mp (hmax (f x))

lemma strict_mono.minimal_of_minimal_image (hf : strict_mono f) {a} (hmin : ∀ p, f a ≤ p) (x : α) :
  a ≤ x :=
hf.le_iff_le.mp (hmin (f x))

lemma strict_anti.minimal_of_maximal_image (hf : strict_anti f) {a} (hmax : ∀ p, p ≤ f a) (x : α) :
  a ≤ x :=
hf.le_iff_le.mp (hmax (f x))

lemma strict_anti.maximal_of_minimal_image (hf : strict_anti f) {a} (hmin : ∀ p, f a ≤ p) (x : α) :
  x ≤ a :=
hf.le_iff_le.mp (hmin (f x))

end preorder

section partial_order
variables [partial_order β] {f : α → β}

lemma monotone.strict_mono_iff_injective (hf : monotone f) :
  strict_mono f ↔ injective f :=
⟨λ h, h.injective, hf.strict_mono_of_injective⟩

lemma antitone.strict_anti_iff_injective (hf : antitone f) :
  strict_anti f ↔ injective f :=
⟨λ h, h.injective, hf.strict_anti_of_injective⟩

end partial_order
end linear_order

/-! #### Monotonicity in `ℕ` and `ℤ` -/

section preorder
variables [preorder α]

lemma monotone_nat_of_le_succ {f : ℕ → α} (hf : ∀ n, f n ≤ f (n + 1)) :
  monotone f | n m h :=
begin
  induction h,
  { refl },
  { transitivity, assumption, exact hf _ }
end

lemma antitone_nat_of_succ_le {f : ℕ → α} (hf : ∀ n, f (n + 1) ≤ f n) :
  antitone f | n m h :=
begin
  induction h,
  { refl },
  { transitivity, exact hf _, assumption }
end

lemma strict_mono_nat_of_lt_succ [preorder β] {f : ℕ → β} (hf : ∀ n, f n < f (n + 1)) :
  strict_mono f :=
by { intros n m hnm, induction hnm with m' hnm' ih, apply hf, exact ih.trans (hf _) }

lemma strict_anti_nat_of_succ_lt [preorder β] {f : ℕ → β} (hf : ∀ n, f (n + 1) < f n) :
  strict_anti f :=
by { intros n m hnm, induction hnm with m' hnm' ih, apply hf, exact (hf _).trans ih }

lemma forall_ge_le_of_forall_le_succ (f : ℕ → α) {a : ℕ} (h : ∀ n, a ≤ n → f n.succ ≤ f n) {b c : ℕ}
  (hab : a ≤ b) (hbc : b ≤ c) :
  f c ≤ f b :=
begin
  induction hbc with k hbk hkb,
  { exact le_rfl },
  { exact (h _ $ hab.trans hbk).trans hkb }
end

-- TODO@Yael: Generalize the following four to succ orders
/-- If `f` is a monotone function from `ℕ` to a preorder such that `x` lies between `f n` and
  `f (n + 1)`, then `x` doesn't lie in the range of `f`. -/
lemma monotone.ne_of_lt_of_lt_nat {f : ℕ → α} (hf : monotone f) (n : ℕ) {x : α}
  (h1 : f n < x) (h2 : x < f (n + 1)) (a : ℕ) :
  f a ≠ x :=
by { rintro rfl, exact (hf.reflect_lt h1).not_le (nat.le_of_lt_succ $ hf.reflect_lt h2) }

/-- If `f` is an antitone function from `ℕ` to a preorder such that `x` lies between `f (n + 1)` and
`f n`, then `x` doesn't lie in the range of `f`. -/
lemma antitone.ne_of_lt_of_lt_nat {f : ℕ → α} (hf : antitone f)
  (n : ℕ) {x : α} (h1 : f (n + 1) < x) (h2 : x < f n) (a : ℕ) : f a ≠ x :=
by { rintro rfl, exact (hf.reflect_lt h2).not_le (nat.le_of_lt_succ $ hf.reflect_lt h1) }

/-- If `f` is a monotone function from `ℤ` to a preorder and `x` lies between `f n` and
  `f (n + 1)`, then `x` doesn't lie in the range of `f`. -/
lemma monotone.ne_of_lt_of_lt_int {f : ℤ → α} (hf : monotone f) (n : ℤ) {x : α}
  (h1 : f n < x) (h2 : x < f (n + 1)) (a : ℤ) :
  f a ≠ x :=
by { rintro rfl, exact (hf.reflect_lt h1).not_le (int.le_of_lt_add_one $ hf.reflect_lt h2) }

/-- If `f` is an antitone function from `ℤ` to a preorder and `x` lies between `f (n + 1)` and
`f n`, then `x` doesn't lie in the range of `f`. -/
lemma antitone.ne_of_lt_of_lt_int {f : ℤ → α} (hf : antitone f)
  (n : ℤ) {x : α} (h1 : f (n + 1) < x) (h2 : x < f n) (a : ℤ) : f a ≠ x :=
by { rintro rfl, exact (hf.reflect_lt h2).not_le (int.le_of_lt_add_one $ hf.reflect_lt h1) }

lemma strict_mono.id_le {φ : ℕ → ℕ} (h : strict_mono φ) : ∀ n, n ≤ φ n :=
λ n, nat.rec_on n (nat.zero_le _)
  (λ n hn, nat.succ_le_of_lt (hn.trans_lt $ h $ nat.lt_succ_self n))

end preorder

lemma subtype.mono_coe [preorder α] (t : set α) : monotone (coe : (subtype t) → α) :=
λ x y, id

lemma subtype.strict_mono_coe [preorder α] (t : set α) : strict_mono (coe : (subtype t) → α) :=
λ x y, id

lemma monotone_fst {α β : Type*} [preorder α] [preorder β] : monotone (@prod.fst α β) :=
λ x y h, h.1

lemma monotone_snd {α β : Type*} [preorder α] [preorder β] : monotone (@prod.snd α β) :=
λ x y h, h.2
