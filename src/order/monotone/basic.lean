/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Yaël Dillies
-/
import order.compare
import order.max
import order.rel_classes

/-!
# Monotonicity

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

* `monotone_nat_of_le_succ`, `monotone_int_of_le_succ`: If `f : ℕ → α` or `f : ℤ → α` and
  `f n ≤ f (n + 1)` for all `n`, then `f` is monotone.
* `antitone_nat_of_succ_le`, `antitone_int_of_succ_le`: If `f : ℕ → α` or `f : ℤ → α` and
  `f (n + 1) ≤ f n` for all `n`, then `f` is antitone.
* `strict_mono_nat_of_lt_succ`, `strict_mono_int_of_lt_succ`: If `f : ℕ → α` or `f : ℤ → α` and
  `f n < f (n + 1)` for all `n`, then `f` is strictly monotone.
* `strict_anti_nat_of_succ_lt`, `strict_anti_int_of_succ_lt`: If `f : ℕ → α` or `f : ℤ → α` and
  `f (n + 1) < f n` for all `n`, then `f` is strictly antitone.

## Implementation notes

Some of these definitions used to only require `has_le α` or `has_lt α`. The advantage of this is
unclear and it led to slight elaboration issues. Now, everything requires `preorder α` and seems to
work fine. Related Zulip discussion:
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Order.20diamond/near/254353352.

## TODO

The above theorems are also true in `ℕ+`, `fin n`... To make that work, we need `succ_order α`
and `succ_archimedean α`.

## Tags

monotone, strictly monotone, antitone, strictly antitone, increasing, strictly increasing,
decreasing, strictly decreasing
-/

open function order_dual

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type*} {r : α → α → Prop}

section monotone_def
variables [preorder α] [preorder β]

/-- A function `f` is monotone if `a ≤ b` implies `f a ≤ f b`. -/
def monotone (f : α → β) : Prop := ∀ ⦃a b⦄, a ≤ b → f a ≤ f b

/-- A function `f` is antitone if `a ≤ b` implies `f b ≤ f a`. -/
def antitone (f : α → β) : Prop := ∀ ⦃a b⦄, a ≤ b → f b ≤ f a

/-- A function `f` is monotone on `s` if, for all `a, b ∈ s`, `a ≤ b` implies `f a ≤ f b`. -/
def monotone_on (f : α → β) (s : set α) : Prop :=
∀ ⦃a⦄ (ha : a ∈ s) ⦃b⦄ (hb : b ∈ s), a ≤ b → f a ≤ f b

/-- A function `f` is antitone on `s` if, for all `a, b ∈ s`, `a ≤ b` implies `f b ≤ f a`. -/
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

/-! ### Monotonicity on the dual order

Strictly, many of the `*_on.dual` lemmas in this section should use `of_dual ⁻¹' s` instead of `s`,
but right now this is not possible as `set.preimage` is not defined yet, and importing it creates
an import cycle.

Often, you should not need the rewriting lemmas. Instead, you probably want to add `.dual`,
`.dual_left` or `.dual_right` to your `monotone`/`antitone` hypothesis.
-/

section order_dual

variables [preorder α] [preorder β] {f : α → β} {s : set α}

@[simp] lemma monotone_comp_of_dual_iff : monotone (f ∘ of_dual) ↔ antitone f := forall_swap
@[simp] lemma antitone_comp_of_dual_iff : antitone (f ∘ of_dual) ↔ monotone f := forall_swap
@[simp] lemma monotone_to_dual_comp_iff : monotone (to_dual ∘ f) ↔ antitone f := iff.rfl
@[simp] lemma antitone_to_dual_comp_iff : antitone (to_dual ∘ f) ↔ monotone f := iff.rfl

@[simp] lemma monotone_on_comp_of_dual_iff : monotone_on (f ∘ of_dual) s ↔ antitone_on f s :=
forall₂_swap
@[simp] lemma antitone_on_comp_of_dual_iff : antitone_on (f ∘ of_dual) s ↔ monotone_on f s :=
forall₂_swap
@[simp] lemma monotone_on_to_dual_comp_iff : monotone_on (to_dual ∘ f) s ↔ antitone_on f s :=
iff.rfl
@[simp] lemma antitone_on_to_dual_comp_iff : antitone_on (to_dual ∘ f) s ↔ monotone_on f s :=
iff.rfl

@[simp] lemma strict_mono_comp_of_dual_iff : strict_mono (f ∘ of_dual) ↔ strict_anti f :=
forall_swap
@[simp] lemma strict_anti_comp_of_dual_iff : strict_anti (f ∘ of_dual) ↔ strict_mono f :=
forall_swap
@[simp] lemma strict_mono_to_dual_comp_iff : strict_mono (to_dual ∘ f) ↔ strict_anti f := iff.rfl
@[simp] lemma strict_anti_to_dual_comp_iff : strict_anti (to_dual ∘ f) ↔ strict_mono f := iff.rfl

@[simp] lemma strict_mono_on_comp_of_dual_iff :
  strict_mono_on (f ∘ of_dual) s ↔ strict_anti_on f s := forall₂_swap
@[simp] lemma strict_anti_on_comp_of_dual_iff :
  strict_anti_on (f ∘ of_dual) s ↔ strict_mono_on f s := forall₂_swap
@[simp] lemma strict_mono_on_to_dual_comp_iff :
  strict_mono_on (to_dual ∘ f) s ↔ strict_anti_on f s := iff.rfl
@[simp] lemma strict_anti_on_to_dual_comp_iff :
  strict_anti_on (to_dual ∘ f) s ↔ strict_mono_on f s := iff.rfl

protected lemma monotone.dual (hf : monotone f) : monotone (to_dual ∘ f ∘ of_dual) := swap hf
protected lemma antitone.dual (hf : antitone f) : antitone (to_dual ∘ f ∘ of_dual) := swap hf
protected lemma monotone_on.dual (hf : monotone_on f s) : monotone_on (to_dual ∘ f ∘ of_dual) s :=
swap₂ hf
protected lemma antitone_on.dual (hf : antitone_on f s) : antitone_on (to_dual ∘ f ∘ of_dual) s :=
swap₂ hf
protected lemma strict_mono.dual (hf : strict_mono f) : strict_mono (to_dual ∘ f ∘ of_dual) :=
swap hf
protected lemma strict_anti.dual (hf : strict_anti f) : strict_anti (to_dual ∘ f ∘ of_dual) :=
swap hf
protected lemma strict_mono_on.dual (hf : strict_mono_on f s) :
  strict_mono_on (to_dual ∘ f ∘ of_dual) s := swap₂ hf
protected lemma strict_anti_on.dual (hf : strict_anti_on f s) :
  strict_anti_on (to_dual ∘ f ∘ of_dual) s := swap₂ hf

alias antitone_comp_of_dual_iff ↔ _ monotone.dual_left
alias monotone_comp_of_dual_iff ↔ _ antitone.dual_left
alias antitone_to_dual_comp_iff ↔ _ monotone.dual_right
alias monotone_to_dual_comp_iff ↔ _ antitone.dual_right
alias antitone_on_comp_of_dual_iff ↔ _ monotone_on.dual_left
alias monotone_on_comp_of_dual_iff ↔ _ antitone_on.dual_left
alias antitone_on_to_dual_comp_iff ↔ _ monotone_on.dual_right
alias monotone_on_to_dual_comp_iff ↔ _ antitone_on.dual_right
alias strict_anti_comp_of_dual_iff ↔ _ strict_mono.dual_left
alias strict_mono_comp_of_dual_iff ↔ _ strict_anti.dual_left
alias strict_anti_to_dual_comp_iff ↔ _ strict_mono.dual_right
alias strict_mono_to_dual_comp_iff ↔ _ strict_anti.dual_right
alias strict_anti_on_comp_of_dual_iff ↔ _ strict_mono_on.dual_left
alias strict_mono_on_comp_of_dual_iff ↔ _ strict_anti_on.dual_left
alias strict_anti_on_to_dual_comp_iff ↔ _ strict_mono_on.dual_right
alias strict_mono_on_to_dual_comp_iff ↔ _ strict_anti_on.dual_right

end order_dual

/-! ### Monotonicity in function spaces -/

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

/-! ### Monotonicity hierarchy -/

section preorder
variables [preorder α]

section preorder
variables [preorder β] {f : α → β} {s : set α} {a b : α}

/-!
These four lemmas are there to strip off the semi-implicit arguments `⦃a b : α⦄`. This is useful
when you do not want to apply a `monotone` assumption (i.e. your goal is `a ≤ b → f a ≤ f b`).
However if you find yourself writing `hf.imp h`, then you should have written `hf h` instead.
-/

lemma monotone.imp (hf : monotone f) (h : a ≤ b) : f a ≤ f b := hf h
lemma antitone.imp (hf : antitone f) (h : a ≤ b) : f b ≤ f a := hf h
lemma strict_mono.imp (hf : strict_mono f) (h : a < b) : f a < f b := hf h
lemma strict_anti.imp (hf : strict_anti f) (h : a < b) : f b < f a := hf h

protected lemma monotone.monotone_on (hf : monotone f) (s : set α) : monotone_on f s :=
λ a _ b _, hf.imp

protected lemma antitone.antitone_on (hf : antitone f) (s : set α) : antitone_on f s :=
λ a _ b _, hf.imp

@[simp] lemma monotone_on_univ : monotone_on f set.univ ↔ monotone f :=
⟨λ h a b, h trivial trivial, λ h, h.monotone_on _⟩

@[simp] lemma antitone_on_univ : antitone_on f set.univ ↔ antitone f :=
⟨λ h a b, h trivial trivial, λ h, h.antitone_on _⟩

protected lemma strict_mono.strict_mono_on (hf : strict_mono f) (s : set α) : strict_mono_on f s :=
λ a _ b _, hf.imp

protected lemma strict_anti.strict_anti_on (hf : strict_anti f) (s : set α) : strict_anti_on f s :=
λ a _ b _, hf.imp

@[simp] lemma strict_mono_on_univ : strict_mono_on f set.univ ↔ strict_mono f :=
⟨λ h a b, h trivial trivial, λ h, h.strict_mono_on _⟩

@[simp] lemma strict_anti_on_univ : strict_anti_on f set.univ ↔ strict_anti f :=
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
variables [partial_order α] [preorder β] {f : α → β} {s : set α}

lemma monotone_iff_forall_lt : monotone f ↔ ∀ ⦃a b⦄, a < b → f a ≤ f b :=
forall₂_congr $ λ a b, ⟨λ hf h, hf h.le, λ hf h, h.eq_or_lt.elim (λ H, (congr_arg _ H).le) hf⟩

lemma antitone_iff_forall_lt : antitone f ↔ ∀ ⦃a b⦄, a < b → f b ≤ f a :=
forall₂_congr $ λ a b, ⟨λ hf h, hf h.le, λ hf h, h.eq_or_lt.elim (λ H, (congr_arg _ H).ge) hf⟩

lemma monotone_on_iff_forall_lt :
  monotone_on f s ↔ ∀ ⦃a⦄ (ha : a ∈ s) ⦃b⦄ (hb : b ∈ s), a < b → f a ≤ f b :=
⟨λ hf a ha b hb h, hf ha hb h.le,
  λ hf a ha b hb h, h.eq_or_lt.elim (λ H, (congr_arg _ H).le) (hf ha hb)⟩

lemma antitone_on_iff_forall_lt :
  antitone_on f s ↔ ∀ ⦃a⦄ (ha : a ∈ s) ⦃b⦄ (hb : b ∈ s), a < b → f b ≤ f a :=
⟨λ hf a ha b hb h, hf ha hb h.le,
  λ hf a ha b hb h, h.eq_or_lt.elim (λ H, (congr_arg _ H).ge) (hf ha hb)⟩

-- `preorder α` isn't strong enough: if the preorder on `α` is an equivalence relation,
-- then `strict_mono f` is vacuously true.
protected lemma strict_mono_on.monotone_on (hf : strict_mono_on f s) : monotone_on f s :=
monotone_on_iff_forall_lt.2 $ λ a ha b hb h, (hf ha hb h).le

protected lemma strict_anti_on.antitone_on (hf : strict_anti_on f s) : antitone_on f s :=
antitone_on_iff_forall_lt.2 $ λ a ha b hb h, (hf ha hb h).le

protected lemma strict_mono.monotone (hf : strict_mono f) : monotone f :=
monotone_iff_forall_lt.2 $ λ a b h, (hf h).le

protected lemma strict_anti.antitone (hf : strict_anti f) : antitone f :=
antitone_iff_forall_lt.2 $ λ a b h, (hf h).le

end partial_order

/-! ### Monotonicity from and to subsingletons -/

namespace subsingleton
variables [preorder α] [preorder β]

protected lemma monotone [subsingleton α] (f : α → β) : monotone f :=
λ a b _, (congr_arg _ $ subsingleton.elim _ _).le

protected lemma antitone [subsingleton α] (f : α → β) : antitone f :=
λ a b _, (congr_arg _ $ subsingleton.elim _ _).le

lemma monotone' [subsingleton β] (f : α → β) : monotone f := λ a b _, (subsingleton.elim _ _).le
lemma antitone' [subsingleton β] (f : α → β) : antitone f := λ a b _, (subsingleton.elim _ _).le

protected lemma strict_mono [subsingleton α] (f : α → β) : strict_mono f :=
λ a b h, (h.ne $ subsingleton.elim _ _).elim

protected lemma strict_anti [subsingleton α] (f : α → β) : strict_anti f :=
λ a b h, (h.ne $ subsingleton.elim _ _).elim

end subsingleton

/-! ### Miscellaneous monotonicity results -/

lemma monotone_id [preorder α] : monotone (id : α → α) := λ a b, id

lemma monotone_on_id [preorder α] {s : set α} : monotone_on id s := λ a ha b hb, id

lemma strict_mono_id [preorder α] : strict_mono (id : α → α) := λ a b, id

lemma strict_mono_on_id [preorder α] {s : set α} : strict_mono_on id s := λ a ha b hb, id

theorem monotone_const [preorder α] [preorder β] {c : β} : monotone (λ (a : α), c) :=
λ a b _, le_rfl

theorem monotone_on_const [preorder α] [preorder β] {c : β} {s : set α} :
  monotone_on (λ (a : α), c) s :=
λ a _ b _ _, le_rfl

theorem antitone_const [preorder α] [preorder β] {c : β} : antitone (λ (a : α), c) :=
λ a b _, le_refl c

theorem antitone_on_const [preorder α] [preorder β] {c : β} {s : set α} :
  antitone_on (λ (a : α), c) s :=
λ a _ b _ _, le_rfl

lemma strict_mono_of_le_iff_le [preorder α] [preorder β] {f : α → β}
  (h : ∀ x y, x ≤ y ↔ f x ≤ f y) : strict_mono f :=
λ a b, (lt_iff_lt_of_le_iff_le' (h _ _) (h _ _)).1

lemma strict_anti_of_le_iff_le [preorder α] [preorder β] {f : α → β}
  (h : ∀ x y, x ≤ y ↔ f y ≤ f x) : strict_anti f :=
λ a b, (lt_iff_lt_of_le_iff_le' (h _ _) (h _ _)).1

lemma injective_of_lt_imp_ne [linear_order α] {f : α → β} (h : ∀ x y, x < y → f x ≠ f y) :
  injective f :=
begin
  intros x y hxy,
  contrapose hxy,
  cases ne.lt_or_lt hxy with hxy hxy,
  exacts [h _ _ hxy, (h _ _ hxy).symm]
end

lemma injective_of_le_imp_le [partial_order α] [preorder β] (f : α → β)
  (h : ∀ {x y}, f x ≤ f y → x ≤ y) : injective f :=
λ x y hxy, (h hxy.le).antisymm (h hxy.ge)

section preorder
variables [preorder α] [preorder β] {f g : α → β} {a : α}

lemma strict_mono.is_max_of_apply (hf : strict_mono f) (ha : is_max (f a)) : is_max a :=
of_not_not $ λ h, let ⟨b, hb⟩ := not_is_max_iff.1 h in (hf hb).not_is_max ha

lemma strict_mono.is_min_of_apply (hf : strict_mono f) (ha : is_min (f a)) : is_min a :=
of_not_not $ λ h, let ⟨b, hb⟩ := not_is_min_iff.1 h in (hf hb).not_is_min ha

lemma strict_anti.is_max_of_apply (hf : strict_anti f) (ha : is_min (f a)) : is_max a :=
of_not_not $ λ h, let ⟨b, hb⟩ := not_is_max_iff.1 h in (hf hb).not_is_min ha

lemma strict_anti.is_min_of_apply (hf : strict_anti f) (ha : is_max (f a)) : is_min a :=
of_not_not $ λ h, let ⟨b, hb⟩ := not_is_min_iff.1 h in (hf hb).not_is_max ha

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

/-! ### Monotonicity under composition -/

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

namespace list

section fold

theorem foldl_monotone [preorder α] {f : α → β → α} (H : ∀ b, monotone (λ a, f a b)) (l : list β) :
  monotone (λ a, l.foldl f a) :=
list.rec_on l (λ _ _, id) (λ i l hl _ _ h, hl (H _ h))

theorem foldr_monotone [preorder β] {f : α → β → β} (H : ∀ a, monotone (f a)) (l : list α) :
  monotone (λ b, l.foldr f b) :=
λ _ _ h, list.rec_on l h (λ i l hl, H i hl)

theorem foldl_strict_mono [preorder α] {f : α → β → α} (H : ∀ b, strict_mono (λ a, f a b))
  (l : list β) : strict_mono (λ a, l.foldl f a) :=
list.rec_on l (λ _ _, id) (λ i l hl _ _ h, hl (H _ h))

theorem foldr_strict_mono [preorder β] {f : α → β → β} (H : ∀ a, strict_mono (f a)) (l : list α) :
  strict_mono (λ b, l.foldr f b) :=
λ _ _ h, list.rec_on l h (λ i l hl, H i hl)

end fold

end list

/-! ### Monotonicity in linear orders  -/

section linear_order
variables [linear_order α]

section preorder
variables [preorder β] {f : α → β} {s : set α}

open ordering

lemma monotone.reflect_lt (hf : monotone f) {a b : α} (h : f a < f b) : a < b :=
lt_of_not_ge (λ h', h.not_le (hf h'))

lemma antitone.reflect_lt (hf : antitone f) {a b : α} (h : f a < f b) : b < a :=
lt_of_not_ge (λ h', h.not_le (hf h'))

lemma monotone_on.reflect_lt (hf : monotone_on f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s)
  (h : f a < f b) :
  a < b :=
lt_of_not_ge $ λ h', h.not_le $ hf hb ha h'

lemma antitone_on.reflect_lt (hf : antitone_on f s) {a b : α}  (ha : a ∈ s) (hb : b ∈ s)
  (h : f a < f b) :
  b < a :=
lt_of_not_ge $ λ h', h.not_le $ hf ha hb h'

lemma strict_mono_on.le_iff_le (hf : strict_mono_on f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) :
  f a ≤ f b ↔ a ≤ b :=
⟨λ h, le_of_not_gt $ λ h', (hf hb ha h').not_le h,
 λ h, h.lt_or_eq_dec.elim (λ h', (hf ha hb h').le) (λ h', h' ▸ le_rfl)⟩

lemma strict_anti_on.le_iff_le (hf : strict_anti_on f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) :
  f a ≤ f b ↔ b ≤ a :=
hf.dual_right.le_iff_le hb ha

lemma strict_mono_on.eq_iff_eq (hf : strict_mono_on f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) :
  f a = f b ↔ a = b :=
⟨λ h, le_antisymm ((hf.le_iff_le ha hb).mp h.le) ((hf.le_iff_le hb ha).mp h.ge),
 by { rintro rfl, refl, }⟩

lemma strict_anti_on.eq_iff_eq (hf : strict_anti_on f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) :
  f a = f b ↔ b = a :=
(hf.dual_right.eq_iff_eq ha hb).trans eq_comm

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
to_dual_compares_to_dual.trans $ hf.dual_right.compares hb ha

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

variables [linear_order β] {f : α → β} {s : set α} {x y : α}

/-- A function between linear orders which is neither monotone nor antitone makes a dent upright or
downright. -/
lemma not_monotone_not_antitone_iff_exists_le_le :
  ¬ monotone f ∧ ¬ antitone f ↔ ∃ a b c, a ≤ b ∧ b ≤ c ∧
    (f a < f b ∧ f c < f b ∨ f b < f a ∧ f b < f c) :=
begin
  simp_rw [monotone, antitone, not_forall, not_le],
  refine iff.symm ⟨_, _⟩,
  { rintro ⟨a, b, c, hab, hbc, ⟨hfab, hfcb⟩ | ⟨hfba, hfbc⟩⟩,
    exacts [⟨⟨_, _, hbc, hfcb⟩, _, _, hab, hfab⟩, ⟨⟨_, _, hab, hfba⟩, _, _, hbc, hfbc⟩] },
  rintro ⟨⟨a, b, hab, hfba⟩, c, d, hcd, hfcd⟩,
  obtain hda | had := le_total d a,
  { obtain hfad | hfda := le_total (f a) (f d),
    { exact ⟨c, d, b, hcd, hda.trans hab, or.inl ⟨hfcd, hfba.trans_le hfad⟩⟩ },
    { exact ⟨c, a, b, hcd.trans hda, hab, or.inl ⟨hfcd.trans_le hfda, hfba⟩⟩ } },
  obtain hac | hca := le_total a c,
  { obtain hfdb | hfbd := le_or_lt (f d) (f b),
    { exact ⟨a, c, d, hac, hcd, or.inr ⟨hfcd.trans $ hfdb.trans_lt hfba, hfcd⟩⟩ },
    obtain hfca | hfac := lt_or_le (f c) (f a),
    { exact ⟨a, c, d, hac, hcd, or.inr ⟨hfca, hfcd⟩⟩ },
    obtain hbd | hdb := le_total b d,
    { exact ⟨a, b, d, hab, hbd, or.inr ⟨hfba, hfbd⟩⟩ },
    { exact ⟨a, d, b, had, hdb, or.inl ⟨hfac.trans_lt hfcd, hfbd⟩⟩ } },
  { obtain hfdb | hfbd := le_or_lt (f d) (f b),
    { exact ⟨c, a, b, hca, hab, or.inl ⟨hfcd.trans $ hfdb.trans_lt hfba, hfba⟩⟩ },
    obtain hfca | hfac := lt_or_le (f c) (f a),
    { exact ⟨c, a, b, hca, hab, or.inl ⟨hfca, hfba⟩⟩ },
    obtain hbd | hdb := le_total b d,
    { exact ⟨a, b, d, hab, hbd, or.inr ⟨hfba, hfbd⟩⟩ },
    { exact ⟨a, d, b, had, hdb, or.inl ⟨hfac.trans_lt hfcd, hfbd⟩⟩ } }
end

/-- A function between linear orders which is neither monotone nor antitone makes a dent upright or
downright. -/
lemma not_monotone_not_antitone_iff_exists_lt_lt :
  ¬ monotone f ∧ ¬ antitone f ↔ ∃ a b c, a < b ∧ b < c ∧
    (f a < f b ∧ f c < f b ∨ f b < f a ∧ f b < f c) :=
begin
  simp_rw [not_monotone_not_antitone_iff_exists_le_le, ←and_assoc],
  refine exists₃_congr (λ a b c, and_congr_left $ λ h, (ne.le_iff_lt _).and $ ne.le_iff_lt _);
    rintro rfl; simpa using h,
end

/-!
### Strictly monotone functions and `cmp`
-/

lemma strict_mono_on.cmp_map_eq (hf : strict_mono_on f s) (hx : x ∈ s) (hy : y ∈ s) :
  cmp (f x) (f y) = cmp x y :=
((hf.compares hx hy).2 (cmp_compares x y)).cmp_eq

lemma strict_mono.cmp_map_eq (hf : strict_mono f) (x y : α) : cmp (f x) (f y) = cmp x y :=
(hf.strict_mono_on set.univ).cmp_map_eq trivial trivial

lemma strict_anti_on.cmp_map_eq (hf : strict_anti_on f s) (hx : x ∈ s) (hy : y ∈ s) :
  cmp (f x) (f y) = cmp y x :=
hf.dual_right.cmp_map_eq hy hx

lemma strict_anti.cmp_map_eq (hf : strict_anti f) (x y : α) : cmp (f x) (f y) = cmp y x :=
(hf.strict_anti_on set.univ).cmp_map_eq trivial trivial

end linear_order

/-! ### Monotonicity in `ℕ` and `ℤ` -/

section preorder
variables [preorder α]

lemma nat.rel_of_forall_rel_succ_of_le_of_lt (r : β → β → Prop) [is_trans β r]
  {f : ℕ → β} {a : ℕ} (h : ∀ n, a ≤ n → r (f n) (f (n + 1))) ⦃b c : ℕ⦄
  (hab : a ≤ b) (hbc : b < c) :
  r (f b) (f c) :=
begin
  induction hbc with k b_lt_k r_b_k,
  exacts [h _ hab, trans r_b_k (h _ (hab.trans_lt b_lt_k).le)]
end

lemma nat.rel_of_forall_rel_succ_of_le_of_le (r : β → β → Prop) [is_refl β r] [is_trans β r]
  {f : ℕ → β} {a : ℕ} (h : ∀ n, a ≤ n → r (f n) (f (n + 1))) ⦃b c : ℕ⦄
  (hab : a ≤ b) (hbc : b ≤ c) :
  r (f b) (f c) :=
hbc.eq_or_lt.elim (λ h, h ▸ refl _) (nat.rel_of_forall_rel_succ_of_le_of_lt r h hab)

lemma nat.rel_of_forall_rel_succ_of_lt (r : β → β → Prop) [is_trans β r]
  {f : ℕ → β} (h : ∀ n, r (f n) (f (n + 1))) ⦃a b : ℕ⦄ (hab : a < b) : r (f a) (f b) :=
nat.rel_of_forall_rel_succ_of_le_of_lt r (λ n _, h n) le_rfl hab

lemma nat.rel_of_forall_rel_succ_of_le (r : β → β → Prop) [is_refl β r] [is_trans β r]
  {f : ℕ → β} (h : ∀ n, r (f n) (f (n + 1))) ⦃a b : ℕ⦄ (hab : a ≤ b) : r (f a) (f b) :=
nat.rel_of_forall_rel_succ_of_le_of_le r (λ n _, h n) le_rfl hab

lemma monotone_nat_of_le_succ {f : ℕ → α} (hf : ∀ n, f n ≤ f (n + 1)) :
  monotone f :=
nat.rel_of_forall_rel_succ_of_le (≤) hf

lemma antitone_nat_of_succ_le {f : ℕ → α} (hf : ∀ n, f (n + 1) ≤ f n) : antitone f :=
@monotone_nat_of_le_succ αᵒᵈ _ _ hf

lemma strict_mono_nat_of_lt_succ {f : ℕ → α} (hf : ∀ n, f n < f (n + 1)) : strict_mono f :=
nat.rel_of_forall_rel_succ_of_lt (<) hf

lemma strict_anti_nat_of_succ_lt {f : ℕ → α} (hf : ∀ n, f (n + 1) < f n) : strict_anti f :=
@strict_mono_nat_of_lt_succ αᵒᵈ _ f hf

namespace nat

/-- If `α` is a preorder with no maximal elements, then there exists a strictly monotone function
`ℕ → α` with any prescribed value of `f 0`. -/
lemma exists_strict_mono' [no_max_order α] (a : α) : ∃ f : ℕ → α, strict_mono f ∧ f 0 = a :=
begin
  have := (λ x : α, exists_gt x),
  choose g hg,
  exact ⟨λ n, nat.rec_on n a (λ _, g), strict_mono_nat_of_lt_succ $ λ n, hg _, rfl⟩
end

/-- If `α` is a preorder with no maximal elements, then there exists a strictly antitone function
`ℕ → α` with any prescribed value of `f 0`. -/
lemma exists_strict_anti' [no_min_order α] (a : α) : ∃ f : ℕ → α, strict_anti f ∧ f 0 = a :=
exists_strict_mono' (order_dual.to_dual a)

variable (α)

/-- If `α` is a nonempty preorder with no maximal elements, then there exists a strictly monotone
function `ℕ → α`. -/
lemma exists_strict_mono [nonempty α] [no_max_order α] : ∃ f : ℕ → α, strict_mono f :=
let ⟨a⟩ := ‹nonempty α›, ⟨f, hf, hfa⟩ := exists_strict_mono' a in ⟨f, hf⟩

/-- If `α` is a nonempty preorder with no minimal elements, then there exists a strictly antitone
function `ℕ → α`. -/
lemma exists_strict_anti [nonempty α] [no_min_order α] : ∃ f : ℕ → α, strict_anti f :=
exists_strict_mono αᵒᵈ

end nat

lemma int.rel_of_forall_rel_succ_of_lt (r : β → β → Prop) [is_trans β r]
  {f : ℤ → β} (h : ∀ n, r (f n) (f (n + 1))) ⦃a b : ℤ⦄ (hab : a < b) : r (f a) (f b) :=
begin
  rcases hab.dest with ⟨n, rfl⟩, clear hab,
  induction n with n ihn,
  { rw int.coe_nat_one, apply h },
  { rw [int.coe_nat_succ, ← int.add_assoc],
    exact trans ihn (h _) }
end

lemma int.rel_of_forall_rel_succ_of_le (r : β → β → Prop) [is_refl β r] [is_trans β r]
  {f : ℤ → β} (h : ∀ n, r (f n) (f (n + 1))) ⦃a b : ℤ⦄ (hab : a ≤ b) : r (f a) (f b) :=
hab.eq_or_lt.elim (λ h, h ▸ refl _) (λ h', int.rel_of_forall_rel_succ_of_lt r h h')

lemma monotone_int_of_le_succ {f : ℤ → α} (hf : ∀ n, f n ≤ f (n + 1)) : monotone f :=
int.rel_of_forall_rel_succ_of_le (≤) hf

lemma antitone_int_of_succ_le {f : ℤ → α} (hf : ∀ n, f (n + 1) ≤ f n) : antitone f :=
int.rel_of_forall_rel_succ_of_le (≥) hf

lemma strict_mono_int_of_lt_succ {f : ℤ → α} (hf : ∀ n, f n < f (n + 1)) : strict_mono f :=
int.rel_of_forall_rel_succ_of_lt (<) hf

lemma strict_anti_int_of_succ_lt {f : ℤ → α} (hf : ∀ n, f (n + 1) < f n) : strict_anti f :=
int.rel_of_forall_rel_succ_of_lt (>) hf

namespace int

variables (α) [nonempty α] [no_min_order α] [no_max_order α]

/-- If `α` is a nonempty preorder with no minimal or maximal elements, then there exists a strictly
monotone function `f : ℤ → α`. -/
lemma exists_strict_mono : ∃ f : ℤ → α, strict_mono f :=
begin
  inhabit α,
  rcases nat.exists_strict_mono' (default : α) with ⟨f, hf, hf₀⟩,
  rcases nat.exists_strict_anti' (default : α) with ⟨g, hg, hg₀⟩,
  refine ⟨λ n, int.cases_on n f (λ n, g (n + 1)), strict_mono_int_of_lt_succ _⟩,
  rintro (n|_|n),
  { exact hf n.lt_succ_self },
  { show g 1 < f 0,
    rw [hf₀, ← hg₀],
    exact hg nat.zero_lt_one },
  { exact hg (nat.lt_succ_self _) }
end

/-- If `α` is a nonempty preorder with no minimal or maximal elements, then there exists a strictly
antitone function `f : ℤ → α`. -/
lemma exists_strict_anti : ∃ f : ℤ → α, strict_anti f := exists_strict_mono αᵒᵈ

end int

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


section preorder
variables [preorder α] [preorder β] [preorder γ] [preorder δ] {f : α → γ} {g : β → δ} {a b : α}

lemma monotone_fst : monotone (@prod.fst α β) := λ a b, and.left
lemma monotone_snd : monotone (@prod.snd α β) := λ a b, and.right

lemma monotone.prod_map (hf : monotone f) (hg : monotone g) : monotone (prod.map f g) :=
λ a b h, ⟨hf h.1, hg h.2⟩

lemma antitone.prod_map (hf : antitone f) (hg : antitone g) : antitone (prod.map f g) :=
λ a b h, ⟨hf h.1, hg h.2⟩

end preorder

section partial_order
variables [partial_order α] [partial_order β] [preorder γ] [preorder δ]
  {f : α → γ} {g : β → δ}

lemma strict_mono.prod_map (hf : strict_mono f) (hg : strict_mono g) : strict_mono (prod.map f g) :=
λ a b, by { simp_rw prod.lt_iff,
  exact or.imp (and.imp hf.imp hg.monotone.imp) (and.imp hf.monotone.imp hg.imp) }

lemma strict_anti.prod_map (hf : strict_anti f) (hg : strict_anti g) : strict_anti (prod.map f g) :=
λ a b, by { simp_rw prod.lt_iff,
  exact or.imp (and.imp hf.imp hg.antitone.imp) (and.imp hf.antitone.imp hg.imp) }

end partial_order

namespace function
variables [preorder α]

lemma const_mono : monotone (const β : α → β → α) := λ a b h i, h
lemma const_strict_mono [nonempty β] : strict_mono (const β : α → β → α) := λ a b, const_lt_const.2

end function
