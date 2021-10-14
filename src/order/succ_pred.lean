/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.bounded_lattice
import order.galois_connection
import order.iterate
import tactic.monotonicity

/-!
# Successor and predecessor

This file defines successor and predecessor orders. `succ a`, the successor of an element `a : α` is
the least element greater than `a`. `pred a` is the greatest element less than `a`. Typical examples
include `ℕ`, `ℤ`, `ℕ+`, `fin n`, but also `enat`, the lexicographic order of a successor/predecessor
order...

## Typeclasses

* `succ_order`: Order equipped with a sensible successor function.
* `pred_order`: Order equipped with a sensible predecessor function.
* `is_succ_archimedean`: `succ_order` where `succ` iterated to an element gives all the greater
  ones.
* `is_pred_archimedean`: `pred_order` where `pred` iterated to an element gives all the greater
  ones.

## Implementation notes

Maximal elements don't have a sensible successor. Thus the naïve typeclass
```lean
class naive_succ_order (α : Type*) [preorder α] :=
(succ : α → α)
(succ_le_iff : ∀ {a b}, succ a ≤ b ↔ a < b)
(lt_succ_iff : ∀ {a b}, a < succ b ↔ a ≤ b)
```
can't apply to an `order_top` because plugging in `a = b = ⊤` into either of `succ_le_iff` and
`lt_succ_iff` yields `⊤ < ⊤` (or more generally `m < m` for a maximal element `m`).
The solution taken here is to remove the implications `≤ → <` and instead require that `a < succ a`
for all non maximal elements (enforced by the combination of `le_succ` and the contrapositive of
`maximal_of_succ_le`).
The stricter condition of every element having a sensible successor can be obtained through the
combination of `succ_order α` and `no_top_order α`.

## TODO

Is `galois_connection pred succ` always true? If not, we should introduce
```lean
class succ_pred_order (α : Type*) [preorder α] extends succ_order α, pred_order α :=
(pred_succ_gc : galois_connection (pred : α → α) succ)
```
This gives `succ (pred n) = n` and `pred (succ n)` for free when `no_bot_order α` and
`no_top_order α` respectively.
-/

open function

/-! ### Successor order -/

variables {α : Type*}

/-- Order equipped with a sensible successor function. -/
@[ext] class succ_order (α : Type*) [preorder α] :=
(succ : α → α)
(le_succ : ∀ a, a ≤ succ a)
(maximal_of_succ_le : ∀ ⦃a⦄, succ a ≤ a → ∀ ⦃b⦄, ¬a < b)
(succ_le_of_lt : ∀ {a b}, a < b → succ a ≤ b)
(le_of_lt_succ : ∀ {a b}, a < succ b → a ≤ b)

namespace succ_order
section preorder
variables [preorder α]

/-- A constructor for `succ_order α` usable when `α` has no maximal element. -/
def succ_order_of_succ_le_iff_of_le_lt_succ (succ : α → α)
  (hsucc_le_iff : ∀ {a b}, succ a ≤ b ↔ a < b)
  (hle_of_lt_succ : ∀ {a b}, a < succ b → a ≤ b) :
  succ_order α :=
{ succ := succ,
  le_succ := λ a, (hsucc_le_iff.1 le_rfl).le,
  maximal_of_succ_le := λ a ha, (lt_irrefl a (hsucc_le_iff.1 ha)).elim,
  succ_le_of_lt := λ a b, hsucc_le_iff.2,
  le_of_lt_succ := λ a b, hle_of_lt_succ }

variables [succ_order α]

@[simp, mono] lemma succ_le_succ {a b : α} (h : a ≤ b) : succ a ≤ succ b :=
begin
  by_cases ha : ∀ ⦃c⦄, ¬a < c,
  { have hba : succ b ≤ a,
    { by_contra H,
      exact ha ((h.trans (le_succ b)).lt_of_not_le H) },
    by_contra H,
    exact ha ((h.trans (le_succ b)).trans_lt ((hba.trans (le_succ a)).lt_of_not_le H)) },
  { push_neg at ha,
    obtain ⟨c, hc⟩ := ha,
    exact succ_le_of_lt ((h.trans (le_succ b)).lt_of_not_le $ λ hba,
      maximal_of_succ_le (hba.trans h) (((le_succ b).trans hba).trans_lt hc)) }
end

lemma succ_mono : monotone (succ : α → α) := λ a b, succ_le_succ

lemma lt_succ_of_not_maximal {a b : α} (h : a < b) : a < succ a :=
(le_succ a).lt_of_not_le (λ ha, maximal_of_succ_le ha h)

section no_top_order
variables [no_top_order α] {a b : α}

lemma lt_succ (a : α) : a < succ a :=
(le_succ a).lt_of_not_le (λ h, not_exists.2 (maximal_of_succ_le h) (no_top a))

lemma lt_succ_iff : a < succ b ↔ a ≤ b :=
⟨le_of_lt_succ, λ h, h.trans_lt $ lt_succ b⟩

lemma succ_le_iff : succ a ≤ b ↔ a < b :=
⟨(lt_succ a).trans_le, succ_le_of_lt⟩

@[simp] lemma succ_le_succ_iff : succ a ≤ succ b ↔ a ≤ b :=
⟨λ h, le_of_lt_succ $ (lt_succ a).trans_le h, λ h, succ_le_of_lt $ h.trans_lt $ lt_succ b⟩

alias succ_le_succ_iff ↔ le_of_succ_le_succ _

@[simp] lemma succ_lt_succ_iff : succ a < succ b ↔ a < b :=
by simp_rw [lt_iff_le_not_le, succ_le_succ_iff]

alias succ_lt_succ_iff ↔ lt_of_succ_lt_succ succ_lt_succ

lemma succ_strict_mono : strict_mono (succ : α → α) := λ a b, succ_lt_succ

end no_top_order

end preorder

section partial_order
variables [partial_order α]

/-- There is at most one way to define the successors in a `partial_order`. -/
instance : subsingleton (succ_order α) :=
begin
  refine subsingleton.intro (λ h₀ h₁, _),
  ext a,
  by_cases ha : @succ _ _ h₀ a ≤ a,
  { refine (ha.trans (@le_succ _ _ h₁ a)).antisymm _,
    by_contra H,
    exact @maximal_of_succ_le _ _ h₀ _ ha _
      ((@le_succ _ _ h₁ a).lt_of_not_le $ λ h, H $ h.trans $ @le_succ _ _ h₀ a) },
  { exact (@succ_le_of_lt _ _ h₀ _ _ $ (@le_succ _ _ h₁ a).lt_of_not_le $ λ h,
      @maximal_of_succ_le _ _ h₁ _ h _ $ (@le_succ _ _ h₀ a).lt_of_not_le ha).antisymm
      (@succ_le_of_lt _ _ h₁ _ _ $ (@le_succ _ _ h₀ a).lt_of_not_le ha) }
end

variables [succ_order α]

lemma le_le_succ_iff {a b : α} : a ≤ b ∧ b ≤ succ a ↔ b = a ∨ b = succ a :=
begin
  split,
  { rintro h,
    rw or_iff_not_imp_left,
    exact λ hba : b ≠ a, h.2.antisymm (succ_le_of_lt $ h.1.lt_of_ne $ hba.symm) },
  rintro (rfl | rfl),
  { exact ⟨le_rfl, le_succ b⟩ },
  { exact ⟨le_succ a, le_rfl⟩ }
end

section no_top_order
variables [no_top_order α] {a b : α}

lemma succ_injective : injective (succ : α → α) :=
begin
  rintro a b,
  simp_rw [eq_iff_le_not_lt, succ_le_succ_iff, succ_lt_succ_iff],
  exact id,
end

lemma succ_eq_succ_iff : succ a = succ b ↔ a = b :=
succ_injective.eq_iff

lemma succ_ne_succ_iff : succ a ≠ succ b ↔ a ≠ b :=
succ_injective.ne_iff

alias succ_ne_succ_iff ↔ ne_of_succ_ne_succ succ_ne_succ

lemma lt_succ_iff_lt_or_eq : a < succ b ↔ (a < b ∨ a = b) :=
lt_succ_iff.trans le_iff_lt_or_eq

lemma le_succ_iff_lt_or_eq : a ≤ succ b ↔ (a ≤ b ∨ a = succ b) :=
by rw [←lt_succ_iff, ←lt_succ_iff, lt_succ_iff_lt_or_eq]

end no_top_order

end partial_order

section order_top
variables [order_top α] [succ_order α]

@[simp] lemma succ_top : succ (⊤ : α) = ⊤ :=
le_top.antisymm (le_succ _)

@[simp] lemma succ_le_iff_eq_top {a : α} : succ a ≤ a ↔ a = ⊤ :=
⟨λ h, eq_top_of_maximal (maximal_of_succ_le h), λ h, by rw [h, succ_top]⟩

@[simp] lemma lt_succ_iff_ne_top {a : α} : a < succ a ↔ a ≠ ⊤ :=
begin
  simp only [lt_iff_le_not_le, true_and, le_succ a],
  exact not_iff_not.2 succ_le_iff_eq_top,
end

end order_top

section order_bot
variables [order_bot α] [succ_order α] [nontrivial α]

lemma bot_lt_succ (a : α) : ⊥ < succ a :=
begin
  obtain ⟨b, hb⟩ := exists_ne (⊥ : α),
  refine bot_lt_iff_ne_bot.2 (λ h, _),
  have := eq_bot_iff.2 ((le_succ a).trans h.le),
  rw this at h,
  exact maximal_of_succ_le h.le (bot_lt_iff_ne_bot.2 hb),
end

lemma succ_ne_bot (a : α) : succ a ≠ ⊥ :=
(bot_lt_succ a).ne'

end order_bot

section linear_order
variables [linear_order α]

/-- A constructor for `succ_order α` usable when `α` is a linear order with no maximal element. -/
def succ_order_of_succ_le_iff (succ : α → α) (hsucc_le_iff : ∀ {a b}, succ a ≤ b ↔ a < b) :
  succ_order α :=
{ succ := succ,
  le_succ := λ a, (hsucc_le_iff.1 le_rfl).le,
  maximal_of_succ_le := λ a ha, (lt_irrefl a (hsucc_le_iff.1 ha)).elim,
  succ_le_of_lt := λ a b, hsucc_le_iff.2,
  le_of_lt_succ := λ a b h, le_of_not_lt ((not_congr hsucc_le_iff).1 h.not_le) }

end linear_order

section complete_lattice
variables [complete_lattice α] [succ_order α]

lemma succ_eq_infi (a : α) : succ a = ⨅ (b : α) (h : a < b), b :=
begin
  refine le_antisymm (le_infi (λ b, le_infi succ_le_of_lt)) _,
  obtain rfl | ha := eq_or_ne a ⊤,
  { rw succ_top,
    exact le_top },
  exact binfi_le _ (lt_succ_iff_ne_top.2 ha),
end

end complete_lattice
end succ_order

/-! ### Predecessor order -/

/-- Order equipped with a sensible predecessor function. -/
@[ext] class pred_order (α : Type*) [preorder α] :=
(pred : α → α)
(pred_le : ∀ a, pred a ≤ a)
(minimal_of_le_pred : ∀ ⦃a⦄, a ≤ pred a → ∀ ⦃b⦄, ¬b < a)
(le_pred_of_lt : ∀ {a b}, a < b → a ≤ pred b)
(le_of_pred_lt : ∀ {a b}, pred a < b → a ≤ b)

namespace pred_order
section preorder
variables [preorder α]

/-- A constructor for `pred_order α` usable when `α` has no minimal element. -/
def pred_order_of_le_pred_iff_of_pred_le_pred (pred : α → α)
  (hle_pred_iff : ∀ {a b}, a ≤ pred b ↔ a < b)
  (hle_of_pred_lt : ∀ {a b}, pred a < b → a ≤ b) :
  pred_order α :=
{ pred := pred,
  pred_le := λ a, (hle_pred_iff.1 le_rfl).le,
  minimal_of_le_pred := λ a ha, (lt_irrefl a (hle_pred_iff.1 ha)).elim,
  le_pred_of_lt := λ a b, hle_pred_iff.2,
  le_of_pred_lt := λ a b, hle_of_pred_lt }

variables [pred_order α]

@[simp, mono] lemma pred_le_pred {a b : α} (h : a ≤ b) : pred a ≤ pred b :=
begin
  by_cases hb : ∀ ⦃c⦄, ¬c < b,
  { have hba : b ≤ pred a,
    { by_contra H,
      exact hb (((pred_le a).trans h).lt_of_not_le H) },
    by_contra H,
    exact hb ((((pred_le b).trans hba).lt_of_not_le H).trans_le ((pred_le a).trans h)) },
  { push_neg at hb,
    obtain ⟨c, hc⟩ := hb,
    exact le_pred_of_lt (((pred_le a).trans h).lt_of_not_le $ λ hba,
      minimal_of_le_pred (h.trans hba) $ hc.trans_le $ hba.trans $ pred_le a) }
end

lemma pred_mono : monotone (pred : α → α) := λ a b, pred_le_pred

lemma pred_lt_of_not_minimal {a b : α} (h : b < a) : pred a < a :=
(pred_le a).lt_of_not_le (λ ha, minimal_of_le_pred ha h)

section no_bot_order
variables [no_bot_order α] {a b : α}

lemma pred_lt (a : α) : pred a < a :=
(pred_le a).lt_of_not_le (λ h, not_exists.2 (minimal_of_le_pred h) (no_bot a))

lemma pred_lt_iff : pred a < b ↔ a ≤ b :=
⟨le_of_pred_lt, (pred_lt a).trans_le⟩

lemma le_pred_iff : a ≤ pred b ↔ a < b :=
⟨λ h, h.trans_lt (pred_lt b), le_pred_of_lt⟩

@[simp] lemma pred_le_pred_iff : pred a ≤ pred b ↔ a ≤ b :=
⟨λ h, le_of_pred_lt $ h.trans_lt (pred_lt b), λ h, le_pred_of_lt $ (pred_lt a).trans_le h⟩

alias pred_le_pred_iff ↔ le_of_pred_le_pred _

@[simp] lemma pred_lt_pred_iff : pred a < pred b ↔ a < b :=
by simp_rw [lt_iff_le_not_le, pred_le_pred_iff]

alias pred_lt_pred_iff ↔ lt_of_pred_lt_pred pred_lt_pred

lemma pred_strict_mono : strict_mono (pred : α → α) := λ a b, pred_lt_pred

end no_bot_order

end preorder

section partial_order
variables [partial_order α]

/-- There is at most one way to define the predecessors in a `partial_order`. -/
instance : subsingleton (pred_order α) :=
begin
  refine subsingleton.intro (λ h₀ h₁, _),
  ext a,
  by_cases ha : a ≤ @pred _ _ h₀ a,
  { refine le_antisymm _ ((@pred_le _ _ h₁ a).trans ha),
    by_contra H,
    exact @minimal_of_le_pred _ _ h₀ _ ha _
      ((@pred_le _ _ h₁ a).lt_of_not_le $ λ h, H $ (@pred_le _ _ h₀ a).trans h) },
  { exact (@le_pred_of_lt _ _ h₁ _ _ $ (@pred_le _ _ h₀ a).lt_of_not_le ha).antisymm
    (@le_pred_of_lt _ _ h₀ _ _ $ (@pred_le _ _ h₁ a).lt_of_not_le $ λ h,
    @minimal_of_le_pred _ _ h₁ _ h _ $ (@pred_le _ _ h₀ a).lt_of_not_le ha) }
end

variables [pred_order α]

lemma pred_le_le_iff {a b : α} : pred a ≤ b ∧ b ≤ a ↔ b = a ∨ b = pred a :=
begin
  split,
  { rintro h,
    rw or_iff_not_imp_left,
    exact λ hba, (le_pred_of_lt $ h.2.lt_of_ne hba).antisymm h.1 },
  rintro (rfl | rfl),
  { exact ⟨pred_le b, le_rfl⟩ },
  { exact ⟨le_rfl, pred_le a⟩ }
end

section no_bot_order
variables [no_bot_order α] {a b : α}

lemma pred_injective : injective (pred : α → α) :=
begin
  rintro a b,
  simp_rw [eq_iff_le_not_lt, pred_le_pred_iff, pred_lt_pred_iff],
  exact id,
end

lemma pred_eq_pred_iff : pred a = pred b ↔ a = b :=
pred_injective.eq_iff

lemma pred_ne_pred_iff : pred a ≠ pred b ↔ a ≠ b :=
pred_injective.ne_iff

lemma pred_lt_iff_lt_or_eq : pred a < b ↔ (a < b ∨ a = b) :=
pred_lt_iff.trans le_iff_lt_or_eq

lemma le_pred_iff_lt_or_eq : pred a ≤ b ↔ (a ≤ b ∨ pred a = b) :=
by rw [←pred_lt_iff, ←pred_lt_iff, pred_lt_iff_lt_or_eq]

end no_bot_order

end partial_order

section order_bot
variables [order_bot α] [pred_order α]

@[simp] lemma pred_bot : pred (⊥ : α) = ⊥ :=
(pred_le _).antisymm bot_le

@[simp] lemma le_pred_iff_eq_bot {a : α} : a ≤ pred a ↔ a = ⊥ :=
⟨λ h, eq_bot_of_minimal (minimal_of_le_pred h), λ h, by rw [h, pred_bot]⟩

@[simp] lemma pred_lt_iff_ne_bot {a : α} : pred a < a ↔ a ≠ ⊥ :=
begin
  simp only [lt_iff_le_not_le, true_and, pred_le a],
  exact not_iff_not.2 le_pred_iff_eq_bot,
end

end order_bot

section order_top
variables [order_top α] [pred_order α]

lemma pred_lt_top [nontrivial α] (a : α) : pred a < ⊤ :=
begin
  obtain ⟨b, hb⟩ := exists_ne (⊤ : α),
  refine lt_top_iff_ne_top.2 (λ h, _),
  have := eq_top_iff.2 (h.ge.trans (pred_le a)),
  rw this at h,
  exact minimal_of_le_pred h.ge (lt_top_iff_ne_top.2 hb),
end

lemma pred_ne_top [nontrivial α] (a : α) : pred a ≠ ⊤ :=
(pred_lt_top a).ne

end order_top

section linear_order
variables [linear_order α]

/-- A constructor for `pred_order α` usable when `α` is a linear order with no maximal element. -/
def pred_order_of_le_pred_iff (pred : α → α) (hle_pred_iff : ∀ {a b}, a ≤ pred b ↔ a < b) :
  pred_order α :=
{ pred := pred,
  pred_le := λ a, (hle_pred_iff.1 le_rfl).le,
  minimal_of_le_pred := λ a ha, (lt_irrefl a (hle_pred_iff.1 ha)).elim,
  le_pred_of_lt := λ a b, hle_pred_iff.2,
  le_of_pred_lt := λ a b h, le_of_not_lt ((not_congr hle_pred_iff).1 h.not_le) }

end linear_order

section complete_lattice
variables [complete_lattice α] [pred_order α]

lemma pred_eq_supr (a : α) : pred a = ⨆ (b : α) (h : b < a), b :=
begin
  refine le_antisymm _ (supr_le (λ b, supr_le le_pred_of_lt)),
  obtain rfl | ha := eq_or_ne a ⊥,
  { rw pred_bot,
    exact bot_le },
  exact @le_bsupr _ _ _ (λ b, b < a) (λ a _, a) (pred a) (pred_lt_iff_ne_bot.2 ha),
end

end complete_lattice
end pred_order

open succ_order pred_order

/-! ### Dual order -/

section order_dual
variables [preorder α]

instance [pred_order α] : succ_order (order_dual α) :=
{ succ := (pred : α → α),
  le_succ := pred_le,
  maximal_of_succ_le := minimal_of_le_pred,
  succ_le_of_lt := λ a b h, le_pred_of_lt h,
  le_of_lt_succ := λ a b, le_of_pred_lt }

instance [succ_order α] : pred_order (order_dual α) :=
{ pred := (succ : α → α),
  pred_le := le_succ,
  minimal_of_le_pred := maximal_of_succ_le,
  le_pred_of_lt := λ a b h, succ_le_of_lt h,
  le_of_pred_lt := λ a b, le_of_lt_succ }

end order_dual

/-! ### `with_bot`, `with_top`
Adding a greatest/least element to a `succ_order` or to a `pred_order`.

As far as successors and predecessors are concerned, there are four ways to add a bottom or top
element to an order:
* Adding a `⊤` to an `order_top`: Preserves `succ` and `pred`.
* Adding a `⊤` to a `no_top_order`: Preserves `succ`. Never preserves `pred`.
* Adding a `⊥` to an `order_bot`: Preserves `succ` and `pred`.
* Adding a `⊥` to a `no_bot_order`: Preserves `pred`. Never preserves `succ`.
where "preserves `(succ/pred)`" means
`(succ/pred)_order α → (succ/pred)_order ((with_top/with_bot) α)`.
-/

section with_top
open with_top

/-! #### Adding a `⊤` to an `order_top` -/

instance [decidable_eq α] [order_top α] [succ_order α] : succ_order (with_top α) :=
{ succ := λ a, match a with
    | ⊤        := ⊤
    | (some a) := ite (a = ⊤) ⊤ (some (succ a))
  end,
  le_succ := λ a, begin
    cases a,
    { exact le_top },
    change ((≤) : with_top α → with_top α → Prop) _ (ite _ _ _),
    split_ifs,
    { exact le_top },
    { exact some_le_some.2 (le_succ a) }
  end,
  maximal_of_succ_le := λ a ha b h, begin
    cases a,
    { exact not_top_lt h },
    change ((≤) : with_top α → with_top α → Prop) (ite _ _ _) _ at ha,
    split_ifs at ha with ha',
    { exact not_top_lt (ha.trans_lt h) },
    { rw [some_le_some, succ_le_iff_eq_top] at ha,
      exact ha' ha }
  end,
  succ_le_of_lt := λ a b h, begin
    cases b,
    { exact le_top },
    cases a,
    { exact (not_top_lt h).elim },
    rw some_lt_some at h,
    change ((≤) : with_top α → with_top α → Prop) (ite _ _ _) _,
    split_ifs with ha,
    { rw ha at h,
      exact (not_top_lt h).elim },
    { exact some_le_some.2 (succ_le_of_lt h) }
  end,
  le_of_lt_succ := λ a b h, begin
    cases a,
    { exact (not_top_lt h).elim },
    cases b,
    { exact le_top },
    change ((<) : with_top α → with_top α → Prop) _ (ite _ _ _) at h,
    rw some_le_some,
    split_ifs at h with hb,
    { rw hb,
      exact le_top },
    { exact le_of_lt_succ (some_lt_some.1 h) }
  end }

instance [order_top α] [pred_order α] : pred_order (with_top α) :=
{ pred := λ a, match a with
    | ⊤        := some ⊤
    | (some a) := some (pred a)
  end,
  pred_le := λ a, match a with
    | ⊤        := le_top
    | (some a) := some_le_some.2 (pred_le a)
  end,
  minimal_of_le_pred := λ a ha b h, begin
    cases a,
    { exact (coe_lt_top (⊤ : α)).not_le ha },
    cases b,
    { exact h.not_le le_top },
    { exact minimal_of_le_pred (some_le_some.1 ha) (some_lt_some.1 h) }
  end,
  le_pred_of_lt := λ a b h, begin
    cases a,
    { exact ((le_top).not_lt h).elim },
    cases b,
    { exact some_le_some.2 le_top },
    exact some_le_some.2 (le_pred_of_lt $ some_lt_some.1 h),
  end,
  le_of_pred_lt := λ a b h, begin
    cases b,
    { exact le_top },
    cases a,
    { exact (not_top_lt $ some_lt_some.1 h).elim },
    { exact some_le_some.2 (le_of_pred_lt $ some_lt_some.1 h) }
  end }

/-! #### Adding a `⊤` to a `no_top_order` -/

instance succ_order_of_no_top [partial_order α] [no_top_order α] [succ_order α] :
  succ_order (with_top α) :=
{ succ := λ a, match a with
    | ⊤        := ⊤
    | (some a) := some (succ a)
  end,
  le_succ := λ a, begin
    cases a,
    { exact le_top },
    { exact some_le_some.2 (le_succ a) }
  end,
  maximal_of_succ_le := λ a ha b h, begin
    cases a,
    { exact not_top_lt h },
    { exact not_exists.2 (maximal_of_succ_le (some_le_some.1 ha)) (no_top a) }
  end,
  succ_le_of_lt := λ a b h, begin
    cases a,
    { exact (not_top_lt h).elim },
    cases b,
    { exact le_top} ,
    { exact some_le_some.2 (succ_le_of_lt $ some_lt_some.1 h) }
  end,
  le_of_lt_succ := λ a b h, begin
    cases a,
    { exact (not_top_lt h).elim },
    cases b,
    { exact le_top },
    { exact some_le_some.2 (le_of_lt_succ $ some_lt_some.1 h) }
  end }

instance [partial_order α] [no_top_order α] [hα : nonempty α] :
  is_empty (pred_order (with_top α)) :=
⟨begin
  introI,
  set b := pred (⊤ : with_top α) with h,
  cases pred (⊤ : with_top α) with a ha; change b with pred ⊤ at h,
  { exact hα.elim (λ a, minimal_of_le_pred h.ge (coe_lt_top a)) },
  { obtain ⟨c, hc⟩ := no_top a,
    rw [←some_lt_some, ←h] at hc,
    exact (le_of_pred_lt hc).not_lt (some_lt_none _) }
end⟩

end with_top

section with_bot
open with_bot

/-! #### Adding a `⊥` to a `bot_order` -/

instance [order_bot α] [succ_order α] : succ_order (with_bot α) :=
{ succ := λ a, match a with
    | ⊥        := some ⊥
    | (some a) := some (succ a)
  end,
  le_succ := λ a, match a with
    | ⊥        := bot_le
    | (some a) := some_le_some.2 (le_succ a)
  end,
  maximal_of_succ_le := λ a ha b h, begin
    cases a,
    { exact (none_lt_some (⊥ : α)).not_le ha },
    cases b,
    { exact not_lt_bot h },
    { exact maximal_of_succ_le (some_le_some.1 ha) (some_lt_some.1 h) }
  end,
  succ_le_of_lt := λ a b h, begin
    cases b,
    { exact (not_lt_bot h).elim },
    cases a,
    { exact some_le_some.2 bot_le },
    { exact some_le_some.2 (succ_le_of_lt $ some_lt_some.1 h) }
  end,
  le_of_lt_succ := λ a b h, begin
    cases a,
    { exact bot_le },
    cases b,
    { exact (not_lt_bot $ some_lt_some.1 h).elim },
    { exact some_le_some.2 (le_of_lt_succ $ some_lt_some.1 h) }
  end }

instance [decidable_eq α] [order_bot α] [pred_order α] : pred_order (with_bot α) :=
{ pred := λ a, match a with
    | ⊥        := ⊥
    | (some a) := ite (a = ⊥) ⊥ (some (pred a))
  end,
  pred_le := λ a, begin
    cases a,
    { exact bot_le },
    change (ite _ _ _ : with_bot α) ≤ some a,
    split_ifs,
    { exact bot_le },
    { exact some_le_some.2 (pred_le a) }
  end,
  minimal_of_le_pred := λ a ha b h, begin
    cases a,
    { exact not_lt_bot h },
    change ((≤) : with_bot α → with_bot α → Prop) _ (ite _ _ _) at ha,
    split_ifs at ha with ha',
    { exact not_lt_bot (h.trans_le ha) },
    { rw [some_le_some, le_pred_iff_eq_bot] at ha,
      exact ha' ha }
  end,
  le_pred_of_lt := λ a b h, begin
    cases a,
    { exact bot_le },
    cases b,
    { exact (not_lt_bot h).elim },
    rw some_lt_some at h,
    change ((≤) : with_bot α → with_bot α → Prop) _ (ite _ _ _),
    split_ifs with hb,
    { rw hb at h,
      exact (not_lt_bot h).elim },
    { exact some_le_some.2 (le_pred_of_lt h) }
  end,
  le_of_pred_lt := λ a b h, begin
    cases b,
    { exact (not_lt_bot h).elim },
    cases a,
    { exact bot_le },
    change ((<) : with_bot α → with_bot α → Prop) (ite _ _ _) _ at h,
    rw some_le_some,
    split_ifs at h with ha,
    { rw ha,
      exact bot_le },
    { exact le_of_pred_lt (some_lt_some.1 h) }
  end }

/-! #### Adding a `⊥` to a `no_bot_order` -/

instance [partial_order α] [no_bot_order α] [hα : nonempty α] :
  is_empty (succ_order (with_bot α)) :=
⟨begin
  introI,
  set b : with_bot α := succ ⊥ with h,
  cases succ (⊥ : with_bot α) with a ha; change b with succ ⊥ at h,
  { exact hα.elim (λ a, maximal_of_succ_le h.le (bot_lt_coe a)) },
  { obtain ⟨c, hc⟩ := no_bot a,
    rw [←some_lt_some, ←h] at hc,
    exact (le_of_lt_succ hc).not_lt (none_lt_some _) }
end⟩

instance pred_order_of_no_bot [partial_order α] [no_bot_order α] [pred_order α] :
  pred_order (with_bot α) :=
{ pred := λ a, match a with
    | ⊥        := ⊥
    | (some a) := some (pred a)
  end,
  pred_le := λ a, begin
    cases a,
    { exact bot_le },
    { exact some_le_some.2 (pred_le a) }
  end,
  minimal_of_le_pred := λ a ha b h, begin
    cases a,
    { exact not_lt_bot h },
    { exact not_exists.2 (minimal_of_le_pred (some_le_some.1 ha)) (no_bot a) }
  end,
  le_pred_of_lt := λ a b h, begin
    cases b,
    { exact (not_lt_bot h).elim },
    cases a,
    { exact bot_le },
    { exact some_le_some.2 (le_pred_of_lt $ some_lt_some.1 h) }
  end,
  le_of_pred_lt := λ a b h, begin
    cases b,
    { exact (not_lt_bot h).elim },
    cases a,
    { exact bot_le },
    { exact some_le_some.2 (le_of_pred_lt $ some_lt_some.1 h) }
  end }

end with_bot

/-! ### Archimedeanness -/

/-- A `succ_order` is succ-archimedean if one can go from any two comparable elements by iterating
`succ` -/
class is_succ_archimedean (α : Type*) [preorder α] [succ_order α] : Prop :=
(exists_succ_iterate_of_le {a b : α} (h : a ≤ b) : ∃ n, succ^[n] a = b)

/-- A `pred_order` is pred-archimedean if one can go from any two comparable elements by iterating
`pred` -/
class is_pred_archimedean (α : Type*) [preorder α] [pred_order α] : Prop :=
(exists_pred_iterate_of_le {a b : α} (h : a ≤ b) : ∃ n, pred^[n] b = a)

export is_succ_archimedean (exists_succ_iterate_of_le)
export is_pred_archimedean (exists_pred_iterate_of_le)

section preorder
variables [preorder α]

section succ_order
variables [succ_order α] [is_succ_archimedean α] {a b : α}

instance : is_pred_archimedean (order_dual α) :=
{ exists_pred_iterate_of_le := λ a b h, by convert @exists_succ_iterate_of_le α _ _ _ _ _ h }

lemma has_le.le.exists_succ_iterate (h : a ≤ b) : ∃ n, succ^[n] a = b :=
exists_succ_iterate_of_le h

lemma exists_succ_iterate_iff_le : (∃ n, succ^[n] a = b) ↔ a ≤ b :=
begin
  refine ⟨_, exists_succ_iterate_of_le⟩,
  rintro ⟨n, rfl⟩,
  exact id_le_iterate_of_id_le le_succ n a,
end

lemma succ.rec {p : α → Prop} (hsucc : ∀ a, p a → p (succ a)) {a b : α} (h : a ≤ b) (ha : p a) :
  p b :=
begin
  obtain ⟨n, rfl⟩ := h.exists_succ_iterate,
  exact iterate.rec _ hsucc ha n,
end

lemma succ.rec_iff {p : α → Prop} (hsucc : ∀ a, p a ↔ p (succ a)) {a b : α} (h : a ≤ b) :
  p a ↔ p b :=
begin
  obtain ⟨n, rfl⟩ := h.exists_succ_iterate,
  exact iterate.rec (λ b, p a ↔ p b) (λ c hc, hc.trans (hsucc _)) iff.rfl n,
end

end succ_order

section pred_order
variables [pred_order α] [is_pred_archimedean α] {a b : α}

instance : is_succ_archimedean (order_dual α) :=
{ exists_succ_iterate_of_le := λ a b h, by convert @exists_pred_iterate_of_le α _ _ _ _ _ h }

lemma has_le.le.exists_pred_iterate (h : a ≤ b) : ∃ n, pred^[n] b = a :=
exists_pred_iterate_of_le h

lemma exists_pred_iterate_iff_le : (∃ n, pred^[n] b = a) ↔ a ≤ b :=
@exists_succ_iterate_iff_le (order_dual α) _ _ _ _ _

lemma pred.rec {p : α → Prop} (hsucc : ∀ a, p a → p (pred a)) {a b : α} (h : b ≤ a) (ha : p a) :
  p b :=
@succ.rec (order_dual α) _ _ _ _ hsucc _ _ h ha

lemma pred.rec_iff {p : α → Prop} (hsucc : ∀ a, p a ↔ p (pred a)) {a b : α} (h : a ≤ b) :
  p a ↔ p b :=
(@succ.rec_iff (order_dual α) _ _ _ _ hsucc _ _ h).symm

end pred_order
end preorder

section linear_order
variables [linear_order α]

section succ_order
variables [succ_order α] [is_succ_archimedean α] {a b : α}

lemma exists_succ_iterate_or : (∃ n, succ^[n] a = b) ∨ ∃ n, succ^[n] b = a :=
(le_total a b).imp exists_succ_iterate_of_le exists_succ_iterate_of_le

lemma succ.rec_linear {p : α → Prop} (hsucc : ∀ a, p a ↔ p (succ a)) (a b : α) : p a ↔ p b :=
(le_total a b).elim (succ.rec_iff hsucc) (λ h, (succ.rec_iff hsucc h).symm)

end succ_order

section pred_order
variables [pred_order α] [is_pred_archimedean α] {a b : α}

lemma exists_pred_iterate_or : (∃ n, pred^[n] b = a) ∨ ∃ n, pred^[n] a = b :=
(le_total a b).imp exists_pred_iterate_of_le exists_pred_iterate_of_le

lemma pred.rec_linear {p : α → Prop} (hsucc : ∀ a, p a ↔ p (pred a)) (a b : α) : p a ↔ p b :=
(le_total a b).elim (pred.rec_iff hsucc) (λ h, (pred.rec_iff hsucc h).symm)

end pred_order
end linear_order

section order_bot
variables [order_bot α] [succ_order α] [is_succ_archimedean α]

lemma succ.rec_bot (p : α → Prop) (hbot : p ⊥) (hsucc : ∀ a, p a → p (succ a)) (a : α) : p a :=
succ.rec hsucc bot_le hbot

end order_bot

section order_top
variables [order_top α] [pred_order α] [is_pred_archimedean α]

lemma pred.rec_top (p : α → Prop) (htop : p ⊤) (hpred : ∀ a, p a → p (pred a)) (a : α) : p a :=
pred.rec hpred le_top htop

end order_top
