/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.bounded_lattice
import order.galois_connection

/-!
# Successor and predecessor

## Typeclasses

* `succ_order`: Order equipped with a sensible successor function.
* `add_succ_order`: Syntax-agreement typeclass stating that the `succ` of a `succ_order`
  coincides with `λ a, a + 1`.
* `pred_order`: Order equipped with a sensible predecessor function.
* `add_pred_order`: Syntax-agreement typeclass stating that the `pred` of a `pred_order`
  coincides with `λ a, a _ 1`.

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

In a `succ_pred_order`, prove `galois_connection pred succ`. This then gives `succ (pred n) = n`
and `pred (succ n)` for free (with `no_bot_order α`, `no_top_order α` respectively).
-/

/-! ### Successor order -/

variables {α : Type*}

/-- Order equipped with a sensible successor function. -/
@[ext] class succ_order (α : Type*) [preorder α] :=
(succ : α → α)
(le_succ : ∀ a, a ≤ succ a)
(maximal_of_succ_le : ∀ ⦃a⦄, succ a ≤ a → ∀ ⦃b⦄, ¬a < b)
(succ_le_of_lt : ∀ {a b}, a < b → succ a ≤ b)
(le_of_lt_succ : ∀ {a b}, a < succ b → a ≤ b)

open function succ_order

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

@[simp] lemma succ_le_succ {a b : α} (h : a ≤ b) :
  succ a ≤ succ b :=
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

section no_top_order
variables [no_top_order α]

lemma lt_succ (a : α) :
  a < succ a :=
(le_succ a).lt_of_not_le (λ h, not_exists.2 (maximal_of_succ_le h) (no_top a))

lemma lt_succ_iff {a b : α} :
  a < succ b ↔ a ≤ b :=
⟨le_of_lt_succ, λ h, h.trans_lt $ lt_succ b⟩

lemma succ_le_iff {a b : α} :
  succ a ≤ b ↔ a < b :=
⟨(lt_succ a).trans_le, succ_le_of_lt⟩

@[simp] lemma succ_le_succ_iff {a b : α} :
  succ a ≤ succ b ↔ a ≤ b :=
⟨λ h, le_of_lt_succ $ (lt_succ a).trans_le h, λ h, succ_le_of_lt $ h.trans_lt $ lt_succ b⟩

alias succ_le_succ_iff ↔ le_of_succ_le_succ _

@[simp] lemma succ_lt_succ_iff {a b : α} :
  succ a < succ b ↔ a < b :=
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
    exact λ hba, h.2.antisymm (succ_le_of_lt $ h.1.lt_of_ne $ ne.symm hba) },
  rintro (rfl | rfl),
  { exact ⟨le_rfl, le_succ b⟩ },
  { exact ⟨le_succ a, le_rfl⟩ }
end

section no_top_order
variables [no_top_order α]

lemma succ_injective :
  injective (succ : α → α) :=
begin
  rintro a b,
  simp_rw [eq_iff_le_not_lt, succ_le_succ_iff, succ_lt_succ_iff],
  exact id,
end

instance : succ_order (with_top α) :=
{ succ := λ a, match a with
    | ⊤        := ⊤
    | (some a) := some (succ a)
  end,
  le_succ := λ a, begin
    cases a,
    exact le_top,
    exact with_top.some_le_some.2 (le_succ a),
  end,
  maximal_of_succ_le := begin
    rintro a ha b h,
    cases a,
    exact le_top.not_lt h,
    exact not_exists.2 (maximal_of_succ_le (with_top.some_le_some.1 ha)) (no_top a),
  end,
  succ_le_of_lt := begin
    rintro a b h,
    cases a,
    exact (le_top.not_lt h).elim,
    cases b,
    exact le_top,
    exact with_top.some_le_some.2 (succ_le_of_lt $ with_top.some_lt_some.1 h),
  end,
  le_of_lt_succ := begin
    rintro a b h,
    cases a,
    exact (le_top.not_lt h).elim,
    cases b,
    exact le_top,
    exact with_top.some_le_some.2 (le_of_lt_succ $ with_top.some_lt_some.1 h),
  end }

lemma succ_eq_succ_iff {a b : α} :
  succ a = succ b ↔ a = b :=
succ_injective.eq_iff

lemma succ_ne_succ_iff {a b : α} :
  succ a ≠ succ b ↔ a ≠ b :=
succ_injective.ne_iff

lemma lt_succ_iff_lt_or_eq {a b : α} : a < succ b ↔ (a < b ∨ a = b) :=
lt_succ_iff.trans le_iff_lt_or_eq

lemma le_succ_iff_lt_or_eq {a b : α} : a ≤ succ b ↔ (a ≤ b ∨ a = succ b) :=
by rw [←lt_succ_iff, ←lt_succ_iff, lt_succ_iff_lt_or_eq]

end no_top_order

end partial_order

section order_top
variables [order_top α] [succ_order α]

@[simp] lemma succ_top :
  succ (⊤ : α) = ⊤ :=
le_top.antisymm (le_succ _)

@[simp] lemma succ_le_iff_eq_top {a : α} :
  succ a ≤ a ↔ a = ⊤ :=
⟨λ h, eq_top_of_maximal (maximal_of_succ_le h), λ h, by rw [h, succ_top]⟩

@[simp] lemma lt_succ_iff_ne_top {a : α} : a < succ a ↔ a ≠ ⊤ :=
begin
  simp only [lt_iff_le_not_le, true_and, le_succ a],
  exact not_iff_not.2 succ_le_iff_eq_top,
end

end order_top

section order_bot
variables [order_bot α] [succ_order α]

lemma bot_lt_succ [nontrivial α] (a : α) :
  ⊥ < succ a :=
begin
  obtain ⟨b, hb⟩ := exists_ne (⊥ : α),
  refine bot_lt_iff_ne_bot.2 (λ h, _),
  have := eq_bot_iff.2 ((le_succ a).trans h.le),
  rw this at h,
  exact maximal_of_succ_le h.le (bot_lt_iff_ne_bot.2 hb),
end

lemma succ_ne_bot [nontrivial α] (a : α) :
  succ a ≠ ⊥ :=
(bot_lt_succ a).ne'

instance : succ_order (with_bot α) :=
{ succ := λ a, match a with
    | ⊥        := some ⊥
    | (some a) := some (succ a)
  end,
  le_succ := λ a, match a with
    | ⊥        := bot_le
    | (some a) := with_bot.some_le_some.2 (le_succ a)
  end,
  maximal_of_succ_le := begin
    rintro a ha b h,
    cases a,
    { exact (with_bot.none_lt_some (⊥ : α)).not_le ha },
    cases b,
    { exact h.not_le bot_le },
    exact maximal_of_succ_le (with_bot.some_le_some.1 ha) (with_bot.some_lt_some.1 h),
  end,
  succ_le_of_lt := begin
    rintro a b h,
    cases b,
    exact (bot_le.not_lt h).elim,
    cases a,
    exact with_bot.some_le_some.2 bot_le,
    exact with_bot.some_le_some.2 (succ_le_of_lt $ with_bot.some_lt_some.1 h),
  end,
  le_of_lt_succ := begin
    rintro a b h,
    cases a,
    exact bot_le,
    cases b,
    exact (bot_le.not_lt $ with_bot.some_lt_some.1 h).elim,
    exact with_bot.some_le_some.2 (le_of_lt_succ $ with_bot.some_lt_some.1 h),
  end }

end order_bot

section linear_order
variables [linear_order α]

/-- A constructor for `succ_order α` usable when `α` is a linear order with no maximal element. -/
def succ_order_of_succ_le_iff (succ : α → α)
  (hsucc_le_iff : ∀ {a b}, succ a ≤ b ↔ a < b) :
  succ_order α :=
{ succ := succ,
  le_succ := λ a, (hsucc_le_iff.1 le_rfl).le,
  maximal_of_succ_le := λ a ha, (lt_irrefl a (hsucc_le_iff.1 ha)).elim,
  succ_le_of_lt := λ a b, hsucc_le_iff.2,
  le_of_lt_succ := λ a b h, le_of_not_lt ((not_congr hsucc_le_iff).1 h.not_le) }

variables [succ_order α]

@[simp] lemma max_succ_succ {a b : α} :
  max (succ a) (succ b) = succ (max a b) :=
succ_mono.max.symm

@[simp] lemma min_succ_succ {a b : α} :
  min (succ a) (succ b) = succ (min a b) :=
succ_mono.min.symm

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

/-! ### Predecessor order -/

/-- Order equipped with a sensible predecessor function. -/
@[ext] class pred_order (α : Type*) [preorder α] :=
(pred : α → α)
(pred_le : ∀ a, pred a ≤ a)
(minimal_of_le_pred : ∀ ⦃a⦄, a ≤ pred a → ∀ ⦃b⦄, ¬b < a)
(le_pred_of_lt : ∀ {a b}, a < b → a ≤ pred b)
(le_of_pred_lt : ∀ {a b}, pred a < b → a ≤ b)

open pred_order

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

@[simp] lemma pred_le_pred {a b : α} (h : a ≤ b) :
  pred a ≤ pred b :=
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

lemma pred_anti : antitone (pred : α → α) := λ a b, pred_le_pred

section no_bot_order
variables [no_bot_order α]

lemma pred_lt (a : α) :
  pred a < a :=
(pred_le a).lt_of_not_le (λ h, not_exists.2 (minimal_of_le_pred h) (no_bot a))

lemma pred_lt_iff {a b : α} :
  pred a < b ↔ a ≤ b :=
⟨le_of_pred_lt, (pred_lt a).trans_le⟩

lemma le_pred_iff {a b : α} :
  a ≤ pred b ↔ a < b :=
⟨λ h, h.trans_lt (pred_lt b), le_pred_of_lt⟩

@[simp] lemma pred_le_pred_iff {a b : α} :
  pred a ≤ pred b ↔ a ≤ b :=
⟨λ h, le_of_pred_lt $ h.trans_lt (pred_lt b), λ h, le_pred_of_lt $ (pred_lt a).trans_le h⟩

alias pred_le_pred_iff ↔ le_of_pred_le_pred _

@[simp] lemma pred_lt_pred_iff {a b : α} :
  pred a < pred b ↔ a < b :=
by simp_rw [lt_iff_le_not_le, pred_le_pred_iff]

alias pred_lt_pred_iff ↔ lt_of_pred_lt_pred pred_lt_pred

lemma pred_strict_anti : strict_anti (pred : α → α) := λ a b, pred_lt_pred

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
variables [no_bot_order α]

lemma pred_injective :
  injective (pred : α → α) :=
begin
  rintro a b,
  simp_rw [eq_iff_le_not_lt, pred_le_pred_iff, pred_lt_pred_iff],
  exact id,
end

instance : pred_order (with_bot α) :=
{ pred := λ a, match a with
    | ⊥        := ⊥
    | (some a) := some (pred a)
  end,
  pred_le := λ a, begin
    cases a,
    exact bot_le,
    exact with_bot.some_le_some.2 (pred_le a),
  end,
  minimal_of_le_pred := begin
    rintro a ha b h,
    cases a,
    exact not_lt_bot h,
    exact not_exists.2 (minimal_of_le_pred (with_bot.some_le_some.1 ha)) (no_bot a),
  end,
  le_pred_of_lt := begin
    rintro a b h,
    cases b,
    exact (not_lt_bot h).elim,
    cases a,
    exact bot_le,
    exact with_bot.some_le_some.2 (le_pred_of_lt $ with_bot.some_lt_some.1 h),
  end,
  le_of_pred_lt := begin
    rintro a b h,
    cases b,
    exact (not_lt_bot h).elim,
    cases a,
    exact bot_le,
    exact with_bot.some_le_some.2 (le_of_pred_lt $ with_bot.some_lt_some.1 h),
  end }

lemma pred_eq_pred_iff {a b : α} :
  pred a = pred b ↔ a = b :=
pred_injective.eq_iff

lemma pred_ne_pred_iff {a b : α} :
  pred a ≠ pred b ↔ a ≠ b :=
pred_injective.ne_iff

lemma pred_lt_iff_lt_or_eq {a b : α} : pred a < b ↔ (a < b ∨ a = b) :=
pred_lt_iff.trans le_iff_lt_or_eq

lemma le_pred_iff_lt_or_eq {a b : α} : pred a ≤ b ↔ (a ≤ b ∨ pred a = b) :=
by rw [←pred_lt_iff, ←pred_lt_iff, pred_lt_iff_lt_or_eq]

end no_bot_order

end partial_order

section order_bot
variables [order_bot α] [pred_order α]

@[simp] lemma pred_bot :
  pred (⊥ : α) = ⊥ :=
(pred_le _).antisymm bot_le

@[simp] lemma le_pred_iff_eq_bot {a : α} :
  a ≤ pred a ↔ a = ⊥ :=
⟨λ h, eq_bot_of_minimal (minimal_of_le_pred h), λ h, by rw [h, pred_bot]⟩

@[simp] lemma pred_lt_iff_ne_bot {a : α} : pred a < a ↔ a ≠ ⊥ :=
begin
  simp only [lt_iff_le_not_le, true_and, pred_le a],
  exact not_iff_not.2 le_pred_iff_eq_bot,
end

end order_bot

section order_top
variables [order_top α] [pred_order α]

lemma pred_lt_top [nontrivial α] (a : α) :
  pred a < ⊤ :=
begin
  obtain ⟨b, hb⟩ := exists_ne (⊤ : α),
  refine lt_top_iff_ne_top.2 (λ h, _),
  have := eq_top_iff.2 (h.ge.trans (pred_le a)),
  rw this at h,
  exact minimal_of_le_pred h.ge (lt_top_iff_ne_top.2 hb),
end

lemma pred_ne_top [nontrivial α] (a : α) :
  pred a ≠ ⊤ :=
(pred_lt_top a).ne

instance : pred_order (with_top α) :=
{ pred := λ a, match a with
    | ⊤        := some ⊤
    | (some a) := some (pred a)
  end,
  pred_le := λ a, match a with
    | ⊤        := le_top
    | (some a) := with_top.some_le_some.2 (pred_le a)
  end,
  minimal_of_le_pred := begin
    rintro a ha b h,
    cases a,
    { exact (with_top.coe_lt_top (⊤ : α)).not_le ha },
    cases b,
    { exact h.not_le le_top },
    { exact minimal_of_le_pred (with_top.some_le_some.1 ha) (with_top.some_lt_some.1 h) }
  end,
  le_pred_of_lt := begin
    rintro a b h,
    cases a,
    { exact ((le_top).not_lt h).elim },
    cases b,
    { exact with_top.some_le_some.2 le_top },
    exact with_top.some_le_some.2 (le_pred_of_lt $ with_top.some_lt_some.1 h),
  end,
  le_of_pred_lt := begin
    rintro a b h,
    cases b,
    { exact le_top },
    cases a,
    { exact (le_top.not_lt $ with_top.some_lt_some.1 h).elim },
    { exact with_top.some_le_some.2 (le_of_pred_lt $ with_top.some_lt_some.1 h) }
  end }

end order_top

section linear_order
variables [linear_order α]

/-- A constructor for `pred_order α` usable when `α` is a linear order with no maximal element. -/
def pred_order_of_le_pred_iff (pred : α → α)
  (hle_pred_iff : ∀ {a b}, a ≤ pred b ↔ a < b) :
  pred_order α :=
{ pred := pred,
  pred_le := λ a, (hle_pred_iff.1 le_rfl).le,
  minimal_of_le_pred := λ a ha, (lt_irrefl a (hle_pred_iff.1 ha)).elim,
  le_pred_of_lt := λ a b, hle_pred_iff.2,
  le_of_pred_lt := λ a b h, le_of_not_lt ((not_congr hle_pred_iff).1 h.not_le) }

variables [pred_order α]

@[simp] lemma max_pred_pred {a b : α} :
  max (pred a) (pred b) = pred (max a b) :=
pred_mono.max.symm

@[simp] lemma min_pred_pred {a b : α} :
  min (pred a) (pred b) = pred (min a b) :=
pred_mono.min.symm

end linear_order

section complete_lattice
variables [complete_lattice α] [pred_order α]

lemma pred_eq_infi (a : α) : pred a = ⨅ (b : α) (h : a < b), b :=
begin
  refine le_antisymm (le_infi (λ b, le_infi le_pred_of_lt)) _,
  obtain rfl | ha := eq_or_ne a ⊤,
  { rw pred_top,
    exact le_top },
  exact binfi_le _ (pred_lt_iff_ne_top.2 ha),
end

end complete_lattice

/-! ### Successor-predecessor order -/

class succ_pred_order (α : Type*) [preorder α] extends succ_order α, pred_order α

/-! ### Dual order-/

variables [preorder α]

instance [pred_order α] : succ_order (order_dual α) :=
{ succ := (pred : α → α),
  le_succ := pred_le,
  maximal_of_succ_le := minimal_of_le_pred,
  succ_le_of_lt := λ a b h, le_pred_of_lt (by convert h),
  le_of_lt_succ := λ a b, le_of_pred_lt }

instance [succ_order α] : pred_order (order_dual α) :=
{ pred := (succ : α → α),
  pred_le := le_succ,
  minimal_of_le_pred := maximal_of_succ_le,
  le_pred_of_lt := λ a b h, succ_le_of_lt (by convert h),
  le_of_pred_lt := λ a b, le_of_lt_succ }

instance [succ_pred_order α] : succ_pred_order (order_dual α) :=
{ ..order_dual.succ_order, ..order_dual.pred_order }
