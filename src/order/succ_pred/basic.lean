/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.complete_lattice
import order.cover
import order.iterate

/-!
# Successor and predecessor

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines successor and predecessor orders. `succ a`, the successor of an element `a : α` is
the least element greater than `a`. `pred a` is the greatest element less than `a`. Typical examples
include `ℕ`, `ℤ`, `ℕ+`, `fin n`, but also `enat`, the lexicographic order of a successor/predecessor
order...

## Typeclasses

* `succ_order`: Order equipped with a sensible successor function.
* `pred_order`: Order equipped with a sensible predecessor function.
* `is_succ_archimedean`: `succ_order` where `succ` iterated to an element gives all the greater
  ones.
* `is_pred_archimedean`: `pred_order` where `pred` iterated to an element gives all the smaller
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
`max_of_succ_le`).
The stricter condition of every element having a sensible successor can be obtained through the
combination of `succ_order α` and `no_max_order α`.

## TODO

Is `galois_connection pred succ` always true? If not, we should introduce
```lean
class succ_pred_order (α : Type*) [preorder α] extends succ_order α, pred_order α :=
(pred_succ_gc : galois_connection (pred : α → α) succ)
```
`covby` should help here.
-/

open function order_dual set

variables {α : Type*}

/-- Order equipped with a sensible successor function. -/
@[ext] class succ_order (α : Type*) [preorder α] :=
(succ : α → α)
(le_succ : ∀ a, a ≤ succ a)
(max_of_succ_le {a} : succ a ≤ a → is_max a)
(succ_le_of_lt {a b} : a < b → succ a ≤ b)
(le_of_lt_succ {a b} : a < succ b → a ≤ b)

/-- Order equipped with a sensible predecessor function. -/
@[ext] class pred_order (α : Type*) [preorder α] :=
(pred : α → α)
(pred_le : ∀ a, pred a ≤ a)
(min_of_le_pred {a} : a ≤ pred a → is_min a)
(le_pred_of_lt {a b} : a < b → a ≤ pred b)
(le_of_pred_lt {a b} : pred a < b → a ≤ b)

instance [preorder α] [succ_order α] : pred_order αᵒᵈ :=
{ pred := to_dual ∘ succ_order.succ ∘ of_dual,
  pred_le := succ_order.le_succ,
  min_of_le_pred := λ _, succ_order.max_of_succ_le,
  le_pred_of_lt := λ a b h, succ_order.succ_le_of_lt h,
  le_of_pred_lt := λ a b, succ_order.le_of_lt_succ }

instance [preorder α] [pred_order α] : succ_order αᵒᵈ :=
{ succ := to_dual ∘ pred_order.pred ∘ of_dual,
  le_succ := pred_order.pred_le,
  max_of_succ_le := λ _, pred_order.min_of_le_pred,
  succ_le_of_lt := λ a b h, pred_order.le_pred_of_lt h,
  le_of_lt_succ := λ a b, pred_order.le_of_pred_lt }

section preorder
variables [preorder α]

/-- A constructor for `succ_order α` usable when `α` has no maximal element. -/
def succ_order.of_succ_le_iff_of_le_lt_succ (succ : α → α)
  (hsucc_le_iff : ∀ {a b}, succ a ≤ b ↔ a < b) (hle_of_lt_succ : ∀ {a b}, a < succ b → a ≤ b) :
  succ_order α :=
{ succ := succ,
  le_succ := λ a, (hsucc_le_iff.1 le_rfl).le,
  max_of_succ_le := λ a ha, (lt_irrefl a $ hsucc_le_iff.1 ha).elim,
  succ_le_of_lt := λ a b, hsucc_le_iff.2,
  le_of_lt_succ := λ a b, hle_of_lt_succ }

/-- A constructor for `pred_order α` usable when `α` has no minimal element. -/
def pred_order.of_le_pred_iff_of_pred_le_pred (pred : α → α)
  (hle_pred_iff : ∀ {a b}, a ≤ pred b ↔ a < b) (hle_of_pred_lt : ∀ {a b}, pred a < b → a ≤ b) :
  pred_order α :=
{ pred := pred,
  pred_le := λ a, (hle_pred_iff.1 le_rfl).le,
  min_of_le_pred := λ a ha, (lt_irrefl a $ hle_pred_iff.1 ha).elim,
  le_pred_of_lt := λ a b, hle_pred_iff.2,
  le_of_pred_lt := λ a b, hle_of_pred_lt }

end preorder

section linear_order
variables [linear_order α]

/-- A constructor for `succ_order α` for `α` a linear order. -/
@[simps] def succ_order.of_core (succ : α → α) (hn : ∀ {a}, ¬ is_max a → ∀ b, a < b ↔ succ a ≤ b)
  (hm : ∀ a, is_max a → succ a = a) : succ_order α :=
{ succ           := succ,
  succ_le_of_lt  := λ a b, classical.by_cases (λ h hab, (hm a h).symm ▸ hab.le) (λ h, (hn h b).mp),
  le_succ        := λ a, classical.by_cases (λ h, (hm a h).symm.le)
                                            (λ h, le_of_lt $ by simpa using (hn h a).not),
  le_of_lt_succ  := λ a b hab, classical.by_cases (λ h, hm b h ▸ hab.le)
                                                  (λ h, by simpa [hab] using (hn h a).not),
  max_of_succ_le := λ a, not_imp_not.mp $ λ h, by simpa using (hn h a).not }

/-- A constructor for `pred_order α` for `α` a linear order. -/
@[simps] def pred_order.of_core {α} [linear_order α] (pred : α → α)
  (hn : ∀ {a}, ¬ is_min a → ∀ b, b ≤ pred a ↔ b < a) (hm : ∀ a, is_min a → pred a = a) :
  pred_order α :=
{ pred           := pred,
  le_pred_of_lt  := λ a b, classical.by_cases (λ h hab, (hm b h).symm ▸ hab.le) (λ h, (hn h a).mpr),
  pred_le        := λ a, classical.by_cases (λ h, (hm a h).le)
                                            (λ h, le_of_lt $ by simpa using (hn h a).not),
  le_of_pred_lt  := λ a b hab, classical.by_cases (λ h, hm a h ▸ hab.le)
                                                  (λ h, by simpa [hab] using (hn h b).not),
  min_of_le_pred := λ a, not_imp_not.mp $ λ h, by simpa using (hn h a).not }

/-- A constructor for `succ_order α` usable when `α` is a linear order with no maximal element. -/
def succ_order.of_succ_le_iff (succ : α → α) (hsucc_le_iff : ∀ {a b}, succ a ≤ b ↔ a < b) :
  succ_order α :=
{ succ := succ,
  le_succ := λ a, (hsucc_le_iff.1 le_rfl).le,
  max_of_succ_le := λ a ha, (lt_irrefl a $ hsucc_le_iff.1 ha).elim,
  succ_le_of_lt := λ a b, hsucc_le_iff.2,
  le_of_lt_succ := λ a b h, le_of_not_lt ((not_congr hsucc_le_iff).1 h.not_le) }

/-- A constructor for `pred_order α` usable when `α` is a linear order with no minimal element. -/
def pred_order.of_le_pred_iff (pred : α → α) (hle_pred_iff : ∀ {a b}, a ≤ pred b ↔ a < b) :
  pred_order α :=
{ pred := pred,
  pred_le := λ a, (hle_pred_iff.1 le_rfl).le,
  min_of_le_pred := λ a ha, (lt_irrefl a $ hle_pred_iff.1 ha).elim,
  le_pred_of_lt := λ a b, hle_pred_iff.2,
  le_of_pred_lt := λ a b h, le_of_not_lt ((not_congr hle_pred_iff).1 h.not_le) }

end linear_order

/-! ### Successor order -/

namespace order
section preorder
variables [preorder α] [succ_order α] {a b : α}

/-- The successor of an element. If `a` is not maximal, then `succ a` is the least element greater
than `a`. If `a` is maximal, then `succ a = a`. -/
def succ : α → α := succ_order.succ

lemma le_succ : ∀ a : α, a ≤ succ a := succ_order.le_succ
lemma max_of_succ_le {a : α} : succ a ≤ a → is_max a := succ_order.max_of_succ_le
lemma succ_le_of_lt {a b : α} : a < b → succ a ≤ b := succ_order.succ_le_of_lt
lemma le_of_lt_succ {a b : α} : a < succ b → a ≤ b := succ_order.le_of_lt_succ

@[simp] lemma succ_le_iff_is_max : succ a ≤ a ↔ is_max a := ⟨max_of_succ_le, λ h, h $ le_succ _⟩

@[simp] lemma lt_succ_iff_not_is_max : a < succ a ↔ ¬ is_max a :=
⟨not_is_max_of_lt, λ ha, (le_succ a).lt_of_not_le $ λ h, ha $ max_of_succ_le h⟩

alias lt_succ_iff_not_is_max ↔ _ lt_succ_of_not_is_max

lemma wcovby_succ (a : α) : a ⩿ succ a :=
⟨le_succ a, λ b hb, (succ_le_of_lt hb).not_lt⟩

lemma covby_succ_of_not_is_max (h : ¬ is_max a) : a ⋖ succ a :=
(wcovby_succ a).covby_of_lt $ lt_succ_of_not_is_max h

lemma lt_succ_iff_of_not_is_max (ha : ¬ is_max a) : b < succ a ↔ b ≤ a :=
⟨le_of_lt_succ, λ h, h.trans_lt $ lt_succ_of_not_is_max ha⟩

lemma succ_le_iff_of_not_is_max (ha : ¬ is_max a) : succ a ≤ b ↔ a < b :=
⟨(lt_succ_of_not_is_max ha).trans_le, succ_le_of_lt⟩

lemma succ_lt_succ_iff_of_not_is_max (ha : ¬ is_max a) (hb : ¬ is_max b) :
  succ a < succ b ↔ a < b :=
by rw [lt_succ_iff_of_not_is_max hb, succ_le_iff_of_not_is_max ha]

lemma succ_le_succ_iff_of_not_is_max (ha : ¬ is_max a) (hb : ¬ is_max b) :
  succ a ≤ succ b ↔ a ≤ b :=
by rw [succ_le_iff_of_not_is_max ha, lt_succ_iff_of_not_is_max hb]

@[simp, mono] lemma succ_le_succ (h : a ≤ b) : succ a ≤ succ b :=
begin
  by_cases hb : is_max b,
  { by_cases hba : b ≤ a,
    { exact (hb $ hba.trans $ le_succ _).trans (le_succ _) },
    { exact succ_le_of_lt ((h.lt_of_not_le hba).trans_le $ le_succ b) } },
  { rwa [succ_le_iff_of_not_is_max (λ ha, hb $ ha.mono h), lt_succ_iff_of_not_is_max hb] }
end

lemma succ_mono : monotone (succ : α → α) := λ a b, succ_le_succ

lemma le_succ_iterate (k : ℕ) (x : α) : x ≤ (succ^[k] x) :=
begin
  conv_lhs { rw (by simp only [function.iterate_id, id.def] : x = (id^[k] x)) },
  exact monotone.le_iterate_of_le succ_mono le_succ k x,
end

lemma is_max_iterate_succ_of_eq_of_lt {n m : ℕ}
  (h_eq : (succ^[n] a) = (succ^[m] a)) (h_lt : n < m) :
  is_max (succ^[n] a) :=
begin
  refine max_of_succ_le (le_trans _ h_eq.symm.le),
  have : succ (succ^[n] a) = (succ^[n + 1] a), by rw function.iterate_succ',
  rw this,
  have h_le : n + 1 ≤ m := nat.succ_le_of_lt h_lt,
  exact monotone.monotone_iterate_of_le_map succ_mono (le_succ a) h_le,
end

lemma is_max_iterate_succ_of_eq_of_ne {n m : ℕ}
  (h_eq : (succ^[n] a) = (succ^[m] a)) (h_ne : n ≠ m) :
  is_max (succ^[n] a) :=
begin
  cases le_total n m,
  { exact is_max_iterate_succ_of_eq_of_lt h_eq (lt_of_le_of_ne h h_ne), },
  { rw h_eq,
    exact is_max_iterate_succ_of_eq_of_lt h_eq.symm (lt_of_le_of_ne h h_ne.symm), },
end

lemma Iio_succ_of_not_is_max (ha : ¬ is_max a) : Iio (succ a) = Iic a :=
set.ext $ λ x, lt_succ_iff_of_not_is_max ha

lemma Ici_succ_of_not_is_max (ha : ¬ is_max a) : Ici (succ a) = Ioi a :=
set.ext $ λ x, succ_le_iff_of_not_is_max ha

lemma Ico_succ_right_of_not_is_max (hb : ¬ is_max b) : Ico a (succ b) = Icc a b :=
by rw [←Ici_inter_Iio, Iio_succ_of_not_is_max hb, Ici_inter_Iic]

lemma Ioo_succ_right_of_not_is_max (hb : ¬ is_max b) : Ioo a (succ b) = Ioc a b :=
by rw [←Ioi_inter_Iio, Iio_succ_of_not_is_max hb, Ioi_inter_Iic]

lemma Icc_succ_left_of_not_is_max (ha : ¬ is_max a) : Icc (succ a) b = Ioc a b :=
by rw [←Ici_inter_Iic, Ici_succ_of_not_is_max ha, Ioi_inter_Iic]

lemma Ico_succ_left_of_not_is_max (ha : ¬ is_max a) : Ico (succ a) b = Ioo a b :=
by rw [←Ici_inter_Iio, Ici_succ_of_not_is_max ha, Ioi_inter_Iio]

section no_max_order
variables [no_max_order α]

lemma lt_succ (a : α) : a < succ a := lt_succ_of_not_is_max $ not_is_max a
@[simp] lemma lt_succ_iff : a < succ b ↔ a ≤ b := lt_succ_iff_of_not_is_max $ not_is_max b
@[simp] lemma succ_le_iff : succ a ≤ b ↔ a < b := succ_le_iff_of_not_is_max $ not_is_max a

lemma succ_le_succ_iff : succ a ≤ succ b ↔ a ≤ b := by simp
lemma succ_lt_succ_iff : succ a < succ b ↔ a < b := by simp

alias succ_le_succ_iff ↔ le_of_succ_le_succ _
alias succ_lt_succ_iff ↔ lt_of_succ_lt_succ succ_lt_succ

lemma succ_strict_mono : strict_mono (succ : α → α) := λ a b, succ_lt_succ

lemma covby_succ (a : α) : a ⋖ succ a := covby_succ_of_not_is_max $ not_is_max a

@[simp] lemma Iio_succ (a : α) : Iio (succ a) = Iic a := Iio_succ_of_not_is_max $ not_is_max _
@[simp] lemma Ici_succ (a : α) : Ici (succ a) = Ioi a := Ici_succ_of_not_is_max $ not_is_max _

@[simp] lemma Ico_succ_right (a b : α) : Ico a (succ b) = Icc a b :=
Ico_succ_right_of_not_is_max $ not_is_max _

@[simp] lemma Ioo_succ_right (a b : α) : Ioo a (succ b) = Ioc a b :=
Ioo_succ_right_of_not_is_max $ not_is_max _

@[simp] lemma Icc_succ_left (a b : α) : Icc (succ a) b = Ioc a b :=
Icc_succ_left_of_not_is_max $ not_is_max _

@[simp] lemma Ico_succ_left (a b : α) : Ico (succ a) b = Ioo a b :=
Ico_succ_left_of_not_is_max $ not_is_max _

end no_max_order
end preorder

section partial_order
variables [partial_order α] [succ_order α] {a b : α}

@[simp] lemma succ_eq_iff_is_max : succ a = a ↔ is_max a :=
⟨λ h, max_of_succ_le h.le, λ h, h.eq_of_ge $ le_succ _⟩

alias succ_eq_iff_is_max ↔ _ _root_.is_max.succ_eq

lemma succ_eq_succ_iff_of_not_is_max (ha : ¬ is_max a) (hb : ¬ is_max b) :
  succ a = succ b ↔ a = b :=
by rw [eq_iff_le_not_lt, eq_iff_le_not_lt,
  succ_le_succ_iff_of_not_is_max ha hb, succ_lt_succ_iff_of_not_is_max ha hb]

lemma le_le_succ_iff : a ≤ b ∧ b ≤ succ a ↔ b = a ∨ b = succ a :=
begin
  refine ⟨λ h, or_iff_not_imp_left.2 $ λ hba : b ≠ a,
    h.2.antisymm (succ_le_of_lt $ h.1.lt_of_ne $ hba.symm), _⟩,
  rintro (rfl | rfl),
  { exact ⟨le_rfl, le_succ b⟩ },
  { exact ⟨le_succ a, le_rfl⟩ }
end

lemma _root_.covby.succ_eq (h : a ⋖ b) : succ a = b :=
(succ_le_of_lt h.lt).eq_of_not_lt $ λ h', h.2 (lt_succ_of_not_is_max h.lt.not_is_max) h'

lemma _root_.wcovby.le_succ (h : a ⩿ b) : b ≤ succ a :=
begin
  obtain h | rfl := h.covby_or_eq,
  { exact h.succ_eq.ge },
  { exact le_succ _ }
end

lemma le_succ_iff_eq_or_le : a ≤ succ b ↔ a = succ b ∨ a ≤ b :=
begin
  by_cases hb : is_max b,
  { rw [hb.succ_eq, or_iff_right_of_imp le_of_eq] },
  { rw [←lt_succ_iff_of_not_is_max hb, le_iff_eq_or_lt] }
end

lemma lt_succ_iff_eq_or_lt_of_not_is_max (hb : ¬ is_max b) : a < succ b ↔ a = b ∨ a < b :=
(lt_succ_iff_of_not_is_max hb).trans le_iff_eq_or_lt

lemma Iic_succ (a : α) : Iic (succ a) = insert (succ a) (Iic a) := ext $ λ _, le_succ_iff_eq_or_le

lemma Icc_succ_right (h : a ≤ succ b) : Icc a (succ b) = insert (succ b) (Icc a b) :=
by simp_rw [←Ici_inter_Iic, Iic_succ, inter_insert_of_mem (mem_Ici.2 h)]

lemma Ioc_succ_right (h : a < succ b) : Ioc a (succ b) = insert (succ b) (Ioc a b) :=
by simp_rw [←Ioi_inter_Iic, Iic_succ, inter_insert_of_mem (mem_Ioi.2 h)]

lemma Iio_succ_eq_insert_of_not_is_max (h : ¬is_max a) : Iio (succ a) = insert a (Iio a) :=
ext $ λ _, lt_succ_iff_eq_or_lt_of_not_is_max h

lemma Ico_succ_right_eq_insert_of_not_is_max (h₁ : a ≤ b) (h₂ : ¬is_max b) :
  Ico a (succ b) = insert b (Ico a b) :=
by simp_rw [←Iio_inter_Ici, Iio_succ_eq_insert_of_not_is_max h₂, insert_inter_of_mem (mem_Ici.2 h₁)]

lemma Ioo_succ_right_eq_insert_of_not_is_max (h₁ : a < b) (h₂ : ¬is_max b) :
  Ioo a (succ b) = insert b (Ioo a b) :=
by simp_rw [←Iio_inter_Ioi, Iio_succ_eq_insert_of_not_is_max h₂, insert_inter_of_mem (mem_Ioi.2 h₁)]

section no_max_order
variables [no_max_order α]

@[simp] lemma succ_eq_succ_iff : succ a = succ b ↔ a = b :=
succ_eq_succ_iff_of_not_is_max (not_is_max a) (not_is_max b)

lemma succ_injective : injective (succ : α → α) := λ a b, succ_eq_succ_iff.1
lemma succ_ne_succ_iff : succ a ≠ succ b ↔ a ≠ b := succ_injective.ne_iff

alias succ_ne_succ_iff ↔ _ succ_ne_succ

lemma lt_succ_iff_eq_or_lt : a < succ b ↔ a = b ∨ a < b := lt_succ_iff.trans le_iff_eq_or_lt

lemma succ_eq_iff_covby : succ a = b ↔ a ⋖ b :=
⟨by { rintro rfl, exact covby_succ _ }, covby.succ_eq⟩

lemma Iio_succ_eq_insert (a : α) : Iio (succ a) = insert a (Iio a) :=
Iio_succ_eq_insert_of_not_is_max $ not_is_max a

lemma Ico_succ_right_eq_insert (h : a ≤ b) : Ico a (succ b) = insert b (Ico a b) :=
Ico_succ_right_eq_insert_of_not_is_max h $ not_is_max b

lemma Ioo_succ_right_eq_insert (h : a < b) : Ioo a (succ b) = insert b (Ioo a b) :=
Ioo_succ_right_eq_insert_of_not_is_max h $ not_is_max b

end no_max_order

section order_top
variables [order_top α]

@[simp] lemma succ_top : succ (⊤ : α) = ⊤ := is_max_top.succ_eq

@[simp] lemma succ_le_iff_eq_top : succ a ≤ a ↔ a = ⊤ := succ_le_iff_is_max.trans is_max_iff_eq_top
@[simp] lemma lt_succ_iff_ne_top : a < succ a ↔ a ≠ ⊤ :=
lt_succ_iff_not_is_max.trans not_is_max_iff_ne_top

end order_top

section order_bot
variable [order_bot α]

@[simp] lemma lt_succ_bot_iff [no_max_order α] : a < succ ⊥ ↔ a = ⊥ :=
by rw [lt_succ_iff, le_bot_iff]

lemma le_succ_bot_iff : a ≤ succ ⊥ ↔ a = ⊥ ∨ a = succ ⊥ :=
by rw [le_succ_iff_eq_or_le, le_bot_iff, or_comm]

variable [nontrivial α]

lemma bot_lt_succ (a : α) : ⊥ < succ a :=
(lt_succ_of_not_is_max not_is_max_bot).trans_le $ succ_mono bot_le

lemma succ_ne_bot (a : α) : succ a ≠ ⊥ := (bot_lt_succ a).ne'

end order_bot
end partial_order

/-- There is at most one way to define the successors in a `partial_order`. -/
instance [partial_order α] : subsingleton (succ_order α) :=
⟨begin
  introsI h₀ h₁,
  ext a,
  by_cases ha : is_max a,
  { exact (@is_max.succ_eq _ _ h₀ _ ha).trans ha.succ_eq.symm },
  { exact @covby.succ_eq _ _ h₀ _ _ (covby_succ_of_not_is_max ha) }
end⟩

section complete_lattice
variables [complete_lattice α] [succ_order α]

lemma succ_eq_infi (a : α) : succ a = ⨅ b (h : a < b), b :=
begin
  refine le_antisymm (le_infi (λ b, le_infi succ_le_of_lt)) _,
  obtain rfl | ha := eq_or_ne a ⊤,
  { rw succ_top,
    exact le_top },
  exact infi₂_le _ (lt_succ_iff_ne_top.2 ha),
end

end complete_lattice

/-! ### Predecessor order -/

section preorder
variables [preorder α] [pred_order α] {a b : α}

/-- The predecessor of an element. If `a` is not minimal, then `pred a` is the greatest element less
than `a`. If `a` is minimal, then `pred a = a`. -/
def pred : α → α := pred_order.pred

lemma pred_le : ∀ a : α, pred a ≤ a := pred_order.pred_le
lemma min_of_le_pred {a : α} : a ≤ pred a → is_min a := pred_order.min_of_le_pred
lemma le_pred_of_lt {a b : α} : a < b → a ≤ pred b := pred_order.le_pred_of_lt
lemma le_of_pred_lt {a b : α} : pred a < b → a ≤ b := pred_order.le_of_pred_lt

@[simp] lemma le_pred_iff_is_min : a ≤ pred a ↔ is_min a := ⟨min_of_le_pred, λ h, h $ pred_le _⟩

@[simp] lemma pred_lt_iff_not_is_min : pred a < a ↔ ¬ is_min a :=
⟨not_is_min_of_lt, λ ha, (pred_le a).lt_of_not_le $ λ h, ha $ min_of_le_pred h⟩

alias pred_lt_iff_not_is_min ↔ _ pred_lt_of_not_is_min

lemma pred_wcovby (a : α) : pred a ⩿ a :=
⟨pred_le a, λ b hb, (le_of_pred_lt hb).not_lt⟩

lemma pred_covby_of_not_is_min (h : ¬ is_min a) : pred a ⋖ a :=
(pred_wcovby a).covby_of_lt $ pred_lt_of_not_is_min h

lemma pred_lt_iff_of_not_is_min (ha : ¬ is_min a) : pred a < b ↔ a ≤ b :=
⟨le_of_pred_lt, (pred_lt_of_not_is_min ha).trans_le⟩

lemma le_pred_iff_of_not_is_min (ha : ¬ is_min a) : b ≤ pred a ↔ b < a :=
⟨λ h, h.trans_lt $ pred_lt_of_not_is_min ha, le_pred_of_lt⟩

@[simp, mono] lemma pred_le_pred {a b : α} (h : a ≤ b) : pred a ≤ pred b := succ_le_succ h.dual

lemma pred_mono : monotone (pred : α → α) := λ a b, pred_le_pred

lemma pred_iterate_le (k : ℕ) (x : α) : (pred^[k] x) ≤ x :=
begin
  conv_rhs { rw (by simp only [function.iterate_id, id.def] : x = (id^[k] x)) },
  exact monotone.iterate_le_of_le pred_mono pred_le k x,
end

lemma is_min_iterate_pred_of_eq_of_lt {n m : ℕ}
  (h_eq : (pred^[n] a) = (pred^[m] a)) (h_lt : n < m) :
  is_min (pred^[n] a) :=
@is_max_iterate_succ_of_eq_of_lt αᵒᵈ _ _ _ _ _ h_eq h_lt

lemma is_min_iterate_pred_of_eq_of_ne {n m : ℕ}
  (h_eq : (pred^[n] a) = (pred^[m] a)) (h_ne : n ≠ m) :
  is_min (pred^[n] a) :=
@is_max_iterate_succ_of_eq_of_ne αᵒᵈ _ _ _ _ _ h_eq h_ne

lemma Ioi_pred_of_not_is_min (ha : ¬ is_min a) : Ioi (pred a) = Ici a :=
set.ext $ λ x, pred_lt_iff_of_not_is_min ha

lemma Iic_pred_of_not_is_min (ha : ¬ is_min a) : Iic (pred a) = Iio a :=
set.ext $ λ x, le_pred_iff_of_not_is_min ha

lemma Ioc_pred_left_of_not_is_min (ha : ¬ is_min a) : Ioc (pred a) b = Icc a b :=
by rw [←Ioi_inter_Iic, Ioi_pred_of_not_is_min ha, Ici_inter_Iic]

lemma Ioo_pred_left_of_not_is_min (ha : ¬ is_min a) : Ioo (pred a) b = Ico a b :=
by rw [←Ioi_inter_Iio, Ioi_pred_of_not_is_min ha, Ici_inter_Iio]

lemma Icc_pred_right_of_not_is_min (ha : ¬ is_min b) : Icc a (pred b) = Ico a b :=
by rw [←Ici_inter_Iic, Iic_pred_of_not_is_min ha, Ici_inter_Iio]

lemma Ioc_pred_right_of_not_is_min (ha : ¬ is_min b) : Ioc a (pred b) = Ioo a b :=
by rw [←Ioi_inter_Iic, Iic_pred_of_not_is_min ha, Ioi_inter_Iio]

section no_min_order
variables [no_min_order α]

lemma pred_lt (a : α) : pred a < a := pred_lt_of_not_is_min $ not_is_min a
@[simp] lemma pred_lt_iff : pred a < b ↔ a ≤ b := pred_lt_iff_of_not_is_min $ not_is_min a
@[simp] lemma le_pred_iff : a ≤ pred b ↔ a < b := le_pred_iff_of_not_is_min $ not_is_min b

lemma pred_le_pred_iff : pred a ≤ pred b ↔ a ≤ b := by simp
lemma pred_lt_pred_iff : pred a < pred b ↔ a < b := by simp

alias pred_le_pred_iff ↔ le_of_pred_le_pred _
alias pred_lt_pred_iff ↔ lt_of_pred_lt_pred pred_lt_pred

lemma pred_strict_mono : strict_mono (pred : α → α) := λ a b, pred_lt_pred

lemma pred_covby (a : α) : pred a ⋖ a := pred_covby_of_not_is_min $ not_is_min a

@[simp] lemma Ioi_pred (a : α) : Ioi (pred a) = Ici a := Ioi_pred_of_not_is_min $ not_is_min a
@[simp] lemma Iic_pred (a : α) : Iic (pred a) = Iio a := Iic_pred_of_not_is_min $ not_is_min a

@[simp] lemma Ioc_pred_left (a b : α) : Ioc (pred a) b = Icc a b :=
Ioc_pred_left_of_not_is_min $ not_is_min _

@[simp] lemma Ioo_pred_left (a b : α) : Ioo (pred a) b = Ico a b :=
Ioo_pred_left_of_not_is_min $ not_is_min _

@[simp] lemma Icc_pred_right (a b : α) : Icc a (pred b) = Ico a b :=
Icc_pred_right_of_not_is_min $ not_is_min _

@[simp] lemma Ioc_pred_right (a b : α) : Ioc a (pred b) = Ioo a b :=
Ioc_pred_right_of_not_is_min $ not_is_min _

end no_min_order
end preorder

section partial_order
variables [partial_order α] [pred_order α] {a b : α}

@[simp] lemma pred_eq_iff_is_min : pred a = a ↔ is_min a :=
⟨λ h, min_of_le_pred h.ge, λ h, h.eq_of_le $ pred_le _⟩

alias pred_eq_iff_is_min ↔ _ _root_.is_min.pred_eq

lemma pred_le_le_iff {a b : α} : pred a ≤ b ∧ b ≤ a ↔ b = a ∨ b = pred a :=
begin
  refine ⟨λ h, or_iff_not_imp_left.2 $ λ hba : b ≠ a,
    (le_pred_of_lt $ h.2.lt_of_ne hba).antisymm h.1, _⟩,
  rintro (rfl | rfl),
  { exact ⟨pred_le b, le_rfl⟩ },
  { exact ⟨le_rfl, pred_le a⟩ }
end

lemma _root_.covby.pred_eq {a b : α} (h : a ⋖ b) : pred b = a :=
(le_pred_of_lt h.lt).eq_of_not_gt $ λ h', h.2 h' $ pred_lt_of_not_is_min h.lt.not_is_min

lemma _root_.wcovby.pred_le (h : a ⩿ b) : pred b ≤ a :=
begin
  obtain h | rfl := h.covby_or_eq,
  { exact h.pred_eq.le },
  { exact pred_le _ }
end

lemma pred_le_iff_eq_or_le : pred a ≤ b ↔ b = pred a ∨ a ≤ b :=
begin
  by_cases ha : is_min a,
  { rw [ha.pred_eq, or_iff_right_of_imp ge_of_eq] },
  { rw [←pred_lt_iff_of_not_is_min ha, le_iff_eq_or_lt, eq_comm] }
end

lemma pred_lt_iff_eq_or_lt_of_not_is_min (ha : ¬ is_min a) : pred a < b ↔ a = b ∨ a < b :=
(pred_lt_iff_of_not_is_min ha).trans le_iff_eq_or_lt

lemma Ici_pred (a : α) : Ici (pred a) = insert (pred a) (Ici a) := ext $ λ _, pred_le_iff_eq_or_le

lemma Ioi_pred_eq_insert_of_not_is_min (ha : ¬ is_min a) :
  Ioi (pred a) = insert a (Ioi a) :=
begin
  ext x, simp only [insert, mem_set_of, @eq_comm _ x a],
  exact pred_lt_iff_eq_or_lt_of_not_is_min ha
end

lemma Icc_pred_left (h : pred a ≤ b) : Icc (pred a) b = insert (pred a) (Icc a b) :=
by simp_rw [←Ici_inter_Iic, Ici_pred, insert_inter_of_mem (mem_Iic.2 h)]

lemma Ico_pred_left (h : pred a < b) : Ico (pred a) b = insert (pred a) (Ico a b) :=
by simp_rw [←Ici_inter_Iio, Ici_pred, insert_inter_of_mem (mem_Iio.2 h)]

section no_min_order
variables [no_min_order α]

@[simp] lemma pred_eq_pred_iff : pred a = pred b ↔ a = b :=
by simp_rw [eq_iff_le_not_lt, pred_le_pred_iff, pred_lt_pred_iff]

lemma pred_injective : injective (pred : α → α) := λ a b, pred_eq_pred_iff.1
lemma pred_ne_pred_iff : pred a ≠ pred b ↔ a ≠ b := pred_injective.ne_iff

alias pred_ne_pred_iff ↔ _ pred_ne_pred

lemma pred_lt_iff_eq_or_lt : pred a < b ↔ a = b ∨ a < b := pred_lt_iff.trans le_iff_eq_or_lt

lemma pred_eq_iff_covby : pred b = a ↔ a ⋖ b :=
⟨by { rintro rfl, exact pred_covby _ }, covby.pred_eq⟩

lemma Ioi_pred_eq_insert (a : α) : Ioi (pred a) = insert a (Ioi a) :=
ext $ λ _, pred_lt_iff_eq_or_lt.trans $ or_congr_left' eq_comm

lemma Ico_pred_right_eq_insert (h : a ≤ b) : Ioc (pred a) b = insert a (Ioc a b) :=
by simp_rw [←Ioi_inter_Iic, Ioi_pred_eq_insert, insert_inter_of_mem (mem_Iic.2 h)]

lemma Ioo_pred_right_eq_insert (h : a < b) : Ioo (pred a) b = insert a (Ioo a b) :=
by simp_rw [←Ioi_inter_Iio, Ioi_pred_eq_insert, insert_inter_of_mem (mem_Iio.2 h)]

end no_min_order

section order_bot
variables [order_bot α]

@[simp] lemma pred_bot : pred (⊥ : α) = ⊥ := is_min_bot.pred_eq

@[simp] lemma le_pred_iff_eq_bot : a ≤ pred a ↔ a = ⊥ := @succ_le_iff_eq_top αᵒᵈ _ _ _ _
@[simp] lemma pred_lt_iff_ne_bot : pred a < a ↔ a ≠ ⊥ := @lt_succ_iff_ne_top αᵒᵈ _ _ _ _

end order_bot

section order_top

variable [order_top α]

@[simp] lemma pred_top_lt_iff [no_min_order α] : pred ⊤ < a ↔ a = ⊤ :=
@lt_succ_bot_iff αᵒᵈ _ _ _ _ _

lemma pred_top_le_iff : pred ⊤ ≤ a ↔ a = ⊤ ∨ a = pred ⊤ := @le_succ_bot_iff αᵒᵈ _ _ _ _

variable [nontrivial α]

lemma pred_lt_top (a : α) : pred a < ⊤ :=
(pred_mono le_top).trans_lt $ pred_lt_of_not_is_min not_is_min_top

lemma pred_ne_top (a : α) : pred a ≠ ⊤ := (pred_lt_top a).ne

end order_top
end partial_order

/-- There is at most one way to define the predecessors in a `partial_order`. -/
instance [partial_order α] : subsingleton (pred_order α) :=
⟨begin
  introsI h₀ h₁,
  ext a,
  by_cases ha : is_min a,
  { exact (@is_min.pred_eq _ _ h₀ _ ha).trans ha.pred_eq.symm },
  { exact @covby.pred_eq _ _ h₀ _ _ (pred_covby_of_not_is_min ha) }
end⟩

section complete_lattice
variables [complete_lattice α] [pred_order α]

lemma pred_eq_supr (a : α) : pred a = ⨆ b (h : b < a), b :=
begin
  refine le_antisymm _ (supr_le (λ b, supr_le le_pred_of_lt)),
  obtain rfl | ha := eq_or_ne a ⊥,
  { rw pred_bot,
    exact bot_le },
  { exact @le_supr₂ _ _ (λ b, b < a) _ (λ a _, a) (pred a) (pred_lt_iff_ne_bot.2 ha) }
end

end complete_lattice

/-! ### Successor-predecessor orders -/

section succ_pred_order
variables [partial_order α] [succ_order α] [pred_order α] {a b : α}

@[simp] lemma succ_pred_of_not_is_min (h : ¬ is_min a) : succ (pred a) = a :=
(pred_covby_of_not_is_min h).succ_eq
@[simp] lemma pred_succ_of_not_is_max (h : ¬ is_max a) : pred (succ a) = a :=
(covby_succ_of_not_is_max h).pred_eq

@[simp] lemma succ_pred [no_min_order α] (a : α) : succ (pred a) = a := (pred_covby _).succ_eq
@[simp] lemma pred_succ [no_max_order α] (a : α) : pred (succ a) = a := (covby_succ _).pred_eq

lemma pred_succ_iterate_of_not_is_max (i : α) (n : ℕ) (hin : ¬ is_max (succ^[n-1] i)) :
  pred^[n] (succ^[n] i) = i :=
begin
  induction n with n hn,
  { simp only [function.iterate_zero, id.def], },
  rw [nat.succ_sub_succ_eq_sub, nat.sub_zero] at hin,
  have h_not_max : ¬ is_max (succ^[n - 1] i),
  { cases n,
    { simpa using hin, },
    rw [nat.succ_sub_succ_eq_sub, nat.sub_zero] at hn ⊢,
    have h_sub_le : (succ^[n] i) ≤ (succ^[n.succ] i),
    { rw function.iterate_succ',
      exact le_succ _, },
    refine λ h_max, hin (λ j hj, _),
    have hj_le : j ≤ (succ^[n] i) := h_max (h_sub_le.trans hj),
    exact hj_le.trans h_sub_le, },
  rw [function.iterate_succ, function.iterate_succ'],
  simp only [function.comp_app],
  rw pred_succ_of_not_is_max hin,
  exact hn h_not_max,
end

lemma succ_pred_iterate_of_not_is_min (i : α) (n : ℕ) (hin : ¬ is_min (pred^[n-1] i)) :
  succ^[n] (pred^[n] i) = i :=
@pred_succ_iterate_of_not_is_max αᵒᵈ _ _ _ i n hin

end succ_pred_order

end order

open order

/-! ### `with_bot`, `with_top`
Adding a greatest/least element to a `succ_order` or to a `pred_order`.

As far as successors and predecessors are concerned, there are four ways to add a bottom or top
element to an order:
* Adding a `⊤` to an `order_top`: Preserves `succ` and `pred`.
* Adding a `⊤` to a `no_max_order`: Preserves `succ`. Never preserves `pred`.
* Adding a `⊥` to an `order_bot`: Preserves `succ` and `pred`.
* Adding a `⊥` to a `no_min_order`: Preserves `pred`. Never preserves `succ`.
where "preserves `(succ/pred)`" means
`(succ/pred)_order α → (succ/pred)_order ((with_top/with_bot) α)`.
-/

namespace with_top

/-! #### Adding a `⊤` to an `order_top` -/

section succ
variables [decidable_eq α] [partial_order α] [order_top α] [succ_order α]

instance : succ_order (with_top α) :=
{ succ := λ a, match a with
    | ⊤        := ⊤
    | (some a) := ite (a = ⊤) ⊤ (some (succ a))
  end,
  le_succ := λ a, begin
    cases a,
    { exact le_top },
    change _ ≤ ite _ _ _,
    split_ifs,
    { exact le_top },
    { exact some_le_some.2 (le_succ a) }
  end,
  max_of_succ_le := λ a ha, begin
    cases a,
    { exact is_max_top },
    change ite _ _ _ ≤ _ at ha,
    split_ifs at ha with ha',
    { exact (not_top_le_coe _ ha).elim },
    { rw [some_le_some, succ_le_iff_eq_top] at ha,
      exact (ha' ha).elim }
  end,
  succ_le_of_lt := λ a b h, begin
    cases b,
    { exact le_top },
    cases a,
    { exact (not_top_lt h).elim },
    rw some_lt_some at h,
    change ite _ _ _ ≤ _,
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
    change _ < ite _ _ _ at h,
    rw some_le_some,
    split_ifs at h with hb,
    { rw hb,
      exact le_top },
    { exact le_of_lt_succ (some_lt_some.1 h) }
  end }

@[simp] lemma succ_coe_top : succ ↑(⊤ : α) = (⊤ : with_top α) := dif_pos rfl
lemma succ_coe_of_ne_top {a : α} (h : a ≠ ⊤) : succ (↑a : with_top α) = ↑(succ a) :=
dif_neg h

end succ

section pred
variables [preorder α] [order_top α] [pred_order α]

instance : pred_order (with_top α) :=
{ pred := λ a, match a with
    | ⊤        := some ⊤
    | (some a) := some (pred a)
  end,
  pred_le := λ a, match a with
    | ⊤        := le_top
    | (some a) := some_le_some.2 (pred_le a)
  end,
  min_of_le_pred := λ a ha, begin
    cases a,
    { exact ((coe_lt_top (⊤ : α)).not_le ha).elim },
    { exact (min_of_le_pred $ some_le_some.1 ha).with_top }
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

@[simp] lemma pred_top : pred (⊤ : with_top α) = ↑(⊤ : α) := rfl
@[simp] lemma pred_coe (a : α) : pred (↑a : with_top α) = ↑(pred a) := rfl

end pred

/-! #### Adding a `⊤` to a `no_max_order` -/

section succ
variables [preorder α] [no_max_order α] [succ_order α]

instance succ_order_of_no_max_order : succ_order (with_top α) :=
{ succ := λ a, match a with
    | ⊤        := ⊤
    | (some a) := some (succ a)
  end,
  le_succ := λ a, begin
    cases a,
    { exact le_top },
    { exact some_le_some.2 (le_succ a) }
  end,
  max_of_succ_le := λ a ha, begin
    cases a,
    { exact is_max_top },
    { exact (not_is_max _ $ max_of_succ_le $ some_le_some.1 ha).elim }
  end,
  succ_le_of_lt := λ a b h, begin
    cases a,
    { exact (not_top_lt h).elim },
    cases b,
    { exact le_top},
    { exact some_le_some.2 (succ_le_of_lt $ some_lt_some.1 h) }
  end,
  le_of_lt_succ := λ a b h, begin
    cases a,
    { exact (not_top_lt h).elim },
    cases b,
    { exact le_top },
    { exact some_le_some.2 (le_of_lt_succ $ some_lt_some.1 h) }
  end }

@[simp] lemma succ_coe (a : α) : succ (↑a : with_top α) = ↑(succ a) := rfl

end succ

section pred
variables [preorder α] [no_max_order α]

instance [hα : nonempty α] : is_empty (pred_order (with_top α)) :=
⟨begin
  introI,
  cases h : pred (⊤ : with_top α) with a ha,
  { exact hα.elim (λ a, (min_of_le_pred h.ge).not_lt $ coe_lt_top a) },
  { obtain ⟨c, hc⟩ := exists_gt a,
    rw [←some_lt_some, ←h] at hc,
    exact (le_of_pred_lt hc).not_lt (some_lt_none _) }
end⟩

end pred

end with_top

namespace with_bot

/-! #### Adding a `⊥` to an `order_bot` -/

section succ
variables [preorder α] [order_bot α] [succ_order α]

instance : succ_order (with_bot α) :=
{ succ := λ a, match a with
    | ⊥        := some ⊥
    | (some a) := some (succ a)
  end,
  le_succ := λ a, match a with
    | ⊥        := bot_le
    | (some a) := some_le_some.2 (le_succ a)
  end,
  max_of_succ_le := λ a ha, begin
    cases a,
    { exact ((none_lt_some (⊥ : α)).not_le ha).elim },
    { exact (max_of_succ_le $ some_le_some.1 ha).with_bot }
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

@[simp] lemma succ_bot : succ (⊥ : with_bot α) = ↑(⊥ : α) := rfl
@[simp] lemma succ_coe (a : α) : succ (↑a : with_bot α) = ↑(succ a) := rfl

end succ

section pred
variables [decidable_eq α] [partial_order α] [order_bot α] [pred_order α]

instance : pred_order (with_bot α) :=
{ pred := λ a, match a with
    | ⊥        := ⊥
    | (some a) := ite (a = ⊥) ⊥ (some (pred a))
  end,
  pred_le := λ a, begin
    cases a,
    { exact bot_le },
    change ite _ _ _ ≤ _,
    split_ifs,
    { exact bot_le },
    { exact some_le_some.2 (pred_le a) }
  end,
  min_of_le_pred := λ a ha, begin
    cases a,
    { exact is_min_bot },
    change _ ≤ ite _ _ _ at ha,
    split_ifs at ha with ha',
    { exact (not_coe_le_bot _ ha).elim },
    { rw [some_le_some, le_pred_iff_eq_bot] at ha,
      exact (ha' ha).elim }
  end,
  le_pred_of_lt := λ a b h, begin
    cases a,
    { exact bot_le },
    cases b,
    { exact (not_lt_bot h).elim },
    rw some_lt_some at h,
    change _ ≤ ite _ _ _,
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
    change ite _ _ _ < _ at h,
    rw some_le_some,
    split_ifs at h with ha,
    { rw ha,
      exact bot_le },
    { exact le_of_pred_lt (some_lt_some.1 h) }
  end }

@[simp] lemma pred_coe_bot : pred ↑(⊥ : α) = (⊥ : with_bot α) := dif_pos rfl
lemma pred_coe_of_ne_bot {a : α} (h : a ≠ ⊥) : pred (↑a : with_bot α) = ↑(pred a) :=
dif_neg h

end pred

/-! #### Adding a `⊥` to a `no_min_order` -/

section succ
variables [preorder α] [no_min_order α]

instance [hα : nonempty α] : is_empty (succ_order (with_bot α)) :=
⟨begin
  introI,
  cases h : succ (⊥ : with_bot α) with a ha,
  { exact hα.elim (λ a, (max_of_succ_le h.le).not_lt $ bot_lt_coe a) },
  { obtain ⟨c, hc⟩ := exists_lt a,
    rw [←some_lt_some, ←h] at hc,
    exact (le_of_lt_succ hc).not_lt (none_lt_some _) }
end⟩

end succ

section pred
variables [preorder α] [no_min_order α] [pred_order α]

instance pred_order_of_no_min_order : pred_order (with_bot α) :=
{ pred := λ a, match a with
    | ⊥        := ⊥
    | (some a) := some (pred a)
  end,
  pred_le := λ a, begin
    cases a,
    { exact bot_le },
    { exact some_le_some.2 (pred_le a) }
  end,
  min_of_le_pred := λ a ha, begin
    cases a,
    { exact is_min_bot },
    { exact (not_is_min _ $ min_of_le_pred $ some_le_some.1 ha).elim }
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

@[simp] lemma pred_coe (a : α) : pred (↑a : with_bot α) = ↑(pred a) := rfl

end pred
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

instance : is_pred_archimedean αᵒᵈ := ⟨λ a b h, by convert exists_succ_iterate_of_le h.of_dual⟩

lemma has_le.le.exists_succ_iterate (h : a ≤ b) : ∃ n, succ^[n] a = b :=
exists_succ_iterate_of_le h

lemma exists_succ_iterate_iff_le : (∃ n, succ^[n] a = b) ↔ a ≤ b :=
begin
  refine ⟨_, exists_succ_iterate_of_le⟩,
  rintro ⟨n, rfl⟩,
  exact id_le_iterate_of_id_le le_succ n a,
end

/-- Induction principle on a type with a `succ_order` for all elements above a given element `m`. -/
@[elab_as_eliminator] lemma succ.rec {P : α → Prop} {m : α}
  (h0 : P m) (h1 : ∀ n, m ≤ n → P n → P (succ n)) ⦃n : α⦄ (hmn : m ≤ n) : P n :=
begin
  obtain ⟨n, rfl⟩ := hmn.exists_succ_iterate, clear hmn,
  induction n with n ih,
  { exact h0 },
  { rw [function.iterate_succ_apply'], exact h1 _ (id_le_iterate_of_id_le le_succ n m) ih }
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

instance : is_succ_archimedean αᵒᵈ := ⟨λ a b h, by convert exists_pred_iterate_of_le h.of_dual⟩

lemma has_le.le.exists_pred_iterate (h : a ≤ b) : ∃ n, pred^[n] b = a :=
exists_pred_iterate_of_le h

lemma exists_pred_iterate_iff_le : (∃ n, pred^[n] b = a) ↔ a ≤ b :=
@exists_succ_iterate_iff_le αᵒᵈ _ _ _ _ _

/-- Induction principle on a type with a `pred_order` for all elements below a given element `m`. -/
@[elab_as_eliminator] lemma pred.rec {P : α → Prop} {m : α}
  (h0 : P m) (h1 : ∀ n, n ≤ m → P n → P (pred n)) ⦃n : α⦄ (hmn : n ≤ m) : P n :=
@succ.rec αᵒᵈ _ _ _ _ _ h0 h1 _ hmn

lemma pred.rec_iff {p : α → Prop} (hsucc : ∀ a, p a ↔ p (pred a)) {a b : α} (h : a ≤ b) :
  p a ↔ p b :=
(@succ.rec_iff αᵒᵈ _ _ _ _ hsucc _ _ h).symm

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

section is_well_order
variables [linear_order α]

@[priority 100]
instance is_well_order.to_is_pred_archimedean [h : is_well_order α (<)] [pred_order α] :
  is_pred_archimedean α :=
⟨λ a, begin
  refine well_founded.fix h.wf (λ b ih hab, _),
  replace hab := hab.eq_or_lt,
  rcases hab with rfl | hab,
  { exact ⟨0, rfl⟩ },
  cases le_or_lt b (pred b) with hb hb,
  { cases (min_of_le_pred hb).not_lt hab },
  obtain ⟨k, hk⟩ := ih (pred b) hb (le_pred_of_lt hab),
  refine ⟨k + 1, _⟩,
  rw [iterate_add_apply, iterate_one, hk],
end⟩

@[priority 100]
instance is_well_order.to_is_succ_archimedean [h : is_well_order α (>)] [succ_order α] :
  is_succ_archimedean α :=
by convert @order_dual.is_succ_archimedean αᵒᵈ _ _ _

end is_well_order

section order_bot
variables [preorder α] [order_bot α] [succ_order α] [is_succ_archimedean α]

lemma succ.rec_bot (p : α → Prop) (hbot : p ⊥) (hsucc : ∀ a, p a → p (succ a)) (a : α) : p a :=
succ.rec hbot (λ x _ h, hsucc x h) (bot_le : ⊥ ≤ a)

end order_bot

section order_top
variables [preorder α] [order_top α] [pred_order α] [is_pred_archimedean α]

lemma pred.rec_top (p : α → Prop) (htop : p ⊤) (hpred : ∀ a, p a → p (pred a)) (a : α) : p a :=
pred.rec htop (λ x _ h, hpred x h) (le_top : a ≤ ⊤)

end order_top
