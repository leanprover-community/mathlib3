/-
Copyright (c) 2022 Yaël Dillies, Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Violeta Hernández Palacios, Grayson Burton, Vladimir Ivanov
-/
import data.finset.basic
import data.int.succ_pred

/-!
# Graded orders

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines graded orders, also known as ranked orders.

A `𝕆`-graded order is an order `α` equipped with a distinguished "grade" function `α → 𝕆` which
should be understood as giving the "height" of the elements. Usual graded orders are `ℕ`-graded,
cograded orders are `ℕᵒᵈ`-graded, but we can also grade by `ℤ`, and polytopes are naturally
`fin n`-graded.

Visually, `grade ℕ a` is the height of `a` in the Hasse diagram of `α`.

## Main declarations

* `grade_order`: Graded order.
* `grade_min_order`: Graded order where minimal elements have minimal grades.
* `grade_max_order`: Graded order where maximal elements have maximal grades.
* `grade_bounded_order`: Graded order where minimal elements have minimal grades and maximal
  elements have maximal grades.
* `grade`: The grade of an element. Because an order can admit several gradings, the first argument
  is the order we grade by.
* `grade_max_order`: Graded orders with maximal elements. All maximal elements have the same grade.
* `max_grade`: The maximum grade in a `grade_max_order`.
* `order_embedding.grade`: The grade of an element in a linear order as an order embedding.

## How to grade your order

Here are the translations between common references and our `grade_order`:
* [Stanley][stanley2012] defines a graded order of rank `n` as an order where all maximal chains
  have "length" `n` (so the number of elements of a chain is `n + 1`). This corresponds to
  `grade_bounded_order (fin (n + 1)) α`.
* [Engel][engel1997]'s ranked orders are somewhere between `grade_order ℕ α` and
  `grade_min_order ℕ α`, in that he requires `∃ a, is_min a ∧ grade ℕ a + 0` rather than
  `∀ a, is_min a → grade ℕ a = 0`. He defines a graded order as an order where all minimal elements
  have grade `0` and all maximal elements have the same grade. This is roughly a less bundled
  version of `grade_bounded_order (fin n) α`, assuming we discard orders with infinite chains.

## Implementation notes

One possible definition of graded orders is as the bounded orders whose flags (maximal chains)
all have the same finite length (see Stanley p. 99). However, this means that all graded orders must
have minimal and maximal elements and that the grade is not data.

Instead, we define graded orders by their grade function, without talking about flags yet.

## References

* [Konrad Engel, *Sperner Theory*][engel1997]
* [Richard Stanley, *Enumerative Combinatorics*][stanley2012]
-/

set_option old_structure_cmd true

open finset nat order_dual

variables {𝕆 ℙ α β : Type*}

/-- An `𝕆`-graded order is an order `α` equipped with a strictly monotone function `grade 𝕆 : α → 𝕆`
which preserves order covering (`covby`). -/
class grade_order (𝕆 α : Type*) [preorder 𝕆] [preorder α] :=
(grade : α → 𝕆)
(grade_strict_mono : strict_mono grade)
(covby_grade ⦃a b : α⦄ : a ⋖ b → grade a ⋖ grade b)

/-- A `𝕆`-graded order where minimal elements have minimal grades. -/
class grade_min_order (𝕆 α : Type*) [preorder 𝕆] [preorder α] extends grade_order 𝕆 α :=
(is_min_grade ⦃a : α⦄ : is_min a → is_min (grade a))

/-- A `𝕆`-graded order where maximal elements have maximal grades. -/
class grade_max_order (𝕆 α : Type*) [preorder 𝕆] [preorder α] extends grade_order 𝕆 α :=
(is_max_grade ⦃a : α⦄ : is_max a → is_max (grade a))

/-- A `𝕆`-graded order where minimal elements have minimal grades and maximal elements have maximal
grades. -/
class grade_bounded_order (𝕆 α : Type*) [preorder 𝕆] [preorder α]
  extends grade_min_order 𝕆 α, grade_max_order 𝕆 α

section preorder -- grading
variables [preorder 𝕆]

section preorder -- graded order
variables [preorder α]

section grade_order
variables (𝕆) [grade_order 𝕆 α] {a b : α}

/-- The grade of an element in a graded order. Morally, this is the number of elements you need to
go down by to get to `⊥`. -/
def grade : α → 𝕆 := grade_order.grade

protected lemma covby.grade (h : a ⋖ b) : grade 𝕆 a ⋖ grade 𝕆 b := grade_order.covby_grade h

variables {𝕆}

lemma grade_strict_mono : strict_mono (grade 𝕆 : α → 𝕆) := grade_order.grade_strict_mono

lemma covby_iff_lt_covby_grade : a ⋖ b ↔ a < b ∧ grade 𝕆 a ⋖ grade 𝕆 b :=
⟨λ h, ⟨h.1, h.grade _⟩, and.imp_right $ λ h c ha hb,
  h.2 (grade_strict_mono ha) $ grade_strict_mono hb⟩

end grade_order

section grade_min_order
variables (𝕆) [grade_min_order 𝕆 α] {a : α}

protected lemma is_min.grade (h : is_min a) : is_min (grade 𝕆 a) := grade_min_order.is_min_grade h

variables {𝕆}

@[simp] lemma is_min_grade_iff : is_min (grade 𝕆 a) ↔ is_min a :=
⟨grade_strict_mono.is_min_of_apply, is_min.grade _⟩

end grade_min_order

section grade_max_order
variables (𝕆) [grade_max_order 𝕆 α] {a : α}

protected lemma is_max.grade (h : is_max a) : is_max (grade 𝕆 a) := grade_max_order.is_max_grade h

variables {𝕆}

@[simp] lemma is_max_grade_iff : is_max (grade 𝕆 a) ↔ is_max a :=
⟨grade_strict_mono.is_max_of_apply, is_max.grade _⟩

end grade_max_order
end preorder -- graded order

lemma grade_mono [partial_order α] [grade_order 𝕆 α] : monotone (grade 𝕆 : α → 𝕆) :=
grade_strict_mono.monotone

section linear_order -- graded order
variables [linear_order α] [grade_order 𝕆 α] {a b : α}

lemma grade_injective : function.injective (grade 𝕆 : α → 𝕆) := grade_strict_mono.injective
@[simp] lemma grade_le_grade_iff : grade 𝕆 a ≤ grade 𝕆 b ↔ a ≤ b := grade_strict_mono.le_iff_le
@[simp] lemma grade_lt_grade_iff : grade 𝕆 a < grade 𝕆 b ↔ a < b := grade_strict_mono.lt_iff_lt
@[simp] lemma grade_eq_grade_iff : grade 𝕆 a = grade 𝕆 b ↔ a = b := grade_injective.eq_iff
lemma grade_ne_grade_iff : grade 𝕆 a ≠ grade 𝕆 b ↔ a ≠ b := grade_injective.ne_iff

lemma grade_covby_grade_iff : grade 𝕆 a ⋖ grade 𝕆 b ↔ a ⋖ b :=
(covby_iff_lt_covby_grade.trans $ and_iff_right_of_imp $ λ h, grade_lt_grade_iff.1 h.1).symm

end linear_order -- graded order
end preorder -- grading

section partial_order
variables [partial_order 𝕆] [preorder α]

@[simp] lemma grade_bot [order_bot 𝕆] [order_bot α] [grade_min_order 𝕆 α] : grade 𝕆 (⊥ : α) = ⊥ :=
(is_min_bot.grade _).eq_bot

@[simp] lemma grade_top [order_top 𝕆] [order_top α] [grade_max_order 𝕆 α] : grade 𝕆 (⊤ : α) = ⊤ :=
(is_max_top.grade _).eq_top

end partial_order

/-! ### Instances -/

variables [preorder 𝕆] [preorder ℙ] [preorder α] [preorder β]

instance preorder.to_grade_bounded_order : grade_bounded_order α α :=
{ grade := id,
  is_min_grade := λ _, id,
  is_max_grade := λ _, id,
  grade_strict_mono := strict_mono_id,
  covby_grade := λ a b, id }

@[simp] lemma grade_self (a : α) : grade α a = a := rfl

/-! #### Dual -/

instance [grade_order 𝕆 α] : grade_order 𝕆ᵒᵈ αᵒᵈ :=
{ grade := to_dual ∘ grade 𝕆 ∘ of_dual,
  grade_strict_mono := grade_strict_mono.dual,
  covby_grade := λ a b h, (h.of_dual.grade _).to_dual }

instance [grade_max_order 𝕆 α] : grade_min_order 𝕆ᵒᵈ αᵒᵈ :=
{ is_min_grade := λ _, is_max.grade _,
  ..order_dual.grade_order }

instance [grade_min_order 𝕆 α] : grade_max_order 𝕆ᵒᵈ αᵒᵈ :=
{ is_max_grade := λ _, is_min.grade _,
  ..order_dual.grade_order }

instance [grade_bounded_order 𝕆 α] : grade_bounded_order 𝕆ᵒᵈ αᵒᵈ :=
{ ..order_dual.grade_min_order, ..order_dual.grade_max_order }

@[simp] lemma grade_to_dual [grade_order 𝕆 α] (a : α) :
  grade 𝕆ᵒᵈ (to_dual a) = to_dual (grade 𝕆 a) := rfl
@[simp] lemma grade_of_dual [grade_order 𝕆 α] (a : αᵒᵈ) :
  grade 𝕆 (of_dual a) = of_dual (grade 𝕆ᵒᵈ a) := rfl

/-! #### Lifting a graded order -/

/-- Lifts a graded order along a strictly monotone function. -/
@[reducible] -- See note [reducible non-instances]
def grade_order.lift_left [grade_order 𝕆 α] (f : 𝕆 → ℙ) (hf : strict_mono f)
  (hcovby : ∀ a b, a ⋖ b → f a ⋖ f b) : grade_order ℙ α :=
{ grade := f ∘ grade 𝕆,
  grade_strict_mono := hf.comp grade_strict_mono,
  covby_grade := λ a b h, hcovby _ _ $ h.grade _ }

/-- Lifts a graded order along a strictly monotone function. -/
@[reducible] -- See note [reducible non-instances]
def grade_min_order.lift_left [grade_min_order 𝕆 α] (f : 𝕆 → ℙ) (hf : strict_mono f)
  (hcovby : ∀ a b, a ⋖ b → f a ⋖ f b) (hmin : ∀ a, is_min a → is_min (f a)) :
  grade_min_order ℙ α :=
{ is_min_grade := λ a ha, hmin _ $ ha.grade _,
  ..grade_order.lift_left f hf hcovby }

/-- Lifts a graded order along a strictly monotone function. -/
@[reducible] -- See note [reducible non-instances]
def grade_max_order.lift_left [grade_max_order 𝕆 α] (f : 𝕆 → ℙ) (hf : strict_mono f)
  (hcovby : ∀ a b, a ⋖ b → f a ⋖ f b) (hmax : ∀ a, is_max a → is_max (f a)) :
  grade_max_order ℙ α :=
{ is_max_grade := λ a ha, hmax _ $ ha.grade _,
  ..grade_order.lift_left f hf hcovby }

/-- Lifts a graded order along a strictly monotone function. -/
@[reducible] -- See note [reducible non-instances]
def grade_bounded_order.lift_left [grade_bounded_order 𝕆 α] (f : 𝕆 → ℙ) (hf : strict_mono f)
  (hcovby : ∀ a b, a ⋖ b → f a ⋖ f b) (hmin : ∀ a, is_min a → is_min (f a))
  (hmax : ∀ a, is_max a → is_max (f a)) :
  grade_bounded_order ℙ α :=
{ ..grade_min_order.lift_left f hf hcovby hmin, ..grade_max_order.lift_left f hf hcovby hmax }

/-- Lifts a graded order along a strictly monotone function. -/
@[reducible] -- See note [reducible non-instances]
def grade_order.lift_right [grade_order 𝕆 β] (f : α → β) (hf : strict_mono f)
  (hcovby : ∀ a b, a ⋖ b → f a ⋖ f b) : grade_order 𝕆 α :=
{ grade := grade 𝕆 ∘ f,
  grade_strict_mono := grade_strict_mono.comp hf,
  covby_grade := λ a b h, (hcovby _ _ h).grade _ }

/-- Lifts a graded order along a strictly monotone function. -/
@[reducible] -- See note [reducible non-instances]
def grade_min_order.lift_right [grade_min_order 𝕆 β] (f : α → β) (hf : strict_mono f)
  (hcovby : ∀ a b, a ⋖ b → f a ⋖ f b) (hmin : ∀ a, is_min a → is_min (f a)) :
  grade_min_order 𝕆 α :=
{ is_min_grade := λ a ha, (hmin _ ha).grade _,
  ..grade_order.lift_right f hf hcovby }

/-- Lifts a graded order along a strictly monotone function. -/
@[reducible] -- See note [reducible non-instances]
def grade_max_order.lift_right [grade_max_order 𝕆 β] (f : α → β) (hf : strict_mono f)
  (hcovby : ∀ a b, a ⋖ b → f a ⋖ f b) (hmax : ∀ a, is_max a → is_max (f a)) :
  grade_max_order 𝕆 α :=
{ is_max_grade := λ a ha, (hmax _ ha).grade _,
  ..grade_order.lift_right f hf hcovby }

/-- Lifts a graded order along a strictly monotone function. -/
@[reducible] -- See note [reducible non-instances]
def grade_bounded_order.lift_right [grade_bounded_order 𝕆 β] (f : α → β) (hf : strict_mono f)
  (hcovby : ∀ a b, a ⋖ b → f a ⋖ f b) (hmin : ∀ a, is_min a → is_min (f a))
  (hmax : ∀ a, is_max a → is_max (f a)) : grade_bounded_order 𝕆 α :=
{ ..grade_min_order.lift_right f hf hcovby hmin, ..grade_max_order.lift_right f hf hcovby hmax }

/-! #### `fin n`-graded to `ℕ`-graded to `ℤ`-graded -/

/-- A `fin n`-graded order is also `ℕ`-graded. We do not mark this an instance because `n` is not
inferrable. -/
@[reducible] -- See note [reducible non-instances]
def grade_order.fin_to_nat (n : ℕ) [grade_order (fin n) α] : grade_order ℕ α :=
grade_order.lift_left (_ : fin n → ℕ) fin.coe_strict_mono $ λ _ _, covby.coe_fin

/-- A `fin n`-graded order is also `ℕ`-graded. We do not mark this an instance because `n` is not
inferrable. -/
@[reducible] -- See note [reducible non-instances]
def grade_min_order.fin_to_nat (n : ℕ) [grade_min_order (fin n) α] : grade_min_order ℕ α :=
grade_min_order.lift_left (_ : fin n → ℕ) fin.coe_strict_mono (λ _ _, covby.coe_fin) $ λ a h, begin
    unfreezingI { cases n },
    { exact (@fin.elim0 (λ _, false) $ grade (fin 0) a).elim },
    rw [h.eq_bot, fin.bot_eq_zero],
    exact is_min_bot,
  end

instance grade_order.nat_to_int [grade_order ℕ α] : grade_order ℤ α :=
grade_order.lift_left _ int.coe_nat_strict_mono $ λ _ _, covby.cast_int
