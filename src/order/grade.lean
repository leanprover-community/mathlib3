/-
Copyright (c) 2022 Yaël Dillies, Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Violeta Hernández Palacios, Grayson Burton, Vladimir Ivanov
-/
import data.nat.interval
import data.int.succ_pred
import order.atoms

/-!
# Graded orders

This file defines graded orders, also known as ranked orders.

A `𝕆`-graded order is an order `α` equipped with a distinguished "grade" function `α → 𝕆` which
should be understood as giving the "height" of the elements. Usual graded orders are `ℕ`-graded,
cograded orders are `order_dual ℕ`-graded, but we can also grade by `ℤ`, and polytopes are naturally
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

variables {𝕆 α β : Type*}

section
variables {a b : Prop}

lemma iff.not_left (h : a ↔ ¬ b) : ¬ a ↔ b := h.not.trans not_not
lemma iff.not_right (h : ¬ a ↔ b) : a ↔ ¬ b := not_not.symm.trans h.not

end

section
variables [preorder 𝕆] [preorder α] {f : α → 𝕆} {a : α}

lemma strict_mono.is_max_of_apply (hf : strict_mono f) (ha : is_max (f a)) : is_max a :=
by { by_contra, obtain ⟨b, hb⟩ := not_is_max_iff.1 h, exact (hf hb).not_is_max ha }

lemma strict_mono.is_min_of_apply (hf : strict_mono f) (ha : is_min (f a)) : is_min a :=
by { by_contra, obtain ⟨b, hb⟩ := not_is_min_iff.1 h, exact (hf hb).not_is_min ha }

lemma strict_anti.is_max_of_apply (hf : strict_anti f) (ha : is_min (f a)) : is_max a :=
by { by_contra, obtain ⟨b, hb⟩ := not_is_max_iff.1 h, exact (hf hb).not_is_min ha }

lemma strict_anti.is_min_of_apply (hf : strict_anti f) (ha : is_max (f a)) : is_min a :=
by { by_contra, obtain ⟨b, hb⟩ := not_is_min_iff.1 h, exact (hf hb).not_is_max ha }

end

section order_top
variables [partial_order α] [preorder 𝕆] [order_top α] {f : α → 𝕆} {a : α}

@[simp] lemma not_lt_top_iff : ¬ a < ⊤ ↔ a = ⊤ := lt_top_iff_ne_top.not_left

lemma strict_mono.apply_eq_top_iff (hf : strict_mono f) : f a = f ⊤ ↔ a = ⊤ :=
⟨λ h, not_lt_top_iff.1 $ λ ha, (hf ha).ne h, congr_arg _⟩

lemma strict_anti.apply_eq_top_iff (hf : strict_anti f) : f a = f ⊤ ↔ a = ⊤ :=
⟨λ h, not_lt_top_iff.1 $ λ ha, (hf ha).ne' h, congr_arg _⟩

end order_top

section order_bot
variables [partial_order α] [preorder 𝕆] [order_bot α] {f : α → 𝕆} {a : α}

@[simp] lemma not_bot_lt_iff : ¬ ⊥ < a ↔ a = ⊥ := bot_lt_iff_ne_bot.not_left

lemma strict_mono.apply_eq_bot_iff (hf : strict_mono f) : f a = f ⊥ ↔ a = ⊥ :=
⟨λ h, not_bot_lt_iff.1 $ λ ha, (hf ha).ne' h, congr_arg _⟩

lemma strict_anti.apply_eq_bot_iff (hf : strict_anti f) : f a = f ⊥ ↔ a = ⊥ :=
⟨λ h, not_bot_lt_iff.1 $ λ ha, (hf ha).ne h, congr_arg _⟩

end order_bot

lemma fin.coe_strict_mono {n : ℕ} : strict_mono (coe : fin n → ℕ) := λ _ _, id
lemma nat.cast_strict_mono [ordered_semiring α] [nontrivial α] : strict_mono (coe : ℕ → α) :=
λ _ _, nat.cast_lt.2
lemma int.coe_nat_strict_mono : strict_mono (coe : ℕ → ℤ) := λ _ _, int.coe_nat_lt.2

/-- A strictly monotone function from a linear order as an order embedding. -/
protected def strict_mono.order_embedding [linear_order α] [preorder β] (f : α → β)
  (hf : strict_mono f) : α ↪o β := ⟨⟨f, hf.injective⟩, λ _ _, hf.le_iff_le⟩

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

section preorder
variables [preorder 𝕆]

section preorder
variables [preorder α]

section grade_order
variables (𝕆) [grade_order 𝕆 α] {a b : α}

/-- The grade of an element in a graded order. Morally, this is the number of elements you need to
go down by to get to `⊥`. -/
def grade (a : α) : 𝕆 := grade_order.grade a

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
end preorder

lemma grade_mono [partial_order α] [grade_order 𝕆 α] : monotone (grade 𝕆 : α → 𝕆) :=
grade_strict_mono.monotone

section linear_order
variables [linear_order α] [grade_order 𝕆 α] {a b : α}

lemma grade_injective : function.injective (grade 𝕆 : α → 𝕆) := grade_strict_mono.injective
@[simp] lemma grade_le_grade_iff : grade 𝕆 a ≤ grade 𝕆 b ↔ a ≤ b := grade_strict_mono.le_iff_le
@[simp] lemma grade_lt_grade_iff : grade 𝕆 a < grade 𝕆 b ↔ a < b := grade_strict_mono.lt_iff_lt
@[simp] lemma grade_eq_grade_iff : grade 𝕆 a = grade 𝕆 b ↔ a = b := grade_injective.eq_iff
lemma grade_ne_grade_iff : grade 𝕆 a ≠ grade 𝕆 b ↔ a ≠ b := grade_injective.ne_iff

lemma grade_covby_grade_iff : grade 𝕆 a ⋖ grade 𝕆 b ↔ a ⋖ b :=
(covby_iff_lt_covby_grade.trans $ and_iff_right_of_imp $ λ h, grade_lt_grade_iff.1 h.1).symm

end linear_order
end preorder

section partial_order
variables [partial_order 𝕆] [preorder α]

@[simp] lemma grade_bot [order_bot 𝕆] [order_bot α] [grade_min_order 𝕆 α] : grade 𝕆 (⊥ : α) = ⊥ :=
(is_min_bot.grade _).eq_bot

@[simp] lemma grade_top [order_top 𝕆] [order_top α] [grade_max_order 𝕆 α] : grade 𝕆 (⊤ : α) = ⊤ :=
(is_max_top.grade _).eq_top

end partial_order

/-! ### Instances -/

variables [preorder 𝕆] [preorder α] [preorder β]

instance preorder.to_grade_bounded_order : grade_bounded_order α α :=
{ grade := id,
  is_min_grade := λ _, id,
  is_max_grade := λ _, id,
  grade_strict_mono := strict_mono_id,
  covby_grade := λ a b, id }

@[simp] lemma grade_self (a : α) : grade α a = a := rfl

/-! #### Dual -/

instance [grade_order 𝕆 α] : grade_order (order_dual 𝕆) (order_dual α) :=
{ grade := to_dual ∘ grade 𝕆 ∘ of_dual,
  grade_strict_mono := grade_strict_mono.dual,
  covby_grade := λ a b h, (h.of_dual.grade _).to_dual }

instance [grade_max_order 𝕆 α] : grade_min_order (order_dual 𝕆) (order_dual α) :=
{ is_min_grade := λ _, is_max.grade _,
  ..order_dual.grade_order }

instance [grade_min_order 𝕆 α] : grade_max_order (order_dual 𝕆) (order_dual α) :=
{ is_max_grade := λ _, is_min.grade _,
  ..order_dual.grade_order }

instance [grade_bounded_order 𝕆 α] : grade_bounded_order (order_dual 𝕆) (order_dual α) :=
{ ..order_dual.grade_min_order, ..order_dual.grade_max_order }

@[simp] lemma grade_to_dual [grade_order 𝕆 α] (a : α) :
  grade (order_dual 𝕆) (to_dual a) = to_dual (grade 𝕆 a) := rfl
@[simp] lemma grade_of_dual [grade_order 𝕆 α] (a : order_dual α) :
  grade 𝕆 (of_dual a) = of_dual (grade (order_dual 𝕆) a) := rfl

/-! #### `fin n`-graded to `ℕ`-graded to `ℤ`-graded -/

/-- A `fin n`-graded order is also `ℕ`-graded. We do not mark this an instance because `n` is not
inferrable. -/
@[reducible] -- See note [reducible non-instances]
def grade_order.fin_to_nat {n : ℕ} [grade_order (fin n) α] : grade_order ℕ α :=
{ grade := coe ∘ grade (fin n),
  grade_strict_mono := fin.coe_strict_mono.comp grade_strict_mono,
  covby_grade := λ a b h, (h.grade $ fin n).coe_fin }

/-- A `fin n`-graded order is also `ℕ`-graded. We do not mark this an instance because `n` is not
inferrable. -/
@[reducible] -- See note [reducible non-instances]
def grade_min_order.fin_to_nat {n : ℕ} [grade_min_order (fin n) α] : grade_min_order ℕ α :=
{ grade := coe ∘ grade (fin n),
  is_min_grade := λ a h, begin
    unfreezingI { cases n },
    { exact (@fin.elim0 (λ _, false) $ grade (fin 0) a).elim },
    dsimp,
    rw [(h.grade _).eq_bot, fin.bot_eq_zero],
    exact is_min_bot,
  end,
  ..grade_order.fin_to_nat }

instance grade_order.nat_to_int [grade_order ℕ α] : grade_order ℤ α :=
{ grade := coe ∘ grade ℕ,
  grade_strict_mono := int.coe_nat_strict_mono.comp grade_strict_mono,
  covby_grade := λ a b h, (h.grade _).cast_int }

/-! #### Lifting a graded order -/

/-- Lifts a graded order along an order embedding. -/
def grade_order.lift [grade_order 𝕆 β] {f : α ↪o β} (hf : (set.range f).ord_connected) :
  grade_order 𝕆 α :=
{ grade := λ a, grade 𝕆 (f a),
  grade_strict_mono := grade_strict_mono.comp f.strict_mono,
  covby_grade := λ a b hab, (hf.image_covby_image_iff.2 hab).grade _ }
