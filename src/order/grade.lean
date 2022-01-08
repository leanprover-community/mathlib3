/-
Copyright (c) 2022 Yaël Dillies, Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Violeta Hernández Palacios, Grayson Burton, Vladimir Ivanov
-/
import data.nat.interval
import data.nat.succ_pred
import order.atoms

/-!
# Graded orders

This file defines graded orders, also known as ranked orders.

A graded order is an order in which every element has some finite "height", that

## Main declarations

* `grade_order`: Graded order.
* `grade`: The grade of an element.
* `order_embedding.grade`: The grade of an element in a linear order as an order embedding.

## Implementation notes

The standard approach is to define graded orders as the bounded orders whose flags (maximal chains)
all have the same finite length (see Stanley p. 99).

However, this means that graded orders all have a top and that we must reconstruct the grade of an
element by how many elements we need to go down to reach `⊥`. Unpractical, really.

Instead, we define graded orders by their grade function, without talking about flags yet.

## References

* [Konrad Engel, *Sperner Theory*][engel1997]
* [Richard Stanley, *Enumerative Combinatorics*][stanley2012]
-/

open finset nat order_dual

variables {α β : Type*}

/-- A graded order is an order equipped with a grade function which tells how far a given element is
away from `⊥`. Precisely, `grade a` is the height of `a` in the Hasse diagram of `α`. -/
class grade_order (α : Type*) [preorder α] [order_bot α] :=
(grade : α → ℕ)
(grade_bot : grade ⊥ = 0)
(strict_mono : strict_mono grade)
(grade_of_covers ⦃a b : α⦄ : a ⋖ b → grade a + 1 = grade b)

section preorder
variables [preorder α] [order_bot α] [grade_order α] {a b : α}

/-- The grade of an element in a graded order. Morally, this is the number of elements you need to
go down by to get to `⊥`. -/
def grade (a : α) : ℕ := grade_order.grade a

lemma grade_bot : grade (⊥ : α) = 0 := grade_order.grade_bot
lemma grade_strict_mono : strict_mono (grade : α → ℕ) := grade_order.strict_mono

protected lemma covers.grade (h : a ⋖ b) : grade a + 1 = grade b := grade_order.grade_of_covers h

/-- If two elements in a graded partial order cover each other, so do their grades. This is just a
restatement of the covering condition. -/
lemma covers.grade_covers (h : a ⋖ b) : grade a ⋖ grade b := covers_iff_succ_eq.2 h.grade

lemma covers_iff_grade_succ_eq_lt : a ⋖ b ↔ grade a + 1 = grade b ∧ a < b :=
⟨λ h, ⟨h.grade, h.1⟩, λ h, ⟨h.2, λ c ha hb,
  (covers_iff_succ_eq.2 h.1).2 (grade_strict_mono ha) $ grade_strict_mono hb⟩⟩

end preorder

section partial_order
variables [partial_order α]

section order_bot
variables [order_bot α] [grade_order α] {a b : α}

lemma grade_mono : monotone (grade : α → ℕ) := grade_strict_mono.monotone

/-- An element has grade `0` iff it is the bottom element. -/
@[simp]
lemma grade_eq_zero_iff (a : α) : grade a = 0 ↔ a = ⊥ :=
begin
  refine ⟨λ h, _, _⟩,
  { by_contra ha,
    exact (h.le.trans grade_bot.ge).not_lt (grade_strict_mono $ bot_lt_iff_ne_bot.2 ha) },
  { rintro rfl,
    exact grade_bot }
end

end order_bot

section bounded_order
variables [bounded_order α] [grade_order α] {a b : α}

lemma grade_le_grade_top (a : α) : grade a ≤ grade (⊤ : α) := grade_mono le_top

lemma has_lt.lt.grade_lt_grade_top (h : a < b) : grade a < grade (⊤ : α) :=
grade_strict_mono $ h.trans_le le_top

@[simp] lemma grade_lt_grade_top_of_nonempty_Ioi (h : (set.Ioi a).nonempty) :
  grade a < grade (⊤ : α) :=
has_lt.lt.grade_lt_grade_top h.some_mem

/-- An element has the top grade iff it is the top element. -/
@[simp]
lemma grade_eq_grade_top_iff (a : α) : grade a = grade (⊤ : α) ↔ a = ⊤ :=
begin
  refine ⟨λ h, _, λ h, by rw h⟩,
  by_contra ha,
  exact not_le_of_lt (grade_strict_mono $ lt_top_iff_ne_top.2 ha) h.ge,
end

variables (α)

open order_dual

instance : grade_order (order_dual α) :=
{ grade := λ a, grade (⊤ : α) - grade (of_dual a),
  grade_bot := nat.sub_self _,
  strict_mono := λ (a b : α) hab,
    (tsub_lt_tsub_iff_left_of_le $ grade_le_grade_top a).2 (grade_strict_mono hab),
  grade_of_covers := λ a b h, begin
    rw [←h.of_dual.grade, ←tsub_tsub],
    exact (tsub_add_cancel_of_le $ nat.succ_le_iff.2 $ nat.sub_pos_of_lt $
      h.1.of_dual.grade_lt_grade_top),
  end }

/-- `order_dual α` have the same top grade as `α`. -/
@[simp] lemma grade_top_dual : grade (⊤ : order_dual α) = grade (⊤ : α) :=
by { change grade ⊤ - grade ⊥ = grade ⊤, rw [grade_bot, nat.sub_zero] }

end bounded_order
end partial_order

section linear_order
variables [linear_order α]

section order_bot
variables [order_bot α] [grade_order α] {a b : α}

/-- The grade of a linear order is injective. -/
lemma grade_injective : function.injective (grade : α → ℕ) := grade_strict_mono.injective
lemma grade_le_iff_le {a b : α} : grade a ≤ grade b ↔ a ≤ b := grade_strict_mono.le_iff_le
lemma grade_lt_iff_lt {a b : α} : grade a < grade b ↔ a < b := grade_strict_mono.lt_iff_lt
lemma grade_eq_iff_eq {a b : α} : grade a = grade b ↔ a = b := grade_injective.eq_iff
lemma grade_ne_iff_ne {a b : α} : grade a ≠ grade b ↔ a ≠ b := grade_injective.ne_iff

/-- `grade` as an order embedding into `ℕ` for a linear order `α`. -/
protected def order_embedding.grade : α ↪o ℕ :=
{ to_fun := _,
  inj' := grade_injective,
  map_rel_iff' := λ _ _, grade_le_iff_le }

lemma covers_iff_grade : a ⋖ b ↔ grade a + 1 = grade b :=
⟨covers.grade, λ h, covers_iff_grade_succ_eq_lt.2 ⟨h, grade_lt_iff_lt.1 $ succ_le_iff.1 h.le⟩⟩

/-- Two elements in a linear order cover each other iff their grades do. -/
@[imp] lemma grade_covers_grade_iff (a b : α) : grade a ⋖ grade b ↔ a ⋖ b :=
⟨λ h, covers_iff_grade.2 $ covers_iff_succ_eq.1 h, covers.grade_covers⟩

/-- Constructs a locally finite order instance from a grade function on a linear order. -/
noncomputable def grade_order.to_locally_finite_order : locally_finite_order α :=
{ finset_Icc := λ a b, (Icc (grade a) (grade b)).preimage grade (grade_injective.inj_on _),
  finset_Ico := λ a b, (Ico (grade a) (grade b)).preimage grade (grade_injective.inj_on _),
  finset_Ioc := λ a b, (Ioc (grade a) (grade b)).preimage grade (grade_injective.inj_on _),
  finset_Ioo := λ a b, (Ioo (grade a) (grade b)).preimage grade (grade_injective.inj_on _),
  finset_mem_Icc := λ a b x,
    by rw [mem_preimage, mem_Icc, grade_strict_mono.le_iff_le, grade_strict_mono.le_iff_le],
  finset_mem_Ico := λ a b x,
    by rw [mem_preimage, mem_Ico, grade_strict_mono.le_iff_le, grade_strict_mono.lt_iff_lt],
  finset_mem_Ioc := λ a b x,
    by rw [mem_preimage, mem_Ioc, grade_strict_mono.le_iff_le, grade_strict_mono.lt_iff_lt],
  finset_mem_Ioo := λ a b x,
    by rw [mem_preimage, mem_Ioo, grade_strict_mono.lt_iff_lt, grade_strict_mono.lt_iff_lt] }

end order_bot
end linear_order

/-! ### Instances -/

/-! #### Natural numbers -/

namespace nat

instance : grade_order ℕ :=
{ grade := id,
  grade_bot := rfl,
  strict_mono := strict_mono_id,
  grade_of_covers := λ a b, covers_iff_succ_eq.1 }

protected lemma grade (n : ℕ) : grade n = n := rfl

end nat

/-! #### `fin` -/

namespace fin

instance (n : ℕ) : grade_order (fin (n + 1)) :=
{ grade := coe,
  grade_bot := rfl,
  strict_mono := strict_mono_id,
  grade_of_covers := λ _ _ h, nat.covers_iff_succ_eq.1 $ (fin.val_covers_iff _ _).2 h }

protected lemma grade {n : ℕ} (k : fin (n + 1)) : grade k = k := rfl

end fin

/-! #### `unique` -/

section unique
variables (α) [unique α] [preorder α]

/-- In terms of polytopes, a *nullitope*. -/
def unique.to_grade_order [order_bot α] : grade_order α :=
{ grade := λ _, 0,
  grade_bot := rfl,
  strict_mono := subsingleton.strict_mono _,
  grade_of_covers := λ a b h, (h.1.ne $ subsingleton.elim _ _).elim }

variables {α}

protected lemma unique.grade [grade_order α] (a : α) : grade (a : α) = 0 := rfl

instance : grade_order unit := unique.to_grade_order

@[simp] protected lemma unit.grade (a : unit) : grade (a : unit) = 0 := rfl

end unique

/-! #### Simple orders -/

section is_simple_order
variables (α)

/-- In terms of polytopes, a *point*. -/
def is_simple_order.to_grade_order [decidable_eq α] [preorder α] [bounded_order α]
  [is_simple_order α] :
  grade_order α :=
{ grade := λ a, if a = ⊥ then 0 else 1,
  grade_bot := if_pos rfl,
  strict_mono := λ a b h, begin
    convert zero_lt_one,
    { exact if_pos (is_simple_order.eq_bot_of_lt h) },
    { exact if_neg (ne_bot_of_lt h) },
    { apply_instance }
  end,
  grade_of_covers := λ a b h, begin
    convert zero_add 1,
    { exact if_pos (is_simple_order.eq_bot_of_lt h.1) },
    { exact if_neg (ne_bot_of_lt h.1) }
  end }

variables {α}

lemma is_simple_order.grade_top [partial_order α] [bounded_order α] [is_simple_order α]
  [grade_order α] : grade (⊤ : α) = 1 :=
by { rw [←bot_covers_top.grade, grade_bot], apply_instance }

instance : grade_order bool := is_simple_order.to_grade_order

@[simp] protected lemma bool.grade_top : grade (⊤ : bool) = 1 := is_simple_order.grade_top

end is_simple_order

/-! #### Lifting a graded order -/

section lift
variables [preorder α] [order_bot α] [preorder β] [order_bot β] [grade_order β] {a b : α}
  {f : α ↪o β}

/-- Lifts a graded order along an order embedding. -/
def grade_order.lift (hbot : f ⊥ = ⊥) (h : (set.range f).ord_connected) : grade_order α :=
{ grade := λ a, grade (f a),
  grade_bot := by rw [hbot, grade_bot],
  strict_mono := grade_strict_mono.comp f.strict_mono,
  grade_of_covers := λ a b hab, ((image_covers_iff h).2 hab).grade }

end lift
