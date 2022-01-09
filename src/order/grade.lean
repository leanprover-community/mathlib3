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

A graded order is an order with a bottom element in which every element has some finite "height",
that corresponds to how many elements you need to get down by to reach `⊥`.

## Main declarations

* `grade_order`: Graded orders.
* `grade`: The grade of an element.
* `grade_max_order`: Graded orders with maximal elements. All maximal elements have the same grade.
* `max_grade`: The maximum grade in a `grade_max_order`.
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

lemma ge_antisymm [partial_order α] {a b : α} (hab : a ≤ b) (hba : b ≤ a) : b = a :=
le_antisymm hba hab

alias ge_antisymm     ← has_le.le.antisymm'

section
variables {a b : α}

lemma has_le.le.to_dual [has_le α] (h : a ≤ b) : to_dual b ≤ to_dual a := h
lemma has_lt.lt.to_dual [has_lt α] (h : a < b) : to_dual b < to_dual a := h

end

section order_dual
variables {a b : order_dual α}

lemma has_le.le.of_dual [has_le α] (h : a ≤ b) : of_dual b ≤ of_dual a := h
lemma has_lt.lt.of_dual [has_lt α] (h : a < b) : of_dual b < of_dual a := h

end order_dual

lemma bot_is_bot [has_le α] [order_bot α] : is_bot (⊥ : α) := λ _, bot_le
lemma top_is_top [has_le α] [order_top α] : is_top (⊤ : α) := λ _, le_top

section has_le
variables [has_le α] {a b : α}

def is_min (a : α) : Prop := ∀ ⦃b⦄, b ≤ a → a ≤ b

def is_max (a : α) : Prop := ∀ ⦃b⦄, a ≤ b → b ≤ a

@[simp] lemma is_min_to_dual_iff : is_min (to_dual a) ↔ is_max a := iff.rfl
@[simp] lemma is_max_to_dual_iff : is_max (to_dual a) ↔ is_min a := iff.rfl
@[simp] lemma is_min_of_dual_iff {a : order_dual α} : is_min (of_dual a) ↔ is_max a := iff.rfl
@[simp] lemma is_max_of_dual_iff {a : order_dual α} : is_max (of_dual a) ↔ is_min a := iff.rfl

alias is_min_to_dual_iff ↔ _ is_max.to_dual
alias is_max_to_dual_iff ↔ _ is_min.to_dual
alias is_min_of_dual_iff ↔ _ is_max.of_dual
alias is_max_of_dual_iff ↔ _ is_min.of_dual

protected lemma is_bot.is_min [has_le α] {a : α} (h : is_bot a) : is_min a := λ b _, h b
protected lemma is_top.is_max [has_le α] {a : α} (h : is_top a) : is_max a := λ b _, h b

lemma bot_is_min [has_le α] [order_bot α] : is_min (⊥ : α) := bot_is_bot.is_min
lemma top_is_max [has_le α] [order_top α] : is_max (⊤ : α) := top_is_top.is_max

end has_le

section preorder
variables [preorder α] {a b : α}

lemma is_bot.mono (ha : is_bot a) (h : b ≤ a) : is_bot b := λ c, h.trans $ ha _
lemma is_top.mono (ha : is_top a) (h : a ≤ b) : is_top b := λ c, (ha _).trans h
lemma is_min.mono (ha : is_min a) (h : b ≤ a) : is_min b := λ c hc, h.trans $ ha $ hc.trans h
lemma is_max.mono (ha : is_max a) (h : a ≤ b) : is_max b := λ c hc, (ha $ h.trans hc).trans h

lemma is_min.not_lt (h : is_min a) : ¬ b < a := λ hb, hb.not_le $ h hb.le
lemma is_max.not_lt (h : is_max a) : ¬ a < b := λ hb, hb.not_le $ h hb.le

lemma is_min_iff_forall_not_lt : is_min a ↔ ∀ b, ¬ b < a :=
⟨λ h _, h.not_lt, λ h b hba, of_not_not $ λ hab, h _ $ hba.lt_of_not_le hab⟩

lemma is_max_iff_forall_not_lt : is_max a ↔ ∀ b, ¬ a < b :=
⟨λ h _, h.not_lt, λ h b hba, of_not_not $ λ hab, h _ $ hba.lt_of_not_le hab⟩

@[simp] lemma not_is_min [no_bot_order α] (a : α) : ¬ is_min a := λ h, let ⟨b, hb⟩ :=
no_bot a in h.not_lt hb

@[simp] lemma not_is_max [no_top_order α] (a : α) : ¬ is_max a := λ h, let ⟨b, hb⟩ :=
no_top a in h.not_lt hb

protected lemma subsingleton.is_bot [subsingleton α] (a : α) : is_bot a :=
λ _, (subsingleton.elim _ _).le

protected lemma subsingleton.is_top [subsingleton α] (a : α) : is_top a :=
λ _, (subsingleton.elim _ _).le

protected lemma subsingleton.is_min [subsingleton α] (a : α) : is_min a :=
(subsingleton.is_bot _).is_min

protected lemma subsingleton.is_max [subsingleton α] (a : α) : is_max a :=
(subsingleton.is_top _).is_max

end preorder

section partial_order
variables [partial_order α] {a b : α}

protected lemma is_min.eq_of_le (ha : is_min a) (h : b ≤ a) : b = a := h.antisymm $ ha h
protected lemma is_min.eq_of_ge (ha : is_min a) (h : b ≤ a) : a = b := h.antisymm' $ ha h
protected lemma is_max.eq_of_le (ha : is_max a) (h : a ≤ b) : a = b := h.antisymm $ ha h
protected lemma is_max.eq_of_ge (ha : is_max a) (h : a ≤ b) : b = a := h.antisymm' $ ha h

lemma is_min.eq_bot [order_bot α] (h : is_min a) : a = ⊥ := h.eq_of_ge bot_le
lemma is_max.eq_top [order_top α] (h : is_max a) : a = ⊤ := h.eq_of_le le_top

end partial_order

section linear_order
variables [linear_order α] {a b : α}

protected lemma is_min.is_bot (h : is_min a) : is_bot a := λ b, (le_total a b).elim id $ @h _
protected lemma is_max.is_top (h : is_max a) : is_top a := λ b, (le_total b a).elim id $ @h _

@[simp] lemma is_bot_iff_is_min : is_bot a ↔ is_min a := ⟨is_bot.is_min, is_min.is_bot⟩
@[simp] lemma is_top_iff_is_max : is_top a ↔ is_max a := ⟨is_top.is_max, is_max.is_top⟩

end linear_order

/-- A graded order is an order equipped with a grade function which tells how far a given element is
away from the minimal elements. Precisely, `grade a` is the height of `a` in the Hasse diagram of
`α`. -/
class grade_order (α : Type*) [preorder α] :=
(grade : α → ℕ)
(grade_strict_mono : strict_mono grade)
(grade_of_is_min ⦃a : α⦄ : is_min a → grade a = 0)
(grade_of_covers ⦃a b : α⦄ : a ⋖ b → grade a + 1 = grade b)

/-- A graded top order is a graded order with a maximal grade (NOT a maximal *element*). -/
class grade_max_order (α : Type*) [preorder α] extends grade_order α :=
(max_grade : ℕ)
(grade_le_max_grade (a : α) : grade a ≤ max_grade)
(grade_of_is_max ⦃a : α⦄ : is_max a → grade a = max_grade)

section grade_order
section preorder
variables [preorder α] [grade_order α] {a b : α}

/-- The grade of an element in a graded order. Morally, this is the number of elements you need to
go down by to get to `⊥`. -/
def grade (a : α) : ℕ := grade_order.grade a
lemma grade_strict_mono : strict_mono (grade : α → ℕ) := grade_order.grade_strict_mono

protected lemma is_min.grade (h : is_min a) : grade a = 0 := grade_order.grade_of_is_min h
protected lemma covers.grade (h : a ⋖ b) : grade a + 1 = grade b := grade_order.grade_of_covers h

/-- If two elements in a graded partial order cover each other, so do their grades. This is just a
restatement of the covering condition. -/
lemma covers.grade_covers (h : a ⋖ b) : grade a ⋖ grade b := covers_iff_succ_eq.2 h.grade

lemma covers_iff_grade_succ_eq_lt : a ⋖ b ↔ grade a + 1 = grade b ∧ a < b :=
⟨λ h, ⟨h.grade, h.1⟩, λ h, ⟨h.2, λ c ha hb,
  (covers_iff_succ_eq.2 h.1).2 (grade_strict_mono ha) $ grade_strict_mono hb⟩⟩

@[simp] lemma grade_eq_zero_iff : grade a = 0 ↔ is_min a :=
begin
  refine ⟨λ h b hba, _, is_min.grade⟩,
  by_contra hab,
  exact not_lt_bot ((grade_strict_mono $ hba.lt_of_not_le hab).trans_le h.le),
end

section order_bot
variables [order_bot α]

@[simp] lemma grade_bot : grade (⊥ : α) = 0 := bot_is_min.grade

end order_bot

section order_top
variables [order_top α]

lemma has_lt.lt.grade_lt_grade_top (h : a < b) : grade a < grade (⊤ : α) :=
grade_strict_mono $ h.trans_le le_top

@[simp] lemma grade_lt_grade_top_of_nonempty_Ioi (h : (set.Ioi a).nonempty) :
  grade a < grade (⊤ : α) :=
has_lt.lt.grade_lt_grade_top h.some_mem

end order_top
end preorder

section partial_order
variables [partial_order α] [grade_order α] {a b : α}

lemma grade_mono : monotone (grade : α → ℕ) := grade_strict_mono.monotone

section order_top
variables [order_top α]

lemma grade_le_grade_top (a : α) : grade a ≤ grade (⊤ : α) := grade_mono le_top

@[simp] lemma grade_eq_grade_top_iff (a : α) : grade a = grade (⊤ : α) ↔ a = ⊤ :=
begin
  refine ⟨λ h, _, congr_arg _⟩,
  by_contra ha,
  exact not_le_of_lt (grade_strict_mono $ lt_top_iff_ne_top.2 ha) h.ge,
end

/-- Upgrades a graded order with top to a graded top order. -/
@[reducible] -- See note [reducible non-instances]
def grade_order.to_grade_max_order : grade_max_order α :=
{ max_grade := grade (⊤ : α),
  grade_le_max_grade := grade_le_grade_top,
  grade_of_is_max := λ a ha, congr_arg _ ha.eq_top }

end order_top
end partial_order

section linear_order
variables [linear_order α]

section order_bot
variables [order_bot α] [grade_order α] {a b : α}

lemma grade_injective : function.injective (grade : α → ℕ) := grade_strict_mono.injective
lemma grade_le_iff_le : grade a ≤ grade b ↔ a ≤ b := grade_strict_mono.le_iff_le
lemma grade_lt_iff_lt : grade a < grade b ↔ a < b := grade_strict_mono.lt_iff_lt
lemma grade_eq_iff_eq : grade a = grade b ↔ a = b := grade_injective.eq_iff
lemma grade_ne_iff_ne : grade a ≠ grade b ↔ a ≠ b := grade_injective.ne_iff

/-- `grade` as an order embedding into `ℕ` for a linear order `α`. -/
protected def order_embedding.grade : α ↪o ℕ :=
{ to_fun := _,
  inj' := grade_injective,
  map_rel_iff' := λ _ _, grade_le_iff_le }

lemma covers_iff_grade : a ⋖ b ↔ grade a + 1 = grade b :=
⟨covers.grade, λ h, covers_iff_grade_succ_eq_lt.2 ⟨h, grade_lt_iff_lt.1 $ succ_le_iff.1 h.le⟩⟩

@[simp] lemma grade_covers_grade_iff (a b : α) : grade a ⋖ grade b ↔ a ⋖ b :=
⟨λ h, covers_iff_grade.2 $ covers_iff_succ_eq.1 h, covers.grade_covers⟩

/-- Constructs a locally finite order instance from a grade function on a linear order. -/
@[reducible] -- See note [reducible non-instances]
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
end grade_order

section grade_max_order
section preorder
variables (α) [preorder α] [grade_max_order α] {a : α}

/-- The maximal grade of an element of `α`. -/
def max_grade : ℕ := grade_max_order.max_grade α

variables {α}

protected lemma is_max.grade (h : is_max a) : grade a = max_grade α :=
grade_max_order.grade_of_is_max h

lemma grade_le_max_grade (a : α) : grade a ≤ max_grade α := grade_max_order.grade_le_max_grade _

end preorder

section partial_order
variables [partial_order α] [grade_max_order α] {a b : α}

lemma has_lt.lt.grade_lt_max_grade (h : a < b) : grade a < max_grade α :=
(grade_strict_mono h).trans_le $ grade_le_max_grade _

@[simp] lemma grade_lt_max_grade_of_nonempty_Ioi (h : (set.Ioi a).nonempty) :
  grade a < max_grade α :=
has_lt.lt.grade_lt_max_grade h.some_mem

@[simp] lemma grade_eq_max_grade_iff (a : α) : grade a = max_grade α ↔ is_max a :=
begin
  refine ⟨λ h b hab, _, is_max.grade⟩,
  by_contra hba,
  exact (grade_le_max_grade _).not_lt (h.ge.trans_lt $ grade_strict_mono $ hab.lt_of_not_le hba),
end

instance : grade_max_order (order_dual α) :=
{ grade := λ a, max_grade α - grade (of_dual a),
  max_grade := max_grade α,
  grade_of_is_min := λ a h, by rw [h.of_dual.grade, tsub_self],
  grade_of_is_max := λ a h, by { change _ - _ = _, rw [h.of_dual.grade, tsub_zero] },
  grade_strict_mono := λ a b hab,
    (tsub_lt_tsub_iff_left_of_le $ grade_le_max_grade _).2 (grade_strict_mono hab.of_dual),
  grade_of_covers := λ a b h, begin
    rw [←h.of_dual.grade, ←tsub_tsub],
    exact (tsub_add_cancel_of_le $ nat.succ_le_iff.2 $ nat.sub_pos_of_lt $
      h.1.of_dual.grade_lt_max_grade),
  end,
  grade_le_max_grade := λ a, tsub_le_self }

@[simp] protected lemma max_grade_dual : max_grade (order_dual α) = max_grade α := rfl

end partial_order
end grade_max_order

/-! ### Instances -/

/-! #### Natural numbers -/

namespace nat

instance : grade_order ℕ :=
{ grade := id,
  grade_of_is_min := λ _, is_min.eq_bot,
  grade_strict_mono := strict_mono_id,
  grade_of_covers := λ a b, covers_iff_succ_eq.1 }

protected lemma grade (n : ℕ) : grade n = n := rfl

end nat

/-! #### `fin` -/

namespace fin

instance (n : ℕ) : grade_order (fin n) :=
{ grade := coe,
  grade_of_is_min := λ a ha, begin
    cases n,
    { exact a.elim0 },
    { exact congr_arg _ ha.eq_bot }
  end,
  grade_strict_mono := strict_mono_id,
  grade_of_covers := λ _ _ h, nat.covers_iff_succ_eq.1 $ (fin.val_covers_iff _ _).2 h }

instance (n : ℕ) : grade_max_order (fin (n + 1)) := grade_order.to_grade_max_order

protected lemma grade {n : ℕ} (k : fin n) : grade k = k := rfl

end fin

/-! #### `subsingleton` -/

section subsingleton
variables (α) [subsingleton α] [preorder α]

/-- In terms of polytopes, a *nullitope*. -/
@[reducible] -- See note [reducible non-instances]
def subsingleton.to_grade_order : grade_order α :=
{ grade := λ _, 0,
  grade_of_is_min := λ _ _, rfl,
  grade_strict_mono := subsingleton.strict_mono _,
  grade_of_covers := λ a b h, (h.1.ne $ subsingleton.elim _ _).elim }

variables {α}

protected lemma subsingleton.grade [grade_order α] (a : α) : grade (a : α) = 0 :=
(subsingleton.is_min _).grade

--TODO: Instance for `unit`

end subsingleton

/-! #### Simple orders -/

section is_simple_order
variables (α)

/-- In terms of polytopes, a *point*. -/
@[reducible] -- See note [reducible non-instances]
def is_simple_order.to_grade_order [decidable_eq α] [partial_order α] [bounded_order α]
  [is_simple_order α] :
  grade_order α :=
{ grade := λ a, if a = ⊥ then 0 else 1,
  grade_of_is_min := λ a ha, if_pos ha.eq_bot,
  grade_strict_mono := λ a b h, begin
    convert zero_lt_one,
    { exact if_pos (is_simple_order.eq_bot_of_lt h) },
    { exact if_neg (ne_bot_of_gt h) },
    { apply_instance }
  end,
  grade_of_covers := λ a b h, begin
    convert zero_add 1,
    { exact if_pos (is_simple_order.eq_bot_of_lt h.1) },
    { exact if_neg (ne_bot_of_gt h.1) }
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
variables [preorder α] [preorder β] [grade_order β] {a b : α} {f : α ↪o β}

/-- Lifts a graded order along an order embedding. -/
def grade_order.lift (hbot : ∀ a, is_bot a → is_bot (f a)) (h : (set.range f).ord_connected) :
  grade_order α :=
{ grade := λ a, grade (f a),
  grade_of_is_min := by rw [hbot, grade_bot],
  strict_mono := grade_strict_mono.comp f.strict_mono,
  grade_of_covers := λ a b hab, ((image_covers_iff h).2 hab).grade }

end lift
