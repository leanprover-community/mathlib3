/-
Copyright (c) 2022 Joseph Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Hua
-/
import model_theory.syntax

/-!
# The language of rings
## Main Definitions
* `first_order.language.monoid` defines the language of monoids,
  which consists of 1`, `*`.
* `first_order.language.group` defines the language of groups,
  which consists of `0`, `-`, `+`.
* `first_order.language.ring` defines the language of rings,
  which consists of `0`, `1`, `-`, `+`, `*`,
  as the sum of the languages of monoids and groups.
* `first_order.language.Theory.comm_ring` defines the theory of commutative rings.
* `first_order.language.Theory.field` defines the theory of fields.
-/
universes u

namespace first_order
namespace language
open_locale first_order
open Structure

/-- The language of monoids -/
protected def monoid : language :=
language.mk₂ unit empty unit empty empty

/-- The language of groups -/
protected def group : language :=
language.mk₂ unit unit unit empty empty

/-- The language of rings -/
protected def ring : language :=
language.sum language.group language.monoid

variable {α : Type u}

namespace language.ring

/-- The function symbol representing zero. -/
def zero : language.ring.constants := sum.inl ⟨⟩

/-- The function symbol representing one. -/
def one : language.ring.constants := sum.inr ⟨⟩

/-- The function symbol representing negation. -/
def neg : language.ring.functions 1 := sum.inl ⟨⟩

/-- The function symbol representing addition. -/
def add : language.ring.functions 2 := sum.inl ⟨⟩

/-- The function symbol representing multiplication. -/
def mul : language.ring.functions 2 := sum.inr ⟨⟩

@[simp] instance : has_zero (language.ring.term α) := ⟨ constants.term (sum.inl ⟨⟩) ⟩

@[simp] instance : has_one (language.ring.term α) := ⟨ constants.term (sum.inr ⟨⟩) ⟩

@[simp] instance : has_neg (language.ring.term α) :=
  ⟨ λ x, func language.ring.neg ![x] ⟩

@[simp] instance : has_add (language.ring.term α) :=
⟨ λ x y, func language.ring.add ![x, y] ⟩

@[simp] instance : has_mul (language.ring.term α) :=
⟨ λ x y, func language.ring.mul ![x, y] ⟩

@[simp] instance : has_sub (language.ring.term α) := ⟨ λ x y, x + - y ⟩

instance : has_pow (language.ring.term α) ℕ := ⟨ λ t n, npow_rec n t ⟩

@[simp] lemma pow_zero (t : language.ring.term α) : t ^ 0 = 1 := rfl
@[simp] lemma pow_succ {n} (t : language.ring.term α) : t ^ (n + 1) = t * t ^ n := rfl

end language.ring

/-- Any type with instances of `has_one` and `has_mul` is a
  structure in the language of monoids. -/
def monoid.Structure_of_has_one_has_mul {α : Type*} [has_one α] [has_mul α] :
  language.monoid.Structure α :=
Structure.mk₂ (λ _, 1) empty.elim (λ _, has_mul.mul) empty.elim empty.elim

/-- Any type with instances of `has_one`, `has_inv` and `has_mul` is a
  structure in the language of groups. -/
def group_Structure_of_has_zero_has_neg_has_add {α : Type} [has_zero α] [has_neg α] [has_add α] :
  language.group.Structure α :=
Structure.mk₂ (λ _, 0) (λ _, has_neg.neg) (λ _, has_add.add) empty.elim empty.elim

/- Any monoid is a structure in the language of monoids. -/
def _root_.monoid.Structure (M : Type) [monoid M] : language.monoid.Structure M :=
monoid.Structure_of_has_one_has_mul

/- Any group is a structure in the language of groups. -/
def _root_.add_comm_group.Structure (G : Type) [add_comm_group G] : language.group.Structure G :=
group_Structure_of_has_zero_has_neg_has_add

/- Any ring is a structure in the language of ring. -/
def _root_.ring.Structure (R : Type*) [ring R] : language.ring.Structure R :=
@language.sum_Structure _ _ _ (add_comm_group.Structure R) (monoid.Structure R)

namespace functions

variables {L : language} (c₀ c₁ : L.constants) (i : L.functions 1) (a : L.functions 2)
  (m : L.functions 2)

/-- The sentence indicating that a binary function symbol is commutative. -/
protected def comm : L.sentence := ∀' ∀' (m.apply₂ &0 &1 =' m.apply₂ &1 &0)

/-- The sentence indicating that a binary function symbol is associative. -/
protected def assoc : L.sentence :=
∀' ∀' ∀' (m.apply₂ (m.apply₂ &0 &1) &2 =' m.apply₂ &0 (m.apply₂ &1 &2))

/-- The sentence indicating that applying a constant symbol on the right of
  a binary symbol is the identity. -/
protected def mul_id : L.sentence :=
∀' (m.apply₂ &0 c₁.term =' &0)

/-- The sentence indicating that applying a constant symbol on the right of
  a binary symbol is the identity. -/
protected def id_mul : L.sentence :=
∀' (m.apply₂ c₁.term &0 =' &0)

/-- The sentence indicating that left composing a unary symbol with a binary symbol
  is equal to a constant symbol. -/
protected def inv_mul : L.sentence :=
∀' (m.apply₂ (i.apply₁ &0) &0 =' c₁.term)

/-- The sentence indicating that left composing a unary symbol with a binary symbol
  is equal to a constant symbol. -/
protected def mul_inv : L.sentence :=
∀' (m.apply₂ &0 (i.apply₁ &0) =' c₁.term)

/-- The sentence indicating that a binary function symbol distributes over another -/
protected def add_mul : L.sentence :=
∀' ∀' ∀' (m.apply₂ (a.apply₂ &0 &1) &2 =' a.apply₂ (m.apply₂ &0 &2) (m.apply₂ &1 &2))

/-- The sentence indicating that multiplication has an inverse away from a constant zero -/
protected def field_inv : L.sentence :=
∀' (&0 =' c₀.term ⊔ ∃' (m.apply₂ &1 &0 =' c₁.term))

end functions

section ring_theories

open language.ring

/-- The theory of commutative rings. -/
def Theory.comm_ring : Theory language.ring :=
{ functions.assoc add,
  functions.mul_id zero add,
  functions.comm add,
  functions.inv_mul zero neg add,
  functions.assoc mul,
  functions.mul_id one mul,
  functions.comm mul,
  functions.add_mul add mul }

/-- The theory of fields. -/
def Theory.field : Theory language.ring :=
Theory.comm_ring ∪ {
  functions.field_inv zero one mul,
  sentence.card_ge _ 1 }

end ring_theories

end language
end first_order
