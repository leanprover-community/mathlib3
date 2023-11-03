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
universes u v u' v'

namespace first_order
namespace language
open_locale first_order
open Structure

section sentences

variables {L : language.{u v}} (c₀ c₁ : L.constants) (i : L.functions 1) (a m : L.functions 2)

/-- The sentence indicating that a binary functionol is commutative. -/
protected def comm : L.sentence := ∀' ∀' (m.apply₂ &0 &1 =' m.apply₂ &1 &0)

/-- The sentence indicating that a binary function symbol is associative. -/
protected def assoc : L.sentence :=
∀' ∀' ∀' (m.apply₂ (m.apply₂ &0 &1) &2 =' m.apply₂ &0 (m.apply₂ &1 &2))

/-- The sentence indicating that applying a constant symbol on the left of
  a binary symbol is the identity. -/
def id_left : L.sentence :=
∀' (m.apply₂ c₁.term &0 =' &0)

/-- The sentence indicating that applying a constant symbol on the right of
  a binary symbol is the identity. -/
def id_right : L.sentence :=
∀' (m.apply₂ &0 c₁.term =' &0)

/-- The sentence indicating that left composing a unary symbol with a binary symbol
  is equal to a constant symbol. -/
def cancel_left : L.sentence :=
∀' (m.apply₂ (i.apply₁ &0) &0 =' c₁.term)

/-- The sentence indicating that right composing a unary symbol with a binary symbol
  is equal to a constant symbol. -/
def cancel_right : L.sentence :=
∀' (m.apply₂ &0 (i.apply₁ &0) =' c₁.term)

/-- The sentence indicating that a binary function symbol distributes over another -/
protected def distrib : L.sentence :=
∀' ∀' ∀' (m.apply₂ (a.apply₂ &0 &1) &2 =' a.apply₂ (m.apply₂ &0 &2) (m.apply₂ &1 &2))

end sentences

/-- The language of monoids -/
protected def monoid : language :=
language.mk₂ unit empty unit empty empty

/-- The language of additive monoids -/
protected def add_monoid : language :=
language.mk₂ unit empty unit empty empty

/-- The language of groups -/
protected def group : language :=
language.mk₂ unit unit unit empty empty

/-- The language of additive groups -/
protected def add_group : language :=
language.mk₂ unit unit unit empty empty

/-- The language of rings -/
protected def ring : language :=
language.add_group.sum language.monoid

variables (L : language.{u v}) (L' : language.{u' v'})

/-- A language having a symbol representing `0`. -/
class has_zero_symb := (symb : L.constants)

/-- A language having a symbol representing `1`. -/
class has_one_symb := (symb : L.constants)

/-- A language having a symbol representing `-`. -/
class has_neg_symb := (symb : L.functions 1)

/-- A language having a symbol representing `⁻¹`. -/
class has_inv_symb := (symb : L.functions 1)

/-- A language having a symbol representing `+`. -/
class has_add_symb := (symb : L.functions 2)

/-- A language having a symbol representing `*`. -/
class has_mul_symb := (symb : L.functions 2)

namespace sum

variables {L} {L'}

instance has_zero_symb_of_left [L.has_zero_symb] : (L.sum L').has_zero_symb :=
{ symb := sum.inl has_zero_symb.symb }

instance has_zero_symb_of_right [L'.has_zero_symb] : (L.sum L').has_zero_symb :=
{ symb := sum.inr has_zero_symb.symb }

instance has_one_symb_of_left [L.has_one_symb] : (L.sum L').has_one_symb :=
{ symb := sum.inl has_one_symb.symb }

instance has_one_symb_of_right [L'.has_one_symb] : (L.sum L').has_one_symb :=
{ symb := sum.inr has_one_symb.symb }

instance has_neg_symb_of_left [L.has_neg_symb] : (L.sum L').has_neg_symb :=
{ symb := sum.inl has_neg_symb.symb }

instance has_neg_symb_of_right [L'.has_neg_symb] : (L.sum L').has_neg_symb :=
{ symb := sum.inr has_neg_symb.symb }

instance has_add_symb_of_left [L.has_add_symb] : (L.sum L').has_add_symb :=
{ symb := sum.inl has_add_symb.symb }

instance has_add_symb_of_right [L'.has_add_symb] : (L.sum L').has_add_symb :=
{ symb := sum.inr has_add_symb.symb }

instance has_mul_symb_of_left [L.has_mul_symb] : (L.sum L').has_mul_symb :=
{ symb := sum.inl has_mul_symb.symb }

instance has_mul_symb_of_right [L'.has_mul_symb] : (L.sum L').has_mul_symb :=
{ symb := sum.inr has_mul_symb.symb }

end sum

namespace monoid

instance has_one_symb : language.monoid.has_one_symb := { symb := ⟨⟩ }

instance has_mul_symb : language.monoid.has_mul_symb := { symb := ⟨⟩ }

end monoid

namespace add_monoid

instance has_zero_symb : language.add_monoid.has_zero_symb := { symb := ⟨⟩ }

instance add_monoid.has_add_symb : language.add_monoid.has_add_symb := { symb := ⟨⟩ }

end add_monoid

namespace group

instance group.has_one_symb : language.group.has_one_symb := { symb := ⟨⟩ }

instance group.has_inv_symb : language.group.has_inv_symb := { symb := ⟨⟩ }

instance group.has_mul_symb : language.group.has_mul_symb := { symb := ⟨⟩ }

end group

namespace add_group

instance add_group.has_zero_symb : language.add_group.has_zero_symb := { symb := ⟨⟩ }

instance add_group.has_neg_symb : language.add_group.has_neg_symb := { symb := ⟨⟩ }

instance add_group.has_add_symb : language.add_group.has_add_symb := { symb := ⟨⟩ }

end add_group

-- instance why : language.ring.has_one_symb := by apply_instance

variables {L} {α : Type*}

instance [has_zero_symb L] : has_zero (L.term α) := { zero := has_zero_symb.symb.term }

instance [has_one_symb L] : has_one (L.term α) := { one := has_one_symb.symb.term }

instance [has_neg_symb L] : has_neg (L.term α) := { neg := λ x, func has_neg_symb.symb ![x] }

instance [has_inv_symb L] : has_inv (L.term α) := { inv := λ x, func has_inv_symb.symb ![x] }

instance [has_add_symb L] : has_add (L.term α) := { add := λ x y, func has_add_symb.symb ![x, y] }

instance [has_mul_symb L] : has_mul (L.term α) := { mul := λ x y, func has_mul_symb.symb ![x, y] }

section term_pow

variables [has_one_symb L] [has_mul_symb L]

instance : has_pow (L.term α) ℕ := ⟨ λ t n, npow_rec n t ⟩

@[simp] lemma pow_zero (t : L.term α) : t ^ 0 = 1 := rfl
@[simp] lemma pow_succ {n} (t : L.term α) : t ^ (n + 1) = t * t ^ n := rfl

end term_pow

/-- Any type with instances of `has_one` and `has_mul` is a
  structure in the language of monoids. -/
def monoid.Structure_of_has_one_has_mul [has_one α] [has_mul α] :
  language.monoid.Structure α :=
Structure.mk₂ (λ _, 1) empty.elim (λ _, has_mul.mul) empty.elim empty.elim

/-- Any type with instances of `has_zero` and `has_add` is a
  structure in the language of additive monoids. -/
def add_monoid.Structure_of_has_zero_has_add [has_zero α] [has_add α] :
  language.monoid.Structure α :=
Structure.mk₂ (λ _, 0) empty.elim (λ _, has_add.add) empty.elim empty.elim

/-- Any type with instances of `has_one`, `has_inv` and `has_mul` is a
  structure in the language of groups. -/
def group.Structure_of_has_one_has_inv_has_mul [has_one α] [has_inv α] [has_mul α] :
  language.group.Structure α :=
Structure.mk₂ (λ _, 1) (λ _, has_inv.inv) (λ _, has_mul.mul) empty.elim empty.elim

/-- Any type with instances of `has_zero`, `has_neg` and `has_add` is a
  structure in the language of additive groups. -/
def add_group.Structure_of_has_zero_has_neg_has_add [has_zero α] [has_neg α] [has_add α] :
  language.group.Structure α :=
Structure.mk₂ (λ _, 0) (λ _, has_neg.neg) (λ _, has_add.add) empty.elim empty.elim

/-- Any monoid is a structure in the language of monoids. -/
def _root_.monoid.Structure [monoid α] : language.monoid.Structure α :=
monoid.Structure_of_has_one_has_mul

/-- Any additive monoid is a structure in the language of additive monoids. -/
def _root_.add_monoid.Structure [add_monoid α] : language.monoid.Structure α :=
add_monoid.Structure_of_has_zero_has_add

/-- Any group is a structure in the language of groups. -/
def _root_.group.Structure [group α] : language.group.Structure α :=
group.Structure_of_has_one_has_inv_has_mul

/-- Any additive group is a structure in the language of additive groups. -/
def _root_.add_comm_group.Structure [add_comm_group α] : language.group.Structure α :=
add_group.Structure_of_has_zero_has_neg_has_add

/-- Any ring is a structure in the language of ring. -/
def _root_.ring.Structure [ring α] : language.ring.Structure α :=
@language.sum_Structure _ _ _ add_comm_group.Structure monoid.Structure

section sentences

/-- The sentence indicating associativity of addition -/
protected def add_assoc [has_add_symb L] : L.sentence := language.assoc has_add_symb.symb

/-- The sentence indicating commutativity of addition -/
protected def add_comm [has_add_symb L] : L.sentence := language.comm has_add_symb.symb

/-- The sentence indicating associativity of multiplication -/
protected def mul_assoc [has_mul_symb L] : L.sentence := language.assoc has_mul_symb.symb

/-- The sentence indicating commutativity of multiplication -/
protected def mul_comm [has_mul_symb L] : L.sentence := language.comm has_mul_symb.symb

/-- The sentence indicating that zero is a right identity to addition -/
protected def add_zero [has_zero_symb L] [has_add_symb L] : L.sentence :=
id_right has_zero_symb.symb has_add_symb.symb

/-- The sentence indicating that zero is a left identity to addition -/
protected def zero_add [has_zero_symb L] [has_add_symb L] : L.sentence :=
id_left has_zero_symb.symb has_add_symb.symb

/-- The sentence indicating that one is a right identity to addition -/
protected def mul_one [has_one_symb L] [has_mul_symb L] : L.sentence :=
id_right has_one_symb.symb has_mul_symb.symb

/-- The sentence indicating that one is a left identity to addition -/
protected def one_mul [has_one_symb L] [has_mul_symb L] : L.sentence :=
id_left has_one_symb.symb has_mul_symb.symb

/-- The sentence indicating that negation is the left inverse to addition -/
protected def neg_add_self [has_zero_symb L] [has_neg_symb L] [has_add_symb L] : L.sentence :=
cancel_left has_zero_symb.symb has_neg_symb.symb has_add_symb.symb

/-- The sentence indicating that negation is the right inverse to addition -/
protected def add_neg_self [has_zero_symb L] [has_neg_symb L] [has_add_symb L] : L.sentence :=
cancel_right has_zero_symb.symb has_neg_symb.symb has_add_symb.symb

/-- The sentence indicating that left multiplication distributes over addition -/
protected def mul_add [has_add_symb L] [has_mul_symb L] : L.sentence :=
language.distrib has_add_symb.symb has_mul_symb.symb

end sentences

instance ring.has_zero_symb : language.ring.has_zero_symb := sum.has_zero_symb_of_left
instance ring.has_one_symb : language.ring.has_one_symb := sum.has_one_symb_of_right
instance ring.has_neg_symb : language.ring.has_neg_symb := sum.has_neg_symb_of_left
instance ring.has_add_symb : language.ring.has_add_symb := sum.has_add_symb_of_left
instance ring.has_mul_symb : language.ring.has_mul_symb := sum.has_mul_symb_of_right

/-- The theory of commutative rings. -/
def Theory.comm_ring : Theory language.ring :=
{ language.add_assoc,
  language.add_zero,
  language.add_comm,
  language.neg_add_self,
  language.mul_assoc,
  language.mul_one,
  language.mul_comm,
  language.mul_add }

/-- The theory of fields. -/
def Theory.field : Theory language.ring :=
Theory.comm_ring ∪ {
  ∀' (&0 =' 0 ⊔ ∃' ((&1 * &0) =' 1)),
  sentence.card_ge _ 1 }

end language
end first_order
