/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import data.tree
import logic.equiv.basic
import tactic.ring
import tactic.zify

/-!
# Encodable types using trees

This file defines encodings to `tree unit` rather than `ℕ`.
This is especially useful for encoding tree-like data
naturally.

TODO: the `encoding`'s used in `src/computability` should be to trees.

## Main declarations

* `encodable α`: States that there exists an explicit encoding function `encode : α → ℕ` with a
  partial inverse `decode : tree unit → option α`.

-/
open tree

/-- Encoding of a type into a tree structure -/
class tencodable (α : Type*) :=
(encode : α → tree unit)
(decode [] : tree unit → option α)
(encodek : ∀ a, decode (encode a) = some a)

attribute [simp, higher_order] tencodable.encodek

namespace tencodable
variables {α β : Type*} [tencodable α] [tencodable β]

theorem encode_injective : function.injective (@encode α _)
| x y e := option.some.inj $ by rw [← encodek, e, encodek]

@[simp] lemma encode_inj {a b : α} : encode a = encode b ↔ a = b :=
encode_injective.eq_iff

/-- Any tencodable element has decidable equality by checking if the encodings are equal -/
def decidable_eq_of_encodable (α) [tencodable α] : decidable_eq α
| a b := decidable_of_iff _ encode_inj

/-- If `α` is encodable and there is an injection `f : β → α`, then `β` is encodable as well. -/
def of_left_injection {β} (f : β → α) (finv : α → option β) (linv : ∀ b, finv (f b) = some b) :
  tencodable β :=
⟨λ b, encode (f b),
 λ n, (decode α n).bind finv,
 λ b, by simp [linv]⟩

/-- If `α` is encodable and `f : β → α` is invertible, then `β` is encodable as well. -/
def of_left_inverse {β} (f : β → α) (finv : α → β) (linv : ∀ b, finv (f b) = b) : tencodable β :=
of_left_injection f (some ∘ finv) (λ b, congr_arg some (linv b))

/-- Encodability is preserved by equivalence. -/
def of_equiv {β} (α) [tencodable α] (e : β ≃ α) : tencodable β :=
of_left_inverse e e.symm e.left_inv

instance _root_.tree_unit.tencodable : tencodable (tree unit) :=
{ encode := id,
  decode := some,
  encodek := λ _, rfl }

@[simp] lemma encode_tree_unit (x : tree unit) : encode x = x := rfl
@[simp] lemma decode_tree_unit (x : tree unit) : decode (tree unit) x = some x := rfl

@[priority 100] instance _root_.is_empty.to_tencodable [is_empty α] : tencodable α :=
⟨is_empty_elim, λ n, none, is_empty_elim⟩

instance _root_.punit.tencodable : tencodable punit :=
⟨λ_, nil, λ _, some punit.star, λ _, by simp⟩

lemma encode_star : encode punit.star = nil := rfl

section prod

/-- Encoding of a pair of encodable elements -/
instance _root_.prod.tencodable : tencodable (α × β) :=
{ encode := λ x, node () (encode x.1) (encode x.2),
  decode := λ y, (decode α y.left).bind $ λ l, (decode β y.right).bind $ λ r, some (l, r),
  encodek := λ x, by simp }

lemma encode_prod (x : α) (y : β) : encode (x, y) = node () (encode x) (encode y) := rfl

end prod

section bool

/-- Encoding of `bool` -/
instance _root_.bool.tencodable : tencodable bool :=
{ encode := λ b, cond b nil non_nil,
  decode := λ x, some (x = nil : bool),
  encodek := λ b, by cases b; simp }

lemma encode_tt : encode tt = nil := rfl
lemma encode_ff : encode ff = non_nil := rfl

end bool

section list

/-- Interpret a tree as a list of trees according to the left children
  of the nodes on the rightmost path-/
def as_list : tree unit → list (tree unit)
| nil := []
| (node _ a b) := a :: as_list b

/-- Interpret a list of trees as a single tree -/
def of_list : list (tree unit) → tree unit
| [] := nil
| (x :: xs) := node () x (of_list xs)

/-- There is an equivalence between `tree unit` and `list (tree unit)`
  corresponding to taking all of the left children on nodes of the rightmost path.
  We use this to encode lists -/
def equiv_list : tree unit ≃ list (tree unit) :=
{ to_fun := as_list,
  inv_fun := of_list,
  left_inv := λ t, by induction t; simp [as_list, of_list, *],
  right_inv := λ l, by induction l; simp [as_list, of_list, *] }

@[simp] lemma equiv_list_nil : equiv_list nil = [] := rfl
@[simp] lemma equiv_list_node (a b : tree unit) :
  equiv_list (node () a b) = a :: (equiv_list b) := rfl
@[simp] lemma equiv_list_symm_nil : equiv_list.symm [] = nil := rfl
@[simp] lemma equiv_list_symm_cons (a : tree unit) (b : list (tree unit)) :
  equiv_list.symm (a :: b) = node () a (equiv_list.symm b) := rfl

-- TODO: Move to list/lemmas
@[simp] lemma list.nil_all_some {α : Type*} : (@list.nil $ option α).all_some = some [] := rfl
@[simp] lemma list.none_cons_all_some {α} (x : list (option α)) :
  (none :: x).all_some = none := rfl
@[simp] lemma list.some_cons_all_some {α} (x : list (option α)) (y) :
  (some y :: x).all_some = x.all_some.map (list.cons y) := rfl

@[simp] theorem list.map_some_all_some {α} (x : list α) :
  (x.map some).all_some = some x := by induction x; simp [*]

instance _root_.list.tencodable : tencodable (list α) :=
{ encode := λ l, equiv_list.symm (l.map encode),
  decode := λ t, ((equiv_list t).map (decode α)).all_some,
  encodek := λ l, by simp }

lemma encode_nil : encode (@list.nil α) = nil := rfl
lemma encode_cons (x : α) (xs : list α) : encode (x :: xs) = node () (encode x) (encode xs) := rfl

@[simp] lemma encode_list_tree (x : list (tree unit)) : encode x = equiv_list.symm x :=
by simp [encode]

@[simp] lemma decode_list_tree (x : tree unit) :
  decode (list (tree unit)) x = some (equiv_list x) := by simp [decode]

end list

section nat

/-- Interpret a tree as a natural number by counting the leaves
  (subtracting 1 so that it is a surjection) -/
def to_nat (x : tree unit) : ℕ := x.leaves - 1

@[simp] lemma to_nat_nil : to_nat nil = 0 := rfl
@[simp] lemma to_nat_node (a b : tree unit) : to_nat (node () a b) = (to_nat a) + (to_nat b) + 1 :=
begin
  simp only [to_nat, leaves],
  zify [tree.leaves_pos, nat.add_pos_left a.leaves_pos _],
  ring,
end

/-- This is a unary encoding for natural numbers. The canonical
  way of representing `n` is as n ↦ nil.node (nil.node (... etc.)) -/
instance _root_.nat.unary_tencodable : tencodable ℕ :=
{ encode := λ n, (equiv_list.symm $ list.repeat nil n),
  decode := λ t, some (to_nat t),
  encodek := λ n,
begin
  induction n with n ih, { simp, },
  simpa [nat.succ_eq_add_one] using ih,
end }

lemma encode_zero : encode 0 = nil := rfl
lemma encode_succ (n : ℕ) : encode (n + 1) = node () nil (encode n) := rfl

end nat

section option

/-- Encode an `option α`, using `nil` as `none` -/
@[simp] def of_option : option α → tree unit
| none := nil
| (some x) := node () nil (encode x)

/-- Decode an `option α` as a tree -/
@[simp] def to_option : tree unit → option (option α)
| nil := some none
| (node _ x y) := (decode α y).map some

/-- Encoding of `option α` when `α` has an encoding -/
instance : tencodable (option α) :=
{ encode := of_option,
  decode := to_option,
  encodek := λ x, by cases x; simp [of_option, to_option] }

end option

section sum

/-- Encode a sum by using the left child of the root to signal if the right represents α or β -/
@[simp] def of_sum : α ⊕ β → tree unit
| (sum.inl x) := node () nil (encode x)
| (sum.inr x) := node () non_nil (encode x)

/-- Decode a sum by using the left child of the root to signal if the right represents α or β -/
@[simp] def to_sum (x : tree unit) : option (α ⊕ β) :=
  if x.left = nil then (decode α x.right).map sum.inl
  else (decode β x.right).map sum.inr

/-- Encoding of a sum type given encodings for `α` and `β` -/
instance : tencodable (α ⊕ β) :=
{ encode := of_sum,
  decode := to_sum,
  encodek := λ x, by cases x; simp }

end sum

end tencodable
