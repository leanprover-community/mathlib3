/-
Copyright (c) 2019 mathlib community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Wojciech Nawrocki
-/
import data.rbtree.init
import data.num.basic
import order.basic

/-!
# Binary tree

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Provides binary tree storage for values of any type, with O(lg n) retrieval.
See also `data.rbtree` for red-black trees - this version allows more operations
to be defined and is better suited for in-kernel computation.

We also specialize for `tree unit`, which is a binary tree without any
additional data. We provide the notation `a △ b` for making a `tree unit` with children
`a` and `b`.

## References

<https://leanprover-community.github.io/archive/stream/113488-general/topic/tactic.20question.html>
-/

/-- A binary tree with values stored in non-leaf nodes. -/
@[derive has_reflect, derive decidable_eq]
inductive {u} tree (α : Type u) : Type u
| nil : tree
| node : α → tree → tree → tree

namespace tree

universe u
variable {α : Type u}

/-- Construct a string representation of a tree. Provides a `has_repr` instance. -/
def repr [has_repr α] : tree α → string
| nil := "nil"
| (node a t1 t2) := "tree.node " ++ has_repr.repr a
                    ++ " (" ++ repr t1 ++ ") (" ++ repr t2 ++ ")"

instance [has_repr α] : has_repr (tree α) := ⟨tree.repr⟩

instance : inhabited (tree α) := ⟨nil⟩

/-- Makes a `tree α` out of a red-black tree. -/
def of_rbnode : rbnode α → tree α
| rbnode.leaf               := nil
| (rbnode.red_node l a r)   := node a (of_rbnode l) (of_rbnode r)
| (rbnode.black_node l a r) := node a (of_rbnode l) (of_rbnode r)

/-- Finds the index of an element in the tree assuming the tree has been
constructed according to the provided decidable order on its elements.
If it hasn't, the result will be incorrect. If it has, but the element
is not in the tree, returns none. -/
def index_of (lt : α → α → Prop) [decidable_rel lt]
  (x : α) : tree α → option pos_num
| nil := none
| (node a t₁ t₂) :=
  match cmp_using lt x a with
  | ordering.lt := pos_num.bit0 <$> index_of t₁
  | ordering.eq := some pos_num.one
  | ordering.gt := pos_num.bit1 <$> index_of t₂
  end

/-- Retrieves an element uniquely determined by a `pos_num` from the tree,
taking the following path to get to the element:
- `bit0` - go to left child
- `bit1` - go to right child
- `pos_num.one` - retrieve from here -/
def get : pos_num → tree α → option α
| _                nil            := none
| pos_num.one      (node a t₁ t₂) := some a
| (pos_num.bit0 n) (node a t₁ t₂) := t₁.get n
| (pos_num.bit1 n) (node a t₁ t₂) := t₂.get n

/-- Retrieves an element from the tree, or the provided default value
if the index is invalid. See `tree.get`. -/
def get_or_else (n : pos_num) (t : tree α) (v : α) : α :=
  (t.get n).get_or_else v

/-- Apply a function to each value in the tree.  This is the `map` function for the `tree` functor.
TODO: implement `traversable tree`. -/
def map {β} (f : α → β) : tree α → tree β
| nil := nil
| (node a l r) := node (f a) (map l) (map r)

/-- The number of internal nodes (i.e. not including leaves) of a binary tree -/
@[simp] def num_nodes : tree α → ℕ
| nil := 0
| (node _ a b) := a.num_nodes + b.num_nodes + 1

/-- The number of leaves of a binary tree -/
@[simp] def num_leaves : tree α → ℕ
| nil := 1
| (node _ a b) := a.num_leaves + b.num_leaves

/-- The height - length of the longest path from the root - of a binary tree -/
@[simp] def height : tree α → ℕ
| nil := 0
| (node _ a b) := max a.height b.height + 1

lemma num_leaves_eq_num_nodes_succ (x : tree α) : x.num_leaves = x.num_nodes + 1 :=
by { induction x; simp [*, nat.add_comm, nat.add_assoc, nat.add_left_comm], }

lemma num_leaves_pos (x : tree α) : 0 < x.num_leaves :=
by { rw num_leaves_eq_num_nodes_succ, exact x.num_nodes.zero_lt_succ, }

lemma height_le_num_nodes : ∀ (x : tree α), x.height ≤ x.num_nodes
| nil := le_rfl
| (node _ a b) := nat.succ_le_succ
    (max_le
      (trans a.height_le_num_nodes $ a.num_nodes.le_add_right _)
      (trans b.height_le_num_nodes $ b.num_nodes.le_add_left _))

/-- The left child of the tree, or `nil` if the tree is `nil` -/
@[simp] def left : tree α → tree α
| nil := nil
| (node _ l r) := l

/-- The right child of the tree, or `nil` if the tree is `nil` -/
@[simp] def right : tree α → tree α
| nil := nil
| (node _ l r) := r

/- Notation for making a node with `unit` data -/
localized "infixr ` △ `:65 := tree.node ()" in tree

/-- Recursion on `tree unit`; allows for a better `induction` which does not have to worry
  about the element of type `α = unit` -/
@[elab_as_eliminator]
def unit_rec_on {motive : tree unit → Sort*} (t : tree unit) (base : motive nil)
  (ind : ∀ x y, motive x → motive y → motive (x △ y)) : motive t :=
t.rec_on base (λ u, u.rec_on (by exact ind))

lemma left_node_right_eq_self : ∀ {x : tree unit} (hx : x ≠ nil), x.left △ x.right = x
| nil h := by trivial
| (a △ b) _ := rfl

end tree
