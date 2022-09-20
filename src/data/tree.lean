/-
Copyright (c) 2019 mathlib community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Wojciech Nawrocki
-/
import data.rbtree.init
import data.num.basic

/-!
# Binary tree

Provides binary tree storage for values of any type, with O(lg n) retrieval.
See also `data.rbtree` for red-black trees - this version allows more operations
to be defined and is better suited for in-kernel computation.

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

end tree

/-- A unit tree is a binary tree with no data (only units) attached -/
@[derive [has_reflect, decidable_eq]]
inductive unit_tree
| nil : unit_tree
| node : unit_tree → unit_tree → unit_tree

namespace unit_tree

instance : inhabited unit_tree := ⟨nil⟩

/-- A unit tree is the same thing as `tree unit` -/
@[simp] def to_tree : unit_tree → tree punit
| nil := tree.nil
| (node a b) := tree.node punit.star a.to_tree b.to_tree

/-- A unit tree is the same thing as `tree unit` -/
@[simp] def of_tree : tree punit → unit_tree
| tree.nil := nil
| (tree.node () a b) := node (of_tree a) (of_tree b)

@[simp] lemma to_tree_of_tree : ∀ (x : tree unit), (of_tree x).to_tree = x
| tree.nil := rfl
| (tree.node () a b) := by rw [of_tree, to_tree, to_tree_of_tree a, to_tree_of_tree b]

@[simp] lemma of_tree_to_tree (x : unit_tree) : of_tree x.to_tree = x :=
by induction x; simp [*]

/-- A non-nil ptree; useful when we want an arbitrary value other than `nil` -/
abbreviation non_nil : unit_tree := node nil nil

@[simp] lemma non_nil_ne : non_nil ≠ nil := by trivial

/-- The number of internal nodes (i.e. not including leaves) of a binary tree -/
@[simp] def nodes : unit_tree → ℕ
| nil := 0
| (node a b) := a.nodes + b.nodes + 1

/-- The number of leaves of a binary tree -/
@[simp] def leaves : unit_tree → ℕ
| nil := 1
| (node a b) := a.leaves + b.leaves

lemma leaves_eq_internal_nodes_succ (x : unit_tree) :
  x.leaves = x.nodes + 1 :=
by { induction x; simp [*, nat.add_comm, nat.add_assoc, nat.add_right_comm], }

lemma leaves_pos (x : unit_tree) : 0 < x.leaves :=
by { induction x, { exact nat.zero_lt_one, }, apply nat.lt_add_left, assumption, }

/-- The left child of the tree, or `nil` if the tree is `nil` -/
@[simp] def left : unit_tree → unit_tree
| nil := nil
| (node l r) := l

/-- The right child of the tree, or `nil` if the tree is `nil` -/
@[simp] def right : unit_tree → unit_tree
| nil := nil
| (node l r) := r


@[simp] def height : unit_tree → ℕ
| nil := 0
| (node x y) := max (height x) (height y) + 1

end unit_tree
