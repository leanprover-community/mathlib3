/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
import data.tree
import logic.encodable.tree

/-!
# Conversion of iteration to recursion using a stack

This file essentially describes how to eliminate recursion into iteration.

## Recursion with an explicit stack

For W-types, we can define a function `stack_rec`,
which is similar to `rec` except that it explicitly keeps track of the
arguments on the stack, rather than allowing the recursive function to return
higher-order (non-encodable) functions.

For example, consider checking for equality of trees: the recursor has type `tree → tree → bool`,
the motive is `tree → bool`, and the inductive step calls the inductive hypotheses,
which are `left : tree → bool` and `right : tree bool` on the current left and right subtrees.

This is an issue, because `tree → bool` is not encodable, and indeed, any total
complexity class (e.g. the primitive recursive functions) cannot interpret itself,
so it is not possible to have the motive be a representation of the "code" for `tree → bool`.

In general, for a W-type with nodes labeled by `α` and children by `β : α → Type`,
we write `stack_rec : W_type β → γ → δ`, defined primarily by
  - `pre : Π x, β x → γ → γ`: "prepares" the arguments to the inductive hypothesis,
    given the current node's children `Π x, β x` and the current argument `γ`
  - `post : (Π x, (β x → δ) → δ) → γ → δ`: computes the result given the inductive
  hypotheses `(β x → δ)` and the current argument `γ`.

TODO: generalize `stack_rec` to all W-types. Tactic to automatically convert structural
recursion where the motive is itself a function to `stack_rec`. This will enable us
to write functions naturally in Lean and then automatically prove that they are primitive recursive,
polynomial time, etc. using a tactic.
-/

namespace unit_tree
variables {α : Type} {β : Type} (base : α → β) (pre₁ pre₂ : unit_tree → unit_tree → α → α)
  (post : β → β → unit_tree → unit_tree → α → β)

/-- Recursion with an explicit stack for `unit_tree` -/
@[simp]
def stack_rec : unit_tree → α → β
| nil d := base d
| (node x y) d := post (stack_rec x (pre₁ x y d)) (stack_rec y (pre₂ x y d)) x y d

/-- An element on the stack is either the result (`sum.inr (x : β)`), or
  the: tree, the argument α, and potentially what the left branch computed
  if that computation has finished (`option β`)
  -/
abbreviation iterator_stack (α β : Type) := (unit_tree × α × option β) ⊕ β

/-- Do a single step of the iteration. In particular,
    - If the top of the stack is a result, pop the value before that and plug in the result.
    - If the top of the stack is a tree with the left branch uncomputed, push to the stack the
        arguments for the left branch, unless the tree is `nil`, in which case we directly
        compute the result.
    - If the top of the stack is a tree with the left branch computed, push to the stack the
      arguments for the right branch.
  This halts when the stack contains fewer than 2 elements, or the top 2 elements are both results
  -/
@[simp] def stack_step : list (iterator_stack α β) → list (iterator_stack α β)
| (sum.inr res :: sum.inl (tree, arg, none) :: xs) := sum.inl (tree, arg, some res) :: xs
| (sum.inr res :: sum.inl (tree, arg, some left_res) :: xs) :=
    sum.inr (post left_res res tree.left tree.right arg) :: xs
| L@(sum.inl (tree, arg, some left_res) :: xs) :=
  sum.inl (tree.right, pre₂ tree.left tree.right arg, none) :: L
| (sum.inl (nil, arg, none) :: xs) := sum.inr (base arg) :: xs
| L@(sum.inl ((node x y), arg, none) :: xs) := sum.inl (x, pre₁ x y arg, none) :: L
| x := x

@[simp] lemma stack_step_nil : stack_step base pre₁ pre₂ post [] = [] := rfl
@[simp] lemma stack_step_singleton (res : β) :
  stack_step base pre₁ pre₂ post [sum.inr res] = [sum.inr res] := rfl

def time_steps (x : unit_tree) : ℕ := 5 * x.nodes + 1

@[simp] lemma time_steps_nil : time_steps nil = 1 := rfl
lemma time_steps_node (a b) : time_steps (node a b) = 1 + b.time_steps + 2 + a.time_steps + 1 :=
by { simp only [time_steps, nodes, mul_add, show 5 * 1 = 1 + 2 + 1 + 1, from rfl], ac_refl, }

@[simp] lemma stack_step_iterate (x : unit_tree) (arg : α) (xs : list (iterator_stack α β)) :
  (stack_step base pre₁ pre₂ post)^[x.time_steps] (sum.inl (x, arg, none) :: xs) =
  (sum.inr $ x.stack_rec base pre₁ pre₂ post arg) :: xs :=
by induction x generalizing arg xs; simp [time_steps_node, function.iterate_add, *]

lemma stack_step_iterate' (x : unit_tree) (arg : α) {n : ℕ} (hn : 5 * x.nodes + 1 ≤ n) :
  (stack_step base pre₁ pre₂ post)^[n] [sum.inl (x, arg, none)] =
    [sum.inr $ x.stack_rec base pre₁ pre₂ post arg] :=
begin
  rw ← time_steps at hn,
  rcases le_iff_exists_add'.mp hn with ⟨n, rfl⟩,
  simp [function.iterate_add, function.iterate_fixed],
end

end unit_tree

namespace list
variables {α β : Type} {γ : Type*} (base : α → β) (pre : γ → list γ → α → α)
  (post : β → γ → list γ → α → β)

@[simp] def stack_rec : list γ → α → β
| [] a := base a
| (x :: xs) a := post (stack_rec xs (pre x xs a)) x xs a

end list

namespace nat
variables {α β : Type} (base : α → β) (pre : ℕ → α → α) (post : β → ℕ → α → β)

@[simp] def stack_rec : ℕ → α → β
| 0 x := base x
| (n+1) x := post (stack_rec n (pre n x)) n x

end nat
