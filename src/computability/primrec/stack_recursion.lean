import data.tree

namespace tree

abbreviation iterator_stack (α β : Type*) := (tree unit × α × option β) ⊕ β
variables {α : Type} {β : Type} (base : α → β) (pre₁ pre₂ : tree unit → α → α)
  (post : β → β → tree unit → α → β)

@[simp] def stack_step : list (iterator_stack α β) → list (iterator_stack α β)
| (sum.inr res :: sum.inl (tree, arg, none) :: xs) := sum.inl (tree, arg, some res) :: xs
| (sum.inr res :: sum.inl (tree, arg, some left_res) :: xs) :=
    sum.inr (post left_res res tree arg) :: xs
| L@(sum.inl (tree, arg, some left_res) :: xs) := sum.inl (tree.right, pre₂ tree arg, none) :: L
| (sum.inl (nil, arg, none) :: xs) := sum.inr (base arg) :: xs
| L@(sum.inl ((node () x y), arg, none) :: xs) := sum.inl (x, pre₁ (node () x y) arg, none) :: L
| x := x

end tree
