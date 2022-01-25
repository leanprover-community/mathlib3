import control.traversable.derive
import control.traversable.instances

universes u

/- traversable -/
open tactic.interactive

run_cmd do
lawful_traversable_derive_handler' `test ``(is_lawful_traversable) ``list
-- the above creates local instances of `traversable` and `is_lawful_traversable`
-- for `list`
-- do not put in instances because they are not universe polymorphic

@[derive [traversable, is_lawful_traversable]]
structure my_struct (α : Type) :=
  (y : ℤ)

@[derive [traversable, is_lawful_traversable]]
inductive either (α : Type u)
| left : α → ℤ → either
| right : α → either

@[derive [traversable, is_lawful_traversable]]
structure my_struct2 (α : Type u) : Type u :=
  (x : α)
  (y : ℤ)
  (η : list α)
  (k : list (list α))

@[derive [traversable, is_lawful_traversable]]
inductive rec_data3 (α : Type u) : Type u
| nil : rec_data3
| cons : ℕ → α → rec_data3 → rec_data3 → rec_data3

@[derive traversable]
meta structure meta_struct (α : Type u) : Type u :=
  (x : α)
  (y : ℤ)
  (z : list α)
  (k : list (list α))
  (w : expr)

@[derive [traversable,is_lawful_traversable]]
inductive my_tree (α : Type)
| leaf : my_tree
| node : my_tree → my_tree → α → my_tree

section
open my_tree (hiding traverse)

def x : my_tree (list nat) :=
node
  leaf
  (node
    (node leaf leaf [1,2,3])
    leaf
    [3,2])
  [1]

/-- demonstrate the nested use of `traverse`. It traverses each node of the tree and
in each node, traverses each list. For each `ℕ` visited, apply an action `ℕ -> state (list ℕ) unit`
which adds its argument to the state. -/
def ex : state (list ℕ) (my_tree $ list unit) :=
do xs ← traverse (traverse $ λ a, modify $ list.cons a) x,
   pure xs

example : (ex.run []).1 = node leaf (node (node leaf leaf [(), (), ()]) leaf [(), ()]) [()] := rfl
example : (ex.run []).2 = [1, 2, 3, 3, 2, 1] := rfl
example : is_lawful_traversable my_tree := my_tree.is_lawful_traversable

end
