import tactic.core
import data.matrix.basic

section tactic
open tactic

#eval show tactic unit, from do
  ops ← list_binary_operands `(@has_add.add ℕ _) `(3 + (4 * 5 + 6) + 7 / 3),
  guard $ ops = [`(3), `(4*5), `(6), `(7/3)]

#eval show tactic unit, from do
  ops ← list_binary_operands `(@list.append ℕ) `([1, 2] ++ [3, 4] ++ (1 :: [])),
  guard $ ops = [`([1, 2]), `([3, 4]), `([1])]

-- matches should not care about the paths taken to find a typeclass
#eval show tactic unit, from do
  ops ← list_binary_operands `(@has_add.add ℕ _)
    `(@has_add.add _ (add_zero_class.to_has_add _) 1 $
        @has_add.add _ (add_semigroup.to_has_add _) 2 3),
  guard $ ops = [`(1), `(2), `(3)]

end tactic

section expr
open expr

-- this fails
-- #eval show tactic unit, from do
--   let ops := list_summands
--     `(@has_add.add _ (add_zero_class.to_has_add _) 1 $
--         @has_add.add _ (add_semigroup.to_has_add _) 2 3),
--   guard $ ops = [`(1), `(2), `(3)]

def a : fin 2 → fin 2 → ℕ := λ _ _, 0

#eval show tactic unit, from do
  let ops := list_factors `(a * a),
  guard $ ops = [`(a), `(a)]

-- if the operation are actually different, always use the outermost one
#eval show tactic unit, from do
  let ops := list_factors `(a * (a * a : matrix _ _ ℕ)),
  guard $ ops = [`(a), `(a * a : matrix _ _ ℕ)]

#eval show tactic unit, from do
  let ops := list_factors `(a * (a * a : _) : matrix _ _ ℕ),
  guard $ ops = [`(a), `(a * a)]

end expr
