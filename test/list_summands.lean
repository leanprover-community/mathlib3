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
