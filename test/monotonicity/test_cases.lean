/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import tactic.monotonicity.interactive

open list tactic tactic.interactive

meta class elaborable (α : Type) (β : out_param Type) :=
  (elaborate : α → tactic β)

export elaborable (elaborate)

meta instance : elaborable pexpr expr :=
⟨ to_expr ⟩

meta instance elaborable_list {α α'} [elaborable α α'] : elaborable (list α) (list α') :=
⟨ mmap elaborate ⟩

meta def mono_function.elaborate : mono_function ff → tactic mono_function
| (mono_function.non_assoc x y z) :=
mono_function.non_assoc <$> elaborate x
                        <*> elaborate y
                        <*> elaborate z
| (mono_function.assoc x y z) :=
mono_function.assoc <$> elaborate x
                    <*> traverse elaborate y
                    <*> traverse elaborate z
| (mono_function.assoc_comm x y) :=
mono_function.assoc_comm <$> elaborate x
                         <*> elaborate y

meta instance elaborable_mono_function : elaborable (mono_function ff) mono_function :=
⟨ mono_function.elaborate ⟩

meta instance prod_elaborable {α α' β β' : Type} [elaborable α α']  [elaborable β β']
: elaborable (α × β) (α' × β') :=
⟨ λ i, prod.rec_on i (λ x y, prod.mk <$> elaborate x <*> elaborate y) ⟩

meta def parse_mono_function' (l r : pexpr) :=
do l' ← to_expr l,
   r' ← to_expr r,
   parse_ac_mono_function { mono_cfg . } l' r'

run_cmd
do xs ← mmap to_expr [``(1),``(2),``(3)],
   ys ← mmap to_expr [``(1),``(2),``(4)],
   x ← match_prefix { unify := ff } xs ys,
   p ← elaborate ([``(1),``(2)] , [``(3)], [``(4)]),
   guard $ x = p

run_cmd
do xs ← mmap to_expr [``(1),``(2),``(3),``(6),``(7)],
   ys ← mmap to_expr [``(1),``(2),``(4),``(5),``(6),``(7)],
   x ← match_assoc { unify := ff } xs ys,
   p ← elaborate ([``(1), ``(2)], [``(3)], ([``(4), ``(5)], [``(6), ``(7)])),
   guard (x = p)

run_cmd
do x ← to_expr ``(7 + 3 : ℕ) >>= check_ac,
   x ← pp x.2.2.1,
   let y := "(some (is_left_id.left_id, (is_right_id.right_id, 0)))",
   guard (x.to_string = y) <|> fail ("guard: " ++ x.to_string)

meta def test_pp {α} [has_to_tactic_format α] (tag : format) (expected : string) (prog : tactic α) :
  tactic unit :=
do r ← prog,
   pp_r ← pp r,
   guard (pp_r.to_string = expected) <|> fail format!"test_pp: {tag}"

run_cmd
do test_pp "test1"
           "(3 + 6, (4 + 5, ([], has_add.add _ 2 + 1)))"
           (parse_mono_function' ``(1 + 3 + 2 + 6) ``(4 + 2 + 1 + 5)),
   test_pp "test2"
           "([1] ++ [3] ++ [2] ++ [6], ([4] ++ [2] ++ [1] ++ [5], ([], append none _ none)))"
           (parse_mono_function' ``([1] ++ [3] ++ [2] ++ [6]) ``([4] ++ [2] ++ ([1] ++ [5]))),
   test_pp "test3"
           "([3] ++ [2], ([5] ++ [4], ([], append (some [1]) _ (some [2]))))"
           (parse_mono_function' ``([1] ++ [3] ++ [2] ++ [2]) ``([1] ++ [5] ++ ([4] ++ [2])))

def my_id {α : Type*} : α → α := id

@[mono]
lemma test_monotone {α : Type*} [preorder α] : monotone (my_id : α → α) :=
λ x y h, h

example : my_id 0 ≤ my_id 1 :=
begin
  mono,
  simp,
end

@[mono]
lemma test_strict_mono {α : Type*} [preorder α] : strict_mono (my_id : α → α) :=
λ x y h, h

example : my_id 0 < my_id 1 :=
begin
  mono,
  simp,
end
