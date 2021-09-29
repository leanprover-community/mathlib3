/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.category.basic

open category_theory

-- TODO someone might like to generalise this tactic to work with other associative structures.

namespace tactic

meta def repeat_with_results {α : Type} (t : tactic α) : tactic (list α) :=
(do r ← t,
    s ← repeat_with_results,
    return (r :: s)) <|> return []

meta def repeat_count {α : Type} (t : tactic α) : tactic ℕ :=
do r ← repeat_with_results t,
   return r.length

end tactic

namespace conv
open tactic
meta def repeat_with_results {α : Type} (t : tactic α) : tactic (list α) :=
(do r ← t,
    s ← repeat_with_results,
    return (r :: s)) <|> return []

meta def repeat_count {α : Type} (t : tactic α) : tactic ℕ :=
do r ← repeat_with_results t,
   return r.length

meta def slice (a b : ℕ) : conv unit :=
do repeat $ to_expr ``(category.assoc) >>= λ e, tactic.rewrite_target e {symm:=ff},
   iterate_range (a-1) (a-1) (do conv.congr, conv.skip),
   k ← repeat_count $ to_expr ``(category.assoc) >>= λ e, tactic.rewrite_target e {symm:=tt},
   iterate_range (k+1+a-b) (k+1+a-b) conv.congr,
   repeat $ to_expr ``(category.assoc) >>= λ e, tactic.rewrite_target e {symm:=ff},
   rotate 1,
   iterate_exactly' (k+1+a-b) conv.skip

meta def slice_lhs (a b : ℕ) (t : conv unit) : tactic unit :=
do conv.interactive.to_lhs,
   slice a b,
   t

meta def slice_rhs (a b : ℕ) (t : conv unit) : tactic unit :=
do conv.interactive.to_rhs,
   slice a b,
   t

namespace interactive
/--
`slice` is a conv tactic; if the current focus is a composition of several morphisms,
`slice a b` reassociates as needed, and zooms in on the `a`-th through `b`-th morphisms.

Thus if the current focus is `(a ≫ b) ≫ ((c ≫ d) ≫ e)`, then `slice 2 3` zooms to `b ≫ c`.
 -/
meta def slice := conv.slice
end interactive
end conv

namespace tactic
open conv
private meta def conv_target' (c : conv unit) : tactic unit :=
do t ← target,
   (new_t, pr) ← c.convert t,
   replace_target new_t pr,
   try tactic.triv, try (tactic.reflexivity reducible)

namespace interactive
open interactive
open lean.parser

/--
`slice_lhs a b { tac }` zooms to the left hand side, uses associativity for categorical
composition as needed, zooms in on the `a`-th through `b`-th morphisms, and invokes `tac`.
-/
meta def slice_lhs (a b : parse small_nat) (t : conv.interactive.itactic) : tactic unit :=
do conv_target' (conv.interactive.to_lhs >> slice a b >> t)
/--
`slice_rhs a b { tac }` zooms to the right hand side, uses associativity for categorical
composition as needed, zooms in on the `a`-th through `b`-th morphisms, and invokes `tac`.
-/
meta def slice_rhs (a b : parse small_nat) (t : conv.interactive.itactic) : tactic unit :=
do conv_target' (conv.interactive.to_rhs >> slice a b >> t)
end interactive
end tactic

/--
`slice_lhs a b { tac }` zooms to the left hand side, uses associativity for categorical
composition as needed, zooms in on the `a`-th through `b`-th morphisms, and invokes `tac`.

`slice_rhs a b { tac }` zooms to the right hand side, uses associativity for categorical
composition as needed, zooms in on the `a`-th through `b`-th morphisms, and invokes `tac`.
-/
add_tactic_doc
{ name := "slice",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.slice_lhs, `tactic.interactive.slice_rhs],
  tags := ["category theory"] }
