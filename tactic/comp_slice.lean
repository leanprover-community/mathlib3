-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.category

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
/--
`comp_slice` is a conv tactic: if the current focus is a composition of several morphisms,
`comp_slice a b` reassociates as needed, and zooms in on the `a`-th through `b`-th morphisms.

Thus if the current focus is `(a ≫ b) ≫ ((c ≫ d) ≫ e)`, then `comp_slice 2 3` zooms to `b ≫ c`.
 -/
meta def comp_slice (a b : ℕ) : conv unit :=
do repeat $ to_expr ``(category.assoc) >>= λ e, tactic.rewrite_target e {symm:=ff},
   iterate_range (a-1) (a-1) (do conv.congr, conv.skip),
   k ← repeat_count $ to_expr ``(category.assoc) >>= λ e, tactic.rewrite_target e {symm:=tt},
   iterate_range (k+1+a-b) (k+1+a-b) conv.congr,
   repeat $ to_expr ``(category.assoc) >>= λ e, tactic.rewrite_target e {symm:=ff},
   rotate 1,
   iterate_exactly (k+1+a-b) conv.skip

namespace interactive
meta def comp_slice := conv.comp_slice
end interactive
end conv

