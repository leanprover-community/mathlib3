/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jannis Limperg
-/

/-!
# A better `clear` tactic

We define `clear'`, an improved version of the standard `clear` tactic. It
solves the following problem: The `clear` tactic, when called with multiple
hypotheses, sometimes fails even though all hypotheses could be cleared. This is
because `clear` is sensitive to the ordering of hypotheses:

```
example {α : Type} {β : α → Type} (a : α) (b : β a) : unit :=
  begin
    clear a b, -- fails
    exact ()
  end
```

When `clear` tries to clear `a`, we still have `b`, which depends on `a`, in the
context, so the operation fails. We give a tactic `clear'` which recognises this
and clears `b` before `a`.

## Implementation notes

The tactic is implemented by processing the hypotheses in reverse context order:
hypotheses occurring later in the context are cleared first. This guarantees
that the dependency order is observed.
-/

open native

namespace native.rb_map

  meta def index_map_aux {α} [hlt : has_lt α] [decidable_rel hlt.lt]
    : ℕ → rb_map α ℕ → list α → rb_map α ℕ
  | _ m [] := m
  | n m (x :: xs) := index_map_aux (n + 1) (m.insert x n) xs

  /-- `index_map xs` is a map which associates to each element of `xs` its index
  in `xs`. -/
  meta def index_map {α} [hlt : has_lt α] [decidable_rel hlt.lt] (xs : list α)
    : rb_map α ℕ :=
  index_map_aux 0 mk_rb_map xs

  /-- `compare_by_value o x y` is true iff `x` and `y` occur in `o` and the
  associated value of `x` is less than that of `y`.
  -/
  meta def compare_by_value {α β} [hlt : has_lt β] [decidable_rel hlt.lt]
    (o : rb_map α β) (x y : α)
    : bool :=
  let islt : option bool := do
    x_ix ← o.find x,
    y_ix ← o.find y,
    pure (x_ix < y_ix)
  in islt.get_or_else false

end native.rb_map

open native.rb_map


namespace tactic

  /-- `context_order ctx e₁ e₂` is true iff `e₁` appears before `e₂` in `ctx`. -/
  meta def context_order (ctx : list expr) : expr → expr → bool :=
  compare_by_value (index_map ctx)

  /-- `context_order` applied to the local context. -/
  meta def local_context_order : tactic (expr → expr → bool) := do
  ctx ← local_context,
  pure (context_order ctx)

  /-- The inverse of a relation: `inverse_rel r x y` is true iff `r x y` is
      false. -/
  @[reducible] private def inverse_rel {α} (r : α → α → bool) (x y : α) : bool :=
  not (r x y)

  /-- Clears the hypotheses in `hyps` if possible. In contrast to `clear`, the
      order of hypotheses does not matter. See `tactic.interactive.clear'` for
      details.
  -/
  meta def clear' (hyps : list expr) : tactic unit := do
  context_order ← inverse_rel <$> local_context_order,
  monad.mapm' clear (hyps.qsort context_order)

end tactic


namespace tactic.interactive

  open tactic interactive lean.parser

  /-- Clears the hypotheses in `hyps` if possible. In contrast to `clear`, the
  order of hypotheses does not matter, even if there are dependencies between
  them.

  For example, the following test would fail if we replaced `clear'` with
  `clear` (since `b` depends on `a`):

  ```
  example {α : Type} {β : α → Type} (a : α) (b : β a) : unit :=
    begin
      clear' a b,
      exact ()
    end
  ``` -/
  meta def clear' (hyps : parse (many ident)) : tactic unit :=
  monad.mapm get_local hyps >>= tactic.clear'

end tactic.interactive
