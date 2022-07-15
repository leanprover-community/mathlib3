/-
Copyright (c) 2020 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/

/-!

# Workaround for stack overflows with `has_reflect string`

The default `has_reflect string` instance in Lean only work for strings up to
few thousand characters.  Anything larger than that will trigger a stack overflow because
the string is represented as a very deeply nested expression:
https://github.com/leanprover-community/lean/issues/144

This file adds a higher-priority instance for `has_reflect string`, which
behaves exactly the same for small strings (up to 256 characters). Larger
strings are carefully converted into a call to `string.join`.

-/

/--
Splits a string into chunks of at most `size` characters.
-/
meta def string.to_chunks (size : ℕ) : string → opt_param (list string) [] → list string | s acc :=
if s.length ≤ size then s :: acc else
string.to_chunks (s.popn_back size) (s.backn size :: acc)

section
local attribute [semireducible] reflected
meta instance {α} [has_reflect α] : has_reflect (thunk α) | a :=
expr.lam `x binder_info.default (reflect unit) (reflect $ a ())
end

@[priority 2000]
meta instance : has_reflect string | s :=
let chunk_size := 256 in
if s.length ≤ chunk_size then reflect s else
have ts : list (thunk string), from (s.to_chunks chunk_size).map (λ s _, s),
have h : s = string.join (ts.map (λ t, t ())), from undefined,
suffices reflected _ (string.join $ ts.map (λ t, t ())), by rwa h,
`(string.join $ list.map _ _)
