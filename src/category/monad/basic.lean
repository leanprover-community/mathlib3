/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Simon Hudon
-/

import tactic.basic

/-!
# Monad

## Attributes

 * extensionality
 * functor_norm
 * monad_norm

## Implementation Details

Set of rewrite rules and automation for monads in general and
`reader_t`, `state_t`, `except_t` and `option_t` in particular.

The rewrite rules for monads are carefully chosen so that `simp with
functor_norm` will not introduce monadic vocabulary in a context where
applicatives would do just fine but will handle monadic notation
already present in an expression.

In a context where monadic reasoning is desired `simp with monad_norm`
will translate functor and applicative notation into monad notation
and use regular `functor_norm` rules as well.

## Tags

functor, applicative, monad, simp

-/

run_cmd mk_simp_attr `monad_norm [`functor_norm]

attribute [extensionality] reader_t.ext state_t.ext except_t.ext option_t.ext
attribute [functor_norm]   bind_assoc pure_bind bind_pure
attribute [monad_norm] seq_eq_bind_map
universes u v

@[monad_norm]
lemma map_eq_bind_pure_comp (m : Type u → Type v) [monad m] [is_lawful_monad m] {α β : Type u} (f : α → β) (x : m α) :
  f <$> x = x >>= pure ∘ f := by rw bind_pure_comp_eq_map

namespace list
/-- the monad combinator that checks whether p holds for all elements in the list -/
def mall {m : Type → Type v} [monad m] {α} (l : list α) (p : α → m bool) : m bool :=
l.mfoldr (λ a r, (&& r) <$> p a) tt

/-- the monad combinator that checks whether p holds for some element in the list -/
def many {m : Type → Type v} [monad m] {α} (l : list α) (p : α → m bool) : m bool :=
l.mfoldr (λ a r, ( || r) <$> p a) tt
end list
