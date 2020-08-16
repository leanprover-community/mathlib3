/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import data.option.defs
import meta.expr

/-!
# Matching expressions with leading binders

This module defines a family of tactics for matching expressions with leading Π
or λ binders, similar to Core's `mk_local_pis`. They all iterate over an
expression, processing one leading binder at a time. The bound variable is
replaced by either a fresh local constant or a fresh metavariable in the binder
body, 'opening' the binder. We then recurse into this new body. This scheme is
implemented by `tactic.mk_binder`.

Based on `mk_binder`, we define many variations of this recipe:

- `mk_local_{pis,lambdas}` opens all leading Π/λ binders and replaces them with
  fresh local constants. Example:

  ```
  mk_local_lambdas `(λ (x : X) (y : Y), f x y) =
    ([`(_fresh.1), `(_fresh.2)], `(f _fresh.1 _fresh.2))
  ```

  `_fresh.1` and `_fresh.2` are fresh local constants (with types `X` and `Y`,
  respectively). The second component of the pair is the lambda body with
  `x` replaced by `_fresh.1` and `y` replaced by `_fresh.2`.
- `mk_meta_{pis,lambdas}` opens all leading Π/λ binders and replaces them with
  fresh metavariables.
- `mk_{local,meta}_{pis,lambdas}n` opens only the first `n` leading binders.
  These functions fail if there are not at least `n` leading binders. Example:

  ```
  mk_local_pisn `(Π (x : X) (y : Y), P x y) 1 =
    ([`(_fresh.1)], `(Π (y : Y), P _fresh.1 y))
  ```
- `mk_{local,meta}_{pis,lambdas}[n]_whnf` normalises the input expression each
  time before trying to match a binder. Example:

  ```
  mk_local_lambdas_whnf `(let f := λ (x : X), g x y in f) =
    ([`(_fresh.1)], `(g _fresh.1 y))
  ```
- `tactic.get_pi_binders` and `tactic.get_pi_binders_nondep` are more
  specialised instances of `mk_binder`.
-/

namespace tactic

open expr

/-- Auxiliary function for `mk_binders`. -/
@[inline] private meta def mk_binders_aux {α}
  (match_binder : ℕ → expr → tactic (option (name × binder_info × expr × expr)))
  (binder_replacement : name → binder_info → expr → tactic expr)
  (result : ℕ → name → binder_info → expr → expr → tactic (option α)) :
  ℕ → expr → tactic (list α × expr) :=
λ depth e, do
  some (name, bi, type, body) ← match_binder depth e | pure ([], e),
  replacement ← binder_replacement name bi type,
  oa ← result depth name bi type body,
  (as, rest) ← mk_binders_aux (depth + 1) (body.instantiate_var replacement),
  let as' := oa.elim as (λ a, a :: as),
  pure (as', rest)

/--
`mk_binders` implements the common functionality of functions like
`get_pi_binders` and `mk_meta_pis`. It proceeds as follows:

1. Match a pi or lambda binder using `match_binder`. `match_binder` should
   return the name, binder_info, type and body of a leading binder.
   Stop if this returns `none`.
2. Use `binder_replacement` to constructs a replacement for this binder (in
   our applications either a local constant or a metavariable) and instantiate
   the bound variable with this replacement in the binder body.
3. Use `result` to construct a result.
4. Recurse into the binder body.

Returns the list of results and the rest of the expression (with previously
bound variables instantiated with their replacements).

`binder_replacement` and `result` receive the binder information returned by
`match_binder`. `match_binder` and `result` also receive the current recursion
depth.

If `match_binder`, `binder_replacement` or `result` fail at any point, the whole
tactic fails.
-/
@[inline] meta def mk_binders {α}
  (match_binder : ℕ → expr → tactic (option (name × binder_info × expr × expr)))
  (binder_replacement : name → binder_info → expr → tactic expr)
  (result : ℕ → name → binder_info → expr → expr → tactic (option α)) :
  expr → tactic (list α × expr) :=
mk_binders_aux match_binder binder_replacement result 0

/--
A special case of `mk_binders` which returns the binder replacements returned by
`binder_replacement`.
-/
@[inline] meta def mk_binders'
  (match_binder : ℕ → expr → tactic (option (name × binder_info × expr × expr)))
  (binder_replacement : name → binder_info → expr → tactic expr) :
  expr → tactic (list expr × expr) :=
mk_binders match_binder binder_replacement
  (λ _ name bi type _, some <$> binder_replacement name bi type)

/--
Auxiliary function which is used by the `mk_{local,meta}_{pis,lambdas}n` family
of functions. It implements the "match exactly `max_depth` binders" logic.
-/
@[inline] private meta def match_with_depth {α}
  (match_binder : expr → tactic (option α))
  (max_depth : ℕ) (current_depth : ℕ) (e : expr) : tactic (option α) :=
  if current_depth ≥ max_depth then none else do
    (some x) ← match_binder e | failed,
    pure (some x)

/--
Like `tactic.mk_local_pis` but the Π binders of the input expression are
instantiated with new metavariables instead of new local constants.
-/
meta def mk_meta_pis : expr → tactic (list expr × expr) :=
mk_binders' (λ _ e, pure e.match_pi) (λ _ _ t, mk_meta_var t)

/--
Like `tactic.mk_local_pis` but only instantiates the first `n` Π binders. Fails
if `e` does not start with at least `n` Π binders.
-/
meta def mk_local_pisn (e : expr) (n : ℕ) : tactic (list expr × expr) :=
mk_binders' (match_with_depth (pure ∘ match_pi) n) mk_local' e

/--
Like `mk_meta_pis` but only instantiates the first `n` Π binders. Fails if `e`
does not start with at least `n` Π binders.
-/
meta def mk_meta_pisn (e : expr) (n : ℕ) : tactic (list expr × expr) :=
mk_binders' (match_with_depth (pure ∘ match_pi) n) (λ _ _ t, mk_meta_var t) e

/--
Like `mk_local_pis` but the input expression is reduced to weak head normal form
(with transparency `md`) each time before we check whether it is a Π type.
-/
meta def mk_local_pis_whnf (e : expr) (md := semireducible) :
  tactic (list expr × expr) :=
mk_binders' (λ _ e, match_pi <$> whnf e md) mk_local' e

/--
Like `mk_meta_pis` but the input expression is reduced to weak head normal form
(with transparency `md`) each time before we check whether it is a Π type.
-/
meta def mk_meta_pis_whnf (e : expr) (md := semireducible) :
  tactic (list expr × expr) :=
mk_binders' (λ _ e, match_pi <$> whnf e md) (λ _ _ t, mk_meta_var t) e

/--
Like `mk_local_pisn` but the input expression is reduced to weak head normal
form (with transparency `md`) each time before we check whether it is a Π type.
-/
meta def mk_local_pisn_whnf (e : expr) (n : ℕ) (md := semireducible) :
  tactic (list expr × expr) :=
mk_binders' (match_with_depth (λ e, match_pi <$> whnf e md) n)
  mk_local' e

/--
Like `mk_meta_pisn` but the input expression is reduced to weak head normal
form (with transparency `md`) each time before we check whether it is a Π type.
-/
meta def mk_meta_pisn_whnf (e : expr) (n : ℕ) (md := semireducible) :
  tactic (list expr × expr) :=
mk_binders' (match_with_depth (λ e, match_pi <$> whnf e md) n)
  (λ _ _ t, mk_meta_var t) e

/--
A variant of `tactic.mk_local_pis` which returns `binder`s instead of local
constants. See also `expr.pi_binders` (which produces open terms).
-/
meta def get_pi_binders : expr → tactic (list binder × expr) :=
mk_binders (λ _ e, pure e.match_pi) mk_local'
  (λ _ name bi type _, pure $ some $ binder.mk name bi type)

/--
A variant of `get_pi_binders` that returns only nondependent binders (i.e.
those binders that do not occur later in the expression). Also returns the
index of each returned binder (starting at 0).
-/
meta def get_pi_binders_nondep : expr → tactic (list (ℕ × binder) × expr) :=
mk_binders (λ _ e, pure e.match_pi) mk_local'
  (λ depth name bi type body,
    pure $ if body.has_var then none else some (depth, binder.mk name bi type))

/--
`mk_local_lambdas e` instantiates all leading lambda binders of `e` with fresh
local constants. Returns the new local constants and the remainder of `e`.
Example:

```
mk_local_lambdas `(λ (x : X) (y : Y), f x y) =
  ([_fresh.1, _fresh.2], `(f _fresh.1 _fresh.2))
```
-/
meta def mk_local_lambdas : expr → tactic (list expr × expr) :=
mk_binders' (λ _ e, pure e.match_lam) mk_local'

/--
Like `mk_local_lambdas` but instantiates the bound variables with fresh
metavariables instead of fresh local constants.
-/
meta def mk_meta_lambdas : expr → tactic (list expr × expr) :=
mk_binders' (λ _ e, pure e.match_lam) (λ _ _ t, mk_meta_var t)

/--
Like `mk_local_lambdas` but only instantiates the first `n` lambda binders.
Fails if `e` does not start with at least `n` lambda binders.
-/
meta def mk_local_lambdasn (e : expr) (n : ℕ) : tactic (list expr × expr) :=
mk_binders' (match_with_depth (pure ∘ match_lam) n) mk_local' e

/--
Like `mk_meta_lambdas` but only instantiates the first `n` lambda binders.
Fails if `e` does not start with at least `n` lambda binders.
-/
meta def mk_meta_lambdasn (e : expr) (n : ℕ) : tactic (list expr × expr) :=
mk_binders' (match_with_depth (pure ∘ match_lam) n) (λ _ _ t, mk_meta_var t) e

/--
Like `mk_local_lambdas` but the input expression is reduced to weak head normal
form (with transparency `md`) each time before we check whether it start with a
lambda binder.
-/
meta def mk_local_lambdas_whnf (e : expr) (md := semireducible) :
  tactic (list expr × expr) :=
mk_binders' (λ _ e, match_lam <$> whnf e md) mk_local' e

/--
Like `mk_meta_lambdas` but the input expression is reduced to weak head normal
form (with transparency `md`) each time before we check whether it start with a
lambda binder.
-/
meta def mk_meta_lambdas_whnf (e : expr) (md := semireducible) :
  tactic (list expr × expr) :=
mk_binders' (λ _ e, match_lam <$> whnf e md) (λ _ _ t, mk_meta_var t) e

/--
Like `mk_local_lambdasn` but the input expression is reduced to weak head normal
form (with transparency `md`) each time before we check whether it start with a
lambda binder.
-/
meta def mk_local_lambdasn_whnf (e : expr) (n : ℕ) (md := semireducible) :
  tactic (list expr × expr) :=
mk_binders' (match_with_depth (λ e, match_lam <$> whnf e md) n) mk_local' e

/--
Like `mk_meta_lambdasn` but the input expression is reduced to weak head normal
form (with transparency `md`) each time before we check whether it start with a
lambda binder.
-/
meta def mk_meta_lambdasn_whnf (e : expr) (n : ℕ) (md := semireducible) :
  tactic (list expr × expr) :=
mk_binders' (match_with_depth (λ e, match_lam <$> whnf e md) n)
  (λ _ _ t, mk_meta_var t) e

end tactic
