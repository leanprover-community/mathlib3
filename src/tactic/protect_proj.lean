/-
Copyright (c) 2020 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import meta.expr
/-!
# protect_proj user attribute

Attribute to protect the projections of a structure.
If a structure `foo` is marked with the `protect_proj` user attribute, then
all of the projections become projected, meaning they must always be referred to by
their full name `foo.bar`, even when the `foo` namespace is open.
-/

namespace tactic

/-- Tactic that is executed when a structure is marked with the `protect_proj` attribute -/
meta def protect_proj_tac (n : name) (env : environment) : tactic environment :=
option.cases_on (env.structure_fields_full n)
  (do trace ("protect_proj failed: declaration is not a structure"),
    return env)
  (λ l, l.foldl (λ env n, do env ← env, return (env.mk_protected n)) (return env))

/--  -/
@[user_attribute] meta def protect_proj_attr : user_attribute :=
{ name := "protect_proj",
  descr := "Attribute to protect the projections of a structure.
    If a structure `foo` is marked with the `protect_proj` user attribute, then
    all of the projections become projected, meaning they must always be referred to by
    their full name `foo.bar`, even when the `foo` namespace is open.",
  after_set := some (λ n _ _, get_env >>= protect_proj_tac n >>= set_env) }

end tactic
