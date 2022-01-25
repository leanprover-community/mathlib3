/-
Copyright (c) 2020 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton
-/

import tactic.core

/-!
# `with_local_reducibility`

Run a tactic in an environment with a temporarily modified reducibility attribute
for a specified declaration.
-/

namespace tactic

/-- Possible reducibility attributes for a declaration:
reducible, semireducible (the default), irreducible. -/
@[derive decidable_eq]
inductive decl_reducibility
| reducible
| semireducible
| irreducible

/-- Satisfy the inhabited linter -/
instance : inhabited decl_reducibility :=
⟨decl_reducibility.semireducible⟩

/-- Get the reducibility attribute of a declaration.
Fails if the name does not refer to an existing declaration. -/
meta def get_decl_reducibility (n : name) : tactic decl_reducibility :=
do is_irred ← has_attribute' `irreducible n,
   if is_irred then pure decl_reducibility.irreducible else
do is_red ← has_attribute' `reducible n,
   if is_red then pure decl_reducibility.reducible else
do e ← get_env,
   if e.contains n then pure decl_reducibility.semireducible else
   fail format!"get_decl_reducibility: no declaration {n}"

/-- Return the attribute (as a `name`) corresponding to a reducibility level. -/
def decl_reducibility.to_attribute : decl_reducibility → name
| decl_reducibility.reducible := `reducible
| decl_reducibility.semireducible := `semireducible
| decl_reducibility.irreducible := `irreducible

-- Note: even though semireducible definitions don't have the `semireducible` attribute
-- (according to `has_attribute`), setting `semireducible` still has the intended effect
-- of clearing `reducible`/`irreducible`.

/-- Set the reducibility attribute of a declaration.
If `persistent := ff`, this is scoped to the enclosing `section`, like `local attribute`. -/
meta def set_decl_reducibility (n : name) (r : decl_reducibility) (persistent := ff)
  : tactic unit :=
set_basic_attribute r.to_attribute n persistent

/-- Execute a tactic with a temporarily modified reducibility attribute for a declaration. -/
meta def with_local_reducibility {α : Type*} (n : name) (r : decl_reducibility)
  (body : tactic α) : tactic α :=
do r' ← get_decl_reducibility n,
   bracket (set_decl_reducibility n r) body (set_decl_reducibility n r')

end tactic
