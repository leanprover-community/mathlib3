/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jannis Limperg
-/

universes u

meta class variable_names (α : Type u) : Type (u + 1) :=
(names : name × list name)

meta instance : variable_names nat :=
⟨⟨`n, [`m, `o, `p]⟩⟩


namespace tactic

meta def typical_variable_names (t : expr) : tactic (list name) := do
  var_names ← to_expr ``(variable_names.names %%t),
  ⟨n, ns⟩ ← eval_expr (name × list name) var_names,
  pure $ n :: ns

end tactic
