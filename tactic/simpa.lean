/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

namespace tactic
namespace interactive
open interactive interactive.types expr lean.parser

local postfix `?`:9001 := optional

/--
This is a "finishing" tactic modification of `simp`.

* `simpa [rules, ...] using e` will simplify the goal and the type of
  `e` using `rules`, then try to close the goal using `e`.

* `simpa [rules, ...]` will simplify the goal using `rules`, then try
  to close it using `assumption`. -/
meta def simpa (use_iota_eqn : parse $ (tk "!")?) (no_dflt : parse only_flag)
  (hs : parse simp_arg_list) (attr_names : parse with_ident_list)
  (tgt : parse (tk "using" *> texpr)?) (cfg : simp_config_ext := {}) : tactic unit :=
let simp_at lc close_tac :=
  try (simp use_iota_eqn no_dflt hs attr_names (loc.ns lc) cfg) >>
  (close_tac <|> trivial) in
match tgt with
| none := get_local `this >> simp_at [some `this, none] assumption <|> simp_at [none] assumption
| some e := do
  e ← i_to_expr e <|> do {
    ty ← target,
    e ← i_to_expr_strict ``(%%e : %%ty), -- for positional error messages, don't care about the result
    pty ← pp ty, ptgt ← pp e,
    -- Fail deliberately, to advise regarding `simp; exact` usage
    fail ("simpa failed, 'using' expression type not directly " ++
      "inferrable. Try:\n\nsimpa ... using\nshow " ++
      to_fmt pty ++ ",\nfrom " ++ ptgt : format) },
  match e with
  | local_const _ lc _ _ := simp_at [some lc, none] (get_local lc >>= tactic.exact)
  | e := do
    t ← infer_type e,
    assertv `this t e >> simp_at [some `this, none] (get_local `this >>= tactic.exact)
  end
end

end interactive
end tactic
