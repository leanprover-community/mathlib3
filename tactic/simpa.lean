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
This is a "finishing" tactic modification of `simp`. The tactic `simpa [rules, ...] using e`
will simplify the hypothesis `e` using `rules`, then simplify the goal using `rules`, and
try to close the goal using `assumption`. If `e` is a term instead of a local constant,
it is first added to the local context using `have`.
-/
meta def simpa (use_iota_eqn : parse $ (tk "!")?) (no_dflt : parse only_flag)
  (hs : parse simp_arg_list) (attr_names : parse with_ident_list)
  (tgt : parse (tk "using" *> texpr)?) (cfg : simp_config_ext := {}) : tactic unit :=
let simp_at (lc) := try (simp use_iota_eqn no_dflt hs attr_names (loc.ns lc) cfg) >> (assumption <|> trivial) in
match tgt with
| none := get_local `this >> simp_at [some `this, none] <|> simp_at [none]
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
  | local_const _ lc _ _ := simp_at [some lc, none]
  | e := do
    t ← infer_type e,
    assertv `this t e >> simp_at [some `this, none]
  end
end

end interactive
end tactic
