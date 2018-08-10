/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

A mechanism for defining tactics for use in auto params, whose
meaning is defined incrementally through attributes.
-/
namespace tactic

meta def replacer_attr (ntac : name) : user_attribute :=
{ name := ntac,
  descr :=
  "Replaces the definition of `" ++ to_string ntac ++ "`. This should be " ++
  "applied to a definition with the type `tactic unit`, which will be " ++
  "called whenever `" ++ to_string ntac ++ "` is called. The definition " ++
  "can optionally have an argument of type `tactic unit` or " ++
  "`option (tactic unit)` which refers to the previous definition, if any.",
  after_set := some $ λ n _ _, do d ← get_decl n,
    monad.unlessb (d.type =ₐ `(tactic unit) ∨
      d.type =ₐ `(tactic unit → tactic unit) ∨
      d.type =ₐ `(option (tactic unit) → tactic unit)) $
    fail format!"incorrect type for @[{ntac}]" }

meta def replacer_core (ntac : name) : list name → tactic unit
| [] := fail ("no implementation defined for " ++ to_string ntac)
| (n::ns) := do d ← get_decl n, let t := d.type,
  if t =ₐ `(tactic unit) then
    monad.join (mk_const n >>= eval_expr (tactic unit))
  else if t =ₐ `(tactic unit → tactic unit) then
    do tac ← mk_const n >>= eval_expr (tactic unit → tactic unit),
       tac (replacer_core ns)
  else if t =ₐ `(option (tactic unit) → tactic unit) then
    do tac ← mk_const n >>= eval_expr (option (tactic unit) → tactic unit),
       tac (guard (ns ≠ []) >> some (replacer_core ns))
  else failed

meta def replacer (ntac : name) : tactic unit :=
attribute.get_instances ntac >>= replacer_core ntac

/-- Define a new replaceable tactic. -/
meta def def_replacer (ntac : name) : tactic unit :=
let nattr := ntac <.> "attr" in do
  add_decl $ declaration.defn nattr []
    `(user_attribute) `(replacer_attr %%(reflect ntac))
    (reducibility_hints.regular 1 tt) ff,
  set_basic_attribute `user_attribute nattr tt,
  add_decl $ declaration.defn ntac []
    `(tactic unit) `(replacer %%(reflect ntac))
    (reducibility_hints.regular 1 tt) ff,
  add_doc_string ntac $
    "The `" ++ to_string ntac ++ "` tactic is a \"replaceable\" " ++
    "tactic, which means that its meaning is defined by tactics that " ++
    "are defined later with the `@[" ++ to_string ntac ++ "]` attribute. " ++
    "It is intended for use with `auto_param`s for structure fields."

open interactive lean.parser
/-- Define a new replaceable tactic. -/
@[user_command] meta def def_replacer_cmd (meta_info : decl_meta_info)
  (_ : parse $ tk "def_replacer") : lean.parser unit :=
do ntac ← ident, def_replacer ntac

end tactic
