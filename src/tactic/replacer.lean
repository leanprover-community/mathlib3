/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import tactic.core

/-!
# `def_replacer`

A mechanism for defining tactics for use in auto params, whose
meaning is defined incrementally through attributes.
-/

namespace tactic

meta def replacer_core {α : Type} [reflected α]
  (ntac : name) (eval : ∀ β [reflected β], expr → tactic β) :
  list name → tactic α
| [] := fail ("no implementation defined for " ++ to_string ntac)
| (n::ns) := do d ← get_decl n, let t := d.type,
  tac ← do { mk_const n >>= eval (tactic α) } <|>
        do { tac ← mk_const n >>= eval (tactic α → tactic α),
            return (tac (replacer_core ns)) } <|>
        do { tac ← mk_const n >>= eval (option (tactic α) → tactic α),
            return (tac (guard (ns ≠ []) >> some (replacer_core ns))) },
  tac

meta def replacer (ntac : name) {α : Type} [reflected α]
  (F : Type → Type) (eF : ∀ β, reflected β → reflected (F β))
  (R : ∀ β, F β → β) : tactic α :=
attribute.get_instances ntac >>= replacer_core ntac
  (λ β eβ e, R β <$> @eval_expr' (F β) (eF β eβ) e)

meta def mk_replacer₁ : expr → nat → expr × expr
| (expr.pi n bi d b) i :=
  let (e₁, e₂) := mk_replacer₁ b (i+1) in
  (expr.pi n bi d e₁, (`(expr.pi n bi d) : expr) e₂)
| _                  i := (expr.var i, expr.var 0)

meta def mk_replacer₂ (ntac : name) (v : expr × expr) : expr → nat → option expr
| (expr.pi n bi d b) i := do
  b' ← mk_replacer₂ b (i+1),
  some (expr.lam n bi d b')
| `(tactic %%β) i := some $
  (expr.const ``replacer []).mk_app [
    reflect ntac, β, reflect β,
    expr.lam `γ binder_info.default `(Type) v.1,
    expr.lam `γ binder_info.default `(Type) $
    expr.lam `eγ binder_info.inst_implicit ((`(@reflected Type) : expr) β) v.2,
    expr.lam `γ binder_info.default `(Type) $
    expr.lam `f binder_info.default v.1 $
    (list.range i).foldr (λ i e', e' (expr.var (i+2))) (expr.var 0)
  ]
| _ i := none

meta def mk_replacer (ntac : name) (e : expr) : tactic expr :=
mk_replacer₂ ntac (mk_replacer₁ e 0) e 0

meta def valid_types : expr → list expr
| (expr.pi n bi d b) := expr.pi n bi d <$> valid_types b
| `(tactic %%β) := [`(tactic.{0} %%β),
    `(tactic.{0} %%β → tactic.{0} %%β),
    `(option (tactic.{0} %%β) → tactic.{0} %%β)]
| _ := []

meta def replacer_attr (ntac : name) : user_attribute :=
{ name := ntac,
  descr :=
  "Replaces the definition of `" ++ to_string ntac ++ "`. This should be " ++
  "applied to a definition with the type `tactic unit`, which will be " ++
  "called whenever `" ++ to_string ntac ++ "` is called. The definition " ++
  "can optionally have an argument of type `tactic unit` or " ++
  "`option (tactic unit)` which refers to the previous definition, if any.",
  after_set := some $ λ n _ _, do
    d ← get_decl n,
    base ← get_decl ntac,
    guardb ((valid_types base.type).any (=ₐ d.type))
      <|> fail format!"incorrect type for @[{ntac}]" }

/-- Define a new replaceable tactic. -/
meta def def_replacer (ntac : name) (ty : expr) : tactic unit :=
let nattr := ntac <.> "attr" in do
  add_meta_definition nattr []
    `(user_attribute) `(replacer_attr %%(reflect ntac)),
  set_basic_attribute `user_attribute nattr tt,
  v ← mk_replacer ntac ty,
  add_meta_definition ntac [] ty v,
  add_doc_string ntac $
    "The `" ++ to_string ntac ++ "` tactic is a \"replaceable\" " ++
    "tactic, which means that its meaning is defined by tactics that " ++
    "are defined later with the `@[" ++ to_string ntac ++ "]` attribute. " ++
    "It is intended for use with `auto_param`s for structure fields."

open interactive lean.parser
/--
`def_replacer foo` sets up a stub definition `foo : tactic unit`, which can
effectively be defined and re-defined later, by tagging definitions with `@[foo]`.

- `@[foo] meta def foo_1 : tactic unit := ...` replaces the current definition of `foo`.
- `@[foo] meta def foo_2 (old : tactic unit) : tactic unit := ...` replaces the current
  definition of `foo`, and provides access to the previous definition via `old`.
  (The argument can also be an `option (tactic unit)`, which is provided as `none` if
  this is the first definition tagged with `@[foo]` since `def_replacer` was invoked.)

`def_replacer foo : α → β → tactic γ` allows the specification of a replacer with
custom input and output types. In this case all subsequent redefinitions must have the
same type, or the type `α → β → tactic γ → tactic γ` or
`α → β → option (tactic γ) → tactic γ` analogously to the previous cases.
 -/
@[user_command] meta def def_replacer_cmd (_ : parse $ tk "def_replacer") : lean.parser unit :=
do ntac ← ident,
  ty ← optional (tk ":" *> types.texpr),
  match ty with
  | (some p) := do t ← to_expr p, def_replacer ntac t
  | none     := def_replacer ntac `(tactic unit)
  end

add_tactic_doc
{ name                     := "def_replacer",
  category                 := doc_category.cmd,
  decl_names               := [`tactic.def_replacer_cmd],
  tags                     := ["environment", "renaming"] }

meta def unprime : name → tactic name
| nn@(name.mk_string s n) :=
  let s' := (s.split_on ''').head in
  if s'.length < s.length then pure (name.mk_string s' n)
                   else fail format!"expecting primed name: {nn}"
| n := fail format!"invalid name: {n}"

@[user_attribute] meta def replaceable_attr : user_attribute :=
{ name := `replaceable,
  descr := "make definition replaceable in dependent modules",
  after_set := some $ λ n' _ _,
    do { n ← unprime n',
         d ← get_decl n',
         «def_replacer» n d.type,
         (replacer_attr n).set n' () tt } }

end tactic
