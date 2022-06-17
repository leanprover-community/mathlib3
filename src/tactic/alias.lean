/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import tactic.core

/-!
# The `alias` command

This file defines an `alias` command, which can be used to create copies
of a theorem or definition with different names.

Syntax:

```lean
/-- doc string -/
alias my_theorem ← alias1 alias2 ...
```

This produces defs or theorems of the form:

```lean
/-- doc string -/
@[alias] theorem alias1 : <type of my_theorem> := my_theorem

/-- doc string -/
@[alias] theorem alias2 : <type of my_theorem> := my_theorem
```

Iff alias syntax:

```lean
alias A_iff_B ↔ B_of_A A_of_B
alias A_iff_B ↔ ..
```

This gets an existing biconditional theorem `A_iff_B` and produces
the one-way implications `B_of_A` and `A_of_B` (with no change in
implicit arguments). A blank `_` can be used to avoid generating one direction.
The `..` notation attempts to generate the 'of'-names automatically when the
input theorem has the form `A_iff_B` or `A_iff_B_left` etc.
-/

open lean.parser tactic interactive

namespace tactic.alias

/-- An alias can be in one of three forms -/
@[derive has_reflect]
meta inductive target
| plain : name -> target
| forward : name -> target
| backwards : name -> target

/-- The name underlying an alias target -/
meta def target.to_name : target → name
| (target.plain n) := n
| (target.forward n) := n
| (target.backwards n) := n

/-- The docstring for an alias. Used by `alias` _and_ by `to_additive` -/
meta def target.to_string : target → string
| (target.plain n) := sformat!"**Alias** of {n}`."
| (target.forward n) := sformat!"**Alias** of the forward direction of {n}`."
| (target.backwards n) := sformat!"**Alias** of the reverse direction of {n}`."

@[user_attribute] meta def alias_attr : user_attribute unit target :=
{ name := `alias, descr := "This definition is an alias of another.", parser := failed }

meta def alias_direct (d : declaration) (al : name) : tactic unit :=
do updateex_env $ λ env,
  env.add (match d.to_definition with
  | declaration.defn n ls t _ _ _ :=
    declaration.defn al ls t (expr.const n (level.param <$> ls))
      reducibility_hints.abbrev tt
  | declaration.thm n ls t _ :=
    declaration.thm al ls t $ task.pure $ expr.const n (level.param <$> ls)
  | _ := undefined
  end),
  let target := target.plain d.to_name,
  alias_attr.set al target tt,
  add_doc_string al target.to_string

meta def mk_iff_mp_app (iffmp : name) : expr → (ℕ → expr) → tactic expr
| (expr.pi n bi e t) f := expr.lam n bi e <$> mk_iff_mp_app t (λ n, f (n+1) (expr.var n))
| `(%%a ↔ %%b) f := pure $ @expr.const tt iffmp [] a b (f 0)
| _ f := fail "Target theorem must have the form `Π x y z, a ↔ b`"

meta def alias_iff (d : declaration) (al : name) (is_forward : bool) : tactic unit :=
(if al = `_ then skip else get_decl al >> skip) <|> do
  let ls := d.univ_params,
  let t := d.type,
  let target := if is_forward then target.forward d.to_name else target.backwards d.to_name,
  let iffmp := if is_forward then `iff.mp else `iff.mpr,
  v ← mk_iff_mp_app iffmp t (λ_, expr.const d.to_name (level.param <$> ls)),
  t' ← infer_type v,
  updateex_env $ λ env, env.add (declaration.thm al ls t' $ task.pure v),
  alias_attr.set al target tt,
  add_doc_string al target.to_string

meta def make_left_right : name → tactic (name × name)
| (name.mk_string s p) := do
  let buf : char_buffer := s.to_char_buffer,
  let parts := s.split_on '_',
  (left, _::right) ← pure $ parts.span (≠ "iff"),
  let pfx (a b : string) := a.to_list.is_prefix_of b.to_list,
  (suffix', right') ← pure $ right.reverse.span (λ s, pfx "left" s ∨ pfx "right" s),
  let right := right'.reverse,
  let suffix := suffix'.reverse,
  pure (p <.> "_".intercalate (right ++ "of" :: left ++ suffix),
        p <.> "_".intercalate (left ++ "of" :: right ++ suffix))
| _ := failed

/--
The `alias` command can be used to create copies
of a theorem or definition with different names.

Syntax:

```lean
/-- doc string -/
alias my_theorem ← alias1 alias2 ...
```

This produces defs or theorems of the form:

```lean
/-- doc string -/
@[alias] theorem alias1 : <type of my_theorem> := my_theorem

/-- doc string -/
@[alias] theorem alias2 : <type of my_theorem> := my_theorem
```

Iff alias syntax:

```lean
alias A_iff_B ↔ B_of_A A_of_B
alias A_iff_B ↔ ..
```

This gets an existing biconditional theorem `A_iff_B` and produces
the one-way implications `B_of_A` and `A_of_B` (with no change in
implicit arguments). A blank `_` can be used to avoid generating one direction.
The `..` notation attempts to generate the 'of'-names automatically when the
input theorem has the form `A_iff_B` or `A_iff_B_left` etc.
-/
@[user_command] meta def alias_cmd (meta_info : decl_meta_info)
  (_ : parse $ tk "alias") : lean.parser unit :=
do old ← ident,
  d ← (do old ← resolve_constant old, get_decl old) <|>
    fail ("declaration " ++ to_string old ++ " not found"),
  let doc := λ (al : name) (inf : string), meta_info.doc_string.get_or_else $
    sformat!"**Alias** of {inf}`{old}`.",
  do
  { tk "←" <|> tk "<-",
    aliases ← many ident,
    ↑(aliases.mmap' $ λ al, alias_direct d al) } <|>
  do
  { tk "↔" <|> tk "<->",
    (left, right) ←
      mcond ((tk ".." >> pure tt) <|> pure ff)
        (make_left_right old <|> fail "invalid name for automatic name generation")
        (prod.mk <$> types.ident_ <*> types.ident_),
    alias_iff d left tt,
    alias_iff d right ff }

add_tactic_doc
{ name                     := "alias",
  category                 := doc_category.cmd,
  decl_names               := [`tactic.alias.alias_cmd],
  tags                     := ["renaming"] }

meta def get_lambda_body : expr → expr
| (expr.lam _ _ _ b) := get_lambda_body b
| a                  := a

meta def get_alias_target (n : name) : tactic (option target) :=
do tt ← has_attribute' `alias n | pure none,
   v ← alias_attr.get_param n,
   pure $ some v

end tactic.alias
