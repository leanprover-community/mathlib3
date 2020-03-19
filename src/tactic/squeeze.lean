/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/
import category.traversable.basic
import tactic.simpa

open interactive interactive.types lean.parser

meta def loc.to_string_aux : option name → string
| none := "⊢"
| (some x) := to_string x

meta def loc.to_string : loc → string
| (loc.ns []) := ""
| (loc.ns [none]) := ""
| (loc.ns ls) := string.join $ list.intersperse " " (" at" :: ls.map loc.to_string_aux)
| loc.wildcard := " at *"

namespace tactic
namespace interactive

/--
  `erase_simp_args hs s` removes from `s` each name `n` such that `const n` is an element of `hs`
-/
meta def erase_simp_args (hs : list simp_arg_type) (s : name_set) : tactic name_set :=
do
  -- TODO: when Lean 3.4 support is dropped, use `decode_simp_arg_list_with_symm` on the next line:
  (hs, _, _) ← decode_simp_arg_list hs,
  pure $ hs.foldr (λ (h : pexpr) (s : name_set),
    match h.get_app_fn h with
    | (expr.const n _) := s.erase n
    | _ := s
    end) s

/-- Polyfill instance for Lean versions <3.5.1c -/
-- TODO: when Lean 3.4 support is dropped, this instance can be removed
@[priority 1]
meta instance : has_to_tactic_format simp_arg_type := ⟨λ a, match a with
| (simp_arg_type.expr e) := i_to_expr_no_subgoals e >>= pp
| (simp_arg_type.except n) := pure format!"-{n}"
| _ := pure "*" -- should only be called on `simp_arg_type.all_hyps`
end⟩

open list

meta def record_lit : lean.parser pexpr :=
do tk "{",
   ls ← sep_by (skip_info (tk ","))
     ( sum.inl <$> (tk ".." *> texpr) <|>
       sum.inr <$> (prod.mk <$> ident <* tk ":=" <*> texpr)),
   tk "}",
   let (srcs,fields) := partition_map id ls,
   let (names,values) := unzip fields,
   pure $ pexpr.mk_structure_instance
     { field_names := names,
       field_values := values,
       sources := srcs }

meta def rec.to_tactic_format (e : pexpr) : tactic format :=
do r ← e.get_structure_instance_info,
   fs ← mzip_with (λ n v,
     do v ← to_expr v >>= pp,
        pure $ format!"{n} := {v}" )
     r.field_names r.field_values,
   let ss := r.sources.map (λ s, format!" .. {s}"),
   let x : format := format.join $ list.intersperse ", " (fs ++ ss),
   pure format!" {{{x}}"

local postfix `?`:9001 := optional

meta def parse_config : option pexpr → tactic (simp_config_ext × format)
| none := pure ({}, "")
| (some cfg) :=
  do e ← to_expr ``(%%cfg : simp_config_ext),
     fmt ← has_to_tactic_format.to_tactic_format cfg,
     prod.mk <$> eval_expr simp_config_ext e
             <*> rec.to_tactic_format cfg

meta def auto_simp_lemma := [``eq_self_iff_true]

/--
`squeeze_simp` and `squeeze_simpa` perform the same task with
the difference that `squeeze_simp` relates to `simp` while
`squeeze_simpa` relates to `simpa`. The following applies to both
`squeeze_simp` and `squeeze_simpa`.

`squeeze_simp` behaves like `simp` (including all its arguments)
and prints a `simp only` invokation to skip the search through the
`simp` lemma list.

For instance, the following is easily solved with `simp`:

```lean
example : 0 + 1 = 1 + 0 := by simp
```

To guide the proof search and speed it up, we may replace `simp`
with `squeeze_simp`:

```lean
example : 0 + 1 = 1 + 0 := by squeeze_simp
-- prints:
-- Try this: simp only [add_zero, eq_self_iff_true, zero_add]
```

`squeeze_simp` suggests a replacement which we can use instead of
`squeeze_simp`.

```lean
example : 0 + 1 = 1 + 0 := by simp only [add_zero, eq_self_iff_true, zero_add]
```

`squeeze_simp only` prints nothing as it already skips the `simp` list.

This tactic is useful for speeding up the compilation of a complete file.
Steps:

   1. search and replace ` simp` with ` squeeze_simp` (the space helps avoid the
      replacement of `simp` in `@[simp]`) throughout the file.
   2. Starting at the beginning of the file, go to each printout in turn, copy
      the suggestion in place of `squeeze_simp`.
   3. after all the suggestions were applied, search and replace `squeeze_simp` with
      `simp` to remove the occurrences of `squeeze_simp` that did not produce a suggestion.

Known limitation(s):
  * in cases where `squeeze_simp` is used after a `;` (e.g. `cases x; squeeze_simp`),
    `squeeze_simp` will produce as many suggestions as the number of goals it is applied to.
    It is likely that none of the suggestion is a good replacement but they can all be
    combined by concatenating their list of lemmas.
-/
meta def squeeze_simp
  (use_iota_eqn : parse (tk "!")?) (no_dflt : parse only_flag) (hs : parse simp_arg_list)
  (attr_names : parse with_ident_list) (locat : parse location)
  (cfg : parse record_lit?) : tactic unit :=
do g ← main_goal,
   (cfg',c) ← parse_config cfg,
   hs' ← hs.mmap pp,
   simp use_iota_eqn no_dflt hs attr_names locat cfg',
   g ← instantiate_mvars g,
   let vs := g.list_constant,
   vs ← vs.mfilter is_simp_lemma >>= name_set.mmap strip_prefix,
   let vs := auto_simp_lemma.foldl name_set.erase vs,
   vs ← erase_simp_args hs vs,
   let use_iota_eqn := if use_iota_eqn.is_some then "!" else "",
   let attrs := if attr_names.empty then "" else string.join (list.intersperse " " (" with" :: attr_names.map to_string)),
   let loc := loc.to_string locat,
   let args := hs' ++ vs.to_list.map to_fmt,
   trace format!"Try this: simp{use_iota_eqn} only {args}{attrs}{loc}{c}"

meta def squeeze_simpa
  (use_iota_eqn : parse (tk "!")?) (no_dflt : parse only_flag) (hs : parse simp_arg_list)
  (attr_names : parse with_ident_list) (tgt : parse (tk "using" *> texpr)?)
  (cfg : parse record_lit?) : tactic unit :=
do g ← main_goal,
   (cfg',c) ← parse_config cfg,
   tgt' ← traverse (λ t, do t ← to_expr t >>= pp,
                            pure format!" using {t}") tgt,
   simpa use_iota_eqn no_dflt hs attr_names tgt cfg',
   g ← instantiate_mvars g,
   let vs := g.list_constant,
   vs ← vs.mfilter is_simp_lemma >>= name_set.mmap strip_prefix,
   let vs := auto_simp_lemma.foldl name_set.erase vs,
   vs ← erase_simp_args hs vs,
   let use_iota_eqn := if use_iota_eqn.is_some then "!" else "",
   let attrs := if attr_names.empty then "" else string.join (list.intersperse " " (" with" :: attr_names.map to_string)),
   let tgt' := tgt'.get_or_else "",
   hs ← hs.mmap pp,
   let args := hs ++ vs.to_list.map to_fmt,
   trace format!"Try this: simpa{use_iota_eqn} only {args}{attrs}{tgt'}{c}"

end interactive
end tactic

add_tactic_doc
{ name       := "squeeze_simp / squeeze_simpa",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.squeeze_simp, `tactic.interactive.squeeze_simpa],
  tags       := ["simplification"],
  inherit_description_from := `tactic.interactive.squeeze_simp }
