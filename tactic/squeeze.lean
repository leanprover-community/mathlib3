
import meta.rb_map
import tactic.basic
import category.traversable

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

meta def arg.to_tactic_format : simp_arg_type → tactic format
| (simp_arg_type.expr e) := i_to_expr_no_subgoals e >>= pp
| simp_arg_type.all_hyps := pure "*"
| (simp_arg_type.except n) := pure format!"-{n}"

open list

meta def rec.to_tactic_format (e : pexpr) : tactic format :=
do r ← e.get_structure_instance_info,
   fs ← mzip_with (λ n v,
     do v ← to_expr v >>= pp,
        pure $ format!"{n} := {v}" )
     r.field_names r.field_values,
   let ss := r.sources.map (λ s, format!" .. {s}"),
   let x : format := format.join $ list.intersperse ", " (fs ++ ss),
   pure format!" {{{x}}"

meta def parse_config : option pexpr → tactic (simp_config_ext × format)
| none := pure ({}, "")
| (some cfg) :=
  do e ← to_expr ``(%%cfg : simp_config_ext),
     fmt ← has_to_tactic_format.to_tactic_format cfg,
     prod.mk <$> eval_expr simp_config_ext e
             <*> rec.to_tactic_format cfg

meta def squeeze_simp
  (use_iota_eqn : option unit) (no_dflt : bool) (hs : list simp_arg_type)
  (attr_names : list name) (locat : loc)
  (cfg : option pexpr) : tactic string :=
do g ← main_goal,
   (cfg',c) ← parse_config cfg,
   hs' ← hs.mmap arg.to_tactic_format,
   interactive.simp use_iota_eqn no_dflt hs attr_names locat cfg',
   g ← instantiate_mvars g,
   let vs := g.list_constant,
   vs ← vs.mfilter (succeeds ∘ has_attribute `simp),
   let use_iota_eqn := if use_iota_eqn.is_some then "!" else "",
   let attrs := if attr_names.empty then "" else string.join (list.intersperse " " (" with" :: attr_names.map to_string)),
   let loc := loc.to_string locat,
   let args := hs' ++ vs.to_list.map to_fmt,
   pure $ to_string format!"simp{use_iota_eqn} only {args}{attrs}{loc}{c}"

meta def squeeze_simpa
  (use_iota_eqn : option unit) (no_dflt : bool) (hs : list simp_arg_type)
  (attr_names : list name) (tgt : option pexpr)
  (cfg : option pexpr) : tactic string :=
do g ← main_goal,
   (cfg',c) ← parse_config cfg,
   tgt' ← traverse (λ t, do t ← to_expr t >>= pp,
                            pure format!" using {t}") tgt,
   interactive.simpa use_iota_eqn no_dflt hs attr_names tgt cfg',
   g ← instantiate_mvars g,
   let vs := g.list_constant,
   vs ← vs.mfilter (succeeds ∘ has_attribute `simp),
   let use_iota_eqn := if use_iota_eqn.is_some then "!" else "",
   let attrs := if attr_names.empty then "" else string.join (list.intersperse " " (" with" :: attr_names.map to_string)),
   let tgt' := tgt'.get_or_else "",
   hs ← hs.mmap arg.to_tactic_format,
   let args := hs ++ vs.to_list.map to_fmt,
   pure $ to_string format!"simpa{use_iota_eqn} only {args}{attrs}{tgt'}{c}"

namespace interactive

local postfix `?`:9001 := optional

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

/-- `squeeze_simp` behaves like `simp` (including all its arguments)
and prints a `simp only` invokation to skip the search through the
`simp` lemma list.

For instance, the following is easily solved with `simp`:

```
example : 0 + 1 = 1 + 0 := by simp
```

To guide the proof search and speed it up, we may replace `simp`
with `squeeze_simp`:

```
example : 0 + 1 = 1 + 0 := by squeeze_simp
-- prints: simp only [add_zero, eq_self_iff_true, zero_add]
```

`squeeze_simp` suggests a replacement which we can use instead of
`squeeze_simp`.

```
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
do script ← tactic.squeeze_simp use_iota_eqn no_dflt hs attr_names locat cfg,
   when (¬ no_dflt) $ trace script

/-- same as `squeeze_simp` for `simpa` -/
meta def squeeze_simpa
  (use_iota_eqn : parse (tk "!")?) (no_dflt : parse only_flag) (hs : parse simp_arg_list)
  (attr_names : parse with_ident_list) (tgt : parse (tk "using" *> texpr)?)
  (cfg : parse record_lit?) : tactic unit :=
do script ← tactic.squeeze_simpa use_iota_eqn no_dflt hs attr_names tgt cfg,
   when (¬ no_dflt) $ trace script

end interactive
end tactic
