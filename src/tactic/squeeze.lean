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

meta def pos.move_left (p : pos) (n : ℕ) : pos :=
{ line := p.line, column := p.column - n }

namespace expr

meta def alpha_eqv_with_mvar : expr → expr → bool
| (var v) (var v') := v = v'
| (sort u) (sort u') := u = u'
| (const c us) (const c' us') :=
  c = c' ∧ us = us'
| (mvar unique pretty type) (mvar unique' pretty' type') :=
  alpha_eqv_with_mvar type type'
| (local_const unique pretty bi type) (local_const unique' pretty' bi' type') :=
  (unique,pretty,bi) = (unique',pretty',bi') ∧
  alpha_eqv_with_mvar type type'
| (app f e) (app f' e') :=
  alpha_eqv_with_mvar f f' ∧
  alpha_eqv_with_mvar e e'
| (lam var_name bi var_type body) (lam var_name' bi' var_type' body') :=
  alpha_eqv_with_mvar var_type var_type' ∧
  alpha_eqv_with_mvar body body'
| (pi var_name bi var_type body) (pi var_name' bi' var_type' body') :=
  alpha_eqv_with_mvar var_type var_type' ∧
  alpha_eqv_with_mvar body body'
| (elet var_name type assignment body) (elet var_name' type' assignment' body') :=
  alpha_eqv_with_mvar type type' ∧
  alpha_eqv_with_mvar assignment assignment' ∧
  alpha_eqv_with_mvar body body'
| (macro m es) (macro m' es') :=
  expr.macro_def_name m = expr.macro_def_name m' ∧
  (list.map₂ alpha_eqv_with_mvar es es').all id
| _ _ := ff


end expr


namespace tactic

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
meta instance simp_arg_type.has_to_tactic_format : has_to_tactic_format simp_arg_type := ⟨λ a, match a with
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

@[user_attribute]
meta def squeeze_loc_attr : user_attribute unit (option (list (pos × string × list simp_arg_type × string))) :=
{ name := `squeeze_loc,
  parser := fail "this attribute should not be used of definition",
  descr := "table to accumulate multiple `squeeze_simp` suggestions" }

def squeeze_loc_attr_carrier := unit

run_cmd squeeze_loc_attr.set ``squeeze_loc_attr_carrier none tt

meta def mk_suggestion (p : pos) (pre post : string) (args : list simp_arg_type) : tactic unit :=
do xs ← squeeze_loc_attr.get_param ``squeeze_loc_attr_carrier,
   match xs with
   | none := do
     args ← to_line_wrap_format <$> args.mmap pp,
     -- save_info_thunk p $ λ _, format!"{pre}{args}{post}",
     @scope_trace _ p.line p.column $ λ _, _root_.trace sformat!"{pre}{args}{post}" (pure () : tactic unit)
   | some xs := do
     squeeze_loc_attr.set ``squeeze_loc_attr_carrier ((p,pre,args,post) :: xs) ff
     -- trace "insert replacement here"
   end

local postfix `?`:9001 := optional

meta def parse_config : option pexpr → tactic (simp_config_ext × format)
| none := pure ({}, "")
| (some cfg) :=
  do e ← to_expr ``(%%cfg : simp_config_ext),
     fmt ← has_to_tactic_format.to_tactic_format cfg,
     prod.mk <$> eval_expr simp_config_ext e
             <*> rec.to_tactic_format cfg

meta def same_result (pr : expr) (tac : tactic unit) : tactic bool :=
do tgt ← target,
   some (_,p') ← try_core $ solve_aux tgt tac | pure ff,
   p' ← instantiate_mvars p',
   env ← get_env,
   pure $ expr.alpha_eqv_with_mvar pr (env.unfold_all_macros p')

meta def filter_simp_set_aux
  (tac : bool → list simp_arg_type → tactic unit)
  (args : list simp_arg_type) (pr : expr) :
  list simp_arg_type → list simp_arg_type →
  list simp_arg_type → tactic (list simp_arg_type × list simp_arg_type)
| [] ys ds := pure (ys.reverse, ds.reverse)
| (x :: xs) ys ds :=
  do -- b ← same_result pr (simp use_iota_eqn tt (args ++ xs ++ ys) attr_names locat cfg >> trace_state),
     b ← same_result pr (tac tt (args ++ xs ++ ys)),
     if b
       then filter_simp_set_aux xs ys (x:: ds)
       else filter_simp_set_aux xs (x :: ys) ds

declare_trace squeeze.deleted

meta def filter_simp_set (v : expr)
  (tac : bool → list simp_arg_type → tactic unit)
  (args args' : list simp_arg_type) : tactic (list simp_arg_type) :=
do gs ← get_goals,
   set_goals [v],
   tgt ← target,
   (_,pr) ← solve_aux tgt (tac ff (args ++ args')),
   -- (_,pr) ← solve_aux tgt (simp use_iota_eqn no_dflt (args ++ args') attr_names locat cfg),
   env ← get_env,
   pr ← env.unfold_all_macros <$> instantiate_mvars pr,
   (args', _)  ← filter_simp_set_aux tac args pr args' [] [],
   (args₀, ds) ← filter_simp_set_aux tac args' pr args [] [],
   when (is_trace_enabled_for `squeeze.deleted = tt ∧ ¬ ds.empty)
     trace!"deleting provided arguments {ds}",
   prod.fst <$> solve_aux tgt (pure (args₀ ++ args')) <* set_goals gs

meta def name.to_simp_args (n : name) : tactic simp_arg_type :=
do e ← resolve_name n, pure $ simp_arg_type.expr e

/-- tactic combinator to create a `simp`-like tactic that minimizes its
argument list.

 * no_dflt: did the user use the `only` keyword?
 * args:    list of `simp` arguments
 * tac :    how to invoke the underlying `simp` tactic

-/
meta def squeeze_simp_core
  (no_dflt : bool) (args : list simp_arg_type)
  (tac : Π (no_dflt : bool) (args : list simp_arg_type), tactic unit) : tactic (list simp_arg_type):=
do g ← main_goal,
   v ← target >>= mk_meta_var,
   tac no_dflt args,
   g ← instantiate_mvars g,
   let vs := g.list_constant,
   vs ← vs.mfilter is_simp_lemma,
   vs ← vs.mmap strip_prefix,
   vs ← erase_simp_args args vs,
   vs ← vs.to_list.mmap name.to_simp_args,
   filter_simp_set v tac args vs

namespace interactive

attribute [derive decidable_eq] simp_arg_type

/-- combinator meant to aggregate the suggestions issues by multiple calls
of `squeeze_simp` (due, for instance, to `;`).

Can be used as:

```
example {α β} (xs ys : list α) (f : α → β) :
  (xs ++ ys.tail).map f = xs.map f ∧ (xs.tail.map f).length = xs.length :=
begin
  have : xs = ys, admit,
  squeeze_scope
  { split; squeeze_simp, -- `squeeze_simp` is run twice, the first one requires
                         -- `list.map_append` and the second one `[list.length_map, list.length_tail]`
                         -- prints only one message and combine the suggestions:
                         -- > Try this: simp only [list.length_map, list.length_tail, list.map_append]
    squeeze_simp [this]  -- `squeeze_simp` is run only once
                         -- prints:
                         -- > Try this: simp only [this]
 },
end
```

-/
meta def squeeze_scope (tac : itactic) : tactic unit :=
do none ← squeeze_loc_attr.get_param ``squeeze_loc_attr_carrier | pure (),
   squeeze_loc_attr.set ``squeeze_loc_attr_carrier (some []) ff,
   finally tac $ do
     some xs ← squeeze_loc_attr.get_param ``squeeze_loc_attr_carrier | fail "invalid state",
     let m := native.rb_lmap.of_list xs,
     squeeze_loc_attr.set ``squeeze_loc_attr_carrier none ff,
     m.to_list.reverse.mmap' $ λ ⟨p,suggs⟩, do
       { let ⟨pre,_,post⟩ := suggs.head,
         let suggs : list (list simp_arg_type) := suggs.map $ prod.fst ∘ prod.snd,
         -- trace!"{p.line}:{p.column}:",
         mk_suggestion p pre post (suggs.foldl list.union []), pure () }

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
  (key : parse cur_pos)
  (use_iota_eqn : parse (tk "!")?) (no_dflt : parse only_flag) (hs : parse simp_arg_list)
  (attr_names : parse with_ident_list) (locat : parse location)
  (cfg : parse record_lit?) : tactic unit :=
do (cfg',c) ← parse_config cfg,
   args ← squeeze_simp_core no_dflt hs
     (λ l_no_dft l_args, simp use_iota_eqn l_no_dft l_args attr_names locat cfg'),
   let use_iota_eqn := if use_iota_eqn.is_some then "!" else "",
   let attrs := if attr_names.empty then "" else string.join (list.intersperse " " (" with" :: attr_names.map to_string)),
   let loc := loc.to_string locat,
   mk_suggestion (key.move_left 1)
     sformat!"Try this: simp{use_iota_eqn} only "
     sformat!"{attrs}{loc}{c}" args

meta def squeeze_simpa
  (key : parse cur_pos)
  (use_iota_eqn : parse (tk "!")?) (no_dflt : parse only_flag) (hs : parse simp_arg_list)
  (attr_names : parse with_ident_list) (tgt : parse (tk "using" *> texpr)?)
  (cfg : parse record_lit?) : tactic unit :=
do (cfg',c) ← parse_config cfg,
   tgt' ← traverse (λ t, do t ← to_expr t >>= pp,
                            pure format!" using {t}") tgt,
   args ← squeeze_simp_core no_dflt hs
     (λ l_no_dft l_args, simpa use_iota_eqn l_no_dft l_args attr_names tgt cfg'),
   let use_iota_eqn := if use_iota_eqn.is_some then "!" else "",
   let attrs := if attr_names.empty then "" else string.join (list.intersperse " " (" with" :: attr_names.map to_string)),
   let tgt' := tgt'.get_or_else "",
   mk_suggestion (key.move_left 1)
     sformat!"Try this: simpa{use_iota_eqn} only "
     sformat!"{attrs}{tgt'}{c}" args

end interactive
end tactic

add_tactic_doc
{ name       := "squeeze_simp / squeeze_simpa",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.squeeze_simp, `tactic.interactive.squeeze_simpa],
  tags       := ["simplification"],
  inherit_description_from := `tactic.interactive.squeeze_simp }
