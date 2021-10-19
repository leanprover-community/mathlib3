/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import control.traversable.basic
import tactic.simpa

open interactive interactive.types lean.parser

private meta def loc.to_string_aux : option name → string
| none := "⊢"
| (some x) := to_string x

/-- pretty print a `loc` -/
meta def loc.to_string : loc → string
| (loc.ns []) := ""
| (loc.ns [none]) := ""
| (loc.ns ls) := string.join $ list.intersperse " " (" at" :: ls.map loc.to_string_aux)
| loc.wildcard := " at *"

/-- shift `pos` `n` columns to the left -/
meta def pos.move_left (p : pos) (n : ℕ) : pos :=
{ line := p.line, column := p.column - n }

namespace tactic

open list

/-- parse structure instance of the shape `{ field1 := value1, .. , field2 := value2 }` -/
meta def struct_inst : lean.parser pexpr :=
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

/-- pretty print structure instance -/
meta def struct.to_tactic_format (e : pexpr) : tactic format :=
do r ← e.get_structure_instance_info,
   fs ← mzip_with (λ n v,
     do v ← to_expr v >>= pp,
        pure $ format!"{n} := {v}" )
     r.field_names r.field_values,
   let ss := r.sources.map (λ s, format!" .. {s}"),
   let x : format := format.join $ list.intersperse ", " (fs ++ ss),
   pure format!" {{{x}}"

/-- Attribute containing a table that accumulates multiple `squeeze_simp` suggestions -/
@[user_attribute]
private meta def squeeze_loc_attr :
  user_attribute unit (option (list (pos × string × list simp_arg_type × string))) :=
{ name := `_squeeze_loc,
  parser := fail "this attribute should not be used",
  descr := "table to accumulate multiple `squeeze_simp` suggestions" }

/-- dummy declaration used as target of `squeeze_loc` attribute -/
def squeeze_loc_attr_carrier := ()

run_cmd squeeze_loc_attr.set ``squeeze_loc_attr_carrier none tt

/-- Format a list of arguments for use with `simp` and friends. This omits the
list entirely if it is empty. -/
meta def render_simp_arg_list : list simp_arg_type → tactic format
| [] := pure ""
| args := (++) " " <$> to_line_wrap_format <$> args.mmap pp

/-- Emit a suggestion to the user. If inside a `squeeze_scope` block,
the suggestions emitted through `mk_suggestion` will be aggregated so that
every tactic that makes a suggestion can consider multiple execution of the
same invocation.
If `at_pos` is true, make the suggestion at `p` instead of the current position. -/
meta def mk_suggestion (p : pos) (pre post : string) (args : list simp_arg_type)
  (at_pos := ff) : tactic unit :=
do xs ← squeeze_loc_attr.get_param ``squeeze_loc_attr_carrier,
   match xs with
   | none := do
     args ← render_simp_arg_list args,
     if at_pos then
       @scope_trace _ p.line p.column $
         λ _, _root_.trace sformat!"{pre}{args}{post}" (pure () : tactic unit)
     else
       trace sformat!"{pre}{args}{post}"
   | some xs := do
     squeeze_loc_attr.set ``squeeze_loc_attr_carrier ((p,pre,args,post) :: xs) ff
   end

local postfix `?`:9001 := optional

/-- translate a `pexpr` into a `simp` configuration -/
meta def parse_config : option pexpr → tactic (simp_config_ext × format)
| none := pure ({}, "")
| (some cfg) :=
  do e ← to_expr ``(%%cfg : simp_config_ext),
     fmt ← has_to_tactic_format.to_tactic_format cfg,
     prod.mk <$> eval_expr simp_config_ext e
             <*> struct.to_tactic_format cfg

/-- translate a `pexpr` into a `dsimp` configuration -/
meta def parse_dsimp_config : option pexpr → tactic (dsimp_config × format)
| none := pure ({}, "")
| (some cfg) :=
  do e ← to_expr ``(%%cfg : simp_config_ext),
     fmt ← has_to_tactic_format.to_tactic_format cfg,
     prod.mk <$> eval_expr dsimp_config e
             <*> struct.to_tactic_format cfg

/-- `same_result proof tac` runs tactic `tac` and checks if the proof
produced by `tac` is equivalent to `proof`. -/
meta def same_result (pr : proof_state) (tac : tactic unit) : tactic bool :=
do s ← get_proof_state_after tac,
   pure $ some pr = s

private meta def filter_simp_set_aux
  (tac : bool → list simp_arg_type → tactic unit)
  (args : list simp_arg_type) (pr : proof_state) :
  list simp_arg_type → list simp_arg_type →
  list simp_arg_type → tactic (list simp_arg_type × list simp_arg_type)
| [] ys ds := pure (ys.reverse, ds.reverse)
| (x :: xs) ys ds :=
  do b ← same_result pr (tac tt (args ++ xs ++ ys)),
     if b
       then filter_simp_set_aux xs ys (x:: ds)
       else filter_simp_set_aux xs (x :: ys) ds

declare_trace squeeze.deleted

/--
`filter_simp_set g call_simp user_args simp_args` returns `args'` such that, when calling
`call_simp tt /- only -/ args'` on the goal `g` (`g` is a meta var) we end up in the same
state as if we had called `call_simp ff (user_args ++ simp_args)` and removing any one
element of `args'` changes the resulting proof.
-/
meta def filter_simp_set
  (tac : bool → list simp_arg_type → tactic unit)
  (user_args simp_args : list simp_arg_type) : tactic (list simp_arg_type) :=
do some s ← get_proof_state_after (tac ff (user_args ++ simp_args)),
   (simp_args', _)  ← filter_simp_set_aux tac user_args s simp_args [] [],
   (user_args', ds) ← filter_simp_set_aux tac simp_args' s user_args [] [],
   when (is_trace_enabled_for `squeeze.deleted = tt ∧ ¬ ds.empty)
     trace!"deleting provided arguments {ds}",
   pure (user_args' ++ simp_args')

/-- make a `simp_arg_type` that references the name given as an argument -/
meta def name.to_simp_args (n : name) : tactic simp_arg_type :=
do e ← resolve_name' n, pure $ simp_arg_type.expr e

/-- tactic combinator to create a `simp`-like tactic that minimizes its
argument list.

 * `slow`: adds all rfl-lemmas from the environment to the initial list (this is a slower but more
           accurate strategy)
 * `no_dflt`: did the user use the `only` keyword?
 * `args`:    list of `simp` arguments
 * `tac`:     how to invoke the underlying `simp` tactic

-/
meta def squeeze_simp_core
  (slow no_dflt : bool) (args : list simp_arg_type)
  (tac : Π (no_dflt : bool) (args : list simp_arg_type), tactic unit)
  (mk_suggestion : list simp_arg_type → tactic unit) : tactic unit :=
do v ← target >>= mk_meta_var,
   args ← if slow then do
     simp_set ← attribute.get_instances `simp,
     simp_set ← simp_set.mfilter $ has_attribute' `_refl_lemma,
     simp_set ← simp_set.mmap $ resolve_name' >=> pure ∘ simp_arg_type.expr,
     pure $ args ++ simp_set
   else pure args,
   g ← retrieve $ do
   { g ← main_goal,
     tac no_dflt args,
     instantiate_mvars g },
   let vs := g.list_constant,
   vs ← vs.mfilter is_simp_lemma,
   vs ← vs.mmap strip_prefix,
   vs ← vs.to_list.mmap name.to_simp_args,
   with_local_goals' [v] (filter_simp_set tac args vs)
     >>= mk_suggestion,
   tac no_dflt args

namespace interactive

attribute [derive decidable_eq] simp_arg_type

/-- Turn a `simp_arg_type` into a string. -/
meta instance simp_arg_type.has_to_string : has_to_string simp_arg_type :=
⟨λ a, match a with
| simp_arg_type.all_hyps := "*"
| (simp_arg_type.except n) := "-" ++ to_string n
| (simp_arg_type.expr e) := to_string e
| (simp_arg_type.symm_expr e) := "←" ++ to_string e
end⟩

/-- combinator meant to aggregate the suggestions issued by multiple calls
of `squeeze_simp` (due, for instance, to `;`).

Can be used as:

```lean
example {α β} (xs ys : list α) (f : α → β) :
  (xs ++ ys.tail).map f = xs.map f ∧ (xs.tail.map f).length = xs.length :=
begin
  have : xs = ys, admit,
  squeeze_scope
  { split; squeeze_simp,
    -- `squeeze_simp` is run twice, the first one requires
    -- `list.map_append` and the second one
    -- `[list.length_map, list.length_tail]`
    -- prints only one message and combine the suggestions:
    -- > Try this: simp only [list.length_map, list.length_tail, list.map_append]
    squeeze_simp [this]
    -- `squeeze_simp` is run only once
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
         mk_suggestion p pre post (suggs.foldl list.union []) tt, pure () }

/--
`squeeze_simp`, `squeeze_simpa` and `squeeze_dsimp` perform the same
task with the difference that `squeeze_simp` relates to `simp` while
`squeeze_simpa` relates to `simpa` and `squeeze_dsimp` relates to
`dsimp`. The following applies to `squeeze_simp`, `squeeze_simpa` and
`squeeze_dsimp`.

`squeeze_simp` behaves like `simp` (including all its arguments)
and prints a `simp only` invocation to skip the search through the
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
    combined by concatenating their list of lemmas. `squeeze_scope` can be used to
    combine the suggestions: `by squeeze_scope { cases x; squeeze_simp }`
  * sometimes, `simp` lemmas are also `_refl_lemma` and they can be used without appearing in the
    resulting proof. `squeeze_simp` won't know to try that lemma unless it is called as
    `squeeze_simp?`
-/
meta def squeeze_simp
  (key : parse cur_pos)
  (slow_and_accurate : parse (tk "?")?)
  (use_iota_eqn : parse (tk "!")?) (no_dflt : parse only_flag) (hs : parse simp_arg_list)
  (attr_names : parse with_ident_list) (locat : parse location)
  (cfg : parse struct_inst?) : tactic unit :=
do (cfg',c) ← parse_config cfg,
   squeeze_simp_core slow_and_accurate.is_some no_dflt hs
     (λ l_no_dft l_args, simp use_iota_eqn none l_no_dft l_args attr_names locat cfg')
     (λ args,
        let use_iota_eqn := if use_iota_eqn.is_some then "!" else "",
            attrs := if attr_names.empty then ""
                     else string.join (list.intersperse " " (" with" :: attr_names.map to_string)),
            loc := loc.to_string locat in
        mk_suggestion (key.move_left 1)
          sformat!"Try this: simp{use_iota_eqn} only"
          sformat!"{attrs}{loc}{c}" args)

/-- see `squeeze_simp` -/
meta def squeeze_simpa
  (key : parse cur_pos)
  (slow_and_accurate : parse (tk "?")?)
  (use_iota_eqn : parse (tk "!")?) (no_dflt : parse only_flag) (hs : parse simp_arg_list)
  (attr_names : parse with_ident_list) (tgt : parse (tk "using" *> texpr)?)
  (cfg : parse struct_inst?) : tactic unit :=
do (cfg',c) ← parse_config cfg,
   tgt' ← traverse (λ t, do t ← to_expr t >>= pp,
                            pure format!" using {t}") tgt,
   squeeze_simp_core slow_and_accurate.is_some no_dflt hs
     (λ l_no_dft l_args, simpa use_iota_eqn none l_no_dft l_args attr_names tgt cfg')
     (λ args,
        let use_iota_eqn := if use_iota_eqn.is_some then "!" else "",
            attrs := if attr_names.empty then ""
                     else string.join (list.intersperse " " (" with" :: attr_names.map to_string)),
            tgt' := tgt'.get_or_else "" in
        mk_suggestion (key.move_left 1)
          sformat!"Try this: simpa{use_iota_eqn} only"
          sformat!"{attrs}{tgt'}{c}" args)

/-- `squeeze_dsimp` behaves like `dsimp` (including all its arguments)
and prints a `dsimp only` invocation to skip the search through the
`simp` lemma list. See the doc string of `squeeze_simp` for examples.
 -/
meta def squeeze_dsimp
  (key : parse cur_pos)
  (slow_and_accurate : parse (tk "?")?)
  (use_iota_eqn : parse (tk "!")?)
  (no_dflt : parse only_flag) (hs : parse simp_arg_list)
  (attr_names : parse with_ident_list) (locat : parse location)
  (cfg : parse struct_inst?) : tactic unit :=
do (cfg',c) ← parse_dsimp_config cfg,
   squeeze_simp_core slow_and_accurate.is_some no_dflt hs
     (λ l_no_dft l_args, dsimp l_no_dft l_args attr_names locat cfg')
     (λ args,
        let use_iota_eqn := if use_iota_eqn.is_some then "!" else "",
            attrs := if attr_names.empty then ""
                     else string.join (list.intersperse " " (" with" :: attr_names.map to_string)),
            loc := loc.to_string locat in
        mk_suggestion (key.move_left 1)
          sformat!"Try this: dsimp{use_iota_eqn} only"
          sformat!"{attrs}{loc}{c}" args)

end interactive
end tactic

open tactic.interactive
add_tactic_doc
{ name       := "squeeze_simp / squeeze_simpa / squeeze_dsimp / squeeze_scope",
  category   := doc_category.tactic,
  decl_names :=
   [``squeeze_simp,
    ``squeeze_dsimp,
    ``squeeze_simpa,
    ``squeeze_scope],
  tags       := ["simplification", "Try this"],
  inherit_description_from := ``squeeze_simp }
