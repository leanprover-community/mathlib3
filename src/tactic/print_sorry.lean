/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import tactic.core
import data.bool.basic

/-!
# Print sorry

Adds a command `#print_sorry_in nm` that prints all occurrences of `sorry` in declarations used in
`nm`, including all intermediate declarations.

Other searches through the environment can be done using `tactic.find_all_exprs`
-/


namespace tactic
/-- Auxiliary data type for `tactic.find_all_exprs` -/
meta structure find_all_expr_data :=
(matching_subexpr : bool) -- this declaration contains a subexpression on which the test passes
(test_passed : bool) -- the search has found a matching subexpression somewhere
-- name, contains subexpression directly, direct descendants
(descendants : list (name × bool × name_set))
(name_map : name_map bool) -- all data
(direct_descendants : name_set) -- direct descendants of a declaration

/-- Auxiliary declaration for `tactic.find_all_exprs`.

Traverse all declarations occurring in the declaration with the given name,
excluding declarations `n` such that `g n` is true (and all their descendants),
recording the structure of which declaration depends on which,
and whether `f e` is true on any subexpression `e` of the declaration. -/
meta def find_all_exprs_aux (env : environment) (f : expr → bool) (g : name → bool) : name →
  find_all_expr_data → tactic find_all_expr_data
| n ⟨b₀, b₁, l, ns, desc⟩ :=
  match ns.find n with -- Skip declarations that we have already handled.
  | some b := pure ⟨b₀, b || b₁, l, ns, if b then desc.insert n else desc⟩
  | none := if g n then pure ⟨b₀, b₁, l, ns.insert n ff, desc⟩ else do
    d ← env.get n,
    let process (v : expr) : tactic find_all_expr_data :=
      v.mfold ⟨ff, ff, l, ns, mk_name_set⟩ $ λ e _ p,
        if f e then pure ⟨tt, tt, p.descendants, p.name_map, p.direct_descendants⟩ else
        if e.is_constant then find_all_exprs_aux e.const_name p else pure p,
    ⟨b', b, l, ns, desc'⟩ ← process d.value,
    pure ⟨b₀, b₁ || b, if b then (n, b', desc')::l else l, ns.insert n b,
      if b then desc.insert n else desc⟩
  end

/-- `tactic.find_all_exprs env test exclude nm` searches for all declarations (transitively)
  occuring in `nm` that contain a subexpression `e` such that `test e` is true.
  All declarations `n` such that `exclude n` is true (and all their descendants) are ignored. -/
meta def find_all_exprs (env : environment) (test : expr → bool) (exclude : name → bool)
  (nm : name) : tactic $ list $ name × bool × name_set := do
  ⟨_, _, l, _, _⟩ ← find_all_exprs_aux env test exclude nm ⟨ff, ff, [], mk_name_map, mk_name_set⟩,
  pure l

end tactic
open tactic

/-- Print all declarations that (transitively) occur in the value of declaration `nm` and depend on
`sorry`. If `ignore_mathlib` is set true, then all declarations in `mathlib` are
assumed to be `sorry`-free, which greatly reduces the search space. We could also exclude `core`,
but this doesn't speed up the search. -/
meta def print_sorry_in (nm : name) (ignore_mathlib := tt) : tactic unit := do
  env ← get_env,
  dir ← get_mathlib_dir,
  data ← find_all_exprs env (λ e, e.is_sorry.is_some)
    (if ignore_mathlib then env.is_prefix_of_file dir else λ _, ff) nm,
  let to_print : list format := data.map $ λ ⟨nm, contains_sorry, desc⟩,
    let s1 := if contains_sorry then " contains sorry" else "",
        s2 := if contains_sorry && !desc.empty then " and" else "",
        s3 := string.join $ (desc.to_list.map to_string).intersperse ", ",
        s4 := if !desc.empty then format!" depends on {s3}" else "" in
    format!"{nm}{s1}{s2}{s4}.",
  trace $ format.join $ to_print.intersperse format.line

setup_tactic_parser

/-- The command
```
#print_sorry_in nm
```
prints all declarations that (transitively) occur in the value of declaration `nm` and depend on
`sorry`. This command assumes that no `sorry` occurs in mathlib. To find `sorry` in mathlib, use
``#eval print_sorry_in `nm ff`` instead.
Example:
```
def foo1 : false := sorry
def foo2 : false ∧ false := ⟨sorry, foo1⟩
def foo3 : false := foo2.left
def foo4 : true := trivial
def foo5 : true ∧ false := ⟨foo4, foo3⟩
#print_sorry_in foo5
```
prints
```
foo5 depends on foo3.
foo3 depends on foo2.
foo2 contains sorry and depends on foo1.
foo1 contains sorry.
```
-/
@[user_command]
meta def print_sorry_in_cmd (_ : parse $ tk "#print_sorry_in") : parser unit := do
  nm ← ident,
  nm ← resolve_name nm,
  print_sorry_in nm.const_name

add_tactic_doc
{ name                     := "print_sorry_in",
  category                 := doc_category.cmd,
  decl_names               := [`print_sorry_in_cmd],
  tags                     := ["search", "environment", "debugging"] }
