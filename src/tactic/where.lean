/-
Copyright (c) 2019 Keeley Hoek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keeley Hoek
-/

import data.list.defs tactic.core

/-!
# The `where` command

When working in a Lean file with namespaces, parameters, and variables,
it can be confusing to identify what the current "parser context" is.
The command `#where` tries to identify and print information about the current location,
including the active namespace, open namespaces, and declared variables.

This information is not "officially" accessible in the metaprogramming environment;
`#where` retrieves it via a number of hacks that are not always reliable.
While it is very useful as a quick reference, users should not assume its output is correct.
-/

open lean.parser tactic

namespace where

meta def binder_priority : binder_info → ℕ
| binder_info.implicit := 1
| binder_info.strict_implicit := 2
| binder_info.default := 3
| binder_info.inst_implicit := 4
| binder_info.aux_decl := 5

meta def binder_less_important (u v : binder_info) : bool :=
(binder_priority u) < (binder_priority v)

def select_for_which {α β γ : Type} (p : α → β × γ) [decidable_eq β] (b' : β) : list α → list γ × list α
| [] := ([], [])
| (a :: rest) :=
  let (cs, others) := select_for_which rest, (b, c) := p a in
  if b = b' then (c :: cs, others) else (cs, a :: others)

meta def collect_by_aux {α β γ : Type} (p : α → β × γ) [decidable_eq β] : list β → list α → list (β × list γ)
| [] [] := []
| [] _ := undefined_core "didn't find every key entry!"
| (b :: rest) as := let (cs, as) := select_for_which p b as in (b, cs) :: collect_by_aux rest as

meta def collect_by {α β γ : Type} (l : list α) (p : α → β × γ) [decidable_eq β] : list (β × list γ) :=
collect_by_aux p (l.map $ prod.fst ∘ p).erase_dup l

def inflate {α β γ : Type} : list (α × list (β × γ)) → list (α × β × γ)
| [] := []
| ((a, l) :: rest) := (l.map $ λ e, (a, e.1, e.2)) ++ inflate rest

meta def sort_variable_list (l : list (name × binder_info × expr)) : list (expr × binder_info × list name) :=
let l := collect_by l $ λ v, (v.2.2, (v.1, v.2.1)) in
let l := l.map $ λ el, (el.1, collect_by el.2 $ λ v, (v.2, v.1)) in
(inflate l).qsort (λ v u, binder_less_important v.2.1 u.2.1)

meta def collect_implicit_names : list name → list string × list string
| [] := ([], [])
| (n :: ns) :=
let n := to_string n, (ns, ins) := collect_implicit_names ns in
if n.front = '_' then (ns, n :: ins) else (n :: ns, ins)

meta def format_variable : expr × binder_info × list name → tactic string
| (e, bi, ns) := do let (l, r) := bi.brackets,
                    e ← pp e,
                    let (ns, ins) := collect_implicit_names ns,
                    let ns := " ".intercalate $ ns.map to_string,
                    let ns := if ns.length = 0 then [] else [sformat!"{l}{ns} : {e}{r}"],
                    let ins := ins.map $ λ _, sformat!"{l}{e}{r}",
                    return $ " ".intercalate $ ns ++ ins

meta def compile_variable_list (l : list (name × binder_info × expr)) : tactic string :=
" ".intercalate <$> (sort_variable_list l).mmap format_variable

meta def trace_namespace (ns : name) : lean.parser unit :=
do let str := match ns with
   | name.anonymous := "[root namespace]"
   | ns := to_string ns
   end,
   trace format!"namespace {str}"

private meta def strip_namespace (ns n : name) : name :=
n.replace_prefix ns name.anonymous

meta def get_open_namespaces (ns : name) : tactic (list name) :=
do opens ← list.erase_dup <$> tactic.open_namespaces,
   return $ (opens.erase ns).map $ strip_namespace ns

meta def trace_opens (ns : name) : tactic unit :=
do l ← get_open_namespaces ns,
   let str := " ".intercalate $ l.map to_string,
   if l.empty then skip
   else trace format!"open {str}"

meta def trace_variables : lean.parser unit :=
do l ← get_variables,
   str ← compile_variable_list l,
   if l.empty then skip
   else trace format!"variables {str}"

meta def trace_includes : lean.parser unit :=
do l ← get_included_variables,
   let str := " ".intercalate $ l.map $ λ n, to_string n.1,
   if l.empty then skip
   else trace format!"include {str}"

meta def trace_nl : ℕ → tactic unit
| 0 := skip
| (n + 1) := trace "" >> trace_nl n

meta def trace_end (ns : name) : tactic unit :=
trace format!"end {ns}"

meta def trace_where : lean.parser unit :=
do ns ← get_current_namespace,
   trace_namespace ns,
   trace_nl 1,
   trace_opens ns,
   trace_variables,
   trace_includes,
   trace_nl 3,
   trace_end ns

open interactive

reserve prefix `#where`:max

/--
When working in a Lean file with namespaces, parameters, and variables, it can be confusing to
identify what the current "parser context" is. The command `#where` identifies and prints
information about the current location, including the active namespace, open namespaces, and
declared variables.

It is a bug for `#where` to incorrectly report this information (this was not formerly the case);'
please file an issue on GitHub if you observe a failure.
-/
@[user_command]
meta def where_cmd (_ : decl_meta_info) (_ : parse $ tk "#where") : lean.parser unit := trace_where

add_tactic_doc
{ name                     := "#where",
  category                 := doc_category.cmd,
  decl_names               := [`where.where_cmd],
  tags                     := ["environment"] }

end where
