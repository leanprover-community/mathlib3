/-
Copyright (c) 2019 Keeley Hoek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keeley Hoek
-/

import data.list.defs tactic.core

/-!
# The `where` command

When working in a Lean file with namespaces, parameters, and variables, it can be confusing to
identify what the current "parser context" is. The command `#where` identifies and prints
information about the current location, including the active namespace, open namespaces, and
declared variables.

It is a bug for `#where` to incorrectly report this information (this was not formerly the case);
please file an issue on GitHub if you observe a failure.
-/

open lean.parser tactic

namespace where

/-- Assigns a priority to each binder for determining the order in which variables are traced. -/
meta def binder_priority : binder_info → ℕ
| binder_info.implicit := 1
| binder_info.strict_implicit := 2
| binder_info.default := 3
| binder_info.inst_implicit := 4
| binder_info.aux_decl := 5

/-- The relation on binder priorities. -/
meta def binder_less_important (u v : binder_info) : bool :=
(binder_priority u) < (binder_priority v)

/-- Selects the elements of the given `list α` which under the image of `p : α → β × γ` have `β`
component equal to `b'`. Returns the `γ` components of the selected elements under the image of `p`,
and the elements of the original `list α` which were not selected. -/
def select_for_which {α β γ : Type} (p : α → β × γ) [decidable_eq β] (b' : β) : list α → list γ × list α
| [] := ([], [])
| (a :: rest) :=
  let (cs, others) := select_for_which rest, (b, c) := p a in
  if b = b' then (c :: cs, others) else (cs, a :: others)

/-- Helper function for `collect_by`. -/
private meta def collect_by_aux {α β γ : Type} (p : α → β × γ) [decidable_eq β] : list β → list α → list (β × list γ)
| [] [] := []
| [] _ := undefined_core "didn't find every key entry!"
| (b :: rest) as := let (cs, as) := select_for_which p b as in (b, cs) :: collect_by_aux rest as

/-- Returns the elements of `l` under the image of `p`, collecting together elements with the same
`β` component, deleting duplicates. -/
meta def collect_by {α β γ : Type} (l : list α) (p : α → β × γ) [decidable_eq β] : list (β × list γ) :=
collect_by_aux p (l.map $ prod.fst ∘ p).erase_dup l

/-- Given `a : α` and `l : list β` form a new list by mapping `prod.mk a` over `l`. -/
def inflate {α β : Type} : α → list β → list (α × β)
| a l := l.map $ prod.mk a

/-- Sort the variables by their priority as defined above. -/
meta def sort_variable_list (l : list (name × binder_info × expr)) : list (expr × binder_info × list name) :=
let l := collect_by l $ λ v, (v.2.2, (v.1, v.2.1)) in
let l := l.map $ λ el, (el.1, collect_by el.2 $ λ v, (v.2, v.1)) in
(list.join $ l.map $ λ e, let (a,b) := e in inflate a b).qsort (λ v u, binder_less_important v.2.1 u.2.1)

/-- Separate out the names of implicit variables (commonly instances with no name). -/
meta def collect_implicit_names : list name → list string × list string
| [] := ([], [])
| (n :: ns) :=
let n := to_string n, (ns, ins) := collect_implicit_names ns in
if n.front = '_' then (ns, n :: ins) else (n :: ns, ins)

/-- Format an individual variable definitionfor printing. -/
meta def format_variable : expr × binder_info × list name → tactic string
| (e, bi, ns) := do let (l, r) := bi.brackets,
                    e ← pp e,
                    let (ns, ins) := collect_implicit_names ns,
                    let ns := " ".intercalate $ ns.map to_string,
                    let ns := if ns.length = 0 then [] else [sformat!"{l}{ns} : {e}{r}"],
                    let ins := ins.map $ λ _, sformat!"{l}{e}{r}",
                    return $ " ".intercalate $ ns ++ ins

/-- Turn a list of triples of variable names, binder info, and types, into a pretty list. -/
meta def compile_variable_list (l : list (name × binder_info × expr)) : tactic string :=
" ".intercalate <$> (sort_variable_list l).mmap format_variable

/-- Strips the namespace prefix `ns` from `n`. -/
private meta def strip_namespace (ns n : name) : name :=
n.replace_prefix ns name.anonymous

/-- `get_open_namespaces ns` returns a list of the open namespaces, given that we are currently in
the namespace `ns` (which we do not include). -/
meta def get_open_namespaces (ns : name) : tactic (list name) :=
do opens ← list.erase_dup <$> tactic.open_namespaces,
   return $ (opens.erase ns).map $ strip_namespace ns

/-- `#where` output helper which traces the current namespace. -/
meta def trace_namespace (ns : name) : lean.parser unit :=
do let str := match ns with
   | name.anonymous := "[root namespace]"
   | ns := to_string ns
   end,
   trace format!"namespace {str}"

/-- `#where` output helper which traces the open namespaces. -/
meta def trace_open_namespaces (ns : name) : tactic unit :=
do l ← get_open_namespaces ns,
   let str := " ".intercalate $ l.map to_string,
   if l.empty then skip
   else trace format!"open {str}"

/-- `#where` output helper which traces the variables. -/
meta def trace_variables : lean.parser unit :=
do l ← get_variables,
   str ← compile_variable_list l,
   if l.empty then skip
   else trace format!"variables {str}"

/-- `#where` output helper which traces the includes. -/
meta def trace_includes : lean.parser unit :=
do l ← get_included_variables,
   let str := " ".intercalate $ l.map $ λ n, to_string n.1,
   if l.empty then skip
   else trace format!"include {str}"

/-- `#where` output helper which traces newlines. -/
meta def trace_nl (n : ℕ) : tactic unit :=
(list.range n).mmap' $ λ _, trace ""

/-- `#where` output helper which traces the namespace end. -/
meta def trace_end (ns : name) : tactic unit :=
trace format!"end {ns}"

/-- `#where` output main function. -/
meta def trace_where : lean.parser unit :=
do ns ← get_current_namespace,
   trace_namespace ns,
   trace_nl 1,
   trace_open_namespaces ns,
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

It is a bug for `#where` to incorrectly report this information (this was not formerly the case);
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
