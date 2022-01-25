/-
Copyright (c) 2019 Keeley Hoek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keeley Hoek
-/

import tactic.core

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
def select_for_which {α β γ : Type} (p : α → β × γ) [decidable_eq β] (b' : β) :
  list α → list γ × list α
| [] := ([], [])
| (a :: rest) :=
  let (cs, others) := select_for_which rest, (b, c) := p a in
  if b = b' then (c :: cs, others) else (cs, a :: others)

/-- Helper function for `collect_by`. -/
private meta def collect_by_aux {α β γ : Type} (p : α → β × γ) [decidable_eq β] :
  list β → list α → list (β × list γ)
| [] [] := []
| [] _ := undefined_core "didn't find every key entry!"
| (b :: rest) as := let (cs, as) := select_for_which p b as in (b, cs) :: collect_by_aux rest as

/-- Returns the elements of `l` under the image of `p`, collecting together elements with the same
`β` component, deleting duplicates. -/
meta def collect_by {α β γ : Type} (l : list α) (p : α → β × γ) [decidable_eq β] :
  list (β × list γ) :=
collect_by_aux p (l.map $ prod.fst ∘ p).erase_dup l

/-- Sort the variables by their priority as defined by `where.binder_priority`. -/
meta def sort_variable_list (l : list (name × binder_info × expr)) :
  list (expr × binder_info × list name) :=
let l := collect_by l $ λ v, (v.2.2, (v.1, v.2.1)) in
let l := l.map $ λ el, (el.1, collect_by el.2 $ λ v, (v.2, v.1)) in
(list.join $ l.map $ λ e, prod.mk e.1 <$> e.2).qsort (λ v u, binder_less_important v.2.1 u.2.1)

/-- Separate out the names of implicit variables (commonly instances with no name). -/
meta def collect_implicit_names : list name → list string × list string
| [] := ([], [])
| (n :: ns) :=
let n := to_string n, (ns, ins) := collect_implicit_names ns in
if n.front = '_' then (ns, n :: ins) else (n :: ns, ins)

/-- Format an individual variable definition for printing. -/
meta def format_variable : expr × binder_info × list name → tactic string
| (e, bi, ns) := do
  let (l, r) := bi.brackets,
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

/-- Give a slightly friendlier name for `name.anonymous` in the context of your current namespace.
-/
private meta def explain_anonymous_name : name → string
| name.anonymous := "[root namespace]"
| ns := to_string ns

/-- `#where` output helper which traces the current namespace. -/
meta def build_str_namespace (ns : name) : lean.parser string :=
return sformat!"namespace {explain_anonymous_name ns}"

/-- `#where` output helper which traces the open namespaces. -/
meta def build_str_open_namespaces (ns : name) : tactic string :=
do l ← get_open_namespaces ns,
   let str := " ".intercalate $ l.map to_string,
   if l.empty then return ""
   else return sformat!"open {str}"

/-- `#where` output helper which traces the variables. -/
meta def build_str_variables : lean.parser string :=
do l ← get_variables,
   str ← compile_variable_list l,
   if l.empty then return ""
   else return sformat!"variables {str}"

/-- `#where` output helper which traces the includes. -/
meta def build_str_includes : lean.parser string :=
do l ← get_included_variables,
   let str := " ".intercalate $ l.map $ λ n, to_string n.1,
   if l.empty then return ""
   else return sformat!"include {str}"

/-- `#where` output helper which traces the namespace end. -/
meta def build_str_end (ns : name) : tactic string :=
return sformat!"end {explain_anonymous_name ns}"

/-- `#where` output helper which traces newlines. -/
private meta def append_nl (s : string) (n : ℕ) : tactic string :=
return $ s ++ (list.as_string $ (list.range n).map $ λ _, '\n')

/-- `#where` output helper which traces lines, adding a newline if nonempty. -/
private meta def append_line (s : string) (t : lean.parser string) : lean.parser string :=
do v ← t,
   return $ s ++ v ++ (if v.length = 0 then "" else "\n")

/-- `#where` output main function. -/
meta def build_msg : lean.parser string :=
do let msg := "",
   ns ← get_current_namespace,
   msg ← append_line msg $ build_str_namespace ns,
   msg ← append_nl   msg 1,
   msg ← append_line msg $ build_str_open_namespaces ns,
   msg ← append_line msg $ build_str_variables,
   msg ← append_line msg $ build_str_includes,
   msg ← append_nl   msg 3,
   msg ← append_line msg $ build_str_end ns,
   return msg

open interactive

/--
When working in a Lean file with namespaces, parameters, and variables, it can be confusing to
identify what the current "parser context" is. The command `#where` identifies and prints
information about the current location, including the active namespace, open namespaces, and
declared variables.

It is a bug for `#where` to incorrectly report this information (this was not formerly the case);
please file an issue on GitHub if you observe a failure.
-/
@[user_command]
meta def where_cmd (_ : parse $ tk "#where") : lean.parser unit :=
do msg ← build_msg,
   trace msg

add_tactic_doc
{ name                     := "#where",
  category                 := doc_category.cmd,
  decl_names               := [`where.where_cmd],
  tags                     := ["environment"] }

end where
