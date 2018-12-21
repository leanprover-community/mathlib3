import data.list.defs tactic.basic

open lean.parser tactic

namespace where

meta def mk_flag (let_var : option name := none) : lean.parser (name × ℕ) :=
do n ← mk_user_fresh_name,
   emit_code_here $ match let_var with
   | none   := sformat!"def {n} := ()"
   | some v := sformat!"def {n} := let {v} := {v} in ()"
   end,
   nfull ← resolve_constant n,
   return (nfull, n.components.length)

meta def get_namespace_core : name × ℕ → name
| (nfull, l) := nfull.get_nth_prefix l

meta def resolve_var : list name → ℕ → expr
| [] _ := default expr
| (n :: rest) 0 := expr.const n []
| (v :: rest) (n + 1) := resolve_var rest n

meta def resolve_vars_aux : list name → expr → expr
| head (expr.var n) := resolve_var head n
| head (expr.app f a) := expr.app (resolve_vars_aux head f) (resolve_vars_aux head a)
| head (expr.macro m e) := expr.macro m $ e.map (resolve_vars_aux head)
| head (expr.mvar n m e) := expr.mvar n m $ resolve_vars_aux head e
| head (expr.pi n bi t v) :=
  expr.pi n bi (resolve_vars_aux head t) (resolve_vars_aux (n :: head) v)
| head (expr.lam n bi t v) :=
  expr.lam n bi (resolve_vars_aux head t) (resolve_vars_aux (n :: head) v)
| head e := e

meta def resolve_vars : expr → expr :=
resolve_vars_aux []

meta def strip_pi_binders_aux : expr → list (name × binder_info × expr)
| (expr.pi n bi t b) := (n, bi, t) :: strip_pi_binders_aux b
| _ := []

meta def strip_pi_binders : expr → list (name × binder_info × expr) :=
strip_pi_binders_aux ∘ resolve_vars

meta def get_def_variables (n : name) : tactic (list (name × binder_info × expr)) :=
(strip_pi_binders ∘ declaration.type) <$> get_decl n

meta def get_includes_core (flag : name) : tactic (list (name × binder_info × expr)) :=
get_def_variables flag

meta def binder_brackets : binder_info → string × string
| binder_info.implicit        := ("{", "}")
| binder_info.strict_implicit := ("{", "}")
| binder_info.inst_implicit   := ("[", "]")
| _                           := ("(", ")")

meta def binder_priority : binder_info → ℕ
| binder_info.implicit := 1
| binder_info.strict_implicit := 2
| binder_info.default := 3
| binder_info.inst_implicit := 4
| binder_info.aux_decl := 5

meta def binder_less_important (u v : binder_info) : bool :=
(binder_priority u) < (binder_priority v)

meta def is_in_namespace_nonsynthetic (ns n : name) : bool :=
ns.is_prefix_of n ∧ ¬(ns.append `user__).is_prefix_of n

meta def get_all_in_namespace (ns : name) : tactic (list name) :=
do e ← get_env,
   return $ e.fold [] $ λ d l,
     if is_in_namespace_nonsynthetic ns d.to_name then d.to_name :: l else l

meta def fetch_potential_variable_names (ns : name) : tactic (list name) :=
do l ← get_all_in_namespace ns,
   l ← l.mmap get_def_variables,
   return $ list.erase_dup $ l.join.map prod.fst

meta def find_var (n' : name) : list (name × binder_info × expr) → option (name × binder_info × expr)
| [] := none
| ((n, bi, e) :: rest) := if n = n' then some (n, bi, e) else find_var rest

meta def is_variable_name (n : name) : lean.parser (option (name × binder_info × expr)) :=
do { (f, _) ← mk_flag n,
     l ← get_def_variables f,
     return $ l.find $ λ v, n = v.1
   } <|> return none

meta def get_variables_core (ns : name) : lean.parser (list (name × binder_info × expr)) :=
do l ← fetch_potential_variable_names ns,
   list.filter_map id <$> l.mmap is_variable_name

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
| (e, bi, ns) := do let (l, r) := binder_brackets bi,
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

meta def strip_namespace (ns n : name) : name :=
n.replace_prefix ns name.anonymous

meta def get_opens (ns : name) : tactic (list name) :=
do opens ← list.erase_dup <$> open_namespaces,
   return $ (opens.erase ns).map $ strip_namespace ns

meta def trace_opens (ns : name) : tactic unit :=
do l ← get_opens ns,
   let str := " ".intercalate $ l.map to_string,
   if l.empty then skip
   else trace format!"open {str}"

meta def trace_variables (ns : name) : lean.parser unit :=
do l ← get_variables_core ns,
   str ← compile_variable_list l,
   if l.empty then skip
   else trace format!"variables {str}"

meta def trace_includes (f : name) : tactic unit :=
do l ← get_includes_core f,
   let str := " ".intercalate $ l.map $ λ n, to_string n.1,
   if l.empty then skip
   else trace format!"include {str}"

meta def trace_nl : ℕ → tactic unit
| 0 := skip
| (n + 1) := trace "" >> trace_nl n

meta def trace_end (ns : name) : tactic unit :=
trace format!"end {ns}"

meta def trace_where : lean.parser unit :=
do (f, n) ← mk_flag,
   let ns := get_namespace_core (f, n),
   trace_namespace ns,
   trace_nl 1,
   trace_opens ns,
   trace_variables ns,
   trace_includes f,
   trace_nl 3,
   trace_end ns

open interactive

reserve prefix `#where`:max

@[user_command]
meta def where_cmd (_ : decl_meta_info) (_ : parse $ tk "#where") : lean.parser unit := trace_where

end where

namespace lean.parser

open where

meta def get_namespace : lean.parser name :=
get_namespace_core <$> mk_flag

meta def get_includes : lean.parser (list (name × binder_info × expr)) :=
do (f, _) ← mk_flag,
   get_includes_core f

meta def get_variables : lean.parser (list (name × binder_info × expr)) :=
do (f, _) ← mk_flag,
   get_variables_core f

end lean.parser
