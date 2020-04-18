
import tactic.core

namespace tactic
open expr
meta def ctor_name {elab} : expr elab → string
| (var a) := "var"
| (sort a) := "sort"
| (const a a_1) := "const: " ++ to_string a
| (mvar unique pretty type) := "mvar"
| (local_const unique pretty bi type) := "local_const"
| (app a a_1) := "app"
| (lam var_name bi var_type body) := "lam"
| (pi var_name bi var_type body) := "pi"
| (elet var_name type assignment body) := "elet"
| (macro a a_1) := "macro"

meta def enclosing_name : tactic unit :=
do n ← tactic.decl_name,
   tactic.exact `(n)

meta def on_error {α β} (tac : tactic α) (hdl : tactic β) : tactic α
| s := match tac s with
       | (result.success a a_1) := result.success a a_1
       | (result.exception a a_1 s) := (hdl >> result.exception a a_1) s
       end

meta def trace_scope {α} (tac : tactic α) (n : name . enclosing_name) : tactic α :=
do trace!"• begin {n}",
   r ← on_error tac (trace!"• error in {n}"),
   trace!"• end {n}",
   pure r

end tactic
