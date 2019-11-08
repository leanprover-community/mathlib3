import .tactic

namespace tactic
namespace interactive

open back
open interactive interactive.types lean.parser

meta def back (lemmas : parse (optional $ list_of ident)) : tactic unit :=
do lemmas ← lemmas.to_list.join.mmap (λ n, tactic.resolve_name n >>= tactic.i_to_expr_for_apply),
   let cfg : config := {passed_lemmas := lemmas},
   search cfg

end interactive
end tactic
