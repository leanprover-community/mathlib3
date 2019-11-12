import .tactic

namespace tactic
namespace interactive

open back
open interactive interactive.types lean.parser

meta def back (should_trace : parse $ optional (tk "?"))
  (lemmas : parse $ optional $ list_of ident) : tactic unit :=
do prev ← save_tracing should_trace.is_some,

   lemmas ← lemmas.to_list.join.mmap (λ n, tactic.resolve_name n >>= tactic.i_to_expr_for_apply),
   search { passed_lemmas := lemmas },

   restore_tracing prev

end interactive
end tactic
