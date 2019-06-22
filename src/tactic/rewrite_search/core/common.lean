import lib.tactic
import tactic.rewrite_all

import .data

universe u

meta inductive how
| rewrite (rule_index : ℕ) (location : ℕ) (addr : option (list side))
| defeq
| simp  -- TODO handle "explaining" me
meta def how.to_string : how → format
| (how.rewrite idx loc addr) := format!"rewrite {idx} {loc} {addr.iget.to_string}"
| how.defeq := "(defeq)"
| how.simp := "simp"
meta instance how.has_to_format : has_to_format how := ⟨how.to_string⟩

meta structure rewrite :=
(e   : expr)
(prf : tactic expr) -- we defer constructing the proofs until they are needed
(how : how)

namespace tactic.rewrite_search

meta structure core_cfg :=
(max_iterations  : ℕ := 500)
(max_discovers   : ℕ := 0)
(optimal         : bool := tt)
(exhaustive      : bool := ff)
(trace           : bool := ff)
(trace_summary   : bool := ff)
(trace_rules     : bool := ff)
(trace_discovery : bool := tt)
(explain         : bool := ff)
(explain_using_conv : bool := tt)

end tactic.rewrite_search

open tactic

namespace rw_equation

meta def split : expr → tactic (expr × expr)
| `(%%lhs = %%rhs) := return (lhs, rhs)
| `(%%lhs ↔ %%rhs) := return (lhs, rhs)
| _                := fail "target is not an equation or iff"

meta def lhs (e : expr) : tactic expr := prod.fst <$> split e

meta def rhs (e : expr) : tactic expr := prod.snd <$> split e

end rw_equation

meta def is_acceptable_rewrite (t : expr) : bool :=
t.is_eq_or_iff_after_binders

meta def is_acceptable_lemma (r : expr) : tactic bool :=
  is_acceptable_rewrite <$> (infer_type r >>= whnf)

meta def is_acceptable_hyp (r : expr) : tactic bool :=
  do t ← infer_type r >>= whnf, return $ is_acceptable_rewrite t ∧ ¬t.has_meta_var
