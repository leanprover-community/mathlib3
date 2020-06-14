import tactic.nth_rewrite
import tactic.rewrite_search.core.data

universe u

namespace tactic.rewrite_search

@[derive decidable_eq, derive inhabited]
inductive side
| L
| R

def side.other : side → side
| side.L := side.R
| side.R := side.L

def side.to_string : side → string
| side.L := "L"
| side.R := "R"

instance : has_to_string side := ⟨side.to_string⟩

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

meta structure core_cfg :=
(max_iterations     : ℕ := 500)
(optimal            : bool := tt)
(exhaustive         : bool := ff)
(trace              : bool := ff)
(trace_summary      : bool := ff)
(trace_rules        : bool := ff)
(explain            : bool := ff)
(explain_using_conv : bool := tt)

end tactic.rewrite_search

open tactic

namespace rw_equation

/-- Split an expression that is an equation or an iff into its rhs and lhs parts. -/
meta def split : expr → tactic (expr × expr)
| `(%%lhs = %%rhs) := return (lhs, rhs)
| `(%%lhs ↔ %%rhs) := return (lhs, rhs)
| _                := fail "target is not an equation or iff"

/-- The left hand side of an expression (fails if the expression is not an equation or iff). -/
meta def lhs (e : expr) : tactic expr := prod.fst <$> split e

/-- The right hand side of an expression (fails if the expression is not an equation or iff). -/
meta def rhs (e : expr) : tactic expr := prod.snd <$> split e

end rw_equation

/-- Returns true if expression is an equation or iff. -/
meta def is_acceptable_rewrite : expr → bool
| (expr.pi n bi d b) := is_acceptable_rewrite b
| `(%%a = %%b)       := tt
| `(%%a ↔ %%b)       := tt
| _                  := ff

/-- Returns true if the type of expression is an equation or iff. -/
meta def is_acceptable_lemma (r : expr) : tactic bool :=
  is_acceptable_rewrite <$> (infer_type r >>= whnf)

/-- Returns true if the type of expression is an equation or iff
and does not contain metavariables. -/
meta def is_acceptable_hyp (r : expr) : tactic bool :=
  do t ← infer_type r >>= whnf, return $ is_acceptable_rewrite t ∧ ¬t.has_meta_var
