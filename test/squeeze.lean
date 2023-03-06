import data.nat.basic
import data.pnat.defs
import tactic.squeeze

namespace tactic
namespace interactive
setup_tactic_parser

/-- version of squeeze_simp that tests whether the output matches the expected output -/
meta def squeeze_simp_test
  (key : parse cur_pos)
  (slow_and_accurate : parse (tk "?")?)
  (use_iota_eqn : parse (tk "!")?) (no_dflt : parse only_flag) (hs : parse simp_arg_list)
  (attr_names : parse with_ident_list) (locat : parse location)
  (cfg : parse struct_inst?)
  (_ : parse (tk "=")) (l : parse simp_arg_list) : tactic unit :=
do (cfg',c) ← parse_config cfg,
   squeeze_simp_core slow_and_accurate.is_some no_dflt hs
     (λ l_no_dft l_args, simp use_iota_eqn none l_no_dft l_args attr_names locat cfg')
     (λ a, guard (a.map to_string = l.map to_string) <|> fail!"{a.map to_string} expected.")
end interactive
end tactic

-- Test that squeeze_simp succeeds when it closes the goal.
example : 1 = 1 :=
by { squeeze_simp_test = [eq_self_iff_true] }

-- Test that `squeeze_simp` succeeds when given arguments.
example {a b : ℕ} (h : a + a = b) : b + 0 = 2 * a :=
by { squeeze_simp_test [←h, two_mul] = [←h, two_mul, add_zero] }

-- Test that the order of the given hypotheses do not matter.
example {a b : ℕ} (h : a + a = b) : b + 0 = 2 * a :=
by { squeeze_simp_test [←h, two_mul] = [←h, two_mul, add_zero] }

section namespacing1

@[simp] lemma asda {a : ℕ} : 0 ≤ a := nat.zero_le _

@[simp] lemma pnat.asda {a : ℕ+} : 1 ≤ a := pnat.one_le _

open pnat

-- Test that adding two clashing decls to a namespace doesn't break `squeeze_simp`.
example {a : ℕ} {b : ℕ+} : 0 ≤ a ∧ 1 ≤ b :=
by { squeeze_simp_test = [_root_.asda, pnat.asda, and_self] }

end namespacing1

section namespacing2

open nat

local attribute [simp] nat.mul_succ

-- Test that we strip superflous prefixes from `squeeze_simp` output, if needed.
example (n m : ℕ) : n * m.succ = n*m + n :=
by { squeeze_simp_test = [mul_succ] }

end namespacing2

def a := 0
def b := 0
def c := 0
def f : ℕ → ℕ := default
@[simp] lemma k (x) : f x = b := rfl
@[simp] lemma l : f b = c := rfl

-- Test the fix for #3097
example : f (f a) = c := by { squeeze_simp_test = [k, l] }
