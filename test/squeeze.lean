import data.nat.basic
import tactic.squeeze
import data.list.perm

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
     (λ args, guard ((args.map to_string).perm (l.map to_string)) <|> fail!"{args} expected.")
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
by { squeeze_simp_test [←h, two_mul] = [←h, add_zero, two_mul] }
