import data.multiset.basic
import tactic.where

-- First set up the testing framework...

section framework

-- Note that we cannot have any explicit `open`s, we are currently working around this bug:
-- https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/What's.20the.20deal.20with.20.60open.60

@[user_command]
meta def run_parser_from_command_cmd
  (_ : interactive.parse $ lean.parser.tk "run_parser_from_command")
  : lean.parser unit :=
do ns ← lean.parser.ident,
   let ns := if ns = `NONE then name.anonymous else ns,
   n ← lean.parser.ident,
   prog ← lean.parser.of_tactic $ tactic.mk_const (ns ++ n) >>= tactic.eval_expr (lean.parser unit),
   if ns = name.anonymous then tactic.skip else lean.parser.emit_code_here $
     "namespace " ++ ns.to_string,
   prog,
   if ns = name.anonymous then tactic.skip else lean.parser.emit_code_here $
     "end " ++ ns.to_string

meta def remove_dot_aux : list char → list char
| [] := []
| (c :: rest) := (if c = '.' then '_' else c) :: remove_dot_aux rest

meta def remove_dot (s : string) : string :=
(remove_dot_aux s.data).as_string

-- NOTE We must emit fully qualified names below in order to not influence the real tests!
@[user_command]
meta def run_parser_from_tactic_cmd
  (_ : interactive.parse $ lean.parser.tk "run_parser_from_tactic")
  : lean.parser unit :=
do ns ← lean.parser.ident,
   let ns := if ns = `NONE then name.anonymous else ns,
   n ← lean.parser.ident,
   let tac_name := "try_test_" ++ (remove_dot (ns ++ n).to_string),
   lean.parser.emit_code_here $
     "meta def tactic.interactive." ++ tac_name ++
       " (_ : interactive.parse " ++ (ns ++ n).to_string ++ ")" ++ ": tactic unit := tactic.triv",
   if ns = name.anonymous then tactic.skip else lean.parser.emit_code_here $
     "namespace " ++ ns.to_string,
   lean.parser.emit_code_here $
      "example : true := by " ++ (name.mk_string tac_name name.anonymous).to_string,
   if ns = name.anonymous then tactic.skip else lean.parser.emit_code_here $
     "end " ++ ns.to_string

meta def assert_name_eq (n₁ n₂ : name) : lean.parser unit :=
if n₁ = n₂ then return () else tactic.fail sformat!"violation: '{n₁}' ≠ '{n₂}'!"

meta def assert_list_noorder_eq {α : Type} [decidable_eq α] [has_to_string α]
  (l₁ l₂ : list α) : lean.parser unit :=
if (l₁ : multiset α) = (l₂ : multiset α) then return ()
else tactic.fail sformat!"violation: '{l₁}' ≠ '{l₂}'!"

meta def assert_where_msg_eq (s : string) : lean.parser unit :=
do tw ← where.build_msg,
   if s = tw then return ()
   else tactic.fail sformat!"violation:\n'\n{tw}\n'\n\n          ≠\n\n'\n{s}\n'!"

-- Test the test framework...

meta def dummy : lean.parser unit := return ()

run_parser_from_command NONE dummy
run_parser_from_tactic  NONE dummy

end framework

-- TESTS START



-- TEST: `#where` output
-- NOTE: This section must come first because of the `open_namespaces` bug referenced above.
-- NOTE: All other sections have correct answers, but the order of variables (say) may be safely
--       reordered here: changes to `#where` which break this set of tests are possible, without an
--       error.

meta def test_output_1 : lean.parser unit :=
assert_where_msg_eq "namespace [root namespace]\n\n\n\n\nend [root namespace]\n"
meta def test_output_2 : lean.parser unit :=
assert_where_msg_eq "namespace [root namespace]\n\nopen list nat\n\n\n\nend [root namespace]\n"
meta def test_output_3 : lean.parser unit :=
assert_where_msg_eq "namespace [root namespace]\n\nopen list nat\nvariables {c : ℕ → list ℕ} (b a : ℕ) [decidable_eq : ℕ]\n\n\n\nend [root namespace]\n"
meta def test_output_4 : lean.parser unit :=
assert_where_msg_eq "namespace [root namespace]\n\nopen list nat\nvariables {c : ℕ → list ℕ} (b a : ℕ) [decidable_eq : ℕ]\ninclude c a\n\n\n\nend [root namespace]\n"
meta def test_output_5 : lean.parser unit :=
assert_where_msg_eq "namespace a\n\nopen list nat\nvariables {c : ℕ → list ℕ} (b a : ℕ) [decidable_eq : ℕ]\ninclude c a\n\n\n\nend a\n"
meta def test_output_6 : lean.parser unit :=
assert_where_msg_eq "namespace a.b\n\nopen a list nat\nvariables {c : ℕ → list ℕ} (b a : ℕ) [decidable_eq : ℕ]\ninclude c a\n\n\n\nend a.b\n"

section b1

-- #where
run_parser_from_command NONE test_output_1

open nat list

-- #where
run_parser_from_command NONE test_output_2

variables (a b : ℕ) [decidable_eq : ℕ] {c : ℕ → list ℕ}

-- #where
run_parser_from_command NONE test_output_3

include a c

-- #where
run_parser_from_command NONE test_output_4

end b1

namespace a

variables (a b : ℕ) [decidable_eq : ℕ] {c : ℕ → list ℕ}
include a c
open nat list

-- #where
run_parser_from_command NONE test_output_5

namespace b

-- #where
run_parser_from_command NONE test_output_6

end b

end a





-- TEST: `lean.parser.get_current_namespace`

-- Check no namespace
meta def test_no_namespace : lean.parser unit :=
do ns ← lean.parser.get_current_namespace,
   assert_name_eq ns name.anonymous,
   return ()

run_parser_from_command NONE test_no_namespace
run_parser_from_tactic  NONE test_no_namespace

section a1

open nat list

-- Check no namespace with opens
meta def test_no_namespace_w_opens : lean.parser unit :=
do ns ← lean.parser.get_current_namespace,
   assert_name_eq ns name.anonymous,
   return ()

run_parser_from_command NONE test_no_namespace_w_opens
run_parser_from_tactic  NONE test_no_namespace_w_opens

end a1

namespace test1

-- Check a namespace
meta def test_1 : lean.parser unit :=
do ns ← lean.parser.get_current_namespace,
   assert_name_eq ns `test1,
   return ()

open nat list

-- Check a 2 namespaces with opens
meta def test_2 : lean.parser unit :=
do ns ← lean.parser.get_current_namespace,
   assert_name_eq ns `test1,
   return ()

end test1

run_parser_from_command test1 test_1
run_parser_from_command test1 test_2
run_parser_from_tactic  test1 test_1
run_parser_from_tactic  test1 test_2

namespace test1.test2

-- Check a 2 namespaces
meta def test_1 : lean.parser unit :=
do ns ← lean.parser.get_current_namespace,
   assert_name_eq ns `test1.test2,
   return ()

open nat list

-- Check a 2 namespaces with opens
meta def test_2 : lean.parser unit :=
do ns ← lean.parser.get_current_namespace,
   assert_name_eq ns `test1.test2,
   return ()

end test1.test2

run_parser_from_command test1.test2 test_1
run_parser_from_command test1.test2 test_2
run_parser_from_tactic  test1.test2 test_1
run_parser_from_tactic  test1.test2 test_2






-- TEST: `lean.parser.get_variables` and `lean.parser.get_included_variables`

-- Check no variables
meta def test_no_variables : lean.parser unit :=
do ns ← lean.parser.get_variables,
   assert_list_noorder_eq (ns.map prod.fst) [],
   return ()

run_parser_from_command NONE test_no_variables
run_parser_from_tactic  NONE test_no_variables

section a1

variables (a : ℕ)

-- Check 1 variable from command
meta def test_1_variable_from_command : lean.parser unit :=
do ns ← lean.parser.get_variables,
   assert_list_noorder_eq (ns.map prod.fst) [`a],
   return ()

run_parser_from_command NONE test_1_variable_from_command

-- Check 1 variable from tactic
meta def test_1_variable_from_tactic : lean.parser unit :=
do ns ← lean.parser.get_variables,
   assert_list_noorder_eq (ns.map prod.fst) [],
   return ()

run_parser_from_tactic  NONE test_1_variable_from_tactic

end a1

namespace a2

variables (a : ℕ)

-- Check 1 variable from command inside namespace
meta def test_1_variable_from_command : lean.parser unit :=
do ns ← lean.parser.get_variables,
   assert_list_noorder_eq (ns.map prod.fst) [`a],
   return ()

run_parser_from_command NONE test_1_variable_from_command

-- Check 1 variable from tactic inside namespace
meta def test_1_variable_from_tactic : lean.parser unit :=
do ns ← lean.parser.get_variables,
   assert_list_noorder_eq (ns.map prod.fst) [],
   return ()

run_parser_from_tactic NONE test_1_variable_from_tactic

end a2

section a3

-- Check 3 variables with 1 include
meta def test_2_variable_from_command : lean.parser unit :=
do ns ← lean.parser.get_variables,
   assert_list_noorder_eq (ns.map prod.fst) [`a, `b, `c],
   ns ← lean.parser.get_included_variables,
   assert_list_noorder_eq (ns.map prod.fst) [`b],
   return ()

variables (a b c : ℕ)
include b

run_parser_from_command NONE test_2_variable_from_command

end a3
