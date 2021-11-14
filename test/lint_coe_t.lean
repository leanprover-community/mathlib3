import tactic.lint
open tactic

-- bad, because every iteration of tc search will loop, generating nested quotients
section
local attribute [instance]
def a_to_quot {α} (R : setoid α) : has_coe α (quotient R) := ⟨quotient.mk⟩

run_cmd do
  d ← get_decl ``a_to_quot,
  some _ ← linter.has_coe_variable.test d,
  d ← get_decl ``coe_trans,
  some s ← fails_quickly 3000 d,
  guard $ "maximum class-instance resolution depth has been reached".is_prefix_of s
end

-- good, because the term gets smaller in every iteration
noncomputable instance quot_to_a {α} (R : setoid α) : has_coe (quotient R) α :=
⟨λ q, quot.rec_on q (λ a, classical.choice ⟨a⟩) (by cc)⟩

run_cmd do
decl ← get_decl ``quot_to_a,
-- linter does not complain
none ← linter.has_coe_variable.test decl,
skip

-- bad, because it introduces a metavariable
section
local attribute [instance]
def int_to_a {α} [inhabited α] : has_coe ℤ α := ⟨λ _, default _⟩

run_cmd do
decl ← get_decl ``int_to_a,
-- linter does not complain
some _ ← linter.has_coe_variable.test decl,
skip
end
