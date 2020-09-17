import tactic.slim_check

section

open tactic
@[interactive]
meta def mk_slim_check_test : tactic unit := do
tgt ← target,
msg ← (λ s, match interactive.slim_check { random_seed := some 257 } s with
      | result.success x _ := fail "expecting error" s
      | result.exception msg _ _ := result.success (msg.iget ()).to_string s
      end ),
trace!"Try this:
  have : {tgt},
  success_if_fail_with_msg
  {{ slim_check {{ random_seed := some 257 } }
\"{msg}\",
  admit,
  trivial
"

end
