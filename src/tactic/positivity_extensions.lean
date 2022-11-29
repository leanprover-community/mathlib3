import data.fintype.card
import tactic.positivity

namespace tactic
open tactic.positivity

/-- Extension for the `positivity` tactic: `nat.factorial` is always positive. -/
@[positivity]
meta def positivity_factorial : expr → tactic strictness
| `(nat.factorial %%a) := positive <$> mk_app ``nat.factorial_pos [a]
| e := pp e >>= fail ∘ format.bracket "The expression `" "` isn't of the form `n!`"

/-- Extension for the `positivity` tactic: `nat.asc_factorial` is always positive. -/
@[positivity]
meta def positivity_asc_factorial : expr → tactic strictness
| `(nat.asc_factorial %%a %%b) := positive <$> mk_app ``nat.asc_factorial_pos [a, b]
| e := pp e >>= fail ∘ format.bracket "The expression `"
         "` isn't of the form `nat.asc_factorial n k`"

private lemma card_univ_pos (α : Type*) [fintype α] [nonempty α] :
  0 < (finset.univ : finset α).card :=
finset.univ_nonempty.card_pos

/-- Extension for the `positivity` tactic: `finset.card s` is positive if `s` is nonempty. -/
@[positivity]
meta def positivity_finset_card : expr → tactic strictness
| `(finset.card %%s) := do -- TODO: Partial decision procedure for `finset.nonempty`
                          p ← to_expr ``(finset.nonempty %%s) >>= find_assumption,
                          positive <$> mk_app ``finset.nonempty.card_pos [p]
| `(@fintype.card %%α %%i) := positive <$> mk_mapp ``fintype.card_pos [α, i, none]
| e := pp e >>= fail ∘ format.bracket "The expression `"
    "` isn't of the form `finset.card s` or `fintype.card α`"

end tactic
