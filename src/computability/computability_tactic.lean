/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
import computability.primrec.basic

/-!
# Tactic for proving functions are in a computational class

-/

@[user_attribute]
meta def primrec_attr : user_attribute :=
{ name := `primrec,
  descr := "lemmas usable to prove a function is primitive recursive" }

attribute [primrec]
  primrec.id
  primrec.const

@[primrec]
lemma primrec.id' {α} [tencodable α] : primrec (λ x : α, x) := primrec.id

namespace tactic

/- In order to help resolve propositions (which are converted to bool's),
  we simplify -/
meta def simp_to_bool : tactic unit :=
`[simp only [bool.to_bool_not, bool.to_bool_and, bool.to_bool_or, bool.to_bool_coe] { eta := ff }]

#check apply_rules
#check user_attribute
#check tactic.tidy
#check tactic.interactive.mono
#check tactic.repeat

end tactic
