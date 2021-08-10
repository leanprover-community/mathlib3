/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

/-!
# Extra facts about `pprod`
-/

variables {α : Sort*} {β : Sort*}

@[simp] lemma pprod.mk.eta {p : pprod α β} : pprod.mk p.1 p.2 = p :=
pprod.cases_on p (λ a b, rfl)
