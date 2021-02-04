/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import meta.expr

/-
Lean currently uses the name ᾰ for binders which aren't given a name explicitly
(e.g. when using a function arrow to define a Π type). This test is here to make
sure that should this change in the future,
`name.is_likely_generated_binder_name` will be updated accordingly.
-/

example : ℕ → ℕ → ℕ :=
begin
  intros,
  guard_hyp ᾰ : ℕ,
  guard_hyp ᾰ_1 : ℕ,
  (do guard $ name.is_likely_generated_binder_name `ᾰ,
      guard $ name.is_likely_generated_binder_name `ᾰ_1
  ),
  exact ᾰ
end
