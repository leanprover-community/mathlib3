/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import set_theory.ordinal_arithmetic

/-!
### Principal ordinals

We define principal or indecomposable ordinals, and we prove the standard properties about them.

### Todo
* Prove the characterization of additive indecomposable ordinals.
* Prove the characterization of multiplicative indecomposable ordinals.
* Refactor any related theorems from `ordinal_arithmetic` into this file.
-/

universe u

namespace ordinal

/-! ### Principal ordinals -/

/-- An ordinal `o` is said to be principal or indecomposable under an operation when the set of
ordinals less than it is closed under that operation. In standard mathematical usage, this term is
almost exclusively used for additive and multiplicative principal ordinals.

For simplicity, we break usual convention and regard 0 as principal. -/
def principal (op : ordinal → ordinal → ordinal) (o : ordinal) : Prop :=
∀ a b, a < o → b < o → op a b < o

theorem principal_zero {op : ordinal → ordinal → ordinal} : principal op 0 :=
λ a _ h, (ordinal.not_lt_zero a h).elim

theorem principal_one_iff {op : ordinal → ordinal → ordinal} :
  principal op 1 ↔ op 0 0 = 0 :=
begin
  refine ⟨λ h, _, λ h a b ha hb, _⟩,
  { rwa ←lt_one_iff_zero,
    exact h 0 0 zero_lt_one zero_lt_one },
  { rwa [lt_one_iff_zero, ha, hb] at * }
end

theorem iterate_lt_of_principal {op : ordinal → ordinal → ordinal}
  {a o : ordinal} (hao : a < o) (ho : principal op o) (n : ℕ) : (op a)^[n] a < o :=
begin
  induction n with n hn,
  { rwa function.iterate_zero },
  { have := ho a _ hao hn,
    rwa function.iterate_succ' }
end

theorem op_eq_self_of_principal {op : ordinal → ordinal → ordinal} {a o : ordinal.{u}}
  (hao : a < o) (H : is_normal (op a)) (ho : principal op o) (ho' : is_limit o) : op a o = o :=
begin
  refine le_antisymm _ (H.le_self _),
  rw [←is_normal.bsup_eq.{u u} H ho', bsup_le],
  exact λ b hbo, le_of_lt (ho a b hao hbo)
end

theorem nfp_le_of_principal {op : ordinal → ordinal → ordinal}
  {a o : ordinal} (hao : a < o) (ho : principal op o) : nfp (op a) a ≤ o :=
nfp_le.2 $ λ n, le_of_lt (iterate_lt_of_principal hao ho n)

end ordinal
