/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import set_theory.ordinal_arithmetic

universe u

namespace ordinal

/-- An ordinal `o` is said to be principal or indecomposable under an operation when the set of
ordinals less than it is closed under that operation. In standard mathematical usage, this term is
almost exclusively used for additive and multiplicative principal ordinals.

For simplicity, we break usual convention and regard 0 as principal. -/
def principal (op : ordinal.{u} → ordinal.{u} → ordinal.{u}) (o : ordinal.{u}) : Prop :=
∀ {a b}, a < o → b < o → op a b < o

theorem fp_iff_principal {op : ordinal.{u} → ordinal.{u} → ordinal.{u}} (o : ordinal.{u})
  (hop : ∀ a < o, is_normal (op a)) : principal op o ↔ ∀ a < o, op a o = o :=
sorry

theorem zero_principal (op : ordinal.{u} → ordinal.{u} → ordinal.{u}) : principal op 0 :=
λ a _ h, (not_lt_of_le (ordinal.zero_le a) h).elim

/-! ### Additive principal ordinals -/

theorem omega_additive_principal : principal (+) ordinal.omega.{u} :=
@add_lt_omega

theorem mul_omega_additive_principal (o : ordinal.{u}) : principal (+) (o * ordinal.omega.{u}) :=
begin
  intros a b hao hbo,
  -- Since multiplication is normal, there exist c, d < ω such that a < o * c and b < o * d, which
  -- then implies a + b < o * (c + d) < o * ω.
  sorry
end

theorem omega_pow_additive_principal (o : ordinal.{u}) : principal (+) (ordinal.omega.{u} ^ o) :=
begin
  -- If o is zero, this is trivial.
  sorry
end

theorem additive_principal_iff_zero_or_omega_pow (o : ordinal.{u}) :
  principal (+) o ↔ o = 0 ∨ ∃ a : ordinal.{u}, o = ordinal.omega.{u} ^ a :=
sorry

/-! ### Multiplicative principal ordinals -/
theorem omega_multiplicative_principal : principal (*) ordinal.omega.{u} :=
@mul_lt_omega

end ordinal
