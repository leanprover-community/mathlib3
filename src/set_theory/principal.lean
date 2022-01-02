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
∀ a b, a < o → b < o → op a b < o

theorem fp_of_principal {op : ordinal.{u} → ordinal.{u} → ordinal.{u}} {a o : ordinal.{u}}
  (hao : a < o) (H : is_normal (op a)) (ho : principal op o) (ho' : is_limit o) : op a o = o :=
begin
  refine le_antisymm _ (H.le_self _),
  rw [←is_normal.bsup_eq.{u u} H ho', bsup_le],
  exact λ b hbo, le_of_lt (ho a b hao hbo)
end

theorem principal_of_fp {op : ordinal.{u} → ordinal.{u} → ordinal.{u}} {o : ordinal.{u}}
  (H : ∀ a < o, op a o = o) (hop : ∀ a < o, strict_mono (op a)) : principal op o :=
begin
  intros a b hao hbo,
  have := hop a hao hbo,
  rwa H a hao at this
end

theorem zero_principal {op : ordinal.{u} → ordinal.{u} → ordinal.{u}} : principal op 0 :=
λ a _ h, (not_lt_of_le (ordinal.zero_le a) h).elim

/-! ### Additive principal ordinals -/

theorem one_additive_principal : principal (+) 1 :=
begin
  intros a b ha hb,
  rw [←ordinal.succ_zero, ordinal.lt_succ] at *,
  have := ordinal.add_le_add ha hb,
  rwa add_zero at this
end

theorem omega_additive_principal : principal (+) omega.{u} :=
@add_lt_omega

theorem mul_omega_additive_principal (o : ordinal.{u}) : principal (+) (o * omega.{u}) :=
begin
  by_cases ho : o = 0,
  { rw [ho, zero_mul],
    exact zero_principal },
  intros a b hao hbo,
  cases lt_mul_omega hao with m hm,
  cases lt_mul_omega hbo with n hn,
  apply lt_of_le_of_lt (add_le_add_of_lt hm hn),
  rw [←mul_add, mul_lt_mul_iff_left (ordinal.pos_iff_ne_zero.2 ho), lt_omega],
  use m + n,
  simp
end

theorem omega_pow_additive_principal (o : ordinal.{u}) : principal (+) (omega.{u} ^ o) :=
@add_lt_omega_power o

theorem additive_principal_is_limit {o : ordinal.{u}} (ho₁ : 1 < o) (ho : principal (+) o) :
  o.is_limit :=
begin
  refine ⟨λ ho₀, _, λ a hao, _⟩,
  { rw ho₀ at ho₁,
    exact not_lt_of_gt ordinal.zero_lt_one ho₁ },
  by_cases ha : a = 0,
  { rw [ha, succ_zero],
    exact ho₁ },
  refine lt_of_le_of_lt _ (ho a a hao hao),
  rwa [succ_eq_add_one, add_le_add_iff_left, one_le_iff_ne_zero]
end

theorem fp_iff_additive_principal (o : ordinal.{u}) : principal (+) o ↔ ∀ a < o, a + o = o :=
begin
  refine ⟨λ ho a hao, _, λ h, principal_of_fp h (λ a hao, (add_is_normal a).strict_mono)⟩,
  by_cases ho₁ : 1 < o,
  { exact fp_of_principal hao (add_is_normal a) ho (additive_principal_is_limit ho₁ ho) },
  cases lt_or_eq_of_le (le_of_not_gt ho₁) with ho₁ ho₁,
  { rw lt_one_iff_zero at ho₁,
    rw ho₁ at hao,
    exact (ordinal.not_lt_zero a hao).elim },
  rw [ho₁, lt_one_iff_zero] at hao,
  rw hao,
  exact zero_add o
end

theorem additive_principal_iff_zero_or_omega_pow (o : ordinal.{u}) :
  principal (+) o ↔ o = 0 ∨ ∃ a : ordinal.{u}, o = omega.{u} ^ a :=
begin
  by_cases ho : o = 0,
  { rw ho, simp only [zero_principal, or.inl] },
  rw [fp_iff_additive_principal, add_absorp_iff (ordinal.pos_iff_ne_zero.2 ho)],
  exact ⟨or.inr, λ h, h.elim (λ ho', (ho ho').elim) id⟩
end

/-! ### Multiplicative principal ordinals -/

theorem omega_multiplicative_principal : principal (*) omega.{u} :=
@mul_lt_omega

end ordinal
