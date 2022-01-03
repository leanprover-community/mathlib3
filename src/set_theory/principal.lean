/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import set_theory.ordinal_arithmetic

/-!
This file defines principal ordinals, which are the ordinals such that the set of ordinals less than
them is closed under a given operation. We characterize the additive and multiplicative principal
ordinals.

# Main definitions and results

* `principal`: principal ordinals under some operation.
* `add_principal_iff_zero_or_omega_power`: characterizes the additive principal ordinals as either 0
or powers of `ω`.
* `mul_principal_iff_le_two_or_omega_power_power`: characterizes the multiplicative principal
ordinals as either two or powers of powers of `ω`.
-/

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

theorem zero_principal {op : ordinal.{u} → ordinal.{u} → ordinal.{u}} : principal op 0 :=
λ a _ h, (not_lt_of_le (ordinal.zero_le a) h).elim

theorem one_principal_iff {op : ordinal.{u} → ordinal.{u} → ordinal.{u}} :
  principal op 1 ↔ op 0 0 = 0 :=
begin
  refine ⟨λ h, _, λ h a b ha hb, _⟩,
  { rwa ←lt_one_iff_zero,
    exact h 0 0 zero_lt_one zero_lt_one },
  rwa [lt_one_iff_zero, ha, hb] at *
end

theorem iterate_lt_of_principal {op : ordinal.{u} → ordinal.{u} → ordinal.{u}}
  {a o : ordinal.{u}} (hao : a < o) (ho : principal op o) (n : ℕ) : (op a)^[n] a < o :=
begin
  induction n with n hn,
  { rwa function.iterate_zero },
  have := ho a _ hao hn,
  rwa function.iterate_succ'
end

theorem nfp_le_of_principal {op : ordinal.{u} → ordinal.{u} → ordinal.{u}}
  {a o : ordinal.{u}} (hao : a < o) (ho : principal op o) : nfp (op a) a ≤ o :=
begin
  unfold nfp,
  rw sup_le,
  exact λ n, le_of_lt (iterate_lt_of_principal hao ho n)
end

/-! ### Additive principal ordinals -/

theorem one_add_principal : principal (+) 1 :=
by { rw one_principal_iff, exact zero_add 0 }

theorem add_principal_of_le_one {o : ordinal.{u}} (ho : o ≤ 1) : principal (+) o :=
begin
  rcases zero_or_one_of_le_one ho with rfl | rfl,
  { exact zero_principal },
  { exact one_add_principal }
end

theorem omega_add_principal : principal (+) omega.{u} :=
@add_lt_omega

theorem mul_omega_add_principal (o : ordinal.{u}) : principal (+) (o * omega.{u}) :=
begin
  rcases eq_or_ne o 0 with rfl | ho,
  { rw zero_mul,
    exact zero_principal },
  intros a b hao hbo,
  cases lt_mul_omega hao with m hm,
  cases lt_mul_omega hbo with n hn,
  apply lt_of_le_of_lt (add_le_add (le_of_lt hm) (le_of_lt hn)),
  rw [←mul_add, mul_lt_mul_iff_left (ordinal.pos_iff_ne_zero.2 ho), lt_omega],
  exact ⟨_, (nat.cast_add m n).symm⟩
end

theorem mul_omega_le_add_principal {a o : ordinal.{u}} (hao : a < o) (ho : principal (+) o) :
  a * omega.{u} ≤ o :=
by { convert nfp_le_of_principal hao ho, exact mul_omega_nfp_add_self a }

theorem omega_le_add_principal {o : ordinal.{u}} (ho : principal (+) o) (ho₁ : 1 < o) :
  omega.{u} ≤ o :=
by { rw ←one_mul omega.{u}, exact mul_omega_le_add_principal ho₁ ho }

theorem omega_power_add_principal (o : ordinal.{u}) : principal (+) (omega.{u} ^ o) :=
@add_lt_omega_power o

theorem add_principal_is_limit {o : ordinal.{u}} (ho₁ : 1 < o) (ho : principal (+) o) :
  o.is_limit :=
begin
  refine ⟨λ ho₀, _, λ a hao, _⟩,
  { rw ho₀ at ho₁,
    exact not_lt_of_gt ordinal.zero_lt_one ho₁ },
  cases eq_or_ne a 0 with ha ha,
  { rw [ha, succ_zero],
    exact ho₁ },
  refine lt_of_le_of_lt _ (ho a a hao hao),
  rwa [succ_eq_add_one, add_le_add_iff_left, one_le_iff_ne_zero]
end

theorem add_principal_iff_fp (o : ordinal.{u}) : principal (+) o ↔ ∀ a < o, a + o = o :=
begin
  refine ⟨λ ho a hao, _, λ h a b hao hbo, _⟩,
  { cases lt_or_le 1 o with ho₁ ho₁,
    { exact fp_of_principal hao (add_is_normal a) ho (add_principal_is_limit ho₁ ho) },
    rcases zero_or_one_of_le_one ho₁ with rfl | rfl,
    { exact (ordinal.not_lt_zero a hao).elim },
    rw lt_one_iff_zero at hao,
    rw [hao, zero_add] },
  rw ←h a hao,
  exact (add_is_normal a).strict_mono hbo
end

theorem add_principal_iff_zero_or_omega_power (o : ordinal.{u}) :
  principal (+) o ↔ o = 0 ∨ ∃ a : ordinal.{u}, o = omega.{u} ^ a :=
begin
  cases eq_or_ne o 0 with ho ho,
  { rw ho, simp only [zero_principal, or.inl] },
  rw [add_principal_iff_fp, add_absorp_iff (ordinal.pos_iff_ne_zero.2 ho)],
  exact ⟨or.inr, λ h, h.elim (λ ho', (ho ho').elim) id⟩
end

/-! ### Multiplicative principal ordinals -/

theorem one_mul_principal : principal (*) 1 :=
by { rw one_principal_iff, exact zero_mul _ }

theorem two_mul_principal : principal (*) 2 :=
begin
  intros a b ha hb,
  rw ←le_one_iff_lt_two at *,
  convert mul_le_mul ha hb,
  exact (mul_one 1).symm
end

theorem le_two_mul_principal {o : ordinal} (ho : o ≤ 2) : principal (*) o :=
begin
  rcases lt_or_eq_of_le ho with ho | rfl,
  { rcases lt_or_eq_of_le (le_one_iff_lt_two.2 ho) with ho | rfl,
    { rw lt_one_iff_zero.1 ho,
      exact zero_principal },
    exact one_mul_principal },
  exact two_mul_principal
end

theorem omega_mul_principal : principal (*) omega.{u} :=
@mul_lt_omega

theorem power_omega_mul_principal (o : ordinal.{u}) : principal (*) (o ^ omega.{u}) :=
begin
  cases le_or_gt o 1 with ho ho,
  { rcases zero_or_one_of_le_one ho with rfl | rfl,
    { rw ordinal.zero_power omega_ne_zero,
      exact zero_principal },
    rw one_power,
    exact one_mul_principal },
  intros a b hao hbo,
  cases lt_power_omega hao with m hm,
  cases lt_power_omega hbo with n hn,
  apply lt_of_le_of_lt (mul_le_mul (le_of_lt hm) (le_of_lt hn)),
  rw [←power_add, power_lt_power_iff_right ho, lt_omega],
  exact ⟨_, (nat.cast_add m n).symm⟩
end

theorem power_omega_le_mul_principal {a o : ordinal.{u}} (hao : a < o) (ho : principal (*) o) :
  a ^ omega.{u} ≤ o :=
by { convert nfp_le_of_principal hao ho, exact power_omega_nfp_mul_self a }

theorem omega_le_mul_principal {o : ordinal.{u}} (ho : principal (*) o) (ho₂ : 2 < o) :
  omega.{u} ≤ o :=
by { rw ←power_omega (lt_succ_self 1) two_lt_omega, exact power_omega_le_mul_principal ho₂ ho }

theorem add_principal_of_mul_principal {o : ordinal.{u}} (ho : principal (*) o) (ho₂ : o ≠ 2) :
  principal (+) o :=
begin
  cases lt_or_gt_of_ne ho₂ with ho₁ ho₂,
  { change o < succ 1 at ho₁,
    rw lt_succ at ho₁,
    exact add_principal_of_le_one ho₁ },
  refine λ a b hao hbo, lt_of_le_of_lt _ (ho _ 2 (max_lt hao hbo) ho₂),
  rw mul_two,
  exact add_le_add (le_max_left a b) (le_max_right a b)
end

theorem mul_principal_is_limit {o : ordinal.{u}} (ho₂ : 2 < o) (ho : principal (*) o) :
  o.is_limit :=
add_principal_is_limit (one_lt_two.trans ho₂) (add_principal_of_mul_principal ho (ne_of_gt ho₂))

theorem mul_principal_iff_fp (o : ordinal.{u}) :
  principal (*) o ↔ ∀ a, 0 < a → a < o → a * o = o :=
begin
  refine ⟨λ h a ha₀ hao, _, λ h a b hao hbo, _⟩,
  { cases le_or_gt o 2 with ho ho,
    { convert one_mul o,
      apply le_antisymm,
      { have : a < succ 1 := lt_of_lt_of_le hao ho,
        rwa lt_succ at this },
      rwa [←succ_le, succ_zero] at ha₀ },
    exact fp_of_principal hao (mul_is_normal ha₀) h (mul_principal_is_limit ho h) },
  rcases eq_or_ne a 0 with rfl | ha, { rwa zero_mul },
  rw ←ordinal.pos_iff_ne_zero at ha,
  rw ←h a ha hao,
  exact (mul_is_normal ha).strict_mono hbo
end

theorem omega_power_power_is_normal : is_normal (λ a : ordinal.{u}, omega.{u} ^ omega.{u} ^ a) :=
by apply is_normal.trans; exact power_is_normal one_lt_omega

theorem omega_power_power_mul_principal (o : ordinal.{u}) :
  principal (*) (omega.{u} ^ omega.{u} ^ o) :=
by { rw mul_principal_iff_fp, exact λ a, mul_omega_power_power }

theorem mul_principal_power_omega {o : ordinal.{u}} (ho : principal (*) o) (ho₂ : 2 < o) :
  ∃ a : ordinal.{u}, o = omega.{u} ^ a :=
begin
  have := add_principal_of_mul_principal ho (ne_of_gt ho₂),
  rw add_principal_iff_zero_or_omega_power at this,
  cases this with ho₀ h,
  { rw ho₀ at ho₂,
    exact (ordinal.not_lt_zero 2 ho₂).elim },
  exact h
end

theorem lt_omega_power_power_log_log_succ_of_principal {o : ordinal.{u}} (ho : principal (*) o)
  (ho₂ : 2 < o) : o < omega.{u} ^ omega.{u} ^ (log omega.{u} (log omega.{u} o)).succ :=
begin
  have := lt_power_succ_log one_lt_omega (log omega.{u} o),
  rw ←power_lt_power_iff_right one_lt_omega at this,
  cases mul_principal_power_omega ho ho₂ with a ha,
  convert this,
  nth_rewrite 1 ha,
  rwa log_power _ one_lt_omega
end

theorem mul_principal_eq_omega_power_power {o : ordinal.{u}} (ho : principal (*) o) (ho₂ : 2 < o) :
  o = omega.{u} ^ omega.{u} ^ (log omega.{u} (log omega.{u} o)) :=
begin
  apply le_antisymm,
  { by_contra' h,
    apply not_le_of_lt (lt_omega_power_power_log_log_succ_of_principal ho ho₂),
    rw [power_succ, power_mul],
    exact power_omega_le_mul_principal h ho },
  have : omega.{u} ^ (log omega.{u} (log omega.{u} o)) ≤ log omega.{u} o := begin
    apply power_log_le,
    rw [←succ_le, le_log one_lt_omega (zero_lt_two.trans ho₂), succ_zero, power_one],
    exact omega_le_mul_principal ho ho₂
  end,
  rw ←power_le_power_iff_right one_lt_omega at this,
  exact this.trans (power_log_le _ (zero_lt_two.trans ho₂))
end

theorem mul_principal_iff_le_two_or_omega_power_power (o : ordinal.{u}) :
  principal (*) o ↔ o ≤ 2 ∨ ∃ a : ordinal.{u}, o = omega.{u} ^ omega.{u} ^ a :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { rw or_iff_not_imp_left,
    exact λ ho, ⟨_, mul_principal_eq_omega_power_power h (lt_of_not_ge ho)⟩ },
  cases h with ho ho,
  { exact le_two_mul_principal ho },
  rcases ho with ⟨a, rfl⟩,
  exact omega_power_power_mul_principal _
end

end ordinal
