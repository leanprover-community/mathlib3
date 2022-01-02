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

* `principal`: principal ordinals under some operation
* `add_principal_iff_zero_or_omega_pow`: characterizes the additive principal ordinals
* `mul_principal_iff_le_two_or_omega_power_power`: characterizes the multiplicative principal
ordinals
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
by { rw one_principal_iff, exact zero_add _ }

theorem omega_add_principal : principal (+) omega.{u} :=
@add_lt_omega

theorem mul_omega_add_principal (o : ordinal.{u}) : principal (+) (o * omega.{u}) :=
begin
  cases eq_or_ne o 0 with ho ho,
  { rw [ho, zero_mul],
    exact zero_principal },
  intros a b hao hbo,
  cases lt_mul_omega hao with m hm,
  cases lt_mul_omega hbo with n hn,
  apply lt_of_le_of_lt (add_le_add (le_of_lt hm) (le_of_lt hn)),
  rw [←mul_add, mul_lt_mul_iff_left (ordinal.pos_iff_ne_zero.2 ho), lt_omega],
  exact ⟨m + n, (nat.cast_add m n).symm⟩
end

theorem mul_omega_le_add_principal {a o : ordinal.{u}} (hao : a < o) (ho : principal (+) o) :
  a * omega.{u} ≤ o :=
begin
  convert nfp_le_of_principal hao ho,
  exact mul_omega_nfp_add_self a
end

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
    cases lt_or_eq_of_le ho₁ with ho₁ ho₁,
    { rw lt_one_iff_zero at ho₁,
      rw ho₁ at hao,
      exact (ordinal.not_lt_zero a hao).elim },
    rw [ho₁, lt_one_iff_zero] at hao,
    rw hao,
    exact zero_add o },
  have : a + b < a + o := (add_is_normal a).strict_mono hbo,
  rwa h a hao at this
end

theorem add_principal_iff_zero_or_omega_pow (o : ordinal.{u}) :
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
  rw ←mul_one (1 : ordinal),
  exact mul_le_mul ha hb
end

theorem le_two_mul_principal {o : ordinal} (ho : o ≤ 2) : principal (*) o :=
begin
  cases lt_or_eq_of_le ho with ho ho,
  { cases lt_or_eq_of_le (le_one_iff_lt_two.2 ho) with ho ho,
    { rw lt_one_iff_zero.1 ho,
      exact zero_principal },
    rw ho,
    exact one_mul_principal },
  rw ho,
  exact two_mul_principal
end

theorem omega_mul_principal : principal (*) omega.{u} :=
@mul_lt_omega

theorem power_omega_mul_principal (o : ordinal.{u}) : principal (*) (o ^ omega.{u}) :=
begin
  cases le_or_gt o 1 with ho ho,
  { cases lt_or_eq_of_le ho with ho ho,
    { rw lt_one_iff_zero at ho,
      rw [ho, ordinal.zero_power omega_ne_zero],
      exact zero_principal },
    rw [ho, one_power],
    exact one_mul_principal },
  intros a b hao hbo,
  cases lt_power_omega hao with m hm,
  cases lt_power_omega hbo with n hn,
  apply lt_of_le_of_lt (mul_le_mul (le_of_lt hm) (le_of_lt hn)),
  rw [←power_add, power_lt_power_iff_right ho, lt_omega],
  exact ⟨m + n, (nat.cast_add m n).symm⟩
end

-- Move to ordinal_arithmetic?
theorem power_omega_nfp_mul {a b : ordinal.{u}} (hb : 0 < b) (hba : b ≤ a ^ omega.{u}) :
  a ^ omega.{u} = nfp ((*) a) b :=
begin
  sorry
end

-- Move to ordinal_arithmetic?
theorem nfp_mul_zero (a : ordinal) : nfp ((*) 0) a = a :=
begin
  unfold nfp,
  refine le_antisymm _ (le_sup (λ n, ((*) 0)^[n] a) 0),
  rw sup_le,
  intro n,
  induction n with n hn, { refl },
  rw function.iterate_succ',
  change 0 * _ ≤ a,
  rw zero_mul,
  exact ordinal.zero_le a
end

-- Move to ordinal_arithmetic?
theorem power_omega_nfp_mul_self (a : ordinal.{u}) : a ^ omega.{u} = nfp ((*) a) a :=
begin
  cases eq_or_ne a 0 with ha ha,
  { rw [ha, zero_power omega_ne_zero],
    exact (nfp_mul_zero 0).symm },
  rw ←ordinal.pos_iff_ne_zero at ha,
  exact power_omega_nfp_mul ha (le_power_self_left a one_le_omega)
end

-- Move to ordinal_arithmetic?
theorem power_omega_nfp_mul_one {a : ordinal.{u}} (ha : 0 < a) : a ^ omega.{u} = nfp ((*) a) 1 :=
begin
  apply power_omega_nfp_mul zero_lt_one,
  rw one_le_iff_pos,
  exact ordinal.power_pos _ ha
end

theorem power_omega_le_mul_principal {a o : ordinal.{u}} (hao : a < o) (ho : principal (*) o) :
  a ^ omega.{u} ≤ o :=
begin
  convert nfp_le_of_principal hao ho,
  exact power_omega_nfp_mul_self a
end

theorem omega_power_power_is_normal : is_normal (λ a : ordinal.{u}, omega.{u} ^ omega.{u} ^ a) :=
by apply is_normal.trans; exact power_is_normal (one_lt_omega)

theorem omega_power_power_mul_principal (o : ordinal.{u}) :
  principal (*) (omega.{u} ^ omega.{u} ^ o) :=
begin
  apply o.limit_rec_on,
  { rw [power_zero, power_one],
    exact omega_mul_principal },
  { intros a ha,
    rw [power_succ, power_mul],
    exact power_omega_mul_principal _ },
  intros a ha h b c hba hca,
  have : bsup.{u u} a (λ d hd, omega.{u} ^ omega.{u} ^ d) = omega.{u} ^ omega.{u} ^ a :=
    is_normal.bsup_eq.{u u} omega_power_power_is_normal ha,
  rw [←this, lt_bsup] at hba,
  rw [←this, lt_bsup] at hca,
  rcases hba with ⟨d, hd, hbd⟩,
  rcases hca with ⟨e, he, hce⟩,
  apply lt_of_le_of_lt (mul_le_mul (le_of_lt hbd) (le_of_lt hce)),
  rw [←power_add, power_lt_power_iff_right one_lt_omega],
  apply omega_power_add_principal;
  rwa power_lt_power_iff_right one_lt_omega
end

theorem mul_principal_is_limit {o : ordinal.{u}} (ho₂ : 2 < o) (ho : principal (*) o) :
  o.is_limit :=
begin
  refine ⟨λ ho₀, _, λ a hao, _⟩,
  { rw ho₀ at ho₂,
    exact ordinal.not_lt_zero _ ho₂ },
  cases eq_or_ne a 0 with ha ha,
  { rw [ha, succ_zero],
    exact lt_trans (lt_succ_self 1) ho₂ },
  refine @lt_of_le_of_lt _ _ _ (a + a) _ _ _,
  { rw succ_eq_add_one,
    apply add_le_add_left,
    rwa one_le_iff_ne_zero },
  rw ←mul_two a,
  exact ho a 2 hao ho₂
end

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
  cases eq_or_ne a 0 with ha ha,
  { rwa [ha, zero_mul] at * },
  rw ←ordinal.pos_iff_ne_zero at ha,
  rw ←h a ha hao,
  exact (mul_is_normal ha).strict_mono hbo
end

theorem the_big'' {o : ordinal.{u}} (ho : principal (*) o) (ho₂ : 2 < o) :
  ∃ a : ordinal.{u}, o = omega.{u} ^ a :=
begin
  sorry
end

theorem the_big' {o : ordinal.{u}} (ho : principal (*) o) (ho₂ : 2 < o) :
  omega.{u} ^ (log omega.{u} o) = o :=
begin
  cases the_big'' ho ho₂ with a ha,
  rw ha,
  rw log_power
end

theorem the_big {o : ordinal.{u}} (ho : principal (*) o) (ho₂ : 2 < o) :
  o < omega.{u} ^ omega.{u} ^ (log omega.{u} (log omega.{u} o)).succ :=
begin
  have : log omega.{u} o < omega.{u} ^ (log omega.{u} (log omega.{u} o)).succ := begin
  apply lt_power_succ_log one_lt_omega,
  end,
  rw ← power_lt_power_iff_right one_lt_omega at this,
  rwa the_big' ho ho₂ at this,
end

theorem mul_principal_eq_omega_power_power {o : ordinal.{u}} (ho : principal (*) o) (ho₂ : 2 < o) :
  o = omega.{u} ^ omega.{u} ^ (log omega.{u} (log omega.{u} o)) :=
begin
  apply le_antisymm,
  { by_contra' h,
    have := power_omega_le_mul_principal h ho,
    rw [←power_mul, ←power_succ] at this,
    exact not_le_of_lt (the_big ho ho₂) this },
  have : omega.{u} ^ (log omega.{u} (log omega.{u} o)) ≤ log omega.{u} o := begin
    apply power_log_le,
    sorry,
  end,
  rw ←power_le_power_iff_right one_lt_omega at this,
  apply this.trans,
  apply power_log_le,
  sorry
end

theorem mul_principal_iff_le_two_or_omega_power_power (o : ordinal.{u}) :
  principal (*) o ↔ o ≤ 2 ∨ ∃ a : ordinal.{u}, o = omega.{u} ^ omega.{u} ^ a :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { rw or_iff_not_imp_left,
    exact λ ho, ⟨_, mul_principal_eq_omega_power_power h (lt_of_not_ge ho)⟩ },
  cases h with ho ho,
  { exact le_two_mul_principal ho },
  cases ho with a ha,
  rw ha,
  exact omega_power_power_mul_principal _
end

end ordinal
