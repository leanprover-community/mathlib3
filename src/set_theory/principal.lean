/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import set_theory.ordinal_arithmetic

/-!
### Principal ordinals

We define principal or indecomposable ordinals, and we prove the standard properties about them.

### Main definitions and results
* `principal`: A principal or indecomposable ordinal under some binary operation. We include 0 and
any other typically excluded edge cases for simplicity.
* `principal_add_iff_zero_or_omega_power`: the characterization theorem for additive principal
ordinals.

### Todo
* Prove the characterization of multiplicative principal ordinals.
* Refactor any related theorems from `ordinal_arithmetic` into this file.
-/

universe u

namespace ordinal
local infixr ^ := @pow ordinal ordinal ordinal.has_pow

/-! ### Principal ordinals -/

/-- An ordinal `o` is said to be principal or indecomposable under an operation when the set of
ordinals less than it is closed under that operation. In standard mathematical usage, this term is
almost exclusively used for additive and multiplicative principal ordinals.

For simplicity, we break usual convention and regard 0 as principal. -/
def principal (op : ordinal → ordinal → ordinal) (o : ordinal) : Prop :=
∀ ⦃a b⦄, a < o → b < o → op a b < o

theorem principal_zero {op : ordinal → ordinal → ordinal} : principal op 0 :=
λ a _ h, (ordinal.not_lt_zero a h).elim

theorem principal_one_iff {op : ordinal → ordinal → ordinal} :
  principal op 1 ↔ op 0 0 = 0 :=
begin
  refine ⟨λ h, _, λ h a b ha hb, _⟩,
  { rwa ←lt_one_iff_zero,
    exact h zero_lt_one zero_lt_one },
  { rwa [lt_one_iff_zero, ha, hb] at * }
end

theorem iterate_lt_of_principal {op : ordinal → ordinal → ordinal}
  {a o : ordinal} (hao : a < o) (ho : principal op o) (n : ℕ) : (op a)^[n] a < o :=
begin
  induction n with n hn,
  { rwa function.iterate_zero },
  { have := ho hao hn,
    rwa function.iterate_succ' }
end

theorem op_eq_self_of_principal {op : ordinal → ordinal → ordinal} {a o : ordinal.{u}}
  (hao : a < o) (H : is_normal (op a)) (ho : principal op o) (ho' : is_limit o) : op a o = o :=
begin
  refine le_antisymm _ (H.le_self _),
  rw [←is_normal.bsup_eq.{u u} H ho', bsup_le],
  exact λ b hbo, le_of_lt (ho hao hbo)
end

theorem nfp_le_of_principal {op : ordinal → ordinal → ordinal}
  {a o : ordinal} (hao : a < o) (ho : principal op o) : nfp (op a) a ≤ o :=
nfp_le.2 $ λ n, le_of_lt (iterate_lt_of_principal hao ho n)

/-! #### Additive principal ordinals -/

theorem principal_add_one : principal (+) 1 :=
principal_one_iff.2 $ zero_add 0

theorem principal_add_of_le_one {o : ordinal} (ho : o ≤ 1) : principal (+) o :=
begin
  rcases le_one_iff.1 ho with rfl | rfl,
  { exact principal_zero },
  { exact principal_add_one }
end

theorem principal_add_is_limit {o : ordinal} (ho₁ : 1 < o) (ho : principal (+) o) :
  o.is_limit :=
begin
  refine ⟨λ ho₀, _, λ a hao, _⟩,
  { rw ho₀ at ho₁,
    exact not_lt_of_gt ordinal.zero_lt_one ho₁ },
  { cases eq_or_ne a 0 with ha ha,
    { rw [ha, succ_zero],
      exact ho₁ },
    { refine lt_of_le_of_lt _ (ho hao hao),
      rwa [succ_eq_add_one, add_le_add_iff_left, one_le_iff_ne_zero] } }
end

theorem principal_add_iff_add_left_eq_self {o : ordinal} :
  principal (+) o ↔ ∀ a < o, a + o = o :=
begin
  refine ⟨λ ho a hao, _, λ h a b hao hbo, _⟩,
  { cases lt_or_le 1 o with ho₁ ho₁,
    { exact op_eq_self_of_principal hao (add_is_normal a) ho (principal_add_is_limit ho₁ ho) },
    { rcases le_one_iff.1 ho₁ with rfl | rfl,
      { exact (ordinal.not_lt_zero a hao).elim },
      { rw lt_one_iff_zero at hao,
        rw [hao, zero_add] }}},
  { rw ←h a hao,
    exact (add_is_normal a).strict_mono hbo }
end

theorem add_omega {a : ordinal} (h : a < omega) : a + omega = omega :=
begin
  rcases lt_omega.1 h with ⟨n, rfl⟩,
  clear h, induction n with n IH,
  { rw [nat.cast_zero, zero_add] },
  { rwa [nat.cast_succ, add_assoc, one_add_of_omega_le (le_refl _)] }
end

theorem principal_add_omega : principal (+) omega :=
principal_add_iff_add_left_eq_self.2 (λ a, add_omega)

theorem add_omega_opow {a b : ordinal} (h : a < omega ^ b) : a + omega ^ b = omega ^ b :=
begin
  refine le_antisymm _ (le_add_left _ _),
  revert h, refine limit_rec_on b (λ h, _) (λ b _ h, _) (λ b l IH h, _),
  { rw [opow_zero, ← succ_zero, lt_succ, ordinal.le_zero] at h,
    rw [h, zero_add] },
  { rw opow_succ at h,
    rcases (lt_mul_of_limit omega_is_limit).1 h with ⟨x, xo, ax⟩,
    refine le_trans (add_le_add_right (le_of_lt ax) _) _,
    rw [opow_succ, ← mul_add, add_omega xo] },
  { rcases (lt_opow_of_limit omega_ne_zero l).1 h with ⟨x, xb, ax⟩,
    exact (((add_is_normal a).trans (opow_is_normal one_lt_omega)).limit_le l).2 (λ y yb,
      (add_le_add_left (opow_le_opow_right omega_pos (le_max_right _ _)) _).trans
      (le_trans (IH _ (max_lt xb yb) (ax.trans_le $ opow_le_opow_right omega_pos (le_max_left _ _)))
      (opow_le_opow_right omega_pos $ le_of_lt $ max_lt xb yb))) }
end

theorem principal_add_omega_opow (o : ordinal) : principal (+) (omega ^ o) :=
principal_add_iff_add_left_eq_self.2 (λ a, add_omega_opow)

/-- The main characterization theorem for additive principal ordinals. -/
theorem principal_add_iff_zero_or_omega_power {o : ordinal} :
  principal (+) o ↔ o = 0 ∨ ∃ a : ordinal, o = omega ^ a :=
begin
  rcases eq_or_ne o 0 with rfl | ho,
  { simp only [principal_zero, or.inl] },
  { rw [principal_add_iff_add_left_eq_self],
    simp only [ho, false_or],
    refine ⟨λ H, ⟨_, ((lt_or_eq_of_le (opow_log_le _ (ordinal.pos_iff_ne_zero.2 ho)))
        .resolve_left $ λ h, _).symm⟩, λ ⟨b, e⟩, e.symm ▸ λ a, add_omega_opow⟩,
    have := H _ h,
    have := lt_opow_succ_log one_lt_omega o,
    rw [opow_succ, lt_mul_of_limit omega_is_limit] at this,
    rcases this with ⟨a, ao, h'⟩,
    rcases lt_omega.1 ao with ⟨n, rfl⟩, clear ao,
    revert h', apply not_lt_of_le,
    suffices e : omega ^ log omega o * ↑n + o = o,
    { simpa only [e] using le_add_right (omega ^ log omega o * ↑n) o },
    induction n with n IH, {simp only [nat.cast_zero, mul_zero, zero_add]},
    simp only [nat.cast_succ, mul_add_one, add_assoc, this, IH] }
end

theorem add_absorp {a b c : ordinal} (h₁ : a < omega ^ b) (h₂ : omega ^ b ≤ c) : a + c = c :=
by rw [← ordinal.add_sub_cancel_of_le h₂, ← add_assoc, add_omega_opow h₁]

theorem opow_principal_add_is_principal_add {a} (ha : principal (+) a) (b : ordinal) :
  principal (+) (a ^ b) :=
begin
  rcases principal_add_iff_zero_or_omega_power.1 ha with rfl | ⟨c, rfl⟩,
  { rcases eq_or_ne b 0 with rfl | hb,
    { rw opow_zero, exact principal_add_one },
    { rw zero_opow hb, exact ha } },
  { rw ←opow_mul, exact principal_add_omega_opow _ }
end

theorem mul_principal_add_is_principal_add (a : ordinal.{u}) {b : ordinal.{u}} (hb₁ : 1 < b)
  (hb : principal (+) b) : principal (+) (a * b) :=
begin
  rcases eq_zero_or_pos a with rfl | ha,
  { rw zero_mul,
    exact principal_zero },
  { intros c d hc hd,
    rw [←is_normal.bsup_eq.{u u} (mul_is_normal ha) (principal_add_is_limit hb₁ hb), lt_bsup] at *,
    rcases hc with ⟨x, hx, hx'⟩,
    rcases hd with ⟨y, hy, hy'⟩,
    use [x + y, hb hx hy],
    rw mul_add,
    exact add_lt_add hx' hy' }
end

end ordinal
