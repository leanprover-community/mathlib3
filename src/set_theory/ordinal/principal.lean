/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import set_theory.ordinal.fixed_point

/-!
### Principal ordinals

We define principal or indecomposable ordinals, and we prove the standard properties about them.

### Main definitions and results
* `principal`: A principal or indecomposable ordinal under some binary operation. We include 0 and
  any other typically excluded edge cases for simplicity.
* `unbounded_principal`: Principal ordinals are unbounded.
* `principal_add_iff_zero_or_omega_opow`: The main characterization theorem for additive principal
  ordinals.
* `principal_mul_iff_le_two_or_omega_opow_opow`: The main characterization theorem for
  multiplicative principal ordinals.

### Todo
* Prove that exponential principal ordinals are 0, 1, 2, ω, or epsilon numbers, i.e. fixed points
  of `λ x, ω ^ x`.
-/

universe u

noncomputable theory

namespace ordinal
local infixr ^ := @pow ordinal ordinal ordinal.has_pow

/-! ### Principal ordinals -/

/-- An ordinal `o` is said to be principal or indecomposable under an operation when the set of
ordinals less than it is closed under that operation. In standard mathematical usage, this term is
almost exclusively used for additive and multiplicative principal ordinals.

For simplicity, we break usual convention and regard 0 as principal. -/
def principal (op : ordinal → ordinal → ordinal) (o : ordinal) : Prop :=
∀ ⦃a b⦄, a < o → b < o → op a b < o

theorem principal_iff_principal_swap {op : ordinal → ordinal → ordinal} {o : ordinal} :
  principal op o ↔ principal (function.swap op) o :=
by split; exact λ h a b ha hb, h hb ha

theorem principal_zero {op : ordinal → ordinal → ordinal} : principal op 0 :=
λ a _ h, (ordinal.not_lt_zero a h).elim

@[simp] theorem principal_one_iff {op : ordinal → ordinal → ordinal} :
  principal op 1 ↔ op 0 0 = 0 :=
begin
  refine ⟨λ h, _, λ h a b ha hb, _⟩,
  { rwa ←lt_one_iff_zero,
    exact h zero_lt_one zero_lt_one },
  { rwa [lt_one_iff_zero, ha, hb] at * }
end

theorem principal.iterate_lt {op : ordinal → ordinal → ordinal} {a o : ordinal} (hao : a < o)
  (ho : principal op o) (n : ℕ) : (op a)^[n] a < o :=
begin
  induction n with n hn,
  { rwa function.iterate_zero },
  { rw function.iterate_succ', exact ho hao hn }
end

theorem op_eq_self_of_principal {op : ordinal → ordinal → ordinal} {a o : ordinal.{u}}
  (hao : a < o) (H : is_normal (op a)) (ho : principal op o) (ho' : is_limit o) : op a o = o :=
begin
  refine le_antisymm _ (H.self_le _),
  rw [←is_normal.bsup_eq.{u u} H ho', bsup_le_iff],
  exact λ b hbo, (ho hao hbo).le
end

theorem nfp_le_of_principal {op : ordinal → ordinal → ordinal}
  {a o : ordinal} (hao : a < o) (ho : principal op o) : nfp (op a) a ≤ o :=
nfp_le $ λ n, (ho.iterate_lt hao n).le

/-! ### Principal ordinals are unbounded -/

/-- The least strict upper bound of `op` applied to all pairs of ordinals less than `o`. This is
essentially a two-argument version of `ordinal.blsub`. -/
def blsub₂ (op : ordinal → ordinal → ordinal) (o : ordinal) : ordinal :=
lsub (λ x : o.out.α × o.out.α, op (typein (<) x.1) (typein (<) x.2))

theorem lt_blsub₂ (op : ordinal → ordinal → ordinal) {o : ordinal} {a b : ordinal} (ha : a < o)
  (hb : b < o) : op a b < blsub₂ op o :=
begin
  convert lt_lsub _ (prod.mk (enum (<) a (by rwa type_lt)) (enum (<) b (by rwa type_lt))),
  simp only [typein_enum]
end

theorem principal_nfp_blsub₂ (op : ordinal → ordinal → ordinal) (o : ordinal) :
  principal op (nfp (blsub₂.{u u} op) o) :=
λ a b ha hb, begin
  rw lt_nfp at *,
  cases ha with m hm,
  cases hb with n hn,
  cases le_total ((blsub₂.{u u} op)^[m] o) ((blsub₂.{u u} op)^[n] o) with h h,
  { use n + 1,
    rw function.iterate_succ',
    exact lt_blsub₂ op (hm.trans_le h) hn },
  { use m + 1,
    rw function.iterate_succ',
    exact lt_blsub₂ op hm (hn.trans_le h) },
end

theorem unbounded_principal (op : ordinal → ordinal → ordinal) :
  set.unbounded (<) {o | principal op o} :=
λ o, ⟨_, principal_nfp_blsub₂ op o, (le_nfp _ o).not_lt⟩

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

theorem exists_lt_add_of_not_principal_add {a} (ha : ¬ principal (+) a) :
  ∃ (b c) (hb : b < a) (hc : c < a), b + c = a :=
begin
  unfold principal at ha,
  push_neg at ha,
  rcases ha with ⟨b, c, hb, hc, H⟩,
  refine ⟨b, _, hb, lt_of_le_of_ne (sub_le_self a b) (λ hab, _),
    ordinal.add_sub_cancel_of_le hb.le⟩,
  rw [←sub_le, hab] at H,
  exact H.not_lt hc
end

theorem principal_add_iff_add_lt_ne_self {a} :
  principal (+) a ↔ ∀ ⦃b c⦄, b < a → c < a → b + c ≠ a :=
⟨λ ha b c hb hc, (ha hb hc).ne, λ H, begin
  by_contra' ha,
  rcases exists_lt_add_of_not_principal_add ha with ⟨b, c, hb, hc, rfl⟩,
  exact (H hb hc).irrefl
end⟩

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
theorem principal_add_iff_zero_or_omega_opow {o : ordinal} :
  principal (+) o ↔ o = 0 ∨ ∃ a, o = omega ^ a :=
begin
  rcases eq_or_ne o 0 with rfl | ho,
  { simp only [principal_zero, or.inl] },
  { rw [principal_add_iff_add_left_eq_self],
    simp only [ho, false_or],
    refine ⟨λ H, ⟨_, ((lt_or_eq_of_le (opow_log_le_self _ (ordinal.pos_iff_ne_zero.2 ho)))
        .resolve_left $ λ h, _).symm⟩, λ ⟨b, e⟩, e.symm ▸ λ a, add_omega_opow⟩,
    have := H _ h,
    have := lt_opow_succ_log_self one_lt_omega o,
    rw [opow_succ, lt_mul_of_limit omega_is_limit] at this,
    rcases this with ⟨a, ao, h'⟩,
    rcases lt_omega.1 ao with ⟨n, rfl⟩, clear ao,
    revert h', apply not_lt_of_le,
    suffices e : omega ^ log omega o * ↑n + o = o,
    { simpa only [e] using le_add_right (omega ^ log omega o * ↑n) o },
    induction n with n IH, {simp only [nat.cast_zero, mul_zero, zero_add]},
    simp only [nat.cast_succ, mul_add_one, add_assoc, this, IH] }
end

theorem opow_principal_add_of_principal_add {a} (ha : principal (+) a) (b : ordinal) :
  principal (+) (a ^ b) :=
begin
  rcases principal_add_iff_zero_or_omega_opow.1 ha with rfl | ⟨c, rfl⟩,
  { rcases eq_or_ne b 0 with rfl | hb,
    { rw opow_zero, exact principal_add_one },
    { rwa zero_opow hb } },
  { rw ←opow_mul, exact principal_add_omega_opow _ }
end

theorem add_absorp {a b c : ordinal} (h₁ : a < omega ^ b) (h₂ : omega ^ b ≤ c) : a + c = c :=
by rw [← ordinal.add_sub_cancel_of_le h₂, ← add_assoc, add_omega_opow h₁]

theorem mul_principal_add_is_principal_add (a : ordinal.{u}) {b : ordinal.{u}} (hb₁ : b ≠ 1)
  (hb : principal (+) b) : principal (+) (a * b) :=
begin
  rcases eq_zero_or_pos a with rfl | ha,
  { rw zero_mul,
    exact principal_zero },
  { rcases eq_zero_or_pos b with rfl | hb₁',
    { rw mul_zero,
      exact principal_zero },
    { rw [← succ_le,succ_zero] at hb₁',
      intros c d hc hd,
      rw lt_mul_of_limit (principal_add_is_limit (lt_of_le_of_ne hb₁' hb₁.symm) hb) at *,
      { rcases hc with ⟨x, hx, hx'⟩,
        rcases hd with ⟨y, hy, hy'⟩,
        use [x + y, hb hx hy],
        rw mul_add,
        exact add_lt_add hx' hy' },
      assumption' } }
end

/-! #### Multiplicative principal ordinals -/

theorem principal_mul_one : principal (*) 1 :=
by { rw principal_one_iff, exact zero_mul _ }

theorem principal_mul_two : principal (*) 2 :=
λ a b ha hb, begin
  have h₂ : (1 : ordinal).succ = 2 := rfl,
  rw [←h₂, ordinal.lt_succ] at *,
  convert mul_le_mul' ha hb,
  exact (mul_one 1).symm
end

theorem principal_mul_of_le_two {o : ordinal} (ho : o ≤ 2) : principal (*) o :=
begin
  rcases lt_or_eq_of_le ho with ho | rfl,
  { have h₂ : (1 : ordinal).succ = 2 := rfl,
    rw [←h₂, ordinal.lt_succ] at ho,
    rcases lt_or_eq_of_le ho with ho | rfl,
    { rw lt_one_iff_zero.1 ho,
      exact principal_zero },
    { exact principal_mul_one } },
  { exact principal_mul_two }
end

theorem principal_add_of_principal_mul {o : ordinal} (ho : principal (*) o) (ho₂ : o ≠ 2) :
  principal (+) o :=
begin
  cases lt_or_gt_of_ne ho₂ with ho₁ ho₂,
  { change o < succ 1 at ho₁,
    rw lt_succ at ho₁,
    exact principal_add_of_le_one ho₁ },
  { refine λ a b hao hbo, lt_of_le_of_lt _ (ho (max_lt hao hbo) ho₂),
    rw mul_two,
    exact add_le_add (le_max_left a b) (le_max_right a b) }
end

theorem principal_mul_is_limit {o : ordinal.{u}} (ho₂ : 2 < o) (ho : principal (*) o) :
  o.is_limit :=
principal_add_is_limit
  ((ordinal.lt_succ_self 1).trans ho₂)
  (principal_add_of_principal_mul ho (ne_of_gt ho₂))

theorem principal_mul_iff_mul_left_eq {o : ordinal} :
  principal (*) o ↔ ∀ a, 0 < a → a < o → a * o = o :=
begin
  refine ⟨λ h a ha₀ hao, _, λ h a b hao hbo, _⟩,
  { cases le_or_gt o 2 with ho ho,
    { convert one_mul o,
      apply le_antisymm,
      { have : a < succ 1 := hao.trans_le ho,
        rwa lt_succ at this },
      { rwa [←succ_le, succ_zero] at ha₀ } },
    { exact op_eq_self_of_principal hao (mul_is_normal ha₀) h (principal_mul_is_limit ho h) } },
  { rcases eq_or_ne a 0 with rfl | ha, { rwa zero_mul },
    rw ←ordinal.pos_iff_ne_zero at ha,
    rw ←h a ha hao,
    exact (mul_is_normal ha).strict_mono hbo }
end

theorem principal_mul_omega : principal (*) omega :=
λ a b ha hb, match a, b, lt_omega.1 ha, lt_omega.1 hb with
| _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ := by { rw [← nat_cast_mul], apply nat_lt_omega }
end

theorem mul_omega {a : ordinal} (a0 : 0 < a) (ha : a < omega) : a * omega = omega :=
principal_mul_iff_mul_left_eq.1 (principal_mul_omega) a a0 ha

theorem mul_lt_omega_opow {a b c : ordinal}
  (c0 : 0 < c) (ha : a < omega ^ c) (hb : b < omega) : a * b < omega ^ c :=
begin
  rcases zero_or_succ_or_limit c with rfl|⟨c,rfl⟩|l,
  { exact (lt_irrefl _).elim c0 },
  { rw opow_succ at ha,
    rcases ((mul_is_normal $ opow_pos _ omega_pos).limit_lt
      omega_is_limit).1 ha with ⟨n, hn, an⟩,
    apply (mul_le_mul_right' (le_of_lt an) _).trans_lt,
    rw [opow_succ, mul_assoc, mul_lt_mul_iff_left (opow_pos _ omega_pos)],
    exact principal_mul_omega hn hb },
  { rcases ((opow_is_normal one_lt_omega).limit_lt l).1 ha with ⟨x, hx, ax⟩,
    refine (mul_le_mul' (le_of_lt ax) (le_of_lt hb)).trans_lt _,
    rw [← opow_succ, opow_lt_opow_iff_right one_lt_omega],
    exact l.2 _ hx }
end

theorem mul_omega_opow_opow {a b : ordinal} (a0 : 0 < a) (h : a < omega ^ omega ^ b) :
  a * omega ^ omega ^ b = omega ^ omega ^ b :=
begin
  by_cases b0 : b = 0, {rw [b0, opow_zero, opow_one] at h ⊢, exact mul_omega a0 h},
  refine le_antisymm _
    (by simpa only [one_mul] using mul_le_mul_right' (one_le_iff_pos.2 a0) (omega ^ omega ^ b)),
  rcases (lt_opow_of_limit omega_ne_zero (opow_is_limit_left omega_is_limit b0)).1 h
    with ⟨x, xb, ax⟩,
  apply (mul_le_mul_right' (le_of_lt ax) _).trans,
  rw [← opow_add, add_omega_opow xb]
end

theorem principal_mul_omega_opow_opow (o : ordinal) : principal (*) (omega ^ omega ^ o) :=
principal_mul_iff_mul_left_eq.2 (λ a, mul_omega_opow_opow)

theorem principal_add_of_principal_mul_opow {o b : ordinal} (hb : 1 < b)
  (ho : principal (*) (b ^ o)) : principal (+) o :=
λ x y hx hy, begin
  have := ho ((opow_lt_opow_iff_right hb).2 hx) ((opow_lt_opow_iff_right hb).2 hy),
  rwa [←opow_add, opow_lt_opow_iff_right hb] at this
end

/-- The main characterization theorem for multiplicative principal ordinals. -/
theorem principal_mul_iff_le_two_or_omega_opow_opow {o : ordinal} :
  principal (*) o ↔ o ≤ 2 ∨ ∃ a, o = omega ^ omega ^ a :=
begin
  refine ⟨λ ho, _, _⟩,
  { cases le_or_lt o 2 with ho₂ ho₂,
    { exact or.inl ho₂ },
    rcases principal_add_iff_zero_or_omega_opow.1 (principal_add_of_principal_mul ho ho₂.ne')
      with rfl | ⟨a, rfl⟩,
    { exact (ordinal.not_lt_zero 2 ho₂).elim },
    rcases principal_add_iff_zero_or_omega_opow.1
      (principal_add_of_principal_mul_opow one_lt_omega ho) with rfl | ⟨b, rfl⟩,
    { rw opow_zero at ho₂,
      exact ((lt_succ_self 1).not_le ho₂.le).elim },
    exact or.inr ⟨b, rfl⟩ },
  { rintro (ho₂ | ⟨a, rfl⟩),
    { exact principal_mul_of_le_two ho₂ },
    { exact principal_mul_omega_opow_opow a } }
end

theorem mul_omega_dvd {a : ordinal}
  (a0 : 0 < a) (ha : a < omega) : ∀ {b}, omega ∣ b → a * b = b
| _ ⟨b, rfl⟩ := by rw [← mul_assoc, mul_omega a0 ha]

theorem mul_eq_opow_log_succ {a b : ordinal.{u}} (ha : 0 < a) (hb : principal (*) b) (hb₂ : 2 < b) :
  a * b = b ^ (log b a).succ :=
begin
  apply le_antisymm,
  { have hbl := principal_mul_is_limit hb₂ hb,
    rw [←is_normal.bsup_eq.{u u} (mul_is_normal ha) hbl, bsup_le_iff],
    intros c hcb,
    have hb₁ : 1 < b := (lt_succ_self 1).trans hb₂,
    have hbo₀ : b ^ b.log a ≠ 0 := ordinal.pos_iff_ne_zero.1 (opow_pos _ (zero_lt_one.trans hb₁)),
    apply le_trans (mul_le_mul_right' (le_of_lt (lt_mul_succ_div a hbo₀)) c),
    rw [mul_assoc, opow_succ],
    refine mul_le_mul_left' (le_of_lt (hb (hbl.2 _ _) hcb)) _,
    rw [div_lt hbo₀, ←opow_succ],
    exact lt_opow_succ_log_self hb₁ _ },
  { rw opow_succ,
    exact mul_le_mul_right' (opow_log_le_self b ha) b }
end

/-! #### Exponential principal ordinals -/

theorem principal_opow_omega : principal (^) omega :=
λ a b ha hb, match a, b, lt_omega.1 ha, lt_omega.1 hb with
| _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ := by { simp_rw ←nat_cast_opow, apply nat_lt_omega }
end

theorem opow_omega {a : ordinal} (a1 : 1 < a) (h : a < omega) : a ^ omega = omega :=
le_antisymm
  ((opow_le_of_limit (one_le_iff_ne_zero.1 $ le_of_lt a1) omega_is_limit).2
    (λ b hb, (principal_opow_omega h hb).le))
  (right_le_opow _ a1)

end ordinal
