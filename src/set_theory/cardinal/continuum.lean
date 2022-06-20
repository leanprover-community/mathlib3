/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import set_theory.cardinal.ordinal

/-!
# Cardinality of continuum

In this file we define `cardinal.continuum` (notation: `𝔠`, localized in `cardinal`) to be `2 ^ ℵ₀`.
We also prove some `simp` lemmas about cardinal arithmetic involving `𝔠`.

## Notation

- `𝔠` : notation for `cardinal.continuum` in locale `cardinal`.
-/

universes u v

/-- Cardinality of continuum. -/
def cardinal.continuum : cardinal.{u} := 2 ^ cardinal.aleph_0.{u}

localized "notation `𝔠` := cardinal.continuum" in cardinal

open_locale cardinal

namespace cardinal

@[simp] lemma two_power_aleph_0 : 2 ^ aleph_0.{u} = continuum.{u} := rfl

@[simp] lemma lift_continuum : lift.{v} 𝔠 = 𝔠 :=
by rw [←two_power_aleph_0, lift_two_power, lift_aleph_0, two_power_aleph_0]

@[simp] lemma lift_le_continuum (c : cardinal.{v}) : lift.{u} c ≤ 𝔠 ↔ c ≤ 𝔠 :=
by rw [← lift_continuum, lift_le]

@[simp] lemma continuum_le_lift (c : cardinal.{v}) : 𝔠 ≤ lift.{u} c ↔ 𝔠 ≤ c :=
by rw [← lift_continuum, lift_le]

/-!
### Inequalities
-/

lemma aleph_0_lt_continuum : ℵ₀ < 𝔠 := cantor ℵ₀

lemma aleph_0_le_continuum : ℵ₀ ≤ 𝔠 := aleph_0_lt_continuum.le

lemma nat_lt_continuum (n : ℕ) : ↑n < 𝔠 := (nat_lt_aleph_0 n).trans aleph_0_lt_continuum

lemma mk_set_nat : #(set ℕ) = 𝔠 := by simp

lemma continuum_pos : 0 < 𝔠 := nat_lt_continuum 0

lemma continuum_ne_zero : 𝔠 ≠ 0 := continuum_pos.ne'

lemma aleph_one_le_continuum : aleph 1 ≤ 𝔠 :=
by { rw ←succ_aleph_0, exact order.succ_le_of_lt aleph_0_lt_continuum }

lemma _root_.set.not_countable_of_continuum_le_mk {α : Type*} (s : set α) (hs : 𝔠 ≤ #s) :
  ¬s.countable :=
by { rw [← mk_set_le_omega, not_le], exact omega_lt_continuum.trans_le hs }

/-!
### Addition
-/

@[simp] lemma aleph_0_add_continuum : ℵ₀ + 𝔠 = 𝔠 :=
add_eq_right aleph_0_le_continuum aleph_0_le_continuum

@[simp] lemma continuum_add_aleph_0 : 𝔠 + ℵ₀ = 𝔠 :=
(add_comm _ _).trans aleph_0_add_continuum

@[simp] lemma continuum_add_self : 𝔠 + 𝔠 = 𝔠 :=
add_eq_right aleph_0_le_continuum le_rfl

@[simp] lemma nat_add_continuum (n : ℕ) : ↑n + 𝔠 = 𝔠 :=
add_eq_right aleph_0_le_continuum (nat_lt_continuum n).le

@[simp] lemma continuum_add_nat (n : ℕ) : 𝔠 + n = 𝔠 :=
(add_comm _ _).trans (nat_add_continuum n)

/-!
### Multiplication
-/

@[simp] lemma continuum_mul_self : 𝔠 * 𝔠 = 𝔠 :=
mul_eq_left aleph_0_le_continuum le_rfl continuum_ne_zero

@[simp] lemma continuum_mul_aleph_0 : 𝔠 * ℵ₀ = 𝔠 :=
mul_eq_left aleph_0_le_continuum aleph_0_le_continuum aleph_0_ne_zero

@[simp] lemma aleph_0_mul_continuum : ℵ₀ * 𝔠 = 𝔠 :=
(mul_comm _ _).trans continuum_mul_aleph_0

@[simp] lemma nat_mul_continuum {n : ℕ} (hn : n ≠ 0) : ↑n * 𝔠 = 𝔠 :=
mul_eq_right aleph_0_le_continuum (nat_lt_continuum n).le (nat.cast_ne_zero.2 hn)

@[simp] lemma continuum_mul_nat {n : ℕ} (hn : n ≠ 0) : 𝔠 * n = 𝔠 :=
(mul_comm _ _).trans (nat_mul_continuum hn)

/-!
### Power
-/

@[simp] lemma aleph_0_power_aleph_0 : aleph_0.{u} ^ aleph_0.{u} = 𝔠 :=
power_self_eq le_rfl

@[simp] lemma nat_power_aleph_0 {n : ℕ} (hn : 2 ≤ n) : (n ^ aleph_0.{u} : cardinal.{u}) = 𝔠 :=
nat_power_eq le_rfl hn

@[simp] lemma continuum_power_aleph_0 : continuum.{u} ^ aleph_0.{u} = 𝔠 :=
by rw [←two_power_aleph_0, ←power_mul, mul_eq_left le_rfl le_rfl aleph_0_ne_zero]

end cardinal

open cardinal

/-- A typeclass saying that `cardinal.mk α = cardinal.continuum`. -/
class has_card_continuum (α : Type u) : Prop :=
(mk_eq_continuum [] : #α = 𝔠)

export has_card_continuum (mk_eq_continuum)
attribute [simp] mk_eq_continuum

instance _root_.set.univ.has_card_continuum {α} [has_card_continuum α] :
  has_card_continuum (set.univ : set α) :=
⟨mk_univ.trans (mk_eq_continuum _)⟩

/-- A typeclass saying that `cardinal.mk α ≤ cardinal.continuum`. -/
class has_card_le_continuum (α : Type u) : Prop :=
(mk_le_continuum [] : #α ≤ 𝔠)

export has_card_le_continuum (mk_le_continuum)

instance _root_.set.univ.has_card_le_continuum {α} [has_card_le_continuum α] :
  has_card_le_continuum (set.univ : set α) :=
⟨mk_univ.trans_le (mk_le_continuum _)⟩

@[priority 100] -- See Note [lower instance priority]
instance has_card_continuum.to_has_card_le_continuum (α : Type u) [has_card_continuum α] :
  has_card_le_continuum α :=
⟨(mk_eq_continuum α).le⟩

@[priority 100] -- See Note [lower instance priority]
instance encodable.to_has_card_le_continuum (α : Type u) [encodable α] :
  has_card_le_continuum α :=
⟨mk_le_omega.trans omega_le_continuum⟩

@[priority 100] -- See Note [lower instance priority]
instance fintype.to_has_card_le_continuum (α : Type u) [fintype α] :
  has_card_le_continuum α :=
by { haveI := fintype.to_encodable α, exact encodable.to_has_card_le_continuum α }

@[priority 100] -- See Note [lower instance priority]
instance has_card_continuum.to_infinite (α : Type u) [has_card_continuum α] : infinite α :=
by simp [infinite_iff, omega_le_continuum]

lemma nonempty_equiv_of_continuum (α : Type u) (β : Type v) [has_card_continuum α]
  [has_card_continuum β] : nonempty (α ≃ β) :=
lift_mk_eq'.1 $ by simp

lemma equiv.has_card_continuum {α : Type u} {β : Type v} [has_card_continuum β] (e : α ≃ β) :
  has_card_continuum α :=
⟨by rw [← lift_inj, lift_mk_eq'.2 ⟨e⟩, mk_eq_continuum, lift_continuum, lift_continuum]⟩

lemma equiv.has_card_continuum_congr {α : Type u} {β : Type v} (e : α ≃ β) :
  has_card_continuum α ↔ has_card_continuum β :=
⟨λ H, @equiv.has_card_continuum β α H e.symm, λ H, @equiv.has_card_continuum α β H e⟩

instance (α : Type u) (π : α → Type v) [denumerable α] [∀ a, nontrivial (π a)]
  [Π a, encodable (π a)] : has_card_continuum (Π a, π a) :=
⟨calc #(Π a, π a) = prod (λ a : α, #(π a)) : mk_pi _
              ... = 2 ^ lift.{v} (#α)      :
   prod_eq_two_power (λ i, two_le_iff.2 $ exists_pair_ne _) $ λ i, by simp
              ... = 𝔠                      : by simp⟩

instance pi.has_card_continuum' (α : Type u) (π : α → Type v) [denumerable α]
  [∀ a, nontrivial (π a)] [Π a, fintype (π a)] : has_card_continuum (Π a, π a) :=
by { haveI := λ a, fintype.to_encodable (π a), exact pi.has_card_continuum α π }

instance (α : Type u) [denumerable α] : has_card_continuum (set α) :=
pi.has_card_continuum _ _

instance prod.has_card_continuum_left (α : Type u) (β : Type v)
  [has_card_continuum α] [has_card_le_continuum β] [nonempty β] :
  has_card_continuum (α × β) :=
⟨begin
  rw [mk_prod, mk_eq_continuum, lift_continuum, mul_eq_left omega_le_continuum],
  { simp [mk_le_continuum] },
  { rw [ne.def, lift_eq_zero], exact mk_ne_zero β }
end⟩

instance prod.has_card_continuum_right (α : Type u) (β : Type v)
  [has_card_le_continuum α] [nonempty α] [has_card_continuum β] :
  has_card_continuum (α × β) :=
(equiv.prod_comm α β).has_card_continuum
