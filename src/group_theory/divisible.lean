/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import group_theory.subgroup.pointwise
import data.real.basic
import data.complex.basic

/-!
# Divisible Group

An abelian group `A` is said to be divisible iff for all `n ≠ 0` `y ∈ A`, there is an `x ∈ A`
such that `n • x = y`.

## Main results

* `add_comm_group.divisible_iff_smul_top_eq_top` : `A` is divisible iff `n • A = A` for all `n ≠ 0`.
* `add_comm_group.divisble_rat` : `ℚ` is a divisible group.
* `add_comm_group.divisible_real` : `ℝ` is a divisible group.
* `add_comm_group.divisible_complex` : `ℂ` is a divisible group.
* `add_comm_group.divisible_pi` : Any product of divisble group is divisible.

TODO: Show that divisibility implies injectivity in the category of `AddCommGroup`.
-/


namespace add_comm_group

open_locale pointwise

variables (A : Type*) [add_comm_group A]

/--
A divisible group `A` is an abelian group such that `nA = A` for all `n ≠ 0`.
-/
class divisible : Prop :=
(div : ∀ (n : ℤ), n ≠ 0 → function.surjective ((•) n : A → A))


lemma divisible_iff_smul_top_eq_top :
  divisible A ↔ ∀ (n : ℤ), n ≠ 0 → n • (⊤ : add_subgroup A) = ⊤ :=
{ mp := λ ⟨d⟩ n hn,  (add_subgroup.eq_top_iff' (n • ⊤)).mpr $
     λ x, ⟨(d n hn x).some, trivial, (d n hn x).some_spec⟩,
  mpr := λ h, ⟨λ n hn x, begin
    rcases show x ∈ n • (⊤ : add_subgroup A), by rw h n hn; trivial with ⟨x', _, hx⟩,
    exact ⟨x', hx⟩,
  end⟩ }

/-- ℚ is a divisible group. -/
instance divisible_rat : divisible ℚ :=
⟨λ n hn x, ⟨x/n, by rw [zsmul_eq_mul, mul_div_cancel']; exact_mod_cast hn⟩⟩

/-- ℝ is a divisible group. -/
instance divisible_real : divisible ℝ :=
⟨λ n hn x, ⟨x/n, by rw [zsmul_eq_mul, mul_div_cancel']; exact_mod_cast hn⟩⟩

instance divisble_complex : divisible ℂ :=
⟨λ n hn x, ⟨x/n, by rw [zsmul_eq_mul, mul_div_cancel']; exact_mod_cast hn⟩⟩

section pi

variables {ι : Type*} (B : ι → Type*) [Π i, add_comm_group (B i)] [Π i, divisible (B i)]

/-- Any product of divisible group is divisible.-/
instance divisible_pi : divisible (Π i, B i) :=
⟨λ n hn x, ⟨λ i, (divisible.div n hn (x i)).some,
  funext $ λ i, (divisible.div n hn (x i)).some_spec⟩⟩

end pi

end add_comm_group
