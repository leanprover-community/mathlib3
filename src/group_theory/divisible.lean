/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import group_theory.subgroup.pointwise
import group_theory.quotient_group
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
* `add_comm_group.divisible_quotient : Quotient group of divisible group is divisible.
* `add_comm_group.divisible_of_surj` : if `A` is divisible and `A →+ B` is surjective, then `B` is
  divisible.
TODO: Show that divisibility implies injectivity in the category of `AddCommGroup`.
-/


namespace add_comm_group

open_locale pointwise

variables (A : Type*) [add_comm_group A]

/--
A divisible group `A` is an abelian group such that `nA = A` for all `n ≠ 0`.
-/
class divisible :=
(div_int : A → ℤ → A)
(div_zero : ∀ a, div_int a 0 = 0)
(div_cancel : ∀ {n : ℤ} (a : A), n ≠ 0 → n • div_int a n = a)
-- (div : ∀ (n : ℤ), n ≠ 0 → function.surjective ((•) n : A → A))

local infix ` /ℤ ` :50 := divisible.div_int

lemma smul_surj_of_divisible [divisible A] {n : ℤ} (hn : n ≠ 0) :
  function.surjective ((•) n : A → A) :=
λ a, ⟨a /ℤ n, divisible.div_cancel a hn⟩

noncomputable instance divisible_of_smul_surj (surj : ∀ {n : ℤ}, n ≠ 0 → function.surjective ((•) n : A → A)) :
  divisible A :=
{ div_int := λ a n, dite (n = 0) (λ _, 0) (λ h, (surj h a).some),
  div_zero := λ a, dif_pos rfl,
  div_cancel := λ n a h, begin
    rw [dif_neg h, (surj h a).some_spec],
  end }

lemma smul_top_eq_top_of_divisible [divisible A] {n : ℤ} (hn : n ≠ 0) :
  n • (⊤ : add_subgroup A) = ⊤ :=
(add_subgroup.eq_top_iff' (n • ⊤)).mpr $ λ x, ⟨x /ℤ n, trivial, divisible.div_cancel x hn⟩

noncomputable instance divisible_of_smul_top_eq_top (H : ∀ {n : ℤ}, n ≠ 0 → n • (⊤ : add_subgroup A) = ⊤) :
  divisible A:=
add_comm_group.divisible_of_smul_surj _ $ λ n hn a, begin
  rcases (show a ∈ n • (⊤ : add_subgroup A), by simp only [H hn]) with ⟨a, _, rfl⟩,
  exact ⟨_, rfl⟩,
end

/-- ℚ is a divisible group. -/
instance divisible_rat : divisible ℚ :=
{ div_int := λ q n, q / n,
  div_zero := λ q, by norm_num,
  div_cancel := λ n q hn, by rw [zsmul_eq_mul, mul_div_cancel']; exact_mod_cast hn, }

/-- ℝ is a divisible group. -/
noncomputable instance divisible_real : divisible ℝ :=
{ div_int := λ q n, q / n,
  div_zero := λ q, by norm_num,
  div_cancel := λ n q hn, by rw [zsmul_eq_mul, mul_div_cancel']; exact_mod_cast hn, }

noncomputable instance divisble_complex : divisible ℂ :=
{ div_int := λ q n, q / n,
  div_zero := λ q, by norm_num,
  div_cancel := λ n q hn, by rw [zsmul_eq_mul, mul_div_cancel']; exact_mod_cast hn, }

section pi

variables {ι : Type*} (B : ι → Type*) [Π i, add_comm_group (B i)] [Π i, divisible (B i)]

/-- Any product of divisible group is divisible.-/
instance divisible_pi : divisible (Π i, B i) :=
{ div_int := λ x n i, (x i) /ℤ n,
  div_zero := λ x, funext $ λ i, divisible.div_zero _,
  div_cancel := λ n x hn, funext $ λ i, divisible.div_cancel (x i) hn }

end pi

section quotient

variables {B : add_subgroup A} [divisible A]

noncomputable instance divisible_quotient : divisible (A ⧸ B) :=
add_comm_group.divisible_of_smul_surj _ $ λ n hn x, quotient.induction_on' x $ λ a,
  ⟨quotient.mk' (a /ℤ n), (congr_arg _ $ divisible.div_cancel a hn : quotient.mk' _ = _)⟩

end quotient

section hom

variables {A} [divisible A] {B : Type*} [add_comm_group B] (f : A →+ B)

noncomputable instance divisible_of_surj (hf : function.surjective f) : divisible B :=
add_comm_group.divisible_of_smul_surj _ $
  λ n hn x, ⟨f $ (hf x).some /ℤ n, by rw [←f.map_zsmul ((hf x).some /ℤ n) n,
    divisible.div_cancel _ hn, (hf x).some_spec]⟩

end hom

end add_comm_group
