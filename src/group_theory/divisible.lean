/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import group_theory.subgroup.pointwise
import data.real.basic

/-!
# Divisible Group

An abelian group `A` is said to be divisible iff `nA = A` for all `n ≠ 0`.

## Main results

* `add_comm_group.divisbible_of_linear_solvable` : If in a group `A`, `n • x = y` is solveable
  whenever `n ≠ 0`, then `A` is divisible.
* `add_comm_group.divisble_rat` : `ℚ` is a divisible group.
* `add_comm_group.divisible_real` : `ℝ` is a divisible group.
* `add_comm_group.divisible_of_product_divisible` : Any product of divisble group is divisible.

TODO: Show that divisibility implies injectivity in the category of `AddCommGroup`.
-/


namespace add_comm_group

open_locale pointwise

variables (A : Type*) [add_comm_group A]

/--
A divisible group `A` is an abelian group such that `nA = A` for all `n ≠ 0`.
-/
class divisible : Prop :=
(div : ∀ (n : ℤ), n ≠ 0 → n • (⊤ : add_subgroup A) = ⊤)

lemma divisible_of_elemement_divisible
  (sol : ∀ (n : ℤ) (x : A), n ≠ 0 → ∃ (y : A), n • y = x) :
  divisible A :=
{ div := λ n hn, add_subgroup.ext $ λ q,
  { mp := λ _, trivial,
    mpr := λ _, ⟨(sol n q hn).some, ⟨trivial, (sol n q hn).some_spec⟩⟩ } }

lemma divisible_iff_element_divisible :
  divisible A ↔ ∀ (n : ℤ) (x : A), n ≠ 0 → ∃ (y : A), n • y = x :=
⟨λ d n x hn, begin
  rcases show x ∈ (n • ⊤ : add_subgroup A),
  { convert (add_subgroup.mem_top _ : x ∈ ⊤),
    rwa d.div, } with ⟨a', _, ha'⟩,
  exact ⟨a', ha'⟩,
end, add_comm_group.divisible_of_elemement_divisible _⟩

/-- ℚ is a divisible group. -/
instance divisible_rat : divisible ℚ :=
divisible_of_elemement_divisible _ $
  λ n x hn, ⟨x/n, by rw [zsmul_eq_mul, mul_div_cancel']; exact_mod_cast hn⟩

/-- ℝ is a divisible group. -/
instance divisible_real : divisible ℝ :=
divisible_of_elemement_divisible _ $
  λ n x hn, ⟨x/n, by rw [zsmul_eq_mul, mul_div_cancel']; exact_mod_cast hn⟩

section product

variables {ι : Type*} (B : ι → Type*) [Π i, add_comm_group (B i)] [Π i, divisible (B i)]

/-- Any product of divisible group is divisible.-/
instance divisible_of_product_divisible : divisible (Π i, B i) :=
add_comm_group.divisible_of_elemement_divisible _ $
  λ n x hn, ⟨λ i, ((divisible_iff_element_divisible (B i)).mp infer_instance n (x i) hn).some,
    funext $ λ i, ((divisible_iff_element_divisible (B i)).mp infer_instance n (x i) hn).some_spec⟩

end product

end add_comm_group
