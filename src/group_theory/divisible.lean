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
such that `n • x = y`. In this file, we adpot a constructive approach, i.e. we ask for an explicit
`div_int : A → ℤ → A` function such that `div_int a 0 = 0` and `n • div_int a n = a` for `n ≠ 0`.

## Main results
* `add_comm_group.divisible_of_smul_surj` : the constructive definition of divisiblity is implied by
  the condition that `n • x = a` has solutions for all `n ≠ 0` and `a ∈ A`.
* `add_comm_group.smul_surj_of_divisible` : the constructive definition of divisiblity implies
  the condition that `n • x = a` has solutions for all `n ≠ 0` and `a ∈ A`.
* `add_comm_group.divisible_of_smul_top_eq_top` : the constructive definition of divisiblity is
  implied by the condition that `n • A = A` for all `n ≠ 0`.
* `add_comm_group.smul_top_eq_top_of_divisible` : the constructive definition of divisiblity implies
  the condition that `n • A = A` for all `n ≠ 0`.
* `add_comm_group.divisible_prod` : `A × B` is divisible for any divisible `A` and `B`.
* `add_comm_group.divisible_pi` : Any product of divisble group is divisible.
* `add_comm_group.divisible_of_char_zero` : Any field of characteristic zero is divisible.
* `add_comm_group.divisible_quotient` : Quotient group of divisible group is divisible.
* `add_comm_group.divisible_of_surj` : if `A` is divisible and `A →+ B` is surjective, then `B` is
  divisible.
TODO: Show that divisibility implies injectivity in the category of `AddCommGroup`.
-/

namespace add_monoid

variables (A α : Type*) [add_monoid A] [has_scalar α A] [has_zero α]

/--
An `add_monoid A` is `α`-divisible iff `n • x = a` has a solution for all `n ≠ 0 ∈ α` and `a ∈ A`.
Here we adpot a constructive approach where we ask an explicit `div : A → α → A` function such that
* `div a 0 = 0` for all `a ∈ A`
* `n • div a n = a` for all `n ≠ 0 ∈ α` and `a ∈ A`.
-/
class divisible_by :=
(div : A → α → A)
(div_zero : ∀ a, div a 0 = 0)
(div_cancel : ∀ {n : α} (a : A), n ≠ 0 → n • (div a n) = a)

lemma smul_surj_of_divisible_by [divisible_by A α] {n : α} (hn : n ≠ 0) :
  function.surjective ((•) n : A → A) :=
λ x, ⟨divisible_by.div x n, divisible_by.div_cancel _ hn⟩

/--
An `add_monoid A` is `α`-divisible iff `n • _` is a surjective function, i.e. the constructive
version implies the textbook approach.
-/
noncomputable def divisible_by_of_smul_surj
  [Π (n : α), decidable (n = 0)]
  (H : ∀ {n : α}, n ≠ 0 → function.surjective ((•) n : A → A)) :
  divisible_by A α :=
{ div := λ a n, dite (n = 0) (λ _, 0) (λ hn, (H hn a).some),
  div_zero := λ _, dif_pos rfl,
  div_cancel := λ n a hn, by rw [dif_neg hn, (H hn a).some_spec] }

end add_monoid

namespace monoid

variables (A α : Type*) [monoid A] [has_pow A α] [has_zero α]

/--
A `monoid A` is `α`-rootable iff `xⁿ = a` has a solution for all `n ≠ 0 ∈ α` and `a ∈ A`.
Here we adpot a constructive approach where we ask an explicit `root : A → α → A` function such that
* `root a 0 = 1` for all `a ∈ A`
* `(root a n)ⁿ = a` for all `n ≠ 0 ∈ α` and `a ∈ A`.
-/
@[to_additive add_monoid.divisible_by]
class rootable_by :=
(root : A → α → A)
(root_zero : ∀ a, root a 0 = 1)
(root_pow : ∀ {n : α} (a : A), n ≠ 0 → (root a n)^n = a)

@[to_additive add_monoid.smul_surj_of_divisible_by]
lemma root_surj_of_rootable_by [rootable_by A α] {n : α} (hn : n ≠ 0) :
  function.surjective ((flip (^)) n : A → A) :=
λ x, ⟨rootable_by.root x n, rootable_by.root_pow _ hn⟩

/--
A `monoid A` is `α`-rootable iff the `pow _ n` function is surjective, i.e. the constructivec version
implies the textbook approach.
-/
@[to_additive add_monoid.divisible_by_of_smul_surj]
noncomputable def rootable_by_of_root_surj
  [Π (n : α), decidable (n = 0)]
  (H : ∀ {n : α}, n ≠ 0 → function.surjective ((flip (^)) n : A → A)) :
rootable_by A α :=
{ root := λ a n, dite (n = 0) (λ _, 1) (λ hn, (H hn a).some),
  root_zero := λ _, dif_pos rfl,
  root_pow := λ n a hn, by rw dif_neg hn; exact (H hn a).some_spec }

end monoid

namespace add_group

open add_monoid

variables (A : Type*) [add_group A]

/--
An add_group is `ℤ` divisible if it is `ℕ`-divisible.
-/
def divisible_by_int_of_divisible_by_nat [divisible_by A ℕ] :
  divisible_by A ℤ :=
{ div := λ a z, match z with
  | int.of_nat m := (divisible_by.div a m)
  | int.neg_succ_of_nat m := - (divisible_by.div a (m + 1))
  end,
  div_zero := λ a, divisible_by.div_zero a,
  div_cancel := λ z a hn, begin
    cases z,
    { norm_num,
      change z • (divisible_by.div _ _) = _,
      rw divisible_by.div_cancel _ _,
      rw [int.of_nat_eq_coe] at hn,
      exact_mod_cast hn, },
    { norm_num,
      change - ((z+1) • - (divisible_by.div _ _)) = _,
      have := nsmul_zero_sub (divisible_by.div a (z + 1)) (z + 1),
      rw [zero_sub, zero_sub] at this,
      rw [this, neg_neg, divisible_by.div_cancel],
      norm_num, },
  end}

/--
An add_group is `ℕ`-divisible if it is `ℤ`-divisible.
-/
def divisible_by_nat_of_divisible_by_int [divisible_by A ℤ] :
  divisible_by A ℕ :=
{ div := λ a n, divisible_by.div a (n : ℤ),
  div_zero := λ a, divisible_by.div_zero a,
  div_cancel := λ n a hn, begin
    have := divisible_by.div_cancel a (by exact_mod_cast hn : (n : ℤ) ≠ 0),
    norm_num at this,
    assumption,
  end, }

end add_group
#lint
#exit
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

localized "infix ` /ℤ ` :50 := divisible.div_int" in divisible_group

lemma smul_surj_of_divisible [divisible A] {n : ℤ} (hn : n ≠ 0) :
  function.surjective ((•) n : A → A) :=
λ a, ⟨a /ℤ n, divisible.div_cancel a hn⟩

noncomputable instance divisible_of_smul_surj
  (surj : ∀ {n : ℤ}, n ≠ 0 → function.surjective ((•) n : A → A)) :
  divisible A :=
{ div_int := λ a n, dite (n = 0) (λ _, 0) (λ h, (surj h a).some),
  div_zero := λ a, dif_pos rfl,
  div_cancel := λ n a h, begin
    rw [dif_neg h, (surj h a).some_spec],
  end }

lemma smul_top_eq_top_of_divisible [divisible A] {n : ℤ} (hn : n ≠ 0) :
  n • (⊤ : add_subgroup A) = ⊤ :=
add_subgroup.map_top_of_surjective _ $ smul_surj_of_divisible _ hn

noncomputable instance divisible_of_smul_top_eq_top
  (H : ∀ {n : ℤ}, n ≠ 0 → n • (⊤ : add_subgroup A) = ⊤) :
  divisible A:=
add_comm_group.divisible_of_smul_surj _ $ λ n hn a, ⟨(show a ∈ n • (⊤ : add_subgroup A),
  by simp only [H hn]).some, (show a ∈ n • (⊤ : add_subgroup A), by simp only [H hn]).some_spec.2⟩

/-- Any division ring of characteristic zero is divisible -/
@[priority 100]
instance divisible_of_char_zero {𝕜} [division_ring 𝕜] [char_zero 𝕜] : divisible 𝕜 :=
{ div_int := λ q n, q / n,
  div_zero := λ q, by norm_num,
  div_cancel := λ n q hn,
    by rw [zsmul_eq_mul, (int.cast_commute n _).eq, div_mul_cancel q (int.cast_ne_zero.mpr hn)] }

section pi

variables {ι : Type*} (B : ι → Type*) [Π i, add_comm_group (B i)] [Π i, divisible (B i)]

/-- Any product of divisible group is divisible.-/
instance divisible_pi : divisible (Π i, B i) :=
{ div_int := λ x n i, (x i) /ℤ n,
  div_zero := λ x, funext $ λ i, divisible.div_zero _,
  div_cancel := λ n x hn, funext $ λ i, divisible.div_cancel (x i) hn }

end pi

section prod

variable [divisible A]
variables (B : Type*) [add_comm_group B] [divisible B]

instance divisible_prod : divisible (A × B) :=
{ div_int := λ p n, ⟨p.1 /ℤ n, p.2 /ℤ n⟩,
  div_zero := λ p, prod.ext (divisible.div_zero _) (divisible.div_zero _),
  div_cancel := λ n p hn, (prod.ext (divisible.div_cancel p.1 hn) (divisible.div_cancel p.2 hn)) }

end prod


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
