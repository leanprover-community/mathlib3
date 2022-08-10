/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import group_theory.subgroup.pointwise
import group_theory.group_action.pi
import group_theory.quotient_group
import algebra.group.pi

/-!
# Divisible Group and rootable group

In this file, we define a divisible add monoid and a rootable monoid with some basic properties.

## Main definition
* An additive monoid `A` is said to be divisible by `α` iff for all `n ≠ 0 ∈ α` and `y ∈ A`, there
  is an `x ∈ A` such that `n • x = y`. In this file, we adopt a constructive approach, i.e. we ask
  for an explicit `div : A → α → A` function such that `div a 0 = 0` and `n • div a n = a` for all
  `n ≠ 0 ∈ α`.
* A monoid `A` is said to be rootable by `α` iff for all `n ≠ 0 ∈ α` and `y ∈ A`, there is an
  `x ∈ A` such that `x^n = y`. In this file, we adopt a constructive approach, i.e. we ask for an
  explicit `root : A → α → A` function such that `root a 0 = 1` and `(root a n)ⁿ = a` for all
  `n ≠ 0 ∈ α`.

## Main results
For additive monoids and groups:
* `add_monoid.divisible_by_of_smul_surj` : the constructive definition of divisiblity is implied by
  the condition that `n • x = a` has solutions for all `n ≠ 0` and `a ∈ A`.
* `add_monoid.smul_surj_of_divisible_by` : the constructive definition of divisiblity implies
  the condition that `n • x = a` has solutions for all `n ≠ 0` and `a ∈ A`.
* `add_monoid.divisible_by_prod` : `A × B` is divisible for any two divisible additive monoids.
* `add_monoid.divisible_by_pi` : any product of divisble additive monoids is divisible.
* `add_group.divisible_by_int_of_divisible_by_nat` : for additive groups, int divisiblity is implied
  by nat divisiblity.
* `add_group.divisible_by_nat_of_divisible_by_int` : for additive groups, nat divisiblity is implied
  by int divisiblity.
* `add_comm_group.divisible_of_smul_top_eq_top` : the constructive definition of divisiblity is
  implied by the condition that `n • A = A` for all `n ≠ 0`.
* `add_comm_group.smul_top_eq_top_of_divisible` : the constructive definition of divisiblity implies
  the condition that `n • A = A` for all `n ≠ 0`.
* `add_comm_group.divisible_of_char_zero` : any field of characteristic zero is divisible.
* `add_comm_group.divisible_by_quotient` : 1uotient group of divisible group is divisible.
* `add_comm_group.divisible_by_of_surj` : if `A` is divisible and `A →+ B` is surjective, then `B`
  is divisible.

and their multiplicative counterparts:
* `monoid.rootable_by_of_pow_surj` : the constructive definition of rootablity is implied by the
  condition that `xⁿ = y` has solutions for all `n ≠ 0` and `a ∈ A`.
* `monoid.pow_surj_of_rootable_by` : the constructive definition of rootablity implies the
  condition that `xⁿ = y` has solutions for all `n ≠ 0` and `a ∈ A`.
* `monoid.rootable_by_prod` : any product of two rootable monoids is rootable.
* `monoid.rootable_by_pi` : any product of rootable monoids is rootable.
* `group.rootable_by_int_of_rootable_by_nat` : in groups, int rootablity is implied by nat
  rootablity.
* `group.rootable_by_nat_of_rootable_by_int` : in groups, nat rootablity is implied by int
  rootablity.
* `comm_group.rootable_by_quotient` : quotient group of rootable group is rootable.
* `comm_group.rootable_by_of_surj` : if `A` is rootable and `A →* B` is surjective, then `B` is
  rootable.

TODO: Show that divisibility implies injectivity in the category of `AddCommGroup`.
-/

open_locale pointwise

namespace add_monoid

variables (A α : Type*) [add_monoid A] [has_smul α A] [has_zero α]

/--
An `add_monoid A` is `α`-divisible iff `n • x = a` has a solution for all `n ≠ 0 ∈ α` and `a ∈ A`.
Here we adopt a constructive approach where we ask an explicit `div : A → α → A` function such that
* `div a 0 = 0` for all `a ∈ A`
* `n • div a n = a` for all `n ≠ 0 ∈ α` and `a ∈ A`.
-/
class divisible_by :=
(div : A → α → A)
(div_zero : ∀ a, div a 0 = 0)
(div_cancel : ∀ {n : α} (a : A), n ≠ 0 → n • (div a n) = a)

end add_monoid

namespace monoid

variables (A α : Type*) [monoid A] [has_pow A α] [has_zero α]

/--
A `monoid A` is `α`-rootable iff `xⁿ = a` has a solution for all `n ≠ 0 ∈ α` and `a ∈ A`.
Here we adopt a constructive approach where we ask an explicit `root : A → α → A` function such that
* `root a 0 = 1` for all `a ∈ A`
* `(root a n)ⁿ = a` for all `n ≠ 0 ∈ α` and `a ∈ A`.
-/
@[to_additive add_monoid.divisible_by]
class rootable_by :=
(root : A → α → A)
(root_zero : ∀ a, root a 0 = 1)
(root_cancel : ∀ {n : α} (a : A), n ≠ 0 → (root a n)^n = a)

@[to_additive smul_surj_of_divisible_by]
lemma pow_left_surj_of_rootable_by [rootable_by A α] {n : α} (hn : n ≠ 0) :
  function.surjective (λ a, pow a n : A → A) :=
λ x, ⟨rootable_by.root x n, rootable_by.root_cancel _ hn⟩

/--
A `monoid A` is `α`-rootable iff the `pow _ n` function is surjective, i.e. the constructive version
implies the textbook approach.
-/
@[to_additive add_monoid.divisible_by_of_div_surj
"An `add_monoid A` is `α`-divisible iff `n • _` is a surjective function, i.e. the constructive
version implies the textbook approach."]
noncomputable def rootable_by_of_pow_surj
  (H : ∀ {n : α}, n ≠ 0 → function.surjective (λ a, a^n : A → A)) :
rootable_by A α :=
{ root := λ a n, @dite _ (n = 0) (classical.dec _) (λ _, (1 : A)) (λ hn, (H hn a).some),
  root_zero := λ _, by classical; exact dif_pos rfl,
  root_cancel := λ n a hn, by rw dif_neg hn; exact (H hn a).some_spec }

section pi

variables {ι β : Type*} (B : ι → Type*) [Π (i : ι), has_pow (B i) β]
variables [has_zero β] [Π (i : ι), monoid (B i)] [Π i, rootable_by (B i) β]

@[to_additive add_monoid.divisible_by_pi]
instance rootable_by_pi : rootable_by (Π i, B i) β :=
{ root := λ x n i, rootable_by.root (x i) n,
  root_zero := λ x, funext $ λ i, rootable_by.root_zero _,
  root_cancel := λ n x hn, funext $ λ i, rootable_by.root_cancel _ hn }

end pi

section prod

variables {β B B' : Type*} [has_pow B β] [has_pow B' β]
variables [has_zero β] [monoid B] [monoid B'] [rootable_by B β] [rootable_by B' β]

@[to_additive add_monoid.divisible_by_prod]
instance rootable_by_prod : rootable_by (B × B') β :=
{ root := λ p n, (rootable_by.root p.1 n, rootable_by.root p.2 n),
  root_zero := λ p, prod.ext (rootable_by.root_zero _) (rootable_by.root_zero _),
  root_cancel := λ n p hn, prod.ext (rootable_by.root_cancel _ hn) (rootable_by.root_cancel _ hn) }

end prod

end monoid

namespace add_comm_group

open add_monoid

variables (A : Type*) [add_comm_group A]

lemma smul_top_eq_top_of_divisible_by_int [divisible_by A ℤ] {n : ℤ} (hn : n ≠ 0) :
  n • (⊤ : add_subgroup A) = ⊤ :=
add_subgroup.map_top_of_surjective _ $ λ a, ⟨divisible_by.div a n, divisible_by.div_cancel _ hn⟩

/--
If for all `n ≠ 0 ∈ ℤ`, `n • A = A`, then `A` is divisible.
-/
noncomputable def divisible_by_int_of_smul_top_eq_top
  (H : ∀ {n : ℤ} (hn : n ≠ 0), n • (⊤ : add_subgroup A) = ⊤) :
  divisible_by A ℤ :=
{ div := λ a n, dite (n = 0) (λ _, 0)
    (λ hn, (show a ∈ n • (⊤ : add_subgroup A), by rw [H hn]; trivial).some),
  div_zero := λ a, dif_pos rfl,
  div_cancel := λ n a hn, begin
    rw [dif_neg hn],
    generalize_proofs h1,
    exact h1.some_spec.2,
  end }

@[priority 100]
instance divisible_of_char_zero {𝕜} [division_ring 𝕜] [char_zero 𝕜] : divisible_by 𝕜 ℤ :=
{ div := λ q n, q / n,
  div_zero := λ q, by norm_num,
  div_cancel := λ n q hn,
    by rw [zsmul_eq_mul, (int.cast_commute n _).eq, div_mul_cancel q (int.cast_ne_zero.mpr hn)] }

end add_comm_group

namespace group

open monoid

variables (A : Type*) [group A]

/--
A group is `ℤ`-rootable if it is `ℕ`-rootable.
-/
@[to_additive add_group.divisible_by_int_of_divisible_by_nat
"An add group is `ℤ`-divisible if it is `ℕ`-divisible."]
def rootable_by_int_of_rootable_by_nat [rootable_by A ℕ] :
  rootable_by A ℤ :=
{ root := λ a z, match z with
  | int.of_nat n := rootable_by.root a n
  | int.neg_succ_of_nat n := (rootable_by.root a (n + 1))⁻¹
  end,
  root_zero := λ a, rootable_by.root_zero a,
  root_cancel := λ n a hn, begin
    induction n,
    { change (rootable_by.root a _) ^ _ = a,
      norm_num,
      rw [rootable_by.root_cancel],
      rw [int.of_nat_eq_coe] at hn,
      exact_mod_cast hn, },
    { change ((rootable_by.root a _) ⁻¹)^_ = a,
      norm_num,
      rw [rootable_by.root_cancel],
      norm_num, }
  end}

/--A group is `ℕ`-rootable if it is `ℤ`-rootable
-/
@[to_additive add_group.divisible_by_nat_of_divisible_by_int
"An add group is `ℕ`-divisible if it `ℤ`-divisible."]
def rootable_by_nat_of_rootable_by_int [rootable_by A ℤ] :
  rootable_by A ℕ :=
{ root := λ a n, rootable_by.root a (n : ℤ),
  root_zero := λ a, rootable_by.root_zero a,
  root_cancel := λ n a hn, begin
    have := rootable_by.root_cancel a (show (n : ℤ) ≠ 0, by exact_mod_cast hn),
    norm_num at this,
    exact this,
  end }

end group

namespace comm_group

open monoid

section hom

variables {α A B : Type*}
variables [has_zero α] [monoid A] [monoid B] [has_pow A α] [has_pow B α] [rootable_by A α]
variables (f : A → B)

/--
If `f : A → B` is a surjective homomorphism and `A` is `α`-rootable, then `B` is also `α`-rootable.
-/
@[to_additive add_comm_group.divisible_by_of_surj
"If `f : A → B` is a surjective homomorphism and `A` is `α`-divisible, then `B` is also `α`-divisible."]
noncomputable def rootable_by_of_surj (hf : function.surjective f)
  (hpow : ∀ (a : A) (n : α), f (a ^ n) = f a ^ n) : rootable_by B α :=
rootable_by_of_pow_surj _ _ $ λ n hn x,
  let ⟨y, hy⟩ := hf x in ⟨f $ rootable_by.root y n, (by rw [←hpow (rootable_by.root y n) n,
    rootable_by.root_cancel _ hn, hy] : _ ^ _ = x)⟩

end hom

section quotient

variables (A : Type*) [comm_group A] (B : subgroup A)

/--
Any quotient group of a rootable group is rootable.
-/
@[to_additive add_comm_group.divisible_by_quotient
"Any quotient group of a divisible group is divisible"]
noncomputable def rootable_by_quotient [rootable_by A ℕ] : rootable_by (A ⧸ B) ℕ :=
rootable_by_of_pow_surj _ _ $ λ n hn x, quotient.induction_on' x $ λ a,
  ⟨quotient.mk' (rootable_by.root a n),
    (congr_arg _ $ rootable_by.root_cancel _ hn : quotient.mk' _ = _)⟩

end quotient


end comm_group
