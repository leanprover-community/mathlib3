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

open_locale pointwise

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

section pi

variables {ι β : Type*} (B : ι → Type*) [Π (i : ι), add_monoid (B i)] [Π (i : ι), has_scalar β (B i)]
variables [has_zero β] [Π i, divisible_by (B i) β]

instance divsible_by_pi : divisible_by (Π i, B i) β :=
{ div := λ x n i, (divisible_by.div (x i) n),
  div_zero := λ x, funext $ λ i, divisible_by.div_zero _,
  div_cancel := λ n x hn, funext $ λ i, divisible_by.div_cancel _ hn }

end pi

section prod

variables {β B B' : Type*} [has_zero β] [add_monoid B] [add_monoid B']
variables [has_scalar β B] [has_scalar β B'] [divisible_by B β] [divisible_by B' β]

instance divisible_by_prod : divisible_by (B × B') β :=
{ div := λ p n, (divisible_by.div p.1 n, divisible_by.div p.2 n),
  div_zero := λ p, prod.ext (divisible_by.div_zero _) (divisible_by.div_zero _),
  div_cancel := λ n p hn, prod.ext (divisible_by.div_cancel _ hn) (divisible_by.div_cancel _ hn) }

end prod

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

section pi

variables {ι β : Type*} (B : ι → Type*) [Π (i : ι), has_pow (B i) β]

instance has_pow_pi : has_pow (Π i, B i) β :=
{ pow := λ x n i, (x i)^n }

variables [has_zero β] [Π (i : ι), monoid (B i)] [Π i, rootable_by (B i) β]

instance rootable_by_pi : rootable_by (Π i, B i) β :=
{ root := λ x n i, rootable_by.root (x i) n,
  root_zero := λ x, funext $ λ i, rootable_by.root_zero _,
  root_pow := λ n x hn, funext $ λ i, rootable_by.root_pow _ hn }

end pi

section prod

variables {β B B' : Type*} [has_pow B β] [has_pow B' β]

instance has_pow_prod : has_pow (B × B') β :=
{ pow := λ p n, (p.1^n, p.2^n) }

variables [has_zero β] [monoid B] [monoid B'] [rootable_by B β] [rootable_by B' β]

instance rootable_by_prod : rootable_by (B × B') β :=
{ root := λ p n, (rootable_by.root p.1 n, rootable_by.root p.2 n),
  root_zero := λ p, prod.ext (rootable_by.root_zero _) (rootable_by.root_zero _),
  root_pow := λ n p hn, prod.ext (rootable_by.root_pow _ hn) (rootable_by.root_pow _ hn) }

end prod

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
  | int.of_nat m := divisible_by.div a m
  | int.neg_succ_of_nat m := - divisible_by.div a (m + 1)
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
  end }

end add_group

namespace add_comm_group

open add_monoid

variables (A : Type*) [add_comm_group A]

lemma smul_top_eq_top_of_divisible_by_int [divisible_by A ℤ] {n : ℤ} (hn : n ≠ 0) :
  n • (⊤ : add_subgroup A) = ⊤ :=
add_subgroup.map_top_of_surjective _ $ λ a, ⟨divisible_by.div a n, divisible_by.div_cancel _ hn⟩

noncomputable lemma divisible_by_int_of_smul_top_eq_top
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

section quotient

variables {B : add_subgroup A} [divisible_by A ℕ]

noncomputable instance divisible_by_quotient : divisible_by (A ⧸ B) ℕ :=
add_monoid.divisible_by_of_smul_surj _ _ $ λ n hn x, quotient.induction_on' x $ λ a,
  ⟨quotient.mk' (divisible_by.div a n),
    (congr_arg _ (divisible_by.div_cancel _ hn) : quotient.mk' _ = _)⟩

end quotient

section hom

variables {A} [divisible_by A ℕ] {B : Type*} [add_comm_group B] (f : A →+ B)

noncomputable instance divisible_by_of_surj (hf : function.surjective f) : divisible_by B ℕ :=
add_monoid.divisible_by_of_smul_surj _ _ $ λ n hn x,
  ⟨f $ divisible_by.div (hf x).some n, by rw [←f.map_nsmul (divisible_by.div (hf x).some n) n,
    divisible_by.div_cancel _ hn, (hf x).some_spec]⟩

end hom


end add_comm_group

namespace group

open monoid

variables (A : Type*) [group A]

/--
A group is `ℤ`-rootable if it is `ℕ`-rootable.
-/
def rootable_by_int_of_rootable_by_nat [rootable_by A ℕ] :
  rootable_by A ℤ :=
{ root := λ a z, match z with
  | int.of_nat n := rootable_by.root a n
  | int.neg_succ_of_nat n := (rootable_by.root a (n + 1))⁻¹
  end,
  root_zero := λ a, rootable_by.root_zero a,
  root_pow := λ n a hn, begin
    induction n,
    { change (rootable_by.root a _) ^ _ = a,
      norm_num,
      rw [rootable_by.root_pow],
      rw [int.of_nat_eq_coe] at hn,
      exact_mod_cast hn, },
    { change ((rootable_by.root a _) ⁻¹)^_ = a,
      norm_num,
      rw [rootable_by.root_pow],
      norm_num, }
  end}

attribute [to_additive group.rootable_by_int_of_rootable_by_nat]
  add_group.divisible_by_int_of_divisible_by_nat

/--
A group is `ℤ`-rootable if it is `ℕ`-rootable
-/
def rootable_by_nat_of_rootable_by_int [rootable_by A ℤ] :
  rootable_by A ℕ :=
{ root := λ a n, rootable_by.root a (n : ℤ),
  root_zero := λ a, rootable_by.root_zero a,
  root_pow := λ n a hn, begin
    have := rootable_by.root_pow a (show (n : ℤ) ≠ 0, by exact_mod_cast hn),
    norm_num at this,
    exact this,
  end }

attribute [to_additive group.rootable_by_nat_of_rootable_by_int]
  add_group.divisible_by_nat_of_divisible_by_int

end group

namespace comm_group

open monoid

section quotient

variables (A : Type*) [comm_group A] (B : subgroup A)

noncomputable instance rootable_by_quotient [rootable_by A ℕ] : rootable_by (A ⧸ B) ℕ :=
rootable_by_of_root_surj _ _ $ λ n hn x, quotient.induction_on' x $ λ a,
  ⟨quotient.mk' (rootable_by.root a n),
    (congr_arg _ $ rootable_by.root_pow _ hn : quotient.mk' _ = _)⟩

attribute [to_additive rootable_by_quotient] add_comm_group.divisible_by_quotient

end quotient

section hom

variables {A B : Type*} [comm_group A] [comm_group B] [rootable_by A ℕ] (f : A →* B)

noncomputable instance rootable_by_of_surj (hf : function.surjective f) : rootable_by B ℕ :=
rootable_by_of_root_surj _ _ $ λ n hn x,
  ⟨f $ rootable_by.root (hf x).some n, (by rw [←f.map_pow (rootable_by.root (hf x).some n) n,
    rootable_by.root_pow _ hn, (hf x).some_spec] : _ ^ _ = x)⟩

end hom

end comm_group
