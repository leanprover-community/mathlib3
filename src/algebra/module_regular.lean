/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import algebra.group
import algebra.group_power.basic
import algebra.iterate_hom
import algebra.module.basic

/-!
# Action of regular elements on a module

We introduce `M`-regular elements, in the context of an `R`-module `M`.

By definition, an `M`-regular element of a commutative ring acting on an `R`-module `M` is an
element `a ∈ R` such that the function `m ↦ a • m` is injective.
-/

--should it be in the module namespace?

namespace module

variables {R S : Type*} {a b : R} {s : S} (M : Type*)

section has_scalar

variables [has_scalar R M] [has_scalar R S] [has_scalar S M] [is_scalar_tower R S M]

/-- An `M`-regular element is an element `c` such that multiplication on the left by `c` is an
injective map `M → M`. -/
def is_regular (c : R) := function.injective ((•) c : M → M)

section monoid

variables [monoid R] [add_monoid M] [is_scalar_tower R S M]
--semigroup does not have the right instance
--instance semigroup.has_scalar : has_scalar R R := { smul := λ a b, a * b }

/-- In a monoid, the product of `M`-regular elements is `M`-regular. -/
lemma is_regular.mul (ra : is_regular M a) (rs : is_regular M s) :
  is_regular M (a • s) :=
λ a b ab, rs (ra ((smul_assoc _ _ _).symm.trans (ab.trans (smul_assoc _ _ _))))

/--  If an element `b` becomes `M`-regular after multiplying it on the left by an `M`-regular
element, then `b` is `M`-regular. -/
lemma is_regular.of_mul (ab : is_regular M (a • s)) :
  is_regular M s :=
@function.injective.of_comp _ _ _ (λ m : M, a • m) _ (λ c d cd, ab
  (by rwa [smul_assoc, smul_assoc]))

/--  An element is `M`-regular if and only if multiplying it on the left by an `M`-regular element
is `M`-regular. -/
@[simp] lemma mul_is_regular_iff (b : S) (ha : is_regular M a) :
  is_regular M (a • b) ↔ is_regular M b :=
⟨λ ab, is_regular.of_mul M ab, λ ab, is_regular.mul M ha ab⟩

variables [is_scalar_tower R R M]

/--  Two elements `a` and `b` are `M`-regular if and only if both products `a • b` and `b • a`
are `M`-regular. -/
lemma is_regular_mul_and_mul_iff :
  is_regular M (a • b) ∧ is_regular M (b • a) ↔ is_regular M a ∧ is_regular M b :=
begin
  refine ⟨_, _⟩,
  { rintros ⟨ab, ba⟩,
    exact ⟨is_regular.of_mul M ba, is_regular.of_mul M ab⟩ },
  { rintros ⟨ha, hb⟩,
    exact ⟨(mul_is_regular_iff M b ha).mpr hb, (mul_is_regular_iff M a hb).mpr ha⟩ }
end

/--  The "most used" implication of `mul_and_mul_iff`, with split hypotheses, instead of `∧`. -/
lemma is_regular.and_of_mul_of_mul (ab : is_regular M (a • b)) (ba : is_regular M (b • a)) :
  is_regular M a ∧ is_regular M b :=
(is_regular_mul_and_mul_iff M).mp ⟨ab, ba⟩

end monoid

end has_scalar

section mul_action

variables [monoid R] [mul_action R M]

@[simp] lemma is_regular_one : is_regular M (1 : R) :=
begin
  intros a b ab,
  rwa [one_smul, one_smul] at ab,
end

variables [add_monoid M]

/--  Any power of an `M`-regular element is `M`-regular. -/
lemma is_regular.pow (n : ℕ) (ra : is_regular M a) : is_regular M (a ^ n) :=
begin
  induction n with n hn,
  { simp },
  { exact (mul_is_regular_iff M (a ^ n) ra).mpr hn }
end

/--  An element `a` is `M`-regular if and only if a positive power of `a` is `M`-regular. -/
lemma is_regular.pow_iff {n : ℕ} (n0 : 0 < n) :
  is_regular M (a ^ n) ↔ is_regular M a :=
begin
  refine ⟨_, is_regular.pow M n⟩,
  rw [← nat.succ_pred_eq_of_pos n0, pow_succ', ← smul_eq_mul],
  exact is_regular.of_mul M,
end

end mul_action

section semiring

variables [semiring R] [add_comm_monoid M] [semimodule R M]

/--  The element `0` is `M`-regular if and only if `M` is trivial. -/
lemma is_regular.subsingleton (h : is_regular M (0 : R)) : subsingleton M :=
⟨λ a b, h (by repeat { rw zero_smul R _ })⟩

/--  The element `0` is `M`-regular if and only if `M` is trivial. -/
lemma is_regular_zero_iff_subsingleton : is_regular M (0 : R) ↔ subsingleton M :=
⟨λ h, h.subsingleton M, λ H a b h, @subsingleton.elim _ H a b⟩

/--  The `0` element is not `M`-regular, on a non-trivial semimodule. -/
lemma not_is_regular_zero_iff : ¬ is_regular M (0 : R) ↔ nontrivial M :=
begin
  rw [nontrivial_iff, not_iff_comm, is_regular_zero_iff_subsingleton, subsingleton_iff],
  push_neg,
  exact iff.rfl
end

end semiring

section comm_monoid
open module

variables [comm_monoid R] [add_monoid M] [mul_action R M]

/--  A product is `M`-regular if and only if the factors are. -/
lemma is_regular_mul_iff : is_regular M (a • b) ↔ is_regular M a ∧ is_regular M b :=
begin
  rw [← is_regular_mul_and_mul_iff],
  exact ⟨λ ab, ⟨ab, by rwa [smul_eq_mul, mul_comm]⟩, λ rab, rab.1⟩
end

end comm_monoid

section monoid

section monoid_R

variables [monoid R] [semiring S] [add_comm_monoid M] [has_scalar R S] [has_scalar R M]
  [semimodule S M]  [is_scalar_tower R S M]

/-- An element of `S` admitting a left inverse in `R` is `M`-regular. -/
lemma is_regular_of_mul_eq_one (h : a • s = 1) : is_regular M s :=
begin
  have ras : is_regular M (a • s),
  { rw h,
    exact is_regular_one M },
  exact is_regular.of_mul M ras
end

end monoid_R

variables [semiring R] [semiring S] [add_comm_monoid M] [semimodule R S] [semimodule R M]
  [semimodule S M]  [is_scalar_tower R S M]

/-- Any element in `units R` is `M`-regular. -/
lemma units.is_regular (a : units R) : is_regular M (a : R) :=
begin
  have ai : a.inv • a.val = 1,
  { rw smul_eq_mul,
     exact a.inv_val },
  exact is_regular_of_mul_eq_one M ai,
end

/-- A unit is `M`-regular. -/
lemma is_unit.is_regular (ua : is_unit a) : is_regular M a :=
begin
  rcases ua with ⟨a, rfl⟩,
  exact units.is_regular M a,
end

end monoid

end module
