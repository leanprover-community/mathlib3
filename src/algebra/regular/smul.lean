/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import algebra.smul_with_zero
import algebra.regular.basic
/-!
# Action of regular elements on a module

We introduce `M`-regular elements, in the context of an `R`-module `M`.  The corresponding
predicate is called `is_smul_regular`.

There are very limited typeclass assumptions on `R` and `M`, but the "mathematical" case of interest
is a commutative ring `R` acting an a module `M`. Since the properties are "multiplicative", there
is no actual requirement of having an addition, but there is a zero in both `R` and `M`.
Smultiplications involving `0` are, of course, all trivial.

The defining property is that an element `a ∈ R` is `M`-regular if the smultiplication map
`M → M`, defined by `m ↦ a • m`, is injective.

This property is the direct generalization to modules of the property `is_left_regular` defined in
`algebra/regular`.  Lemma `is_smul_regular.is_left_regular_iff` shows that indeed the two notions
coincide.
-/

variables {R S : Type*} (M : Type*) {a b : R} {s : S}

/-- An `M`-regular element is an element `c` such that multiplication on the left by `c` is an
injective map `M → M`. -/
def is_smul_regular [has_scalar R M] (c : R) := function.injective ((•) c : M → M)

lemma is_left_regular.is_smul_regular [has_mul R] {c : R} (h : is_left_regular c) :
  is_smul_regular R c := h

/-- Left-regular multiplication on `R` is equivalent to `R`-regularity of `R` itself. -/
lemma is_left_regular_iff [has_mul R] {a : R} :
  is_left_regular a ↔ is_smul_regular R a := iff.rfl

lemma is_right_regular.is_smul_regular [has_mul R] {c : R} (h : is_right_regular c) :
  is_smul_regular R (opposite.op c) := h

/-- Right-regular multiplication on `R` is equivalent to `Rᵒᵖ`-regularity of `R` itself. -/
lemma is_right_regular_iff [has_mul R] {a : R} :
  is_right_regular a ↔ is_smul_regular R (opposite.op a) := iff.rfl

namespace is_smul_regular

variables {M}

section has_scalar

variables [has_scalar R M] [has_scalar R S] [has_scalar S M] [is_scalar_tower R S M]

/-- The product of `M`-regular elements is `M`-regular. -/
lemma smul (ra : is_smul_regular M a) (rs : is_smul_regular M s) :
  is_smul_regular M (a • s) :=
λ a b ab, rs (ra ((smul_assoc _ _ _).symm.trans (ab.trans (smul_assoc _ _ _))))

/-- If an element `b` becomes `M`-regular after multiplying it on the left by an `M`-regular
element, then `b` is `M`-regular. -/
lemma of_smul (a : R) (ab : is_smul_regular M (a • s)) :
  is_smul_regular M s :=
@function.injective.of_comp _ _ _ (λ m : M, a • m) _ (λ c d cd, ab
  (by rwa [smul_assoc, smul_assoc]))

/-- An element is `M`-regular if and only if multiplying it on the left by an `M`-regular element
is `M`-regular. -/
@[simp] lemma smul_iff (b : S) (ha : is_smul_regular M a) :
  is_smul_regular M (a • b) ↔ is_smul_regular M b :=
⟨of_smul _, ha.smul⟩

lemma is_left_regular [has_mul R] {a : R} (h : is_smul_regular R a) :
  is_left_regular a := h

lemma is_right_regular [has_mul R] {a : R} (h : is_smul_regular R (opposite.op a)) :
  is_right_regular a := h

end has_scalar

section monoid

variables [monoid R] [mul_action R M]

variable (M)

/-- One is `M`-regular always. -/
@[simp] lemma one : is_smul_regular M (1 : R) :=
λ a b ab, by rwa [one_smul, one_smul] at ab

variable {M}

lemma mul (ra : is_smul_regular M a) (rb : is_smul_regular M b) :
  is_smul_regular M (a * b) :=
ra.smul rb

lemma of_mul (ab : is_smul_regular M (a * b)) :
  is_smul_regular M b :=
by { rw ← smul_eq_mul at ab, exact ab.of_smul _ }

@[simp] lemma mul_iff_right  (ha : is_smul_regular M a) :
  is_smul_regular M (a * b) ↔ is_smul_regular M b :=
⟨of_mul, ha.mul⟩

/-- Two elements `a` and `b` are `M`-regular if and only if both products `a * b` and `b * a`
are `M`-regular. -/
lemma mul_and_mul_iff : is_smul_regular M (a * b) ∧ is_smul_regular M (b * a) ↔
  is_smul_regular M a ∧ is_smul_regular M b :=
begin
  refine ⟨_, _⟩,
  { rintros ⟨ab, ba⟩,
    refine ⟨ba.of_mul, ab.of_mul⟩ },
  { rintros ⟨ha, hb⟩,
    exact ⟨ha.mul hb, hb.mul ha⟩ }
end

/-- Any power of an `M`-regular element is `M`-regular. -/
lemma pow (n : ℕ) (ra : is_smul_regular M a) : is_smul_regular M (a ^ n) :=
begin
  induction n with n hn,
  { simp only [one, pow_zero] },
  { rw pow_succ, exact (ra.smul_iff (a ^ n)).mpr hn }
end

/-- An element `a` is `M`-regular if and only if a positive power of `a` is `M`-regular. -/
lemma pow_iff {n : ℕ} (n0 : 0 < n) :
  is_smul_regular M (a ^ n) ↔ is_smul_regular M a :=
begin
  refine ⟨_, pow n⟩,
  rw [← nat.succ_pred_eq_of_pos n0, pow_succ', ← smul_eq_mul],
  exact of_smul _,
end

end monoid

section monoid_with_zero

variables [monoid_with_zero R] [monoid_with_zero S] [has_zero M] [mul_action_with_zero R M]
  [mul_action_with_zero R S] [mul_action_with_zero S M] [is_scalar_tower R S M]

/-- The element `0` is `M`-regular if and only if `M` is trivial. -/
protected lemma subsingleton (h : is_smul_regular M (0 : R)) : subsingleton M :=
⟨λ a b, h (by repeat { rw mul_action_with_zero.zero_smul })⟩

/-- The element `0` is `M`-regular if and only if `M` is trivial. -/
lemma zero_iff_subsingleton : is_smul_regular M (0 : R) ↔ subsingleton M :=
⟨λ h, h.subsingleton, λ H a b h, @subsingleton.elim _ H a b⟩

/-- The `0` element is not `M`-regular, on a non-trivial module. -/
lemma not_zero_iff : ¬ is_smul_regular M (0 : R) ↔ nontrivial M :=
begin
  rw [nontrivial_iff, not_iff_comm, zero_iff_subsingleton, subsingleton_iff],
  push_neg,
  exact iff.rfl
end

/-- The element `0` is `M`-regular when `M` is trivial. -/
lemma zero [sM : subsingleton M] : is_smul_regular M (0 : R) :=
zero_iff_subsingleton.mpr sM

/-- The `0` element is not `M`-regular, on a non-trivial module. -/
lemma not_zero [nM : nontrivial M] : ¬ is_smul_regular M (0 : R) :=
not_zero_iff.mpr nM

/-- An element of `S` admitting a left inverse in `R` is `M`-regular. -/
lemma of_smul_eq_one (h : a • s = 1) : is_smul_regular M s :=
of_smul a (by { rw h, exact one M })

/-- An element of `R` admitting a left inverse is `M`-regular. -/
lemma of_mul_eq_one (h : a * b = 1) : is_smul_regular M b :=
of_mul (by { rw h, exact one M })

end monoid_with_zero

section comm_monoid

variables [comm_monoid R] [mul_action R M]

/-- A product is `M`-regular if and only if the factors are. -/
lemma mul_iff : is_smul_regular M (a * b) ↔
  is_smul_regular M a ∧ is_smul_regular M b :=
begin
  rw ← mul_and_mul_iff,
  exact ⟨λ ab, ⟨ab, by rwa mul_comm⟩, λ rab, rab.1⟩
end

end comm_monoid

end is_smul_regular

section group

variables {G : Type*} [group G]

/-- An element of a group acting on a Type is regular. This relies on the availability
of the inverse given by groups, since there is no `left_cancel_smul` typeclass. -/
lemma is_smul_regular_of_group [mul_action G R] (g : G) : is_smul_regular R g :=
begin
  intros x y h,
  convert congr_arg ((•) g⁻¹) h using 1;
  simp [←smul_assoc]
end

end group

variables [monoid_with_zero R] [has_zero M] [mul_action_with_zero R M]

/-- Any element in `units R` is `M`-regular. -/
lemma units.is_smul_regular (a : units R) : is_smul_regular M (a : R) :=
is_smul_regular.of_mul_eq_one a.inv_val

/-- A unit is `M`-regular. -/
lemma is_unit.is_smul_regular (ua : is_unit a) : is_smul_regular M a :=
begin
  rcases ua with ⟨a, rfl⟩,
  exact a.is_smul_regular M
end
