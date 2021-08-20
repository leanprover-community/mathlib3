/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import algebra.ordered_monoid_lemmas
import algebra.group_with_zero.basic
import logic.embedding

/-!
# Regular elements

We introduce left-regular, right-regular and regular elements.

By definition, a regular element in a commutative ring is a non-zero divisor.
Lemma `is_regular_of_ne_zero` implies that every non-zero element of an integral domain is regular.
Since it assumes that the ring is a `cancel_monoid_with_zero` it applies also, for instance, to `ℕ`.

The lemmas in Section `mul_zero_class` show that the `0` element is (left/right-)regular if and
only if the `mul_zero_class` is trivial.  This is useful when figuring out stopping conditions for
regular sequences: if `0` is ever an element of a regular sequence, then we can extend the sequence
by adding one further `0`.

The final goal is to develop part of the API to prove, eventually, results about non-zero-divisors.
-/
variables {R : Type*} {a b : R}

section has_mul

variable [has_mul R]

/-- A left-regular element is an element `c` such that multiplication on the left by `c`
is injective on the left. -/
def is_left_regular (c : R) := function.injective ((*) c)

/-- A right-regular element is an element `c` such that multiplication on the right by `c`
is injective on the right. -/
def is_right_regular (c : R) := function.injective (* c)

/-- A regular element is an element `c` such that multiplication by `c` both on the left and
on the right is injective. -/
structure is_regular (c : R) : Prop :=
(left : is_left_regular c)
(right : is_right_regular c)

protected lemma mul_le_cancellable.is_left_regular [partial_order R] {a : R}
  (ha : mul_le_cancellable a) : is_left_regular a :=
ha.injective

end has_mul

section semigroup

variable [semigroup R]

/-- In a semigroup, the product of left-regular elements is left-regular. -/
lemma is_left_regular.mul (lra : is_left_regular a) (lrb : is_left_regular b) :
  is_left_regular (a * b) :=
show function.injective ((*) (a * b)), from (comp_mul_left a b) ▸ lra.comp lrb

/-- In a semigroup, the product of right-regular elements is right-regular. -/
lemma is_right_regular.mul (rra : is_right_regular a) (rrb : is_right_regular b) :
  is_right_regular (a * b) :=
show function.injective (* (a * b)), from (comp_mul_right b a) ▸ rrb.comp rra

/--  If an element `b` becomes left-regular after multiplying it on the left by a left-regular
element, then `b` is left-regular. -/
lemma is_left_regular.of_mul (ab : is_left_regular (a * b)) :
  is_left_regular b :=
function.injective.of_comp (by rwa comp_mul_left a b)

/--  An element is left-regular if and only if multiplying it on the left by a left-regular element
is left-regular. -/
@[simp] lemma mul_is_left_regular_iff (b : R) (ha : is_left_regular a) :
  is_left_regular (a * b) ↔ is_left_regular b :=
⟨λ ab, is_left_regular.of_mul ab, λ ab, is_left_regular.mul ha ab⟩

/--  If an element `b` becomes right-regular after multiplying it on the right by a right-regular
element, then `b` is right-regular. -/
lemma is_right_regular.of_mul (ab : is_right_regular (b * a)) :
  is_right_regular b :=
begin
  refine λ x y xy, ab (_ : x * (b * a) = y * (b * a)),
  rw [← mul_assoc, ← mul_assoc],
  exact congr_fun (congr_arg has_mul.mul xy) a,
end

/--  An element is right-regular if and only if multiplying it on the right with a right-regular
element is right-regular. -/
@[simp] lemma mul_is_right_regular_iff (b : R) (ha : is_right_regular a) :
  is_right_regular (b * a) ↔ is_right_regular b :=
⟨λ ab, is_right_regular.of_mul ab, λ ab, is_right_regular.mul ab ha⟩

/--  Two elements `a` and `b` are regular if and only if both products `a * b` and `b * a`
are regular. -/
lemma is_regular_mul_and_mul_iff :
  is_regular (a * b) ∧ is_regular (b * a) ↔ is_regular a ∧ is_regular b :=
begin
  refine ⟨_, _⟩,
  { rintros ⟨ab, ba⟩,
    exact ⟨⟨is_left_regular.of_mul ba.left, is_right_regular.of_mul ab.right⟩,
      ⟨is_left_regular.of_mul ab.left, is_right_regular.of_mul ba.right⟩⟩ },
  { rintros ⟨ha, hb⟩,
    exact ⟨⟨(mul_is_left_regular_iff _ ha.left).mpr hb.left,
        (mul_is_right_regular_iff _ hb.right).mpr ha.right⟩,
      ⟨(mul_is_left_regular_iff _ hb.left).mpr ha.left,
        (mul_is_right_regular_iff _ ha.right).mpr hb.right⟩⟩ }
end

/--  The "most used" implication of `mul_and_mul_iff`, with split hypotheses, instead of `∧`. -/
lemma is_regular.and_of_mul_of_mul (ab : is_regular (a * b)) (ba : is_regular (b * a)) :
  is_regular a ∧ is_regular b :=
is_regular_mul_and_mul_iff.mp ⟨ab, ba⟩

end semigroup

section mul_zero_class

variables [mul_zero_class R]

/--  The element `0` is left-regular if and only if `R` is trivial. -/
lemma is_left_regular.subsingleton (h : is_left_regular (0 : R)) : subsingleton R :=
⟨λ a b, h $ eq.trans (zero_mul a) (zero_mul b).symm⟩

/--  The element `0` is right-regular if and only if `R` is trivial. -/
lemma is_right_regular.subsingleton (h : is_right_regular (0 : R)) : subsingleton R :=
⟨λ a b, h $ eq.trans (mul_zero a) (mul_zero b).symm⟩

/--  The element `0` is regular if and only if `R` is trivial. -/
lemma is_regular.subsingleton (h : is_regular (0 : R)) : subsingleton R :=
h.left.subsingleton

/--  The element `0` is left-regular if and only if `R` is trivial. -/
lemma is_left_regular_zero_iff_subsingleton : is_left_regular (0 : R) ↔ subsingleton R :=
begin
  refine ⟨λ h, h.subsingleton, _⟩,
  intros H a b h,
  exact @subsingleton.elim _ H a b
end

/--  In a non-trivial `mul_zero_class`, the `0` element is not left-regular. -/
lemma not_is_left_regular_zero_iff : ¬ is_left_regular (0 : R) ↔ nontrivial R :=
begin
  rw [nontrivial_iff, not_iff_comm, is_left_regular_zero_iff_subsingleton, subsingleton_iff],
  push_neg,
  exact iff.rfl
end

/--  The element `0` is right-regular if and only if `R` is trivial. -/
lemma is_right_regular_zero_iff_subsingleton : is_right_regular (0 : R) ↔ subsingleton R :=
begin
  refine ⟨λ h, h.subsingleton, _⟩,
  intros H a b h,
  exact @subsingleton.elim _ H a b
end

/--  In a non-trivial `mul_zero_class`, the `0` element is not right-regular. -/
lemma not_is_right_regular_zero_iff : ¬ is_right_regular (0 : R) ↔ nontrivial R :=
begin
  rw [nontrivial_iff, not_iff_comm, is_right_regular_zero_iff_subsingleton, subsingleton_iff],
  push_neg,
  exact iff.rfl
end

/--  The element `0` is regular if and only if `R` is trivial. -/
lemma is_regular_iff_subsingleton : is_regular (0 : R) ↔ subsingleton R :=
⟨λ h, h.left.subsingleton,
 λ h, ⟨is_left_regular_zero_iff_subsingleton.mpr h, is_right_regular_zero_iff_subsingleton.mpr h⟩⟩

/-- A left-regular element of a `nontrivial` `mul_zero_class` is non-zero. -/
lemma is_left_regular.ne_zero [nontrivial R] (la : is_left_regular a) : a ≠ 0 :=
begin
  rintro rfl,
  rcases exists_pair_ne R with ⟨x, y, xy⟩,
  refine xy (la _),
  rw [zero_mul, zero_mul]
end

/-- A right-regular element of a `nontrivial` `mul_zero_class` is non-zero. -/
lemma is_right_regular.ne_zero [nontrivial R] (ra : is_right_regular a) : a ≠ 0 :=
begin
  rintro rfl,
  rcases exists_pair_ne R with ⟨x, y, xy⟩,
  refine xy (ra (_ : x * 0 = y * 0)),
  rw [mul_zero, mul_zero]
end

/-- A regular element of a `nontrivial` `mul_zero_class` is non-zero. -/
lemma is_regular.ne_zero [nontrivial R] (la : is_regular a) : a ≠ 0 :=
la.left.ne_zero

/--  In a non-trivial ring, the element `0` is not left-regular -- with typeclasses. -/
lemma not_is_left_regular_zero [nR : nontrivial R] : ¬ is_left_regular (0 : R) :=
not_is_left_regular_zero_iff.mpr nR

/--  In a non-trivial ring, the element `0` is not right-regular -- with typeclasses. -/
lemma not_is_right_regular_zero [nR : nontrivial R] : ¬ is_right_regular (0 : R) :=
not_is_right_regular_zero_iff.mpr nR

/--  In a non-trivial ring, the element `0` is not regular -- with typeclasses. -/
lemma not_is_regular_zero [nontrivial R] : ¬ is_regular (0 : R) :=
λ h, is_regular.ne_zero h rfl

end mul_zero_class

section comm_semigroup

variable [comm_semigroup R]

/--  A product is regular if and only if the factors are. -/
lemma is_regular_mul_iff : is_regular (a * b) ↔ is_regular a ∧ is_regular b :=
begin
  refine iff.trans _ is_regular_mul_and_mul_iff,
  refine ⟨λ ab, ⟨ab, by rwa mul_comm⟩, λ rab, rab.1⟩
end

end comm_semigroup

section monoid

variables [monoid R]

/--  In a monoid, `1` is regular. -/
lemma is_regular_one : is_regular (1 : R) :=
⟨λ a b ab, (one_mul a).symm.trans (eq.trans ab (one_mul b)),
  λ a b ab, (mul_one a).symm.trans (eq.trans ab (mul_one b))⟩

/-- An element admitting a left inverse is left-regular. -/
lemma is_left_regular_of_mul_eq_one (h : b * a = 1) : is_left_regular a :=
@is_left_regular.of_mul R _ a _ (by { rw h, exact is_regular_one.left })

/-- An element admitting a right inverse is right-regular. -/
lemma is_right_regular_of_mul_eq_one (h : a * b = 1) : is_right_regular a :=
@is_right_regular.of_mul R _ a _ (by { rw h, exact is_regular_one.right })

/-- If `R` is a monoid, an element in `units R` is regular. -/
lemma units.is_regular (a : units R) : is_regular (a : R) :=
⟨is_left_regular_of_mul_eq_one a.inv_mul, is_right_regular_of_mul_eq_one a.mul_inv⟩

/-- A unit in a monoid is regular. -/
lemma is_unit.is_regular (ua : is_unit a) : is_regular a :=
begin
  rcases ua with ⟨a, rfl⟩,
  exact units.is_regular a,
end

end monoid

section left_or_right_cancel_semigroup

/--
The embedding of a left cancellative semigroup into itself
by left multiplication by a fixed element.
 -/
@[to_additive
  "The embedding of a left cancellative additive semigroup into itself
   by left translation by a fixed element.", simps]
def mul_left_embedding {G : Type*} [left_cancel_semigroup G] (g : G) : G ↪ G :=
{ to_fun := λ h, g * h, inj' := mul_right_injective g }

/--
The embedding of a right cancellative semigroup into itself
by right multiplication by a fixed element.
 -/
@[to_additive
  "The embedding of a right cancellative additive semigroup into itself
   by right translation by a fixed element.", simps]
def mul_right_embedding {G : Type*} [right_cancel_semigroup G] (g : G) : G ↪ G :=
{ to_fun := λ h, h * g, inj' := mul_left_injective g }

/--  Elements of a left cancel semigroup are left regular. -/
lemma is_left_regular_of_left_cancel_semigroup [left_cancel_semigroup R] (g : R) :
  is_left_regular g :=
mul_right_injective g

/--  Elements of a right cancel semigroup are right regular. -/
lemma is_right_regular_of_right_cancel_semigroup [right_cancel_semigroup R] (g : R) :
  is_right_regular g :=
mul_left_injective g

end left_or_right_cancel_semigroup

section cancel_monoid

variables [cancel_monoid R]

/--  Elements of a cancel monoid are regular.  Cancel semigroups do not appear to exist. -/
lemma is_regular_of_cancel_monoid (g : R) : is_regular g :=
⟨mul_right_injective g, mul_left_injective g⟩

end cancel_monoid

section cancel_monoid_with_zero

variables  [cancel_monoid_with_zero R]

/--  Non-zero elements of an integral domain are regular. -/
lemma is_regular_of_ne_zero (a0 : a ≠ 0) : is_regular a :=
⟨λ b c, (mul_right_inj' a0).mp, λ b c, (mul_left_inj' a0).mp⟩

/-- In a non-trivial integral domain, an element is regular iff it is non-zero. -/
lemma is_regular_iff_ne_zero [nontrivial R] : is_regular a ↔ a ≠ 0 :=
⟨is_regular.ne_zero, is_regular_of_ne_zero⟩

end cancel_monoid_with_zero
