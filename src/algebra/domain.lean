import algebra.regular.basic

universe u

variables {R : Type u}

/-- A domain is a nontrivial ring with no zero divisors, i.e. satisfying
  the condition `a * b = 0 ↔ a = 0 ∨ b = 0`.

  This is implemented as a mixin for `ring α`.
  To obtain an integral domain use `[comm_ring α] [is_domain α]`. -/
class is_domain (R : Type u) [has_mul R] [has_zero R] extends nontrivial R : Prop :=
(regular_of_ne_zero : ∀ {c : R}, c ≠ 0 → is_regular c)

lemma mul_left_cancel_of_ne_zero [has_mul R] [has_zero R] [is_domain R] {a b c : R}
  (h : a ≠ 0) (H : a * b = a * c) : b = c :=
(is_domain.regular_of_ne_zero h).left H

lemma mul_right_cancel_of_ne_zero [has_mul R] [has_zero R] [is_domain R] {a b c : R}
  (h : b ≠ 0) (H : a * b = c * b) : a = c :=
(is_domain.regular_of_ne_zero h).right H

namespace is_domain

@[priority 0] -- see Note [lower instance priority]
instance to_no_zero_divisors [mul_zero_class R] [is_domain R] :
  no_zero_divisors R :=
⟨λ a b h, or_iff_not_and_not.mpr $
  λ H, H.right $ mul_left_cancel_of_ne_zero H.left $ (mul_zero a).symm ▸ h⟩

@[priority 0] -- see Note [lower instance priority]
instance to_cancel_monoid_with_zero [monoid_with_zero R] [is_domain R] :
  cancel_monoid_with_zero R :=
{ mul_left_cancel_of_ne_zero := λ a b c, mul_left_cancel_of_ne_zero,
  mul_right_cancel_of_ne_zero := λ a b c, mul_right_cancel_of_ne_zero,
  .. (infer_instance : monoid_with_zero R) }

@[priority 0] -- see Note [lower instance priority]
instance to_cancel_comm_monoid_with_zero [comm_monoid_with_zero R] [is_domain R] :
  cancel_comm_monoid_with_zero R :=
{ .. (infer_instance : comm_monoid_with_zero R), .. is_domain.to_cancel_monoid_with_zero }

end is_domain

/-- Pullback an `is_domain` instance along an injective function. -/
protected theorem function.injective.is_domain
  {R S : Type*} [mul_zero_one_class R] [mul_zero_one_class S] [is_domain S]
  (f : R →*₀ S) (hf : function.injective f) :
  is_domain R :=
{ regular_of_ne_zero := λ x h,
  { left := λ y z (H : x * y = x * z),
      have f x * f y = f x * f z, by simp_rw [←map_mul, H],
      hf (mul_left_cancel_of_ne_zero ((function.injective.ne_iff' hf (f.map_zero)).mpr h) this),
    right := λ y z (H : y * x = z * x),
      have f y * f x = f z * f x, by simp_rw [←map_mul, H],
      hf (mul_right_cancel_of_ne_zero ((function.injective.ne_iff' hf (f.map_zero)).mpr h) this) }
  .. pullback_nonzero f f.map_zero f.map_one, }
