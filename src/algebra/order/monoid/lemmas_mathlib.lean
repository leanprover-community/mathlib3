import algebra.order.monoid.lemmas

@[to_additive]
lemma mul_le_cancellable.mul {α : Type*} [has_le α] [semigroup α] {a b : α}
  (ha : mul_le_cancellable a) (hb : mul_le_cancellable b) :
  mul_le_cancellable (a * b) :=
begin
  intros x y h,
  rw [mul_assoc, mul_assoc] at h,
  exact hb (ha h),
end

@[to_additive]
lemma mul_le_cancellable.of_mul_left {α : Type*} [has_le α] [semigroup α]
  [covariant_class α α (*) (≤)] {a b : α} (hab : mul_le_cancellable (a * b)) :
  mul_le_cancellable b :=
begin
  intros x y h,
  apply hab,
  rw [mul_assoc, mul_assoc],
  exact mul_le_mul_left' h a,
end
