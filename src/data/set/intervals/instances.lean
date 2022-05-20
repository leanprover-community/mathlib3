import data.set.intervals.basic
import algebra.order.ring
import algebra.group_power.order

open set

/-- Instances for `(Icc 0 1)` -/

instance {α : Type*} [ordered_semiring α] : monoid (Icc (0:α) 1) := {
  mul := λ p q, ⟨p*q, ⟨mul_nonneg p.2.1 q.2.1, mul_le_one p.2.2 q.2.1 q.2.2⟩⟩,
  mul_assoc := λ p q r, subtype.mk_eq_mk.2 (mul_assoc p q r),
  one := ⟨1, right_mem_Icc.2 zero_le_one⟩,
  one_mul := (by simp),
  mul_one := (by simp),
  npow := λ n p, ⟨p.1 ^ n, ⟨pow_nonneg p.2.1 n, pow_le_one n p.2.1 p.2.2⟩⟩,
  npow_zero' := (by simp [has_one.one]),
  npow_succ' := λ n p, (by {simp only [pow_succ p.val n], refl}) }

instance {α : Type*} [ordered_comm_semiring α] : comm_monoid_with_zero (Icc (0:α) 1) :=
{ mul_comm := λ p q, (by exact subtype.mk_eq_mk.2 (mul_comm _ _)),
  zero := ⟨0, left_mem_Icc.2 zero_le_one⟩,
  zero_mul :=
  begin
    rintros ⟨p1, ⟨p21,p22⟩⟩,
    have : (⟨0 * p1, _⟩ : (Icc (0:α) 1)) = ⟨0, _⟩ * ⟨p1, _⟩, { refl },
    rw ←this,
    simp only [zero_mul],
  end,
  mul_zero :=
  begin
    rintros ⟨p1, ⟨p21,p22⟩⟩,
    have : (⟨p1 * 0, _⟩ : (Icc (0:α) 1)) = ⟨p1, _⟩ * ⟨0, _⟩, { refl },
    rw ←this,
    simp only [mul_zero],
  end,
  ..(show monoid (Icc (0:α) 1), by apply_instance) }

/-- Instances for `(Ico 0 1)` -/

instance {α : Type*} [ordered_semiring α] : semigroup (Ico (0:α) 1) := {
  mul := λ p q, ⟨p*q, ⟨mul_nonneg p.2.1 q.2.1,
    mul_lt_one_of_nonneg_of_lt_one_right p.2.2.le q.2.1 q.2.2⟩⟩,
  mul_assoc := λ p q r, (by exact subtype.mk_eq_mk.2 (mul_assoc p q r)) }

instance {α : Type*} [ordered_comm_semiring α] : comm_semigroup (Ico (0:α) 1) := {
  mul_comm := λ ⟨p1, _⟩ ⟨q1, _⟩,
    (by {apply subtype.mk_eq_mk.2, simp [subtype.coe_mk, mul_comm p1 q1]}),
  ..(show semigroup (Ico (0:α) 1), by apply_instance) }

/-- Instances for `(Ioc 0 1)` -/

instance {α : Type*} [ordered_semiring α] [nontrivial α] : monoid (Ioc (0:α) 1) := {
  mul := λ p q, ⟨p.1 * q.1, ⟨mul_pos p.2.1 q.2.1, mul_le_one p.2.2 (le_of_lt q.2.1) q.2.2⟩⟩,
  mul_assoc := λ p q r, (by simp only [subtype.mk_eq_mk, mul_assoc]),
  one := ⟨1, ⟨zero_lt_one, le_refl 1⟩⟩,
  one_mul := (by simp),
  mul_one := (by simp),
  npow := λ n p, ⟨p.1 ^ n, ⟨pow_pos p.2.1 n, pow_le_one n (le_of_lt p.2.1) p.2.2⟩⟩,
  npow_zero' := λ p, (by {simp only [pow_zero], refl}),
  npow_succ' := λ n ⟨p1, _⟩, (by {simp only [pow_succ p1 n], refl }) }

instance {α : Type*} [ordered_comm_semiring α] [nontrivial α] : comm_monoid (Ioc (0:α) 1) := {
  mul_comm := λ p q, (by {ext1, exact mul_comm p.1 q.1}),
  ..(show monoid (Ioc (0:α) 1), by apply_instance) }

/-- Instances for `(Ioo 0 1)` -/

instance {α : Type*} [ordered_semiring α] : semigroup (Ioo (0:α) 1) := {
  mul := λ p q, ⟨p.1 * q.1, ⟨mul_pos p.2.1 q.2.1,
    mul_lt_one_of_nonneg_of_lt_one_right p.2.2.le q.2.1.le q.2.2⟩⟩,
  mul_assoc := λ p q r, (by simp only [subtype.mk_eq_mk, mul_assoc]) }

instance {α : Type*} [ordered_comm_semiring α] : comm_semigroup (Ioo (0:α) 1) := {
  mul_comm := λ ⟨p1, _⟩ ⟨q1, _⟩,
    (by {apply subtype.mk_eq_mk.2, simp [subtype.coe_mk, mul_comm p1 q1]}),
  ..(show semigroup (Ioo (0:α) 1), by apply_instance) }
