import data.set.intervals.basic
import algebra.order.ring
import algebra.group_power.order

open set

instance {α : Type*} [ordered_semiring α] : monoid (Icc (0:α) 1) := {
  mul := λ p q, ⟨p*q, ⟨mul_nonneg p.2.1 q.2.1, mul_le_one p.2.2 q.2.1 q.2.2⟩⟩,
  mul_assoc := λ p q r, subtype.mk_eq_mk.2 (mul_assoc p q r),
  one := ⟨1, right_mem_Icc.2 zero_le_one⟩,
  one_mul := λ p, (by simp),
  mul_one := λ p, (by simp),
  npow := λ n p, ⟨p.1 ^ n, ⟨pow_nonneg p.2.1 n, pow_le_one n p.2.1 p.2.2⟩⟩,
  npow_zero' := λ p, (by simp [has_one.one]),
  npow_succ' :=
  begin
    refine λ n p, _,
    simp only [pow_succ p.val n],
    refl,
  end,
}




instance {α : Type*} [ordered_comm_semiring α] : comm_monoid_with_zero (Icc (0:α) 1) :=
{
  mul_comm :=
begin
  refine λ p q, _,
  apply subtype.mk_eq_mk.2,
  apply mul_comm,
end ,

  zero := ⟨0,left_mem_Icc.2 zero_le_one⟩,

  zero_mul :=
begin
  refine λ p, _,
  rcases p with ⟨p1, ⟨p21,p22⟩⟩,
  suffices : (⟨0 * p1, _⟩ : (Icc (0:α) 1)) = ⟨0, _⟩ * ⟨p1, _⟩,
  { rw ←this, simp only [zero_mul] },
  refl,
end ,

  mul_zero :=
begin
  refine λ p, _,
  rcases p with ⟨p1, ⟨p21,p22⟩⟩,
  suffices : (⟨p1 * 0, _⟩ : (Icc (0:α) 1)) = ⟨p1, _⟩ * ⟨0, _⟩,
  {rw ←this, simp only [mul_zero] },
  refl,
end ,

  ..(show monoid (Icc (0:α) 1), by apply_instance)
}



-- Yaël Dillies: What you really should do is provide `comm_monoid_with_zero (Icc 0 1)`. Then you'll get powers for free.  You can also do
-- `comm_semigroup_with_zero (Ico 0 1)`,
-- `comm_monoid (Ioc 0 1)`,
-- `comm_semigroup (Ioo 0 1)`,
-- `comm_monoid_with_zero (Icc (-1) 1)`,
-- `comm_monoid_with_zero (Ioc (-1) 1`,
-- `comm_semigroup_with_zero (Ioo (-1) 1)`,
-- and also provide `has_distrib_neg` instances where applicable.
