import analysis.normed.field.basic
import analysis.normed.group.ball_sphere

open set metric

variables {𝕜 : Type*}

def subsemigroup.unit_ball (𝕜 : Type*) [non_unital_semi_normed_ring 𝕜] :
  subsemigroup 𝕜 :=
{ carrier := ball (0 : 𝕜) 1,
  mul_mem' := λ x y hx hy,
    begin
      rw [mem_ball_zero_iff] at *,
      exact (norm_mul_le x y).trans_lt (mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _)
        hx hy.le)
    end }

instance [non_unital_semi_normed_ring 𝕜] : semigroup (ball (0 : 𝕜) 1) :=
mul_mem_class.to_semigroup (subsemigroup.unit_ball 𝕜)

instance [semi_normed_comm_ring 𝕜] : comm_semigroup (ball (0 : 𝕜) 1) :=
mul_mem_class.to_comm_semigroup (subsemigroup.unit_ball 𝕜)

instance [non_unital_semi_normed_ring 𝕜] : has_distrib_neg (ball (0 : 𝕜) 1) :=
subtype.coe_injective.has_distrib_neg (coe : ball (0 : 𝕜) 1 → 𝕜) (λ _, rfl) (λ _ _, rfl)

def subsemigroup.unit_closed_ball (𝕜 : Type*) [non_unital_semi_normed_ring 𝕜] :
  subsemigroup 𝕜 :=
{ carrier := closed_ball 0 1,
  mul_mem' := λ x y hx hy,
    begin
      rw [mem_closed_ball_zero_iff] at *,
      exact (norm_mul_le x y).trans (mul_le_one hx (norm_nonneg _) hy)
    end }

instance [non_unital_semi_normed_ring 𝕜] : semigroup (closed_ball (0 : 𝕜) 1) :=
mul_mem_class.to_semigroup (subsemigroup.unit_closed_ball 𝕜)

instance [non_unital_semi_normed_ring 𝕜] : has_distrib_neg (closed_ball (0 : 𝕜) 1) :=
subtype.coe_injective.has_distrib_neg (coe : closed_ball (0 : 𝕜) 1 → 𝕜) (λ _, rfl) (λ _ _, rfl)

def submonoid.unit_closed_ball (𝕜 : Type*) [semi_normed_ring 𝕜] [norm_one_class 𝕜] :
  submonoid 𝕜 :=
{ carrier := closed_ball 0 1,
  one_mem' := mem_closed_ball_zero_iff.2 norm_one.le,
  .. subsemigroup.unit_closed_ball 𝕜 }

instance [semi_normed_ring 𝕜] [norm_one_class 𝕜] : monoid (closed_ball (0 : 𝕜) 1) :=
submonoid_class.to_monoid (submonoid.unit_closed_ball 𝕜)

instance [semi_normed_comm_ring 𝕜] [norm_one_class 𝕜] : comm_monoid (closed_ball (0 : 𝕜) 1) :=
submonoid_class.to_comm_monoid (submonoid.unit_closed_ball 𝕜)

def submonoid.unit_sphere (𝕜 : Type*) [normed_division_ring 𝕜] : submonoid 𝕜 :=
{ carrier := sphere (0 : 𝕜) 1,
  mul_mem' := λ x y hx hy, by { rw [mem_sphere_zero_iff_norm] at *, simp * },
  one_mem' := mem_sphere_zero_iff_norm.2 norm_one }

instance [normed_division_ring 𝕜] : monoid (sphere (0 : 𝕜) 1) :=
submonoid_class.to_monoid (submonoid.unit_sphere 𝕜)

instance [normed_field 𝕜] : comm_monoid (sphere (0 : 𝕜) 1) :=
submonoid_class.to_comm_monoid (submonoid.unit_sphere 𝕜)

instance [normed_division_ring 𝕜] : has_distrib_neg (sphere (0 : 𝕜) 1) :=
subtype.coe_injective.has_distrib_neg (coe : sphere (0 : 𝕜) 1 → 𝕜) (λ _, rfl) (λ _ _, rfl)
