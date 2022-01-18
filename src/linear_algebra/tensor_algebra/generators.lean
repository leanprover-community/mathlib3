/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.tensor_algebra.basic
import linear_algebra.direct_sum.basic
import ring_theory.graded_algebra.basic

/-!
# Results about the generators and grading structure of the tensor algebra
-/

namespace tensor_algebra
variables {R M : Type*} [comm_ring R] [add_comm_monoid M] [module R M]

open_locale direct_sum

def to_direct_sum_ι_range : tensor_algebra R M →ₐ[R] (⨁ i : ℕ, ↥((ι R : M →ₗ[_] _).range ^ i)) :=
lift _ $ (direct_sum.lof R ℕ (λ i, ↥((ι R : M →ₗ[_] _).range ^ i)) 1) ∘ₗ (ι R).cod_restrict _
  (λ m, by simpa only [pow_one] using linear_map.mem_range_self _ m)

@[simp] lemma to_direct_sum_ι_range_ι (m : M) :
  to_direct_sum_ι_range (ι R m) =
    direct_sum.of (λ i, ↥((ι R : M →ₗ[_] _).range ^ i)) 1
      (⟨ι R m, by simpa only [pow_one] using linear_map.mem_range_self _ m⟩) :=
lift_ι_apply _ _

instance graded_algebra : graded_algebra (λ i : ℕ, ((ι R : M →ₗ[_] _).range ^ i)) :=
graded_algebra.of_alg_hom to_direct_sum_ι_range
  (begin
    intros i ⟨x, hx⟩,
    apply submodule.pow_induction' _ _ _ hx,
    induction i,
    -- { rw pow_zero at hx,
    --   obtain ⟨r, rfl : algebra_map _ _ r = x⟩ := hx,
    --   rw alg_hom.commutes,
    --   refl, },
    -- { rw pow_succ at hx,
    --   refine submodule.mul_induction_on hx _ _ _ _,
    --   rw submodule.mem_mul },
  end)
  _

lemma supr_ι_range_eq_top : (⨆ i : ℕ, (ι R : M →ₗ[_] _).range ^ i) = ⊤ :=
begin
  rw [submodule.supr_pow_eq_range, algebra.to_submodule_eq_top, algebra.eq_top_iff],
  intro x,
  simp_rw [alg_hom.mem_range, direct_sum.to_algebra_apply],
  induction x using tensor_algebra.induction,
  case h_grade0 : r {
    refine ⟨direct_sum.of _ 0 _, _⟩,
    refine ⟨algebra_map _ _ r, _⟩,
    { simp only [pow_zero, submodule.algebra_map_mem], },
    rw [direct_sum.to_semiring_of],
    refl },
  case h_grade1 : m {
    refine ⟨direct_sum.of _ 1 _, _⟩,
    refine ⟨ι R m, _⟩,
    { simp only [pow_one, linear_map.mem_range_self], },
    rw [direct_sum.to_semiring_of],
    refl },
  case h_add : x y hx hy {
    obtain ⟨fx, rfl⟩ := hx,
    obtain ⟨fy, rfl⟩ := hy,
    exact ⟨_, ring_hom.map_add _ _ _⟩, },
  case h_mul : x y hx hy {
    obtain ⟨fx, rfl⟩ := hx,
    obtain ⟨fy, rfl⟩ := hy,
    exact ⟨_, ring_hom.map_mul _ _ _⟩, },
end

end tensor_algebra
