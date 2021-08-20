/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.tensor_algebra.basic
import linear_algebra.direct_sum.basic

/-!
# Results about the generators and grading structure of the tensor algebra
-/

namespace tensor_algebra
variables {R M : Type*} [comm_ring R] [add_comm_monoid M] [module R M]

lemma supr_ι_range_eq_top : (⨆ i : ℕ, (ι R : M →ₗ[_] _).range ^ i) = ⊤ :=
begin
  rw [submodule.supr_pow_eq_top_iff, subsemiring.eq_top_iff'],
  intro x,
  rw ring_hom.mem_srange,
  induction x using tensor_algebra.induction,
  case h_grade0 : r {
    refine ⟨direct_sum.of _ 0 _, _⟩,
    refine ⟨algebra_map _ _ r, _⟩,
    { simp only [pow_zero, submodule.mem_one, exists_apply_eq_apply], },
    rw [direct_sum.to_semiring_of],
    refl },
  case h_grade1 : m {
    refine ⟨direct_sum.of _ 1 _, _⟩,
    refine ⟨ι R m, _⟩,
    { simp only [pow_one, linear_map.mem_range, exists_apply_eq_apply], },
    rw [direct_sum.to_semiring_of],
    refl },
  case h_add : x y hx hy {
    obtain ⟨fx, rfl⟩ := hx,
    obtain ⟨fy, rfl⟩ := hy,
    rw ←ring_hom.map_add,
    exact ⟨_, rfl⟩, },
  case h_mul : x y hx hy {
    obtain ⟨fx, rfl⟩ := hx,
    obtain ⟨fy, rfl⟩ := hy,
    rw ←ring_hom.map_mul,
    exact ⟨_, rfl⟩, },
end

end tensor_algebra
