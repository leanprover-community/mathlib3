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

lemma to_direct_sum_ι_range_coe (i : ℕ) (x : ↥((ι R : M →ₗ[_] _).range ^ i)) :
  to_direct_sum_ι_range (x : tensor_algebra R M) =
    direct_sum.of (λ (i : ℕ), ↥((ι R).range ^ i)) i x :=
begin
  cases x with x hx,
  dsimp only [subtype.coe_mk],
  apply submodule.pow_induction_on' _ (λ r, _) (λ x y i hx hy ihx ihy, _) (λ m hm i x hx ih, _) hx,
  { rw alg_hom.commutes, refl },
  { rw [alg_hom.map_add, ihx, ihy, ←map_add], refl },
  obtain ⟨_, rfl⟩ := hm,
  rw [alg_hom.map_mul, ih, to_direct_sum_ι_range_ι, direct_sum.of_mul_of],
  apply direct_sum.of_eq_of_graded_monoid_eq,
  sorry
end

lemma submodule_coe_alg_hom_comp_to_direct_sum_ι_range :
  (direct_sum.submodule_coe_alg_hom ((^) (ι R : M →ₗ[R] _).range : ℕ → submodule R _)).comp
    to_direct_sum_ι_range = alg_hom.id R (tensor_algebra R M) :=
begin
  ext m,
  dsimp,
  rw [to_direct_sum_ι_range_ι, direct_sum.submodule_coe_alg_hom_of, subtype.coe_mk],
end

instance graded_algebra : graded_algebra ((^) (ι R : M →ₗ[R] _).range : ℕ → submodule R _) :=
begin
  refine graded_algebra.of_alg_hom _ (show tensor_algebra R M →ₐ[R] _, from to_direct_sum_ι_range) _ _,
  swap,
  dsimp,
  -- convert submodule_coe_alg_hom_comp_to_direct_sum_ι_range using 1,
  -- change _ = ι R m,
  -- dsimp,
  -- rw [to_direct_sum_ι_range_ι],
  -- exact (to_direct_sum_ι_range : tensor_algebra R M →ₐ[R] (⨁ i : ℕ, ↥((ι R : M →ₗ[_] _).range ^ i)))
  -- { sorry },
  -- { sorry }
end
-- graded_algebra.of_alg_hom _
--   (to_direct_sum_ι_range : tensor_algebra R M →ₐ[R] _)
--   (begin
--     rintros i ⟨x, hx⟩,
--     -- apply submodule.pow_induction' _ _ _ hx,
--     -- induction i,
--     -- { rw pow_zero at hx,
--     --   obtain ⟨r, rfl : algebra_map _ _ r = x⟩ := hx,
--     --   rw alg_hom.commutes,
--     --   refl, },
--     -- { rw pow_succ at hx,
--     --   refine submodule.mul_induction_on hx _ _ _ _,
--     --   rw submodule.mem_mul },
--   end)
--   _

#exit

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
