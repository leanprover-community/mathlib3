/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.clifford_algebra.basic
import linear_algebra.direct_sum.basic
import data.zmod.basic
import ring_theory.graded_algebra.basic

/-!
# Results about the generators and grading structure of the clifford algebra

Many of these results are copied with minimal modification from the tensor algebra
-/

namespace clifford_algebra
variables {R M : Type*} [comm_ring R] [add_comm_group M] [module R M]
variables {Q : quadratic_form R M}

open_locale direct_sum

variables (Q)

/-- The even and odd submodule, defined as the supremum of the even or odd powers of
`(ι Q).range`. -/
def even_odd (i : zmod 2) : submodule R (clifford_algebra Q) :=
⨆ (j : {n : ℕ // ↑n = i}), (ι Q).range ^ (j : ℕ)
-- Sup ((^) (ι Q).range '' ((coe : ℕ → zmod 2)  ⁻¹' {i}))

lemma one_le_even_odd_zero : 1 ≤ even_odd Q 0 :=
begin
  refine le_trans _ (le_supr _ ⟨0, nat.cast_zero⟩),
  exact (pow_zero _).ge,
end

lemma range_ι_le_even_odd_one : (ι Q).range ≤ even_odd Q 1 :=
begin
  refine le_trans _ (le_supr _ ⟨1, nat.cast_one⟩),
  exact (pow_one _).ge,
end

lemma even_odd_mul_le (i j : zmod 2) : even_odd Q i * even_odd Q j ≤ even_odd Q (i + j) :=
begin
  simp_rw [even_odd, submodule.supr_eq_span, submodule.span_mul_span],
  apply submodule.span_mono,
  intros z hz,
  obtain ⟨x, y, hx, hy, rfl⟩ := hz,
  obtain ⟨xi, hx'⟩ := set.mem_Union.mp hx,
  obtain ⟨yi, hy'⟩ := set.mem_Union.mp hy,
  refine set.mem_Union.mpr ⟨⟨xi + yi, by simp only [nat.cast_add, xi.prop, yi.prop]⟩, _⟩,
  simp only [subtype.coe_mk, nat.cast_add, pow_add],
  exact submodule.mul_mem_mul hx' hy',
  -- obtain rfl | hi := eq_or_ne ↑xi i; [obtain rfl | hj := eq_or_ne ↑yi j, skip];
  --   simp only [eq_self_iff_true, set.Union_true, submodule.span_eq, set_like.mem_coe] at hx' hy' ⊢,
  -- { exact submodule.mul_mem_mul hx' hy', },
  -- { have : y = 0, by simpa [hj] using hy',
  --   rw [this, mul_zero],
  --   exact submodule.zero_mem _, },
  -- { have : x = 0, by simpa [hi] using hx',
  --   rw [this, zero_mul],
  --   exact submodule.zero_mem _, },
end


instance even_odd.graded_monoid : set_like.graded_monoid (even_odd Q) :=
{ one_mem := submodule.one_le.mp (one_le_even_odd_zero Q),
  mul_mem := λ i j p q hp hq, submodule.mul_le.mp (even_odd_mul_le Q _ _) _ hp _ hq }

/-- A version of `exterior_algebra.ι` that maps directly into the graded structure. This is
primarily an auxiliary construction used to provide `exterior_algebra.graded_algebra`. -/
def graded_algebra.ι : M →ₗ[R] ⨁ i : zmod 2, even_odd Q i :=
direct_sum.lof R (zmod 2) (λ i, ↥(even_odd Q i)) 1
  ∘ₗ (ι Q).cod_restrict _ (λ m, range_ι_le_even_odd_one Q $ linear_map.mem_range_self _ m)

lemma graded_algebra.ι_apply (m : M) :
  graded_algebra.ι Q m =
    direct_sum.of (λ i, ↥(even_odd Q i)) 1
      (⟨ι Q m, range_ι_le_even_odd_one Q $ linear_map.mem_range_self _ m⟩) := rfl

lemma graded_algebra.ι_sq_scalar (m : M) :
  graded_algebra.ι Q m * graded_algebra.ι Q m = algebra_map R _ (Q m) :=
begin
  rw [graded_algebra.ι_apply, direct_sum.of_mul_of, direct_sum.algebra_map_apply],
  refine direct_sum.of_eq_of_graded_monoid_eq (sigma.subtype_ext rfl $ ι_sq_scalar _ _),
end

/-- The exterior algebra is graded by the powers of the submodule `(exterior_algebra.ι R).range`. -/
instance graded_algebra :
  graded_algebra (even_odd Q) :=
graded_algebra.of_alg_hom _
  (lift _ $ ⟨graded_algebra.ι Q, graded_algebra.ι_sq_scalar Q⟩)
  -- the proof from here onward is identical to the `tensor_algebra` case
  (begin
    ext m,
    dsimp only [linear_map.comp_apply, alg_hom.to_linear_map_apply, alg_hom.comp_apply,
      alg_hom.id_apply],
    rw [lift_ι_apply, graded_algebra.ι_apply, direct_sum.submodule_coe_alg_hom_of, subtype.coe_mk],
  end)
  (λ i x, begin
    cases x with x hx,
    dsimp only [subtype.coe_mk, direct_sum.lof_eq_of],
    simp_rw [even_odd, submodule.supr_eq_span] at hx,
    sorry,
    -- apply submodule.pow_induction_on' _
    --   (λ r, _) (λ x y i hx hy ihx ihy, _) (λ m hm i x hx ih, _) hx,
    -- { rw [alg_hom.commutes, direct_sum.algebra_map_apply], refl },
    -- { rw [alg_hom.map_add, ihx, ihy, ←map_add], refl },
    -- { obtain ⟨_, rfl⟩ := hm,
    --   rw [alg_hom.map_mul, ih, lift_ι_apply, graded_algebra.ι_apply, direct_sum.of_mul_of],
    --   exact direct_sum.of_eq_of_graded_monoid_eq (sigma.subtype_ext (add_comm _ _) rfl) }
  end)

lemma supr_ι_range_eq_top : (⨆ i : ℕ, (ι Q).range ^ i) = ⊤ :=
begin
  rw [submodule.supr_pow_eq_top_iff, subsemiring.eq_top_iff'],
  intro x,
  rw ring_hom.mem_srange,
  induction x using clifford_algebra.induction,
  case h_grade0 : r {
    refine ⟨direct_sum.of _ 0 _, _⟩,
    refine ⟨algebra_map _ _ r, _⟩,
    { simp only [pow_zero, submodule.mem_one, exists_apply_eq_apply], },
    rw [direct_sum.to_semiring_of],
    refl },
  case h_grade1 : m {
    refine ⟨direct_sum.of _ 1 _, _⟩,
    refine ⟨ι Q m, _⟩,
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

end clifford_algebra
