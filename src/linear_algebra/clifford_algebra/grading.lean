/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.clifford_algebra.basic
import data.zmod.basic
import ring_theory.graded_algebra.basic

/-!
# Results about the grading structure of the clifford algebra

The main result is `clifford_algebra.graded_algebra`, which says that the clifford algebra is a
ℤ₂-graded algebra (or "superalgebra").
-/

namespace clifford_algebra
variables {R M : Type*} [comm_ring R] [add_comm_group M] [module R M]
variables {Q : quadratic_form R M}

open_locale direct_sum

variables (Q)

/-- The even or odd submodule, defined as the supremum of the even or odd powers of
`(ι Q).range`. `even_odd 0` is the even submodule, and `even_odd 1` is the odd submodule. -/
def even_odd (i : zmod 2) : submodule R (clifford_algebra Q) :=
⨆ (j : {n : ℕ // ↑n = i}), (ι Q).range ^ (j : ℕ)

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

lemma ι_mem_even_odd_one (m : M) : ι Q m ∈ even_odd Q 1 :=
range_ι_le_even_odd_one Q $ linear_map.mem_range_self _ m

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
end

instance even_odd.graded_monoid : set_like.graded_monoid (even_odd Q) :=
{ one_mem := submodule.one_le.mp (one_le_even_odd_zero Q),
  mul_mem := λ i j p q hp hq, submodule.mul_le.mp (even_odd_mul_le Q _ _) _ hp _ hq }

/-- A version of `clifford_algebra.ι` that maps directly into the graded structure. This is
primarily an auxiliary construction used to provide `clifford_algebra.graded_algebra`. -/
def graded_algebra.ι : M →ₗ[R] ⨁ i : zmod 2, even_odd Q i :=
direct_sum.lof R (zmod 2) (λ i, ↥(even_odd Q i)) 1 ∘ₗ (ι Q).cod_restrict _ (ι_mem_even_odd_one Q)

lemma graded_algebra.ι_apply (m : M) :
  graded_algebra.ι Q m = direct_sum.of (λ i, ↥(even_odd Q i)) 1 (⟨ι Q m, ι_mem_even_odd_one Q m⟩) :=
rfl

lemma graded_algebra.ι_sq_scalar (m : M) :
  graded_algebra.ι Q m * graded_algebra.ι Q m = algebra_map R _ (Q m) :=
begin
  rw [graded_algebra.ι_apply, direct_sum.of_mul_of, direct_sum.algebra_map_apply],
  refine direct_sum.of_eq_of_graded_monoid_eq (sigma.subtype_ext rfl $ ι_sq_scalar _ _),
end

/-- The clifford algebra is graded by the even and odd parts. -/
instance graded_algebra : graded_algebra (even_odd Q) :=
graded_algebra.of_alg_hom _
  (lift _ $ ⟨graded_algebra.ι Q, graded_algebra.ι_sq_scalar Q⟩)
  -- the proof from here onward is mostly similar to the `tensor_algebra` case, with some extra
  -- handling for the `supr` in `even_odd`.
  (begin
    ext m,
    dsimp only [linear_map.comp_apply, alg_hom.to_linear_map_apply, alg_hom.comp_apply,
      alg_hom.id_apply],
    rw [lift_ι_apply, graded_algebra.ι_apply, direct_sum.submodule_coe_alg_hom_of, subtype.coe_mk],
  end)
  (λ i' x', begin
    cases x' with x' hx',
    dsimp only [subtype.coe_mk, direct_sum.lof_eq_of],
    refine submodule.supr_induction' _ (λ i x hx, _) _ (λ x y hx hy ihx ihy, _) hx',
    { obtain ⟨i, rfl⟩ := i,
      dsimp only [subtype.coe_mk] at hx,
      refine submodule.pow_induction_on' _
        (λ r, _) (λ x y i hx hy ihx ihy, _) (λ m hm i x hx ih, _) hx,
      { rw [alg_hom.commutes, direct_sum.algebra_map_apply], refl },
      { rw [alg_hom.map_add, ihx, ihy, ←map_add], refl },
      { obtain ⟨_, rfl⟩ := hm,
        rw [alg_hom.map_mul, ih, lift_ι_apply, graded_algebra.ι_apply, direct_sum.of_mul_of],
        refine direct_sum.of_eq_of_graded_monoid_eq (sigma.subtype_ext _ _),
          dsimp only [graded_monoid.mk, subtype.coe_mk],
        { rw [nat.succ_eq_add_one, add_comm], refl },
        refl } },
    { rw alg_hom.map_zero,
      apply eq.symm,
      apply dfinsupp.single_eq_zero.mpr, refl, },
    { rw [alg_hom.map_add, ihx, ihy, ←map_add], refl },
  end)

lemma supr_ι_range_eq_top : (⨆ i : ℕ, (ι Q).range ^ i) = ⊤ :=
begin
  rw [← (graded_algebra.is_internal $ λ i, even_odd Q i).supr_eq_top, eq_comm],
  dunfold even_odd,
  calc    (⨆ (i : zmod 2) (j : {n // ↑n = i}), (ι Q).range ^ ↑j)
        = (⨆ (i : Σ i : zmod 2, {n : ℕ // ↑n = i}), (ι Q).range ^ (i.2 : ℕ)) : by rw supr_sigma
    ... = (⨆ (i : ℕ), (ι Q).range ^ i) : supr_congr (λ i, i.2) (λ i, ⟨⟨_, i, rfl⟩, rfl⟩) (λ _, rfl),
end

end clifford_algebra
