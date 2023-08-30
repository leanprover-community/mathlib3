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

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

lemma ι_mul_ι_mem_even_odd_zero (m₁ m₂ : M) :
  ι Q m₁ * ι Q m₂ ∈ even_odd Q 0 :=
submodule.mem_supr_of_mem ⟨2, rfl⟩ begin
  rw [subtype.coe_mk, pow_two],
  exact submodule.mul_mem_mul (linear_map.mem_range_self (ι Q) m₁)
    (linear_map.mem_range_self (ι Q) m₂)
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
  rw [graded_algebra.ι_apply Q, direct_sum.of_mul_of, direct_sum.algebra_map_apply],
  refine direct_sum.of_eq_of_graded_monoid_eq (sigma.subtype_ext rfl $ ι_sq_scalar _ _),
end

lemma graded_algebra.lift_ι_eq (i' : zmod 2) (x' : even_odd Q i') :
  lift Q ⟨by apply graded_algebra.ι Q, graded_algebra.ι_sq_scalar Q⟩ x' =
    direct_sum.of (λ i, even_odd Q i) i' x' :=
begin
  cases x' with x' hx',
  dsimp only [subtype.coe_mk, direct_sum.lof_eq_of],
  refine submodule.supr_induction' _ (λ i x hx, _) _ (λ x y hx hy ihx ihy, _) hx',
  { obtain ⟨i, rfl⟩ := i,
    dsimp only [subtype.coe_mk] at hx,
    refine submodule.pow_induction_on_left' _
      (λ r, _) (λ x y i hx hy ihx ihy, _) (λ m hm i x hx ih, _) hx,
    { rw [alg_hom.commutes, direct_sum.algebra_map_apply], refl },
    { rw [alg_hom.map_add, ihx, ihy, ←map_add], refl },
    { obtain ⟨_, rfl⟩ := hm,
      rw [alg_hom.map_mul, ih, lift_ι_apply, graded_algebra.ι_apply Q, direct_sum.of_mul_of],
      refine direct_sum.of_eq_of_graded_monoid_eq (sigma.subtype_ext _ _);
        dsimp only [graded_monoid.mk, subtype.coe_mk],
      { rw [nat.succ_eq_add_one, add_comm, nat.cast_add, nat.cast_one] },
      refl } },
  { rw alg_hom.map_zero,
    apply eq.symm,
    apply dfinsupp.single_eq_zero.mpr, refl, },
  { rw [alg_hom.map_add, ihx, ihy, ←map_add], refl },
end

/-- The clifford algebra is graded by the even and odd parts. -/
instance graded_algebra : graded_algebra (even_odd Q) :=
graded_algebra.of_alg_hom (even_odd Q)
  -- while not necessary, the `by apply` makes this elaborate faster
  (lift Q ⟨by apply graded_algebra.ι Q, graded_algebra.ι_sq_scalar Q⟩)
  -- the proof from here onward is mostly similar to the `tensor_algebra` case, with some extra
  -- handling for the `supr` in `even_odd`.
  (begin
    ext m,
    dsimp only [linear_map.comp_apply, alg_hom.to_linear_map_apply, alg_hom.comp_apply,
      alg_hom.id_apply],
    rw [lift_ι_apply, graded_algebra.ι_apply Q, direct_sum.coe_alg_hom_of, subtype.coe_mk],
  end)
  (by apply graded_algebra.lift_ι_eq Q)

lemma supr_ι_range_eq_top : (⨆ i : ℕ, (ι Q).range ^ i) = ⊤ :=
begin
  rw [← (direct_sum.decomposition.is_internal (even_odd Q)).submodule_supr_eq_top, eq_comm],
  calc    (⨆ (i : zmod 2) (j : {n // ↑n = i}), (ι Q).range ^ ↑j)
        = (⨆ (i : Σ i : zmod 2, {n : ℕ // ↑n = i}), (ι Q).range ^ (i.2 : ℕ)) : by rw supr_sigma
    ... = (⨆ (i : ℕ), (ι Q).range ^ i)
        : function.surjective.supr_congr (λ i, i.2) (λ i, ⟨⟨_, i, rfl⟩, rfl⟩) (λ _, rfl),
end

lemma even_odd_is_compl : is_compl (even_odd Q 0) (even_odd Q 1) :=
(direct_sum.decomposition.is_internal (even_odd Q)).is_compl zero_ne_one $ begin
  have : (finset.univ : finset (zmod 2)) = {0, 1} := rfl,
  simpa using congr_arg (coe : finset (zmod 2) → set (zmod 2)) this,
end

/-- To show a property is true on the even or odd part, it suffices to show it is true on the
scalars or vectors (respectively), closed under addition, and under left-multiplication by a pair
of vectors. -/
@[elab_as_eliminator]
lemma even_odd_induction (n : zmod 2) {P : Π x, x ∈ even_odd Q n → Prop}
  (hr : ∀ v (h : v ∈ (ι Q).range ^ n.val),
    P v (submodule.mem_supr_of_mem ⟨n.val, n.nat_cast_zmod_val⟩ h))
  (hadd : ∀ {x y hx hy}, P x hx → P y hy → P (x + y) (submodule.add_mem _ hx hy))
  (hιι_mul : ∀ m₁ m₂ {x hx}, P x hx → P (ι Q m₁ * ι Q m₂ * x)
    (zero_add n ▸ set_like.mul_mem_graded (ι_mul_ι_mem_even_odd_zero Q m₁ m₂) hx))
  (x : clifford_algebra Q) (hx : x ∈ even_odd Q n) : P x hx :=
begin
  apply submodule.supr_induction' _ _ (hr 0 (submodule.zero_mem _)) @hadd,
  refine subtype.rec _,
  simp_rw [subtype.coe_mk, zmod.nat_coe_zmod_eq_iff, add_comm n.val],
  rintros n' ⟨k, rfl⟩ xv,
  simp_rw [pow_add, pow_mul],
  refine submodule.mul_induction_on' _ _,
  { intros a ha b hb,
    refine submodule.pow_induction_on_left' ((ι Q).range ^ 2) _ _ _ ha,
    { intro r,
      simp_rw ←algebra.smul_def,
      exact hr _ (submodule.smul_mem _ _ hb), },
    { intros x y n hx hy,
      simp_rw add_mul,
      apply hadd, },
    { intros x hx n y hy ihy,
      revert hx,
      simp_rw pow_two,
      refine submodule.mul_induction_on' _ _,
      { simp_rw linear_map.mem_range,
        rintros _ ⟨m₁, rfl⟩ _ ⟨m₂, rfl⟩,
        simp_rw mul_assoc _ y b,
        refine hιι_mul _ _ ihy, },
      { intros x hx y hy ihx ihy,
        simp_rw add_mul,
        apply hadd ihx ihy } } },
  { intros x y hx hy,
    apply hadd }
end

/-- To show a property is true on the even parts, it suffices to show it is true on the
scalars, closed under addition, and under left-multiplication by a pair of vectors. -/
@[elab_as_eliminator]
lemma even_induction  {P : Π x, x ∈ even_odd Q 0 → Prop}
  (hr : ∀ r : R, P (algebra_map _ _ r) (set_like.algebra_map_mem_graded _ _))
  (hadd : ∀ {x y hx hy}, P x hx → P y hy → P (x + y) (submodule.add_mem _ hx hy))
  (hιι_mul : ∀ m₁ m₂ {x hx}, P x hx → P (ι Q m₁ * ι Q m₂ * x)
    (zero_add 0 ▸ set_like.mul_mem_graded (ι_mul_ι_mem_even_odd_zero Q m₁ m₂) hx))
  (x : clifford_algebra Q) (hx : x ∈ even_odd Q 0) : P x hx :=
begin
  refine even_odd_induction Q 0 (λ rx, _) @hadd hιι_mul x hx,
  simp_rw [zmod.val_zero, pow_zero],
  rintro ⟨r, rfl⟩,
  exact hr r,
end

/-- To show a property is true on the odd parts, it suffices to show it is true on the
vectors, closed under addition, and under left-multiplication by a pair of vectors. -/
@[elab_as_eliminator]
lemma odd_induction {P : Π x, x ∈ even_odd Q 1 → Prop}
  (hι : ∀ v, P (ι Q v) (ι_mem_even_odd_one _ _))
  (hadd : ∀ {x y hx hy}, P x hx → P y hy → P (x + y) (submodule.add_mem _ hx hy))
  (hιι_mul : ∀ m₁ m₂ {x hx}, P x hx → P (ι Q m₁ * ι Q m₂ * x)
    (zero_add (1 : zmod 2) ▸ set_like.mul_mem_graded (ι_mul_ι_mem_even_odd_zero Q m₁ m₂) hx))
  (x : clifford_algebra Q) (hx : x ∈ even_odd Q 1) : P x hx :=
begin
  refine even_odd_induction Q 1 (λ ιv, _) @hadd hιι_mul x hx,
  simp_rw [zmod.val_one, pow_one],
  rintro ⟨v, rfl⟩,
  exact hι v,
end

end clifford_algebra
