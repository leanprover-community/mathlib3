/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import ring_theory.subsemiring

/-!
#  Equality between `add_submonoid.closure M` and `subsemiring.closure M`

Let `R` be a semiring and let `M` be a multiplicative submonoid of `R`.
The additive closure of `M` is a subsemiring of `R`.  If `R` is commutative, then so
is the additive closure of `M`.
-/
variables {R : Type*} {a b : R}

section add_closure_of_submonoid

variables [semiring R] (M : submonoid R)

/-- The product of an element of the additive closure of a multiplicative submonoid `M`
and an element of `M` is contained in the additive closure of `M`. -/
lemma submonoid.mul_right_mem_add_closure
  (ha : a ∈ add_submonoid.closure (M : set R)) (hb : b ∈ M) :
  a * b ∈ add_submonoid.closure (M : set R) :=
begin
  revert b,
  refine add_submonoid.closure_induction ha _ _ _; clear ha a,
  { exact λ r hr b hb, add_submonoid.mem_closure.mpr (λ y hy, hy (M.mul_mem hr hb)) },
  { exact λ b hb, by simp only [zero_mul, (add_submonoid.closure (M : set R)).zero_mem] },
  { simp_rw add_mul,
    exact λ r s hr hs b hb, (add_submonoid.closure (M : set R)).add_mem (hr hb) (hs hb) }
end

/-- The product of an element of `M` and an element of the additive closure of a multiplicative
submonoid `M` is contained in the additive closure of `M`. -/
lemma submonoid.mul_left_mem_add_closure (ha : a ∈ M) (hb : b ∈ add_submonoid.closure (M : set R)) :
  a * b ∈ add_submonoid.closure (M : set R) :=
begin
  revert a,
  refine add_submonoid.closure_induction hb _ _ _; clear hb b,
  { exact λ r hr b hb, add_submonoid.mem_closure.mpr (λ y hy, hy (M.mul_mem hb hr)) },
  { exact λ b hb, by simp only [mul_zero, (add_submonoid.closure (M : set R)).zero_mem] },
  { simp_rw mul_add,
    exact λ r s hr hs b hb, (add_submonoid.closure (M : set R)).add_mem (hr hb) (hs hb) }
end

variable {M}

/-- The product of two elements of the additive closure of a submonoid `M` is an element of the
additive closure of `M`. -/
lemma submonoid.mul_mem_add_closure
  (ha : a ∈ add_submonoid.closure (M : set R)) (hb : b ∈ add_submonoid.closure (M : set R)) :
  a * b ∈ add_submonoid.closure (M : set R) :=
begin
  revert a,
  refine add_submonoid.closure_induction hb _ _ _; clear hb b,
  { exact λ r hr b hb, M.mul_right_mem_add_closure hb hr },
  { exact λ b hb, by simp only [mul_zero, (add_submonoid.closure (M : set R)).zero_mem] },
  { simp_rw mul_add,
    exact λ r s hr hs b hb, (add_submonoid.closure (M : set R)).add_mem (hr hb) (hs hb) }
end

/-- The additive closure of a submonoid is a subsemiring. -/
def submonoid.to_subsemiring (M : submonoid R) : subsemiring R :=
{ one_mem' := add_submonoid.mem_closure.mpr (λ y hy, hy M.one_mem),
  mul_mem' := λ x y, submonoid.mul_mem_add_closure,
  ..add_submonoid.closure (M : set R)}

lemma subsemiring.to_subsemiring_coe :
  (M.to_subsemiring : set R) = add_submonoid.closure (M : set R) := rfl

lemma subsemiring.to_subsemiring_to_add_submonoid :
  M.to_subsemiring.to_add_submonoid = add_submonoid.closure (M : set R) := rfl

/-- The elements of the additive closure of a multiplicative submonoid `M` are exactly the
elements of the subsemiring closure of `M`. -/
lemma subsemiring.clss : (add_submonoid.closure (M : set R) : set R) = subsemiring.closure (M : set R) :=
begin
  refine set.ext (λ x, ⟨λ hx, _, λ hx, _⟩),
  { refine subsemiring.mem_coe.mpr _,
    rintros - ⟨H1, rfl⟩,
    rintros - ⟨H2, rfl⟩,
    exact add_submonoid.mem_closure.mp hx H1.to_add_submonoid H2 },
  { refine (subsemiring.mem_closure.mp hx) M.to_subsemiring (λ s sM, _),
    rintros - ⟨H1, rfl⟩,
    rintros - ⟨H2, rfl⟩,
    exact H2 sM }
end

open subsemiring

lemma subsemiring.mem_closure_iff {s : set R} {x} :
  x ∈ closure s ↔ x ∈ add_submonoid.closure (submonoid.closure s : set R) :=
begin
  erw [← add_submonoid.mem_coe, clss],
  refine ⟨λ hx, closure_mono (submonoid.subset_closure) hx, λ hx, (mem_closure.mp hx) _ _⟩,
  exact λ y hy, (submonoid.mem_closure.mp hy) (subsemiring.to_submonoid (closure s)) subset_closure
end


end add_closure_of_submonoid
