/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import ring_theory.subsemiring

/-!
#  Equality between `add_submonoid.closure S` and `subsemiring.closure S`

Let `R` be a semiring and let `S` be a multiplicative submonoid of `R`.
The additive closure of `S` is a subsemiring of `R`.  If `R` is commutative, then so
is the additive closure of `S`.
-/
variables {R : Type*} {a b : R}

section semiring

variables [semiring R] (S : submonoid R)

/-- The product of an element of the additive closure of a multiplicative submonoid `S`
and an element of `S` is contained in the additive closure of `S`. -/
lemma submonoid.mul_mem_add_closure (ha : a ∈ add_submonoid.closure (S : set R)) (hb : b ∈ S) :
  a * b ∈ add_submonoid.closure (S : set R) :=
begin
  revert b,
  refine add_submonoid.closure_induction ha _ _ _; clear ha a,
  { exact λ r hr b hb, add_submonoid.mem_closure.mpr (λ y hy, hy (S.mul_mem hr hb)) },
  { exact λ b hb, by simp only [zero_mul, (add_submonoid.closure (S : set R)).zero_mem] },
  { simp_rw add_mul,
    exact λ r s hr hs b hb, (add_submonoid.closure (S : set R)).add_mem (hr hb) (hs hb) }
end

/-- The product of an element of `S` and an element of the additive closure of a multiplicative
submonoid `S` is contained in the additive closure of `S`. -/
lemma submonoid.mem_add_closure_mul (ha : a ∈ S) (hb : b ∈ add_submonoid.closure (S : set R)) :
  a * b ∈ add_submonoid.closure (S : set R) :=
begin
  revert a,
  refine add_submonoid.closure_induction hb _ _ _; clear hb b,
  { exact λ r hr b hb, add_submonoid.mem_closure.mpr (λ y hy, hy (S.mul_mem hb hr)) },
  { exact λ b hb, by simp only [mul_zero, (add_submonoid.closure (S : set R)).zero_mem] },
  { simp_rw mul_add,
    exact λ r s hr hs b hb, (add_submonoid.closure (S : set R)).add_mem (hr hb) (hs hb) }
end

variable {S}

/-- The product of two elements of the additive closure of a submonoid `S` is an element of the
additive closure of `S`. -/
lemma mul_mem
  (ha : a ∈ add_submonoid.closure (S : set R)) (hb : b ∈ add_submonoid.closure (S : set R)) :
  a * b ∈ add_submonoid.closure (S : set R) :=
begin
  revert a,
  refine add_submonoid.closure_induction hb _ _ _; clear hb b,
  { exact λ r hr b hb, S.mul_mem_add_closure hb hr },
  { exact λ b hb, by simp only [mul_zero, (add_submonoid.closure (S : set R)).zero_mem] },
  { simp_rw mul_add,
    exact λ r s hr hs b hb, (add_submonoid.closure (S : set R)).add_mem (hr hb) (hs hb) }
end

/-- The additive closure of a submonoid is a subsemiring. -/
def submonoid.to_subsemiring (S : submonoid R) : subsemiring R :=
{ one_mem' := add_submonoid.mem_closure.mpr (λ y hy, hy S.one_mem),
  mul_mem' := λ x y, mul_mem,
  ..add_submonoid.closure (S : set R)}

lemma to_subsemiring_coe : (S.to_subsemiring : set R) = add_submonoid.closure (S : set R) := rfl

lemma to_subsemiring_to_add_submonoid :
  S.to_subsemiring.to_add_submonoid = add_submonoid.closure (S : set R) := rfl

/-- The elements of the additive closure of a multiplicative submonoid `S` are exactly the
elements of the subsemiring closure of `S`. -/
lemma clss : (add_submonoid.closure (S : set R) : set R) = subsemiring.closure (S : set R) :=
by ext; simp [subsemiring.mem_closure_iff]

end semiring
