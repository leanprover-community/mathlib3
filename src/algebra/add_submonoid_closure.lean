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

variables [semiring R] {S : submonoid R}

/-- The additive closure of a multiplicative submonoid. -/
def clom (S : submonoid R) := (add_submonoid.closure (S : set R))

/-- An element of a multiplicative submonoid `S` is also an element of the
additive closure of `S`. -/
lemma cl_mem (sa : a ∈ S) : a ∈ clom S :=
add_submonoid.mem_closure.mpr (λ y hy, hy sa)

/-- The additive closure of a multiplicative submonoid contains zero. -/
@[simp] lemma zero_mem (S : submonoid R) : (0 : R) ∈ (clom S) :=
(clom S).zero_mem

/-- The additive closure of a multiplicative submonoid contains one. -/
@[simp] lemma one_mem (S : submonoid R) : (1 : R) ∈ (clom S) :=
cl_mem S.one_mem

/-- The product of an element of the additive closure of a multiplicative submonoid `S`
and an element of `S` is contained in the additive closure of `S`. -/
lemma clom_mul_mem (ha : a ∈ clom S) (hb : b ∈ S) :
  a * b ∈ clom S :=
begin
  revert b,
  refine add_submonoid.closure_induction ha _ _ _; clear ha a,
  { exact λ r hr b hb, cl_mem (S.mul_mem hr hb) },
  { simp },
  { intros r s hr hs b hb,
    rw add_mul,
    exact (clom S).add_mem (hr hb) (hs hb) }
end

/-- The product of two elements of the additive closure of a submonoid `S` is an element of the
additive closure of `S`. -/
lemma mul_mem (ha : a ∈ clom S) (hb : b ∈ clom S) :
  a * b ∈ clom S :=
begin
  revert a,
  refine add_submonoid.closure_induction hb _ _ _; clear hb b,
  { exact λ r hr b hb, clom_mul_mem hb hr },
  { simp only [implies_true_iff, mul_zero, zero_mem] },
  { intros r s hr hs b hb,
    rw mul_add,
    exact (clom S).add_mem (hr hb) (hs hb) }
end

/-- The additive closure of a submonoid is a subsemiring. -/
def fff (S : submonoid R) : subsemiring R :=
{ carrier := clom S,
  one_mem' := one_mem _,
  mul_mem' := λ x y, mul_mem,
  zero_mem' := zero_mem _,
  add_mem' := λ x y, (clom S).add_mem }

/-- A subsemiring is automatically a semiring. -/
instance : semiring (clom S) := subsemiring.to_semiring (fff S)

/-- The elements of the additive closure of a multiplicative submonoid `S` are exactly the
elements of the subsemiring closure of `S`. -/
lemma clss : (clom S).carrier = subsemiring.closure (S : set R) :=
begin
  ext x,
  refine ⟨λ hx, _, λ hx, _⟩,
  { refine subsemiring.mem_coe.mpr _,
    rintros - ⟨H1, rfl⟩,
    rintros - ⟨H2, rfl⟩,
    exact add_submonoid.mem_closure.mp hx H1.to_add_submonoid H2 },
  { refine (subsemiring.mem_closure.mp hx) (fff S) (λ s sS, _),
    rintros - ⟨H1, rfl⟩,
    rintros - ⟨H2, rfl⟩,
    exact H2 sS }
end

end semiring

section comm_semiring

variables [comm_semiring R] {S : submonoid R}

instance : comm_semiring (clom S) := subsemiring.to_comm_semiring (fff S)

end comm_semiring
