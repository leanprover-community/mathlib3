/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Eric Wieser, Jujian Zhang
-/
import ring_theory.graded_algebra.homogeneous_ideal
import data.zmod.basic
import tactic.derive_fintype

/-!
# A homogeneous prime that is homogeneously prime but not prime

In `src/ring_theory/graded_algebra/radical.lean`,  we assumed that the underline grading is indexed
by a `linear_ordered_cancel_add_comm_monoid` to prove that a homogeneous ideal is prime if and only
if it is homogeneously prime. This file is aimed to show that even if this assumption isn't strictly
necessary, the assumption of "being cancellative" is. We construct a counterexample where the
underlying indexing set is a `linear_ordered_add_comm_monoid` but is not cancellative and the
statement is false.

We achieve this by considering the ring `R=ℤ/4ℤ`. We first give the two element set `ι = {0, 1}` a
structure of linear ordered additive commutative monoid by setting `0 + 0 = 0` and `_ + _ = 1` and
`0 < 1`. Then we use `ι` to grade `R²` by setting `{(a, a) | a ∈ R}` to have grade `0`; and
`{(0, b) | b ∈ R}` to have grade 1. Then the ideal `I = span {(0, 2)} ⊆ ℤ/4ℤ` is homogeneous and not
prime. But it is homogeneously prime, i.e. if `(a, b), (c, d)` are two homogeneous elements then
`(a, b) * (c, d) ∈ I` implies either `(a, b) ∈ I` or `(c, d) ∈ I`.


## Tags

homogeneous, prime
-/

namespace counterexample_not_prime_but_homogeneous_prime

open direct_sum
local attribute [reducible] with_zero

abbreviation two := with_zero unit

instance : linear_ordered_add_comm_monoid two :=
{ add_le_add_left := by delta two with_zero; dec_trivial,
  ..(_ : linear_order two),
  ..(_ : add_comm_monoid two)}

section

variables (R : Type*) [comm_ring R]

/-- The grade 0 part of `R²` is `{(a, a) | a ∈ R}`. -/
def submodule_z : submodule R (R × R) :=
{ carrier := { zz | zz.1 = zz.2 },
  zero_mem' := rfl,
  add_mem' := λ a b ha hb, congr_arg2 (+) ha hb,
  smul_mem' := λ a b hb, congr_arg ((*) a) hb }

/-- The grade 1 part of `R²` is `{(0, b) | b ∈ R}`. -/
def submodule_o : submodule R (R × R) := (linear_map.fst R R R).ker

/-- Given the above grading (see `submodule_z` and `submodule_o`),
  we turn `R²` into a graded ring. -/
def grading : two → submodule R (R × R)
| 0 := submodule_z R
| 1 := submodule_o R

lemma grading.one_mem : (1 : (R × R)) ∈ grading R 0 :=
eq.refl (1, 1).fst

lemma grading.mul_mem : ∀ ⦃i j : two⦄ {a b : (R × R)} (ha : a ∈ grading R i) (hb : b ∈ grading R j),
  a * b ∈ grading R (i + j)
| 0 0 a b (ha : a.1 = a.2) (hb : b.1 = b.2) := show a.1 * b.1 = a.2 * b.2, by rw [ha, hb]
| 0 1 a b (ha : a.1 = a.2) (hb : b.1 = 0)   := show a.1 * b.1 = 0, by rw [hb, mul_zero]
| 1 0 a b (ha : a.1 = 0) hb                 := show a.1 * b.1 = 0, by rw [ha, zero_mul]
| 1 1 a b (ha : a.1 = 0) hb                 := show a.1 * b.1 = 0, by rw [ha, zero_mul]

end

local notation `R` := zmod 4

/-- `R² ≅ {(a, a) | a ∈ R} ⨁ {(0, b) | b ∈ R}` by `(x, y) ↦ (x, x) + (0, y - x)`. -/
def grading.decompose : (R × R) →+ direct_sum two (λ i, grading R i) :=
{ to_fun := λ zz, of (λ i, grading R i) 0 ⟨(zz.1, zz.1), rfl⟩ +
    of (λ i, grading R i) 1 ⟨(0, zz.2 - zz.1), rfl⟩,
  map_zero' := by { ext1 (_|⟨⟨⟩⟩); refl },
  map_add' := begin
    rintros ⟨a1, b1⟩ ⟨a2, b2⟩,
    rw [add_add_add_comm, ←map_add, ←map_add],
    dsimp only [prod.mk_add_mk],
    simp_rw [add_sub_add_comm],
    congr,
  end }

lemma grading.right_inv :
  function.right_inverse (coe_linear_map (grading R)) grading.decompose := λ zz,
begin
  induction zz using direct_sum.induction_on with i zz d1 d2 ih1 ih2,
  { simp only [map_zero],},
  { rcases i with (_|⟨⟨⟩⟩); rcases zz with ⟨⟨a, b⟩, (hab : _ = _)⟩;
    dsimp at hab; cases hab; dec_trivial! },
  { simp only [map_add, ih1, ih2], },
end

lemma grading.left_inv :
  function.left_inverse (coe_linear_map (grading R)) grading.decompose := λ zz,
begin
  cases zz with a b,
  unfold grading.decompose,
  simp only [add_monoid_hom.coe_mk, map_add, coe_linear_map_of, subtype.coe_mk, prod.mk_add_mk,
    add_zero, add_sub_cancel'_right],
end

instance : graded_algebra (grading R) :=
{ one_mem := grading.one_mem R,
  mul_mem := grading.mul_mem R,
  decompose' := grading.decompose,
  left_inv := by { convert grading.left_inv, },
  right_inv := by { convert grading.right_inv, } }

/-- The counterexample is the ideal `I = span {(2, 2)}`. -/
def I : ideal (R × R) := ideal.span {((2, 2) : (R × R))}.

set_option class.instance_max_depth 34

lemma I_not_prime : ¬ I.is_prime :=
begin
  rintro ⟨rid1, rid2⟩,
  apply rid1, clear rid1, revert rid2,
  simp only [I, ideal.mem_span_singleton, ideal.eq_top_iff_one],
  dec_trivial, -- this is what we change the max instance depth for, it's only 2 above the default
end

set_option class.instance_max_depth 32

lemma I_is_homogeneous : I.is_homogeneous (grading R) :=
begin
  rw ideal.is_homogeneous.iff_exists,
  refine ⟨{⟨(2, 2), ⟨0, rfl⟩⟩}, _⟩,
  rw set.image_singleton,
  refl,
end

lemma homogeneous_mem_or_mem {x y : (R × R)} (hx : set_like.is_homogeneous (grading R) x)
  (hy : set_like.is_homogeneous (grading R) y)
  (hxy : x * y ∈ I) : x ∈ I ∨ y ∈ I :=
begin
  simp only [I, ideal.mem_span_singleton] at hxy ⊢,
  cases x, cases y,
  obtain ⟨(_|⟨⟨⟩⟩), hx : _ = _⟩ := hx;
  obtain ⟨(_|⟨⟨⟩⟩), hy : _ = _⟩ := hy;
  dsimp at hx hy;
  cases hx; cases hy; clear hx hy;
  dec_trivial!,
end

end counterexample_not_prime_but_homogeneous_prime
