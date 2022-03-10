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

In `src/ring_theory/graded_algebra/radical.lean`,  we assumed that the underline grading is inedxed
by a `linear_ordered_cancel_add_comm_monoid` to prove that a homogeneous ideal is prime if and only
if it is homogeneously prime. This file is aimed to show that even if this assumption isn't strictly
necessary, the assumption of "being cancellative" is. We construct a counterexample where the
underlying indexing set is a `linear_ordered_add_comm_monoid` but is not cancellative and the
statement is false.

We first give the two element set `ι = {0, 1}` a structure of linear ordered additive commutative
monoid by setting `0 + 0 = 0` and `_ + _ = 1` and `0 < 1`. Then we use `ι` to grade `R²` by
setting `{(a, a) | a ∈ R}` to have grade `0`; and `{(0, b) | b ∈ R}` to have grade 1. Then the ideal
`I = span {(0, 2)}` is certainly homogeneous and not prime. But it is also homogeneously prime, i.e.
if `(a, b), (c, d)` are two homogeneous elements then `(a, b) * (c, d) ∈ I` implies either
`(a, b) ∈ I` or `(c, d) ∈ I`.


## Tags

homogeneous, prime
-/

namespace counterexample_not_prime_but_homogeneous_prime

open direct_sum
local attribute [reducible] with_zero

@[derive [add_comm_monoid, linear_order, has_one]]
abbreviation two := with_zero unit

instance : linear_ordered_add_comm_monoid two :=
{ add_le_add_left := by delta two with_zero; dec_trivial,
  ..(_ : linear_order two),
  ..(_ : add_comm_monoid two)}

section

variables (R : Type*) [comm_ring R]

/--
The grade 0 part of `R²` is `{(a, a) | a ∈ R}`.
-/
def submodule_z : submodule R (R × R) :=
{ carrier := { zz | zz.1 = zz.2 },
  zero_mem' := rfl,
  add_mem' := λ a b ha hb, congr_arg2 (+) ha hb,
  smul_mem' := λ a b hb, congr_arg ((*) a) hb }

/--
The grade 1 part of `R²` is `{(0, b) | b ∈ R}`.
-/
def submodule_o : submodule R (R × R) :=
{ carrier := { zz | zz.1 = 0 },
  zero_mem' := rfl,
  add_mem' := λ a b (ha : a.1 = 0) (hb : b.1 = 0), show a.1 + b.1 = 0, by rw [ha, hb, zero_add],
  smul_mem' := λ a b (hb : b.1 = 0), show a * b.1 = 0, by rw [hb, mul_zero] }

/--
Give the above grading (see `submodule_z` and `submodule_o`), we turn `R²` into a graded ring.
-/
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

notation `R` := zmod 4

/--
`R² ≅ {(a, a) | a ∈ R} ⨁ {(0, b) | b ∈ R}` by `(x, y) ↦ (x, x) + (0, y - x)`.
-/
def grading.decompose : (R × R) →+ direct_sum two (λ i, grading R i) :=
{ to_fun := λ zz, of (λ i, grading R i) 0 ⟨(zz.1, zz.1), rfl⟩ +
    of (λ i, grading R i) 1 ⟨(0, zz.2 - zz.1), rfl⟩,
  map_zero' := by { ext1 (_|i), refl, cases i, refl },
  map_add' := begin
    rintros ⟨a1, b1⟩ ⟨a2, b2⟩,
    have aux0 : (none : two) = 0 := rfl,
    have aux1 : ∀ i : unit, (some i : two) = 1, { rintro ⟨⟩, refl },
    ext (_|_) : 3; try { rw [aux0] }; try { rw[aux1] };
    simp only [prod.fst_add, prod.snd_add, add_apply, of_eq_same, add_zero, zero_add,
      submodule.coe_add, subtype.coe_mk, prod.mk_add_mk];
    repeat { erw [of_eq_of_ne] };
    try { apply option.no_confusion };
    simp only [submodule.coe_zero, prod.fst_zero, prod.snd_zero, fin.add_zero, zero_add],
    ext : 2;
    simp only [prod.mk_add_mk, submodule.coe_add, subtype.coe_mk, fin.zero_add],
    abel,
  end }

lemma grading.left_inv :
  function.left_inverse grading.decompose (submodule_coe (grading R)) := λ zz,
begin
  induction zz using direct_sum.induction_on with i zz d1 d2 ih1 ih2,
  { simp only [map_zero],},
  { rcases i with (_|i); try { cases i };
    rcases zz with ⟨⟨a, b⟩, (hab : _ = _)⟩;
    dsimp at hab; cases hab; dec_trivial!, },
  { simp only [map_add, ih1, ih2], },
end

lemma grading.right_inv :
  function.right_inverse grading.decompose (submodule_coe (grading R)) := λ zz,
begin
  cases zz with a b,
  unfold grading.decompose,
  simp only [add_monoid_hom.coe_mk, map_add, submodule_coe_of, subtype.coe_mk, prod.mk_add_mk,
    add_zero, add_sub_cancel'_right],
end

instance : graded_algebra (grading R) :=
{ one_mem := grading.one_mem R,
  mul_mem := grading.mul_mem R,
  decompose' := grading.decompose,
  left_inv := by { convert grading.left_inv, },
  right_inv := by { convert grading.right_inv, } }

/--
The counterexample is the ideal `I = span {(2, 2)}`.
-/
def I : ideal (R × R) := ideal.span {((2, 2) : (R × R))}.

lemma I_not_prime : ¬ I.is_prime :=
begin
  rintro ⟨rid1, rid2⟩,
  apply rid1, clear rid1, revert rid2,
  simp only [I, ideal.mem_span_singleton, ideal.eq_top_iff_one],
  dec_trivial,
end

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
  obtain ⟨(_|i), hx⟩ := hx; try { cases i }; change _ = _ at hx;
  obtain ⟨(_|i), hy⟩ := hy; try { cases i }; change _ = _ at hy;
  dsimp at hx hy;
  cases hx; cases hy; clear hx hy;
  dec_trivial!,
end

end counterexample_not_prime_but_homogeneous_prime
