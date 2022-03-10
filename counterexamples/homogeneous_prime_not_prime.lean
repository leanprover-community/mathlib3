/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Johan Commelin, Eric Wieser
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

/--
The underlying indexing set with two elements `z` for zero and `o` for one
-/
@[derive [inhabited, decidable_eq, fintype]]
inductive two
| z
| o

open two

lemma two.o_ne_z : o ≠ z := dec_trivial
lemma two.z_ne_o : z ≠ o := dec_trivial

instance has_add : has_add two :=
{ add := λ m n,
  match m, n with
  | z, z := z
  | z, o := o
  | o, z := o
  | o, o := o
  end }

instance : add_comm_monoid two :=
{ zero := z,
  add := (+),
  add_comm := dec_trivial,
  add_zero := dec_trivial,
  zero_add := dec_trivial,
  add_assoc := dec_trivial}

instance : has_lt two :=
{ lt := λ i j,
  match i, j with
  | z, z := false
  | z, o := true
  | o, o := false
  | o, z := false
  end }

instance : decidable_rel ((<) : two → two → Prop) :=
λ i j, by { cases i; cases j; try {exact decidable.is_false id}, exact decidable.is_true trivial }

lemma two.z_lt_o : z < o := dec_trivial

instance : has_le two :=
{ le := λ i j, i < j ∨ i = j }

instance : decidable_rel ((≤) : two → two → Prop) :=
λ i j, or.decidable

instance : linear_order two :=
{ le := (≤),
  le_refl := dec_trivial,
  le_trans := dec_trivial,
  le_antisymm := dec_trivial,
  le_total := dec_trivial,
  decidable_le := by apply_instance }

instance : linear_ordered_add_comm_monoid two :=
{ add_le_add_left := dec_trivial,
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
| z := submodule_z R
| o := submodule_o R

lemma grading.one_mem : (1 : (R × R)) ∈ grading R 0 :=
eq.refl (1, 1).fst

lemma grading.mul_mem : ∀ ⦃i j : two⦄ {a b : (R × R)} (ha : a ∈ grading R i) (hb : b ∈ grading R j),
  a * b ∈ grading R (i + j)
| z z a b (ha : a.1 = a.2) (hb : b.1 = b.2) := show a.1 * b.1 = a.2 * b.2, by rw [ha, hb]
| z o a b (ha : a.1 = a.2) (hb : b.1 = 0)   := show a.1 * b.1 = 0, by rw [hb, mul_zero]
| o z a b (ha : a.1 = 0) hb                 := show a.1 * b.1 = 0, by rw [ha, zero_mul]
| o o a b (ha : a.1 = 0) hb                 := show a.1 * b.1 = 0, by rw [ha, zero_mul]

end

notation `R` := zmod 4

/--
`R² ≅ {(a, a) | a ∈ R} ⨁ {(0, b) | b ∈ R}` by `(x, y) ↦ (x, x) + (0, y - x)`.
-/
def grading.decompose : (R × R) →+ direct_sum two (λ i, grading R i) :=
{ to_fun := λ zz, of (λ i, grading R i) z ⟨(zz.1, zz.1), rfl⟩ +
    of (λ i, grading R i) o ⟨(0, zz.2 - zz.1), rfl⟩,
  map_zero' := by ext1 (_|_); refl,
  map_add' := begin
    rintros ⟨a1, b1⟩ ⟨a2, b2⟩,
    ext (_|_);
    simp only [prod.fst_add, prod.snd_add, add_apply, of_eq_same, add_zero, zero_add,
      submodule.coe_add, subtype.coe_mk, prod.mk_add_mk,
      of_eq_of_ne _ _ _ _ two.o_ne_z, of_eq_of_ne _ _ _ _ two.z_ne_o],
    ext : 2;
    simp only [prod.mk_add_mk, submodule.coe_add, subtype.coe_mk, fin.zero_add],
    abel,
  end }

lemma grading.left_inv :
  function.left_inverse grading.decompose (submodule_coe (grading R)) := λ zz,
begin
  induction zz using direct_sum.induction_on with i zz d1 d2 ih1 ih2,
  { simp only [map_zero],},
  { cases i;
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
  refine ⟨{⟨(2, 2), ⟨z, rfl⟩⟩}, _⟩,
  rw set.image_singleton,
  refl,
end

lemma homogeneous_mem_or_mem {x y : (R × R)} (hx : set_like.is_homogeneous (grading R) x)
  (hy : set_like.is_homogeneous (grading R) y)
  (hxy : x * y ∈ I) : x ∈ I ∨ y ∈ I :=
begin
  simp only [I, ideal.mem_span_singleton] at hxy ⊢,
  cases x, cases y,
  obtain ⟨_|_, hx : _ = _⟩ := hx;
  obtain ⟨_|_, hy : _ = _⟩ := hy;
  dsimp at hx hy;
  cases hx; cases hy; clear hx hy;
  dec_trivial!,
end

end counterexample_not_prime_but_homogeneous_prime
