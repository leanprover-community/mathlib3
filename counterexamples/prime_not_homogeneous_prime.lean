/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import ring_theory.graded_algebra.homogeneous_ideal
import tactic.derive_fintype

/-!
# A homogeneous prime that is homogeneously prime but not prime

In `src/ring_theory/graded_algebra/radical.lean`,  we assumed that the underline grading is inedxed
by a `linear_ordered_cancel_add_comm_monoid` to prove that a homogeneous ideal is prime if and only
if it is homogeneously prime, this file is aimed to show that even if this assumption isn't strictly
necessary, the assumption of "being cancellative" certainly is. We construct a counterexample where the
underlying indexing set is a `linear_ordered_add_comm_monoid` but is not cancellative and the
statement is false.

We first give the two element set `ι = {0, 1}` a structure of linear ordered additive commutative
monoid by setting `0 + 0 = 0` and `_ + _ = 1` and `0 < 1`. Then we use `ι` to grade `ℤ²` by
setting `{(a, a) | a ∈ ℤ}` to have grade `0`; and `{(0, b) | b ∈ ℤ}`. Then the ideal
`I = span {(0, 2)}` is certainly homogeneous and not prime. But it is also homogeneously prime, i.e.
if `(a, b), (c, d)` are two homogeneous element then `(a, b) * (c, d) ∈ I` implies either
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

lemma two.o_ne_z : o ≠ z := by tauto
lemma two.z_ne_o : z ≠ o := by tauto

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
{ lt := λ i j, begin
  cases i; cases j,
  { exact false },
  { exact true },
  { exact false },
  { exact false },
end }

instance : decidable_rel ((<) : two → two → Prop) :=
λ i j, by cases i; cases j; apply_instance

lemma two.z_lt_o : z < o := dec_trivial

instance : has_le two :=
{ le := λ i j, i < j ∨ i = j }

instance : decidable_rel ((≤) : two → two → Prop) :=
λ i j, or.decidable

lemma two.not_o_le_z : ¬ o ≤ z := dec_trivial

lemma two.z_le_o : z ≤ o := dec_trivial

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

/--
We consider the ring `ℤ²`, later we see that `span {(0, 2)}` is a working counterexample.
-/
@[derive comm_ring]
def Z_sq : Type := ℤ × ℤ

/--
The grade 0 part of `ℤ²` is `{(a, a) | a ∈ ℤ}`.
-/
def submodule_z : submodule ℤ Z_sq :=
{ carrier := { zz | zz.1 = zz.2 },
  zero_mem' := rfl,
  add_mem' := λ a b ha hb, congr_arg2 (+) ha hb,
  smul_mem' := λ a b hb, congr_arg ((*) a) hb }

/--
The grade 1 part of `ℤ²` is `{(0, b) | b ∈ ℤ}`.
-/
def submodule_o : submodule ℤ Z_sq :=
{ carrier := { zz | zz.1 = 0 },
  zero_mem' := rfl,
  add_mem' := λ a b (ha : a.1 = 0) (hb : b.1 = 0), show a.1 + b.1 = 0, by rw [ha, hb, zero_add],
  smul_mem' := λ a b (hb : b.1 = 0), show a * b.1 = 0, by rw [hb, mul_zero] }

/--
Give the above grading (see `submodule_z` and `submodule_o`), we turn `ℤ²` into a graded ring.
-/
def grading : two → submodule ℤ Z_sq
| z := submodule_z
| o := submodule_o

lemma grading.one_mem : (1 : Z_sq) ∈ grading 0 :=
eq.refl (1, 1).fst

lemma grading.mul_mem : ∀ ⦃i j : two⦄ {a b : Z_sq} (ha : a ∈ grading i) (hb : b ∈ grading j),
  a * b ∈ grading (i + j)
| z z a b (ha : a.1 = a.2) (hb : b.1 = b.2) := show a.1 * b.1 = a.2 * b.2, by rw [ha, hb]
| z o a b (ha : a.1 = a.2) (hb : b.1 = 0)   := show a.1 * b.1 = 0, by rw [hb, mul_zero]
| o z a b (ha : a.1 = 0) hb                 := show a.1 * b.1 = 0, by rw [ha, zero_mul]
| o o a b (ha : a.1 = 0) hb                 := show a.1 * b.1 = 0, by rw [ha, zero_mul]

/--
`ℤ² ≅ {(a, a) | a ∈ ℤ} ⨁ {(0, b) | b ∈ ℤ}` by `(x, y) ↦ (x, x) + (0, y - x)`.
-/
def grading.decompose : Z_sq →+ direct_sum two (λ i, grading i) :=
{ to_fun := λ zz, of (λ i, grading i) z ⟨(zz.1, zz.1), rfl⟩ +
    of (λ i, grading i) o ⟨(0, zz.2 - zz.1), rfl⟩,
  map_zero' := begin
    simp only [show (0 : Z_sq).1 = 0, from rfl, show (0 : Z_sq).2 = 0, from rfl],
    ext;
    cases i,
    { simp only [zero_apply, add_apply, map_add, of_eq_same],
      rw of_eq_of_ne _ _ _ _ two.o_ne_z,
      refl, },
    { simp only [zero_apply, add_apply, map_add, of_eq_same],
      rw of_eq_of_ne _ _ _ _ two.z_ne_o,
      refl, },
    { simp only [zero_apply, add_apply, map_add, of_eq_same],
      rw of_eq_of_ne _ _ _ _ two.o_ne_z,
      refl, },
    { simp only [zero_apply, add_apply, map_add, of_eq_same],
      rw of_eq_of_ne _ _ _ _ two.z_ne_o,
      refl, },
  end,
  map_add' := λ zz1 zz2, begin
    cases zz1 with a1 b1,
    cases zz2 with a2 b2,
    simp only [prod.fst_add, prod.snd_add],
    ext;
    cases i,
    { simp only [add_apply, map_add, of_eq_same],
      rw [of_eq_of_ne _ _ _ _ two.o_ne_z, add_zero, of_eq_of_ne _ _ _ _ two.o_ne_z,
        of_eq_of_ne _ _ _ _ two.o_ne_z, add_zero, add_zero],
      change a1 + a2 = a1 + a2,
      refl, },
    { simp only [add_apply, map_add, of_eq_same],
      rw [of_eq_of_ne _ _ _ _ two.z_ne_o, zero_add, of_eq_of_ne _ _ _ _ two.z_ne_o,
        of_eq_of_ne _ _ _ _ two.z_ne_o, zero_add, zero_add],
      change (0 : ℤ) = 0 + 0,
      rw zero_add, },
    { simp only [add_apply, map_add, of_eq_same],
      rw [of_eq_of_ne _ _ _ _ two.o_ne_z, add_zero, of_eq_of_ne _ _ _ _ two.o_ne_z,
        of_eq_of_ne _ _ _ _ two.o_ne_z, add_zero, add_zero],
      change a1 + a2 = a1 + a2,
      refl, },
    { simp only [add_apply, map_add, of_eq_same],
      rw [of_eq_of_ne _ _ _ _ two.z_ne_o, zero_add, of_eq_of_ne _ _ _ _ two.z_ne_o,
        of_eq_of_ne _ _ _ _ two.z_ne_o, zero_add, zero_add],
      change b1 + b2 - (a1 + a2) = (b1 - a1) + (b2 - a2),
      ring, },
  end }

lemma grading.decompose_z (zz : Z_sq) :
  (grading.decompose zz) z = ⟨(zz.1, zz.1), rfl⟩ :=
begin
  cases zz with a b,
  unfold grading.decompose,
  simp only [add_monoid_hom.coe_mk, add_apply, of_eq_same, add_right_eq_self],
  rw of_eq_of_ne _ _ _ _ two.o_ne_z,
end

lemma grading.decompose_o (zz : Z_sq) :
  (grading.decompose zz) o = ⟨(0, zz.2 - zz.1), rfl⟩ :=
begin
  cases zz with a b,
  unfold grading.decompose,
  simp only [add_monoid_hom.coe_mk, add_apply, of_eq_same, add_left_eq_self],
  rw of_eq_of_ne _ _ _ _ two.z_ne_o,
end

lemma grading.left_inv :
  function.left_inverse grading.decompose (submodule_coe grading) := λ zz,
begin
  induction zz using direct_sum.induction_on with i zz d1 d2 ih1 ih2,
  { simp only [map_zero],},
  { cases i,
    { rcases zz with ⟨⟨a, b⟩, (rfl : a = b)⟩,
      ext; cases i,
      { rw grading.decompose_z,
        simp, },
      { rw grading.decompose_o,
        simp only [subtype.coe_mk],
        rw of_eq_of_ne,
        refl,
        exact two.z_ne_o, },
      { rw grading.decompose_z,
        simp, },
      { rw grading.decompose_o,
        simp only [submodule_coe_of, subtype.coe_mk, sub_self],
        rw of_eq_of_ne,
        refl,
        exact two.z_ne_o, }, },
    { rcases zz with ⟨⟨a, b⟩, (rfl : a = 0)⟩,
      ext; cases i,
      { rw grading.decompose_z,
        simp only [submodule_coe_of, subtype.coe_mk, sub_self],
        rw of_eq_of_ne,
        refl,
        exact two.o_ne_z, },
      { rw grading.decompose_o,
        simp, },
      { rw grading.decompose_z,
        simp only [submodule_coe_of, subtype.coe_mk, sub_self],
        rw of_eq_of_ne,
        refl,
        exact two.o_ne_z, },
      { rw grading.decompose_o,
        simp, }, } },
  { simp only [map_add, ih1, ih2], },
end

lemma grading.right_inv :
  function.right_inverse grading.decompose (submodule_coe grading) := λ zz,
begin
  cases zz with a b,
  unfold grading.decompose,
  simp only [add_monoid_hom.coe_mk, map_add, submodule_coe_of, subtype.coe_mk, prod.mk_add_mk,
    add_zero, add_sub_cancel'_right],
end

instance : graded_algebra grading :=
{ one_mem := grading.one_mem,
  mul_mem := grading.mul_mem,
  decompose' := grading.decompose,
  left_inv := grading.left_inv,
  right_inv := grading.right_inv }

/--
The counterexample is the ideal `I = span {(2, 2)}`.
-/
def I : ideal Z_sq := ideal.span {((2, 2) : Z_sq)}.

lemma I_not_prime : ¬ I.is_prime :=
begin
  intro rid,
  cases rid with rid1 rid2,
  have : ((1, 2) : Z_sq) * ((2, 1) : Z_sq) ∈ I,
  { change ((2, 2) : Z_sq) ∈ I,
    rw [I, ideal.mem_span_singleton], },
  specialize rid2 this,
  cases rid2,
  { rw [I, ideal.mem_span_singleton] at rid2,
    rcases rid2 with ⟨⟨a, b⟩, h⟩,
    change ((1, 2) : Z_sq) = (2 * a, 2 * b) at h,
    rw [prod.eq_iff_fst_eq_snd_eq] at h,
    have h2 : (1 : ℤ) = 2 * a := h.1,
    apply_fun abs at h2,
    rw [abs_mul, abs_of_nonneg, abs_of_nonneg] at h2,
    have : 1 ≤ |a|,
    all_goals { linarith, }, },
  { rw [I, ideal.mem_span_singleton] at rid2,
    rcases rid2 with ⟨⟨a, b⟩, h⟩,
    change ((2, 1) : Z_sq) = (2 * a, 2 * b) at h,
    rw [prod.eq_iff_fst_eq_snd_eq] at h,
    have h2 : (1 : ℤ) = 2 * b := h.2,
    apply_fun abs at h2,
    rw [abs_mul, abs_of_nonneg, abs_of_nonneg] at h2,
    have : 1 ≤ |b|,
    all_goals { linarith, }, }
end

lemma I_is_homogeneous : I.is_homogeneous grading :=
begin
  rw ideal.is_homogeneous.iff_exists,
  refine ⟨{⟨(2, 2), ⟨z, rfl⟩⟩}, _⟩,
  rw set.image_singleton,
  refl,
end

lemma homogeneous_mem_or_mem {x y : Z_sq} (hx : set_like.is_homogeneous grading x)
  (hy : set_like.is_homogeneous grading y)
  (hxy : x * y ∈ I) : x ∈ I ∨ y ∈ I :=
have dvd1 : ∀ (a b : Z_sq), a ∣ b ↔ a.1 ∣ b.1 ∧ a.2 ∣ b.2, begin
  rintros ⟨a, b⟩ ⟨c, d⟩,
  split,
  { rintros ⟨⟨x, y⟩, eq1⟩,
    simp only [prod.mk_mul_mk] at eq1,
    rw prod.eq_iff_fst_eq_snd_eq at eq1,
    exact ⟨⟨x, eq1.1⟩, ⟨y, eq1.2⟩⟩, },
  { rintros ⟨⟨x, hx⟩, ⟨y, hy⟩⟩,
    refine ⟨⟨x, y⟩, _⟩,
    ext,
    convert hx,
    convert hy, },
end,
begin
  unfold I at hxy ⊢,
  rw ideal.mem_span_singleton at hxy,
  rcases hxy with ⟨⟨a, b⟩, hz⟩,
  simp only [prod.mk_mul_mk] at hz,
  rw prod.eq_iff_fst_eq_snd_eq at hz,
  have eq1 : x.1 * y.1 = 2 * a := hz.1,
  have eq2 : x.2 * y.2 = 2 * b := hz.2,
  have d1 : 2 ∣ x.1 * y.1 := ⟨a, eq1⟩,
  have d2 : 2 ∣ x.2 * y.2 := ⟨b, eq2⟩,
  have p : prime (2 : ℤ) := int.prime_two,
  replace d1 := prime.dvd_or_dvd p d1,
  replace d2 := prime.dvd_or_dvd p d2,
  rcases hx with ⟨(_|_), hx⟩;
  rcases hy with ⟨(_|_), hy⟩,
  { change x.1 = x.2 at hx,
    change y.1 = y.2 at hy,
    cases d1,
    { left,
      rw [ideal.mem_span_singleton, dvd1],
      exact ⟨d1, by { convert d1, rw hx, }⟩, },
    { right,
      rw [ideal.mem_span_singleton, dvd1],
      exact ⟨d1, by { convert d1, rw hy, }⟩, }, },
  { change x.1 = x.2 at hx,
    change y.1 = 0 at hy,
    cases d2,
    { left,
      rw [ideal.mem_span_singleton, dvd1],
      exact ⟨by convert d2, d2⟩, },
    { cases d1,
      { left,
        rw [ideal.mem_span_singleton, dvd1],
        exact ⟨d1, by { convert d1, rw hx }⟩ },
      { right,
        rw [ideal.mem_span_singleton, dvd1],
        exact ⟨d1, d2⟩ } }, },
  { change x.1 = 0 at hx,
    change y.1 = y.2 at hy,
    cases d1,
    { cases d2,
      { left,
        rw [ideal.mem_span_singleton, dvd1],
        exact ⟨d1, d2⟩ },
      { right,
        rw [ideal.mem_span_singleton, dvd1],
        exact ⟨by convert d2, d2⟩ }, },
    { right,
      rw [ideal.mem_span_singleton, dvd1],
      exact ⟨d1, by { convert d1, rw hy }⟩, }, },
  { change x.1 = 0 at hx,
    change y.1 = 0 at hy,
    cases d1;
    cases d2,
    { left,
      rw [ideal.mem_span_singleton, dvd1],
      exact ⟨d1, d2⟩, },
    { right,
      rw [ideal.mem_span_singleton, dvd1],
      exact ⟨by { rw hy, exact dvd_zero _ }, d2⟩, },
    { left,
      rw [ideal.mem_span_singleton, dvd1],
      exact ⟨by { rw hx, exact dvd_zero _ }, d2⟩, },
    { right,
      rw [ideal.mem_span_singleton, dvd1],
      exact ⟨d1, d2⟩ } },
end

end counterexample_not_prime_but_homogeneous_prime
