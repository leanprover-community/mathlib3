/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import algebra.regular
import data.nat.choose.sum
import data.mv_polynomial.basic
import data.zmod.basic

/-!
# Regular elements

We introduce left-regular, right-regular and regular elements.

By definition, a regular element in a commutative ring is a non-zero divisor.
Lemma `is_regular_of_cancel_monoid_with_zero` implies that every non-zero element of an integral
domain is regular.

The lemmas in Section `mul_zero_class` show that the `0` element is (left/right-)regular if and
only if the `mul_zero_class` is trivial.  This is useful when figuring out stopping conditions for
regular sequences: if `0` is ever an element of a regular sequence, then we can extend the sequence
by adding one further `0`.

The final goal is to develop part of the API to prove, eventually, results about non-zero-divisors.
-/
variables {R : Type*} {a b : R}

section monoid

variable [monoid R]

lemma comm_mul_pow_of_comm (a b : R) (n : ℕ) (ab : a * b = b * a) :
  a * b ^ n = b ^ n * a :=
begin
  induction n with n hn,
  { rw [pow_zero, mul_one, one_mul] },
  { rw [pow_succ, mul_assoc, ← hn, ← mul_assoc b, ← ab, mul_assoc] }
end

lemma mul_pow_of_comm (a b : R) (n : ℕ) (ab : a * b = b * a) :
  (a * b) ^ n = a ^ n * b ^ n :=
begin
  induction n with n hn,
  { rw [pow_zero, pow_zero, pow_zero, mul_one] },
  { rw [pow_succ, hn, mul_assoc, ← mul_assoc b, comm_mul_pow_of_comm b a n ab.symm, mul_assoc,
      ← pow_succ, ← mul_assoc, ← pow_succ] }
end

end monoid

section monoid_with_zero

variable [monoid_with_zero R]

def nilpotent (r : R) : Prop := ∃ e : ℕ, r ^ e = 0

lemma nilpotent.pow_of_nilpotent (r : R) : nilpotent r ↔ ∀ n : ℕ, 0 < n → nilpotent (r ^ n) :=
⟨λ ⟨e, he⟩ n n0, ⟨e, by rwa [← pow_mul, n.mul_comm e, pow_mul, he, zero_pow]⟩, λ h,
  by { rw ← pow_one r, exact h 1 nat.one_pos }⟩

lemma nilpotent.mul_of_comm_of_nilpotent {a b : R} (ab : a * b = b * a) (an : nilpotent a) :
  nilpotent (a * b) :=
begin
  rcases an with ⟨e, he⟩,
  refine ⟨e, _⟩,
  rw [mul_pow_of_comm _ _ _ ab, he, zero_mul],
end

end monoid_with_zero

section semiring

variable [semiring R]

open_locale big_operators classical

open mv_polynomial

def aev_comm (f : mv_polynomial (fin 2) ℕ) (a b : R) (ab : a * b = b * a) : R :=
∑ (v : fin 2 →₀ ℕ) in f.support, (f.coeff v) * a ^ (v 0) * b ^ (v 1)

lemma mv_polynomial.support_one_1 : @C ℕ (fin 2) _ 1 = monomial 0 1 := rfl

lemma mv_polynomial.support_one : (@C (zmod 2) (fin 2) _ 1).support = {begin
  refine {support := begin
    refine {val := {0, 1}, nodup := dec_trivial},
  end, to_fun := λ _, 1, mem_support_to_fun := by dec_trivial},
end} :=
begin
  tidy?,
  simp,
  exact dec_trivial,
  dsimp at *,
  ext1,
  simp only [finsupp.mem_support_iff, ne.def, finset.mem_singleton] at *,
  fsplit,
  { intros a,
    ext1,
    cases a_1,
    dsimp at *,

    unfold_coes,
     },
  { intros a b,
     },
end


#exit

lemma mv_polynomial.support_one : @C ℕ (fin 2) _ 1 = finsupp.single { support := { val := {0, 1},
  nodup := dec_trivial },
  to_fun := 0,
  mem_support_to_fun := begin
    intros a,
    refine ⟨_, _⟩,
    { simp only [pi.one_apply, ne.def, not_false_iff, one_ne_zero, forall_true_iff],
    simp, },
    simp,library_search,
    intros ha,
    simp at ha,
    simp,
    {intros ᾰ, cases a, dsimp at *, simp at *,

    },
  end  } 1 }
#exit

lemma mv_polynomial.support_one : (@C ℕ (fin 2) _ 1).support = begin
  refine singleton _,
  refine finsupp.single _ 1,
--  exact 0,
end :=
begin
  ext,
  rw [finset.mem_singleton, C_1],
  refine ⟨λ ha, _, λ ha, _⟩,
  by_contra h,
  simp at ha,
  apply ha,
  {tidy?},

  --tidy?,
end


lemma mv_polynomial.support_C (a : R) : (C a).support = (begin

end : finset ) := true

def ring_map_comm {a b : R} (ab : a * b = b * a) : mv_polynomial (fin 2) ℕ →+* R :=
begin
  refine {to_fun := λ f, aev_comm f a b ab,
  map_one' := begin
    simp [aev_comm],

    rw support_monomia,
  end, map_mul' := _, map_zero' := _, map_add' := _},

end



lemma ring_map_comm {a b : R} (ab : a * b = b * a) :
  ∃ f : mv_polynomial (fin 2) ℕ →+* R, f (X 0) = a ∧ f (X 1) = b :=
begin
  refine ⟨_, _, _⟩,
  refine {to_fun :=
  begin
    intros x,
    induction x,
    refine @finset.induction_on (fin 2 →₀ ℕ) _ _ x_support _ _,

    apply finset.induction_on x_support _ _,

  end, map_one' := _, map_mul' := _, map_zero' := _, map_add' := _},
end

lemma nilpotent.add_of_comm_of_nilpotent {a b : R}
  (ab : a * b = b * a) (an : nilpotent a) (bn : nilpotent b) :
  nilpotent (a + b) :=
begin
  rcases an with ⟨e, ae⟩,
  rcases bn with ⟨f, bf⟩,
  refine ⟨e + f, _⟩,
  generalize' ex : e + f = ef,
  revert ex e f,
  induction ef with ef hef,
  { intros e ae f bf ex,
    rcases add_eq_zero_iff.mp ex with ⟨rfl, F⟩,
    rw pow_zero at ae,
    rw [← one_mul (_ ^ _), ae, zero_mul] },
  {
    intros e ae f bf ex,
    rw [pow_succ, add_mul],
  },

  induction ex with ex iex,

  cases e,
  { rw pow_zero at he,
    rw [← one_mul (_ ^ _), he, zero_mul] },

  rw add_pow,
  rw [mul_pow_of_comm _ _ _ ab, he, zero_mul],
end

end semiring

section comm_monoid_with_zero

variable [comm_monoid_with_zero R]

lemma nilpotent.mul_of_nilpotent {a : R} (b : R) (an : nilpotent a) :
  nilpotent (a * b) :=
begin
  rcases an with ⟨e, he⟩,
  refine ⟨e, _⟩,
  rw [mul_pow, he, zero_mul]
end

end comm_monoid_with_zero

section comm_semiring

variable [comm_ring R]

/-- essentially exists as `sq_sub_sq`-/
lemma add_mul_sub {r s : R} : r ^ 2 + -s ^ 2 = (r + -s) * (r + s) :=
begin
  rw [pow_two s, ← sub_eq_add_neg, ← sub_eq_add_neg, ← pow_two, sq_sub_sq],
  exact mul_comm _ _,
end

lemma is_reg_sq_sub_sq_of_nilp {r n : R} (rp : is_regular (r + n)) (rm : is_regular (r - n)) :
  is_regular (r ^ 2 - n ^ 2) :=
begin
  rw sq_sub_sq,
  exact is_regular_mul_iff.mpr ⟨rp, rm⟩,
end

lemma nilp {r n : R} {o : ℕ} (hr : is_regular r) (no : n ^ o = (0 : R)) :
  is_regular (r + n) :=
begin
  revert n,
  induction o with o ho,
  { exact λ n no, by rwa [← mul_one n, ← pow_zero (n : R), no, mul_zero, add_zero] },
  intros n no,
  have : is_regular (r ^ 2 + (- n ^ 2)),
  { by_cases n0 : n = 0,
    { rw [n0, zero_pow (nat.succ_pos 1), neg_zero, add_zero],
      exact is_regular.pow 2 hr },
    by_cases o0 : o = 0,
    { rw [o0, pow_one] at no,
      exact absurd no n0 },
    have : r ^ 2 + -n ^ 2 = (r + -n) * (r + n),
    { extract_goal,
      rw [mul_add, add_mul, add_mul, pow_two, pow_two, add_assoc, add_comm _ (- n * _), add_comm (- n * r), neg_mul_eq_neg_mul, add_assoc, mul_comm r n],
      apply (add_right_inj _).mpr,
      apply self_eq_add_right.mpr,
      rw [neg_mul_eq_neg_mul_symm, add_right_neg] },
    apply ho,
    rw [neg_pow, ← pow_mul],
    apply mul_eq_zero_of_right,
    have : o.succ ≤ 2 * o,
    { refine nat.succ_le_of_lt _,
      rw two_mul,
      exact lt_add_of_le_of_pos rfl.le (pos_iff_ne_zero.mpr o0) },
    rcases le_iff_exists_add.mp this with ⟨k, hk⟩,
    rw [hk, pow_add, no, zero_mul] },
  have : r + -n ^ 2 = (r + n ^ 2) * (r - n ^ 2),
  {
    rw [mul_sub, add_mul, add_mul],
  },
  have : is_regular (r - n ^ 2),
  {
    apply ho (- n ^ 2),
  },
  apply is_regular
  convert is_regular_zer
end

#exit
lemma nilp {r s n : R} {o : ℕ} (hr : is_regular r) (no : n ^ o = (0 : R)) :
  is_regular (r + s * n) :=
begin
  revert n s,
  induction o with o ho,
  { exact λ n s no, by rwa [← mul_one n, ← pow_zero (n : R), no, mul_zero, mul_zero, add_zero] },
  intros n s no,
  have : is_regular (r + (- n ^ 2)),
  {
    apply ho,
  },
  have : is_regular ((r + n) * (r - n)),
  {
    apply is_regular_mul_iff.mpr,
    apply ho no (-1) (n ^ 2),
  },
  apply is_regular
  convert is_regular_zer
end

end comm_semiring
