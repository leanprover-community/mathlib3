/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import data.nat.choose.sum
import algebra.algebra.bilinear
import ring_theory.ideal.operations

/-!
# Nilpotent elements

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

  * `is_nilpotent`
  * `is_nilpotent_neg_iff`
  * `commute.is_nilpotent_add`
  * `commute.is_nilpotent_mul_left`
  * `commute.is_nilpotent_mul_right`
  * `commute.is_nilpotent_sub`

-/

universes u v

variables {R S : Type u} {x y : R}

/-- An element is said to be nilpotent if some natural-number-power of it equals zero.

Note that we require only the bare minimum assumptions for the definition to make sense. Even
`monoid_with_zero` is too strong since nilpotency is important in the study of rings that are only
power-associative. -/
def is_nilpotent [has_zero R] [has_pow R ℕ] (x : R) : Prop := ∃ (n : ℕ), x^n = 0

lemma is_nilpotent.mk [has_zero R] [has_pow R ℕ] (x : R) (n : ℕ)
  (e : x ^ n = 0) : is_nilpotent x := ⟨n, e⟩

lemma is_nilpotent.zero [monoid_with_zero R] : is_nilpotent (0 : R) := ⟨1, pow_one 0⟩

lemma is_nilpotent.neg [ring R] (h : is_nilpotent x) : is_nilpotent (-x) :=
begin
  obtain ⟨n, hn⟩ := h,
  use n,
  rw [neg_pow, hn, mul_zero],
end

@[simp] lemma is_nilpotent_neg_iff [ring R] : is_nilpotent (-x) ↔ is_nilpotent x :=
⟨λ h, neg_neg x ▸ h.neg, λ h, h.neg⟩

lemma is_nilpotent.map [monoid_with_zero R] [monoid_with_zero S] {r : R}
  {F : Type*} [monoid_with_zero_hom_class F R S] (hr : is_nilpotent r) (f : F) :
    is_nilpotent (f r) :=
by { use hr.some, rw [← map_pow, hr.some_spec, map_zero] }

/-- A structure that has zero and pow is reduced if it has no nonzero nilpotent elements. -/
@[mk_iff] class is_reduced (R : Type*) [has_zero R] [has_pow R ℕ] : Prop :=
(eq_zero : ∀ (x : R), is_nilpotent x → x = 0)

@[priority 900]
instance is_reduced_of_no_zero_divisors [monoid_with_zero R] [no_zero_divisors R] : is_reduced R :=
⟨λ _ ⟨_, hn⟩, pow_eq_zero hn⟩

@[priority 900]
instance is_reduced_of_subsingleton [has_zero R] [has_pow R ℕ] [subsingleton R] :
  is_reduced R := ⟨λ _ _, subsingleton.elim _ _⟩

lemma is_nilpotent.eq_zero [has_zero R] [has_pow R ℕ] [is_reduced R]
  (h : is_nilpotent x) : x = 0 :=
is_reduced.eq_zero x h

@[simp] lemma is_nilpotent_iff_eq_zero [monoid_with_zero R] [is_reduced R] :
  is_nilpotent x ↔ x = 0 :=
⟨λ h, h.eq_zero, λ h, h.symm ▸ is_nilpotent.zero⟩

lemma is_reduced_of_injective [monoid_with_zero R] [monoid_with_zero S]
  {F : Type*} [monoid_with_zero_hom_class F R S] (f : F)
  (hf : function.injective f) [_root_.is_reduced S] : _root_.is_reduced R :=
begin
  constructor,
  intros x hx,
  apply hf,
  rw map_zero,
  exact (hx.map f).eq_zero,
end

lemma ring_hom.ker_is_radical_iff_reduced_of_surjective {S F} [comm_semiring R] [comm_ring S]
  [ring_hom_class F R S] {f : F} (hf : function.surjective f) :
  (ring_hom.ker f).is_radical ↔ is_reduced S :=
by simp_rw [is_reduced_iff, hf.forall, is_nilpotent, ← map_pow, ← ring_hom.mem_ker]; refl

/-- An element `y` in a monoid is radical if for any element `x`, `y` divides `x` whenever it
  divides a power of `x`. -/
def is_radical [has_dvd R] [has_pow R ℕ] (y : R) : Prop := ∀ (n : ℕ) x, y ∣ x ^ n → y ∣ x

lemma zero_is_radical_iff [monoid_with_zero R] : is_radical (0 : R) ↔ is_reduced R :=
by { simp_rw [is_reduced_iff, is_nilpotent, exists_imp_distrib, ← zero_dvd_iff], exact forall_swap }

lemma is_radical_iff_span_singleton [comm_semiring R] :
  is_radical y ↔ (ideal.span ({y} : set R)).is_radical :=
begin
  simp_rw [is_radical, ← ideal.mem_span_singleton],
  exact forall_swap.trans (forall_congr $ λ r, exists_imp_distrib.symm),
end

lemma is_radical_iff_pow_one_lt [monoid_with_zero R] (k : ℕ) (hk : 1 < k) :
  is_radical y ↔ ∀ x, y ∣ x ^ k → y ∣ x :=
⟨λ h x, h k x, λ h, k.cauchy_induction_mul
  (λ n h x hd, h x $ (pow_succ' x n).symm ▸ hd.mul_right x) 0 hk
  (λ x hd, pow_one x ▸ hd) (λ n _ hn x hd, h x $ hn _ $ (pow_mul x k n).subst hd)⟩

lemma is_reduced_iff_pow_one_lt [monoid_with_zero R] (k : ℕ) (hk : 1 < k) :
  is_reduced R ↔ ∀ x : R, x ^ k = 0 → x = 0 :=
by simp_rw [← zero_is_radical_iff, is_radical_iff_pow_one_lt k hk, zero_dvd_iff]

namespace commute

section semiring

variables [semiring R] (h_comm : commute x y)

include h_comm

lemma is_nilpotent_add (hx : is_nilpotent x) (hy : is_nilpotent y) : is_nilpotent (x + y) :=
begin
  obtain ⟨n, hn⟩ := hx,
  obtain ⟨m, hm⟩ := hy,
  use n + m - 1,
  rw h_comm.add_pow',
  apply finset.sum_eq_zero,
  rintros ⟨i, j⟩ hij,
  suffices : x^i * y^j = 0, { simp only [this, nsmul_eq_mul, mul_zero], },
  cases nat.le_or_le_of_add_eq_add_pred (finset.nat.mem_antidiagonal.mp hij) with hi hj,
  { rw [pow_eq_zero_of_le hi hn, zero_mul], },
  { rw [pow_eq_zero_of_le hj hm, mul_zero], },
end

lemma is_nilpotent_mul_left (h : is_nilpotent x) : is_nilpotent (x * y) :=
begin
  obtain ⟨n, hn⟩ := h,
  use n,
  rw [h_comm.mul_pow, hn, zero_mul],
end

lemma is_nilpotent_mul_right (h : is_nilpotent y) : is_nilpotent (x * y) :=
by { rw h_comm.eq, exact h_comm.symm.is_nilpotent_mul_left h, }

end semiring

section ring

variables [ring R] (h_comm : commute x y)

include h_comm

lemma is_nilpotent_sub (hx : is_nilpotent x) (hy : is_nilpotent y) : is_nilpotent (x - y) :=
begin
  rw ← neg_right_iff at h_comm,
  rw ← is_nilpotent_neg_iff at hy,
  rw sub_eq_add_neg,
  exact h_comm.is_nilpotent_add hx hy,
end

end ring

end commute

section comm_semiring

variable [comm_semiring R]

/-- The nilradical of a commutative semiring is the ideal of nilpotent elements. -/
def nilradical (R : Type*) [comm_semiring R] : ideal R := (0 : ideal R).radical

lemma mem_nilradical : x ∈ nilradical R ↔ is_nilpotent x := iff.rfl

lemma nilradical_eq_Inf (R : Type*) [comm_semiring R] :
  nilradical R = Inf { J : ideal R | J.is_prime } :=
(ideal.radical_eq_Inf ⊥).trans $ by simp_rw and_iff_right bot_le

lemma nilpotent_iff_mem_prime : is_nilpotent x ↔ ∀ (J : ideal R), J.is_prime → x ∈ J :=
by { rw [← mem_nilradical, nilradical_eq_Inf, submodule.mem_Inf], refl }

lemma nilradical_le_prime (J : ideal R) [H : J.is_prime] : nilradical R ≤ J :=
(nilradical_eq_Inf R).symm ▸ Inf_le H

@[simp] lemma nilradical_eq_zero (R : Type*) [comm_semiring R] [is_reduced R] : nilradical R = 0 :=
ideal.ext $ λ _, is_nilpotent_iff_eq_zero

end comm_semiring

namespace linear_map

variables (R) {A : Type v} [comm_semiring R] [semiring A] [algebra R A]

@[simp] lemma is_nilpotent_mul_left_iff (a : A) :
  is_nilpotent (mul_left R a) ↔ is_nilpotent a :=
begin
  split; rintros ⟨n, hn⟩; use n;
  simp only [mul_left_eq_zero_iff, pow_mul_left] at ⊢ hn;
  exact hn,
end

@[simp] lemma is_nilpotent_mul_right_iff (a : A) :
  is_nilpotent (mul_right R a) ↔ is_nilpotent a :=
begin
  split; rintros ⟨n, hn⟩; use n;
  simp only [mul_right_eq_zero_iff, pow_mul_right] at ⊢ hn;
  exact hn,
end

end linear_map

namespace module.End

variables {M : Type v} [ring R] [add_comm_group M] [module R M]
variables {f : module.End R M} {p : submodule R M} (hp : p ≤ p.comap f)

lemma is_nilpotent.mapq (hnp : is_nilpotent f) : is_nilpotent (p.mapq p f hp) :=
begin
  obtain ⟨k, hk⟩ := hnp,
  use k,
  simp [← p.mapq_pow, hk],
end

end module.End
