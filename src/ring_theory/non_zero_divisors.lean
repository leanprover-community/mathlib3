/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Devon Tuma
-/

import group_theory.submonoid.operations
import group_theory.submonoid.membership

/-!
# Non-zero divisors

In this file we define the submonoid `non_zero_divisors` of a `monoid_with_zero`.
-/

section non_zero_divisors

/-- The submonoid of non-zero-divisors of a `monoid_with_zero` `R`. -/
def non_zero_divisors (R : Type*) [monoid_with_zero R] : submonoid R :=
{ carrier := {x | ∀ z, z * x = 0 → z = 0},
  one_mem' := λ z hz, by rwa mul_one at hz,
  mul_mem' := λ x₁ x₂ hx₁ hx₂ z hz,
    have z * x₁ * x₂ = 0, by rwa mul_assoc,
    hx₁ z $ hx₂ (z * x₁) this }

variables {R A : Type*} [comm_ring R] [integral_domain A]

lemma mul_mem_non_zero_divisors {a b : R} :
  a * b ∈ non_zero_divisors R ↔ a ∈ non_zero_divisors R ∧ b ∈ non_zero_divisors R :=
begin
  split,
  { intro h,
    split; intros x h'; apply h,
    { rw [←mul_assoc, h', zero_mul] },
    { rw [mul_comm a b, ←mul_assoc, h', zero_mul] } },
  { rintros ⟨ha, hb⟩ x hx,
    apply ha,
    apply hb,
    rw [mul_assoc, hx] },
end

lemma eq_zero_of_ne_zero_of_mul_right_eq_zero {x y : A} (hnx : x ≠ 0) (hxy : y * x = 0) : y = 0 :=
or.resolve_right (eq_zero_or_eq_zero_of_mul_eq_zero hxy) hnx

lemma eq_zero_of_ne_zero_of_mul_left_eq_zero {x y : A} (hnx : x ≠ 0) (hxy : x * y = 0) : y = 0 :=
or.resolve_left (eq_zero_or_eq_zero_of_mul_eq_zero hxy) hnx

lemma mem_non_zero_divisors_iff_ne_zero {x : A} : x ∈ non_zero_divisors A ↔ x ≠ 0 :=
⟨λ hm hz, zero_ne_one (hm 1 $ by rw [hz, one_mul]).symm,
λ hnx z, eq_zero_of_ne_zero_of_mul_right_eq_zero hnx⟩

lemma map_ne_zero_of_mem_non_zero_divisors [nontrivial R] {B : Type*} [ring B] {g : R →+* B}
  (hg : function.injective g) {x : non_zero_divisors R} : g x ≠ 0 :=
λ h0, one_ne_zero (x.2 1 ((one_mul x.1).symm ▸ (hg (trans h0 g.map_zero.symm))))

lemma map_mem_non_zero_divisors {B : Type*} [integral_domain B] {g : A →+* B}
  (hg : function.injective g) {x : non_zero_divisors A} : g x ∈ non_zero_divisors B :=
λ z hz, eq_zero_of_ne_zero_of_mul_right_eq_zero
  (map_ne_zero_of_mem_non_zero_divisors hg) hz

lemma le_non_zero_divisors_of_domain {M : submonoid A}
  (hM : ↑0 ∉ M) : M ≤ non_zero_divisors A :=
λ x hx y hy, or.rec_on (eq_zero_or_eq_zero_of_mul_eq_zero hy)
  (λ h, h) (λ h, absurd (h ▸ hx : (0 : A) ∈ M) hM)

lemma powers_le_non_zero_divisors_of_domain {a : A} (ha : a ≠ 0) :
  submonoid.powers a ≤ non_zero_divisors A :=
le_non_zero_divisors_of_domain (λ h, absurd (h.rec_on (λ _ hn, pow_eq_zero hn)) ha)

lemma map_le_non_zero_divisors_of_injective {B : Type*} [integral_domain B]
  {f : A →+* B} (hf : function.injective f)
  {M : submonoid A} (hM : M ≤ non_zero_divisors A) : M.map ↑f ≤ non_zero_divisors B :=
le_non_zero_divisors_of_domain (λ h, let ⟨x, hx, hx0⟩ := h in
  zero_ne_one (hM (hf (trans hx0 (f.map_zero.symm)) ▸ hx : 0 ∈ M) 1 (mul_zero 1)).symm)

lemma prod_zero_iff_exists_zero {R : Type*} [comm_semiring R] [no_zero_divisors R] [nontrivial R]
  {s : multiset R} : s.prod = 0 ↔ ∃ (r : R) (hr : r ∈ s), r = 0 :=
begin
  split, swap,
  { rintros ⟨r, hrs, rfl⟩,
    exact multiset.prod_eq_zero hrs, },   
  refine multiset.induction _ (λ a s ih, _) s,
  { intro habs,
    simpa using habs, },
  { rw multiset.prod_cons,
    intro hprod,
    replace hprod := eq_zero_or_eq_zero_of_mul_eq_zero hprod,
    cases hprod with ha,
    { exact ⟨a, multiset.mem_cons_self a s, ha⟩ },
    { apply (ih hprod).imp _,
      rintros b ⟨hb₁, hb₂⟩,
      exact ⟨multiset.mem_cons_of_mem hb₁, hb₂⟩, }, },
end


end non_zero_divisors
