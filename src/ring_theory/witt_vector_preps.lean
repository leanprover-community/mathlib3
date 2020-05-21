-- this should all be moved

import algebra.inj_surj
import data.nat.choose
import data.int.gcd
import data.mv_polynomial
import data.zmod.basic
import data.fintype.card
import ring_theory.multiplicity
import algebra.invertible
import number_theory.basic

universes u v w u₁

-- ### FOR_MATHLIB
-- everything in this section should move to other files

section finset

variables {G : Type u} [comm_group G]
variables {H : Type v} [comm_group H]
variables (i : G → H) [is_group_hom i]
variables {X : Type w} [decidable_eq X] (s : finset X) (f : X → G)

-- Generalise this to arbitrary property that is respected by addition/multiplication:
-- example applications: sum_pos, sum_neg, ... others?
lemma dvd_sum {α : Type*} {β : Type*} [decidable_eq α] [comm_ring β]
  (s : finset α) (f : α → β) (b : β) (H : ∀ a ∈ s, b ∣ f a) :
  b ∣ s.sum f :=
begin
  let t := s,
  replace H : ∀ a ∈ t, b ∣ f a := H,
  have hs : s ⊆ t := finset.subset.refl s,
  revert hs,
  apply finset.induction_on s, {simp},
  intros a s' ha IH hs',
  rw finset.insert_subset at hs',
  cases hs' with has hs',
  simp [*, dvd_add]
end

lemma coe_nat_dvd {α : Type*} [comm_ring α] (m n : ℕ) (h : m ∣ n) :
  (m : α) ∣ n :=
by { rcases h with ⟨k, rfl⟩, refine ⟨k, by norm_cast⟩ }

end finset

namespace mv_polynomial

variables {σ : Type*} {R : Type*} [comm_semiring R]

noncomputable def C_ (σ : Type*) {R : Type*} [comm_semiring R] : R →+* mv_polynomial σ R :=
ring_hom.of C

example (x y : R) : C_ σ (x * y) = C_ σ x * C_ σ y := C_mul

lemma ring_hom_ext {σ : Type*} {R : Type*} {A : Type*} [comm_ring R] [comm_ring A]
  (f g : mv_polynomial σ R →+* A)
  (hC : ∀ r, f (C r) = g (C r)) (hX : ∀ i, f (X i) = g (X i)) :
  f = g :=
begin
  ext p : 1,
  apply mv_polynomial.induction_on' p,
  { intros m r, rw [monomial_eq, finsupp.prod],
    simp only [monomial_eq, ring_hom.map_mul, ring_hom.map_prod, ring_hom.map_pow, hC, hX], },
  { intros p q hp hq, simp only [ring_hom.map_add, hp, hq] }
end

lemma alg_hom_ext {σ : Type*} (R : Type*) [comm_ring R]
  (A : Type*) [comm_ring A] [algebra R A]
  (f g : mv_polynomial σ R →ₐ[R] A)
  (hf : ∀ i : σ, f (X i) = g (X i)) : f = g :=
begin
  apply alg_hom.coe_ring_hom_inj,
  apply ring_hom_ext,
  { intro r,
    calc f (C r) = algebra_map R A r : f.commutes r
             ... = g (C r)           : (g.commutes r).symm },
  { simpa only [hf] },
end

end mv_polynomial

namespace alg_hom
open mv_polynomial

lemma map_aeval {σ : Type*}
  {R : Type*} {A : Type*} {B : Type*}
   [comm_ring R] [comm_ring A] [algebra R A] [comm_ring B] [algebra R B]
  (f : σ → A) (φ : A →ₐ[R] B) :
  φ.comp (aeval R A f) = (aeval R B (λ i, φ (f i))) :=
begin
  apply mv_polynomial.alg_hom_ext,
  intros i,
  rw [comp_apply, aeval_X, aeval_X],
end

end alg_hom

namespace mv_polynomial

open mv_polynomial finsupp

lemma eval₂_assoc'
  {S : Type*} [comm_semiring S]
  {T : Type*} [comm_semiring T]
  {σ : Type*}
  {τ : Type*}
  (f : S → T) [is_semiring_hom f]
  (φ : σ → T) (q : τ → mv_polynomial σ S)
  (p : mv_polynomial τ S) :
  eval₂ f (λ t, eval₂ f φ (q t)) p = eval₂ f φ (eval₂ C q p) :=
by { rw eval₂_comp_left (eval₂ f φ), congr, funext, simp }

noncomputable def map_hom
  {S : Type*} [comm_semiring S]
  {T : Type*} [comm_semiring T]
  (σ : Type*)
  (f : S →+* T) :
  mv_polynomial σ S →+* mv_polynomial σ T :=
ring_hom.of (mv_polynomial.map f)

lemma map_eval₂'
  {R : Type*} [comm_semiring R]
  {S : Type*} [comm_semiring S]
  {T : Type*} [comm_semiring T]
  {σ : Type*}
  (φ : S →+* T)
  (f : R →+* S)
  (g : σ → S)
  (p : mv_polynomial σ R) :
  φ (eval₂ f g p) = eval₂ (φ.comp f) (λ i, φ (g i)) p :=
begin
  apply p.induction_on,
  { intros, rw [eval₂_C, eval₂_C, ring_hom.coe_comp] },
  { intros p₁ p₂ hp₁ hp₂, rw [eval₂_add, eval₂_add, ring_hom.map_add, hp₁, hp₂] },
  { intros q n h, rw [eval₂_mul, eval₂_mul, ring_hom.map_mul, eval₂_X, eval₂_X, h] }
end


end mv_polynomial

namespace modp
variables {α : Type*} [comm_ring α] {p : ℕ} (hp : nat.prime p)

-- notation x ` modᵢ ` I := (ideal.quotient.mk_hom I x)
-- notation x ` modₛ ` s := (ideal.quotient.mk_hom (ideal.span s) x)
notation x ` modₑ ` a := (ideal.quotient.mk (ideal.span ({a})) x)

lemma char_one.one_eq_zero [char_p α 1] : (1 : α) = 0 :=
by exact_mod_cast char_p.cast_eq_zero α 1

lemma char_one.elim [char_p α 1] (a b : α) : a = b :=
by rw [← one_mul a, ← one_mul b, char_one.one_eq_zero, zero_mul, zero_mul]

instance char_one_of_is_unit (h : is_unit (p : α)) :
  char_p (ideal.span ({p} : set α)).quotient 1 :=
⟨begin
  intro n,
  have helper : ∀ m : ℕ, (m : (ideal.span ({p} : set α)).quotient) =
    ideal.quotient.mk (ideal.span ({p} : set α)) (m : α),
  { intro m, induction m with m ih, {refl}, simp [ih] },
  split,
  { intro hn, exact one_dvd n },
  { rintro ⟨c, rfl⟩,
    rw is_unit_iff_exists_inv at h,
    rcases h with ⟨b, hb⟩,
    rw [helper, nat.cast_mul, nat.cast_one, ← hb,
      ideal.quotient.eq_zero_iff_mem, mul_assoc],
    exact ideal.mul_mem_right _ (ideal.subset_span $ set.mem_singleton p) }
end⟩

include hp
instance (h : ¬ is_unit (p : α)) : char_p (ideal.span ({p} : set α)).quotient p :=
⟨begin
  intro n,
  have helper : ∀ m : ℕ, (m : (ideal.span ({p} : set α)).quotient) =
    ideal.quotient.mk (ideal.span ({p} : set α)) (m : α),
  { intro m, induction m with m ih, {refl}, simp [ih] },
  split,
  { intro H,
    rw [helper, ideal.quotient.eq_zero_iff_mem, ideal.mem_span_singleton] at H,
    rcases H with ⟨c, hc⟩,
    cases nat.coprime_or_dvd_of_prime hp n with hn hn,
    swap, {exact hn},
    have key := nat.gcd_eq_gcd_ab p n,
    delta nat.coprime at hn, rw hn at key,
    replace key := congr_arg (λ k : ℤ, (k : α)) key,
    simp only [int.cast_coe_nat, int.cast_add, int.coe_nat_zero, int.cast_mul, int.cast_one,
      int.coe_nat_succ, zero_add, hc] at key,
    rw [mul_assoc, ← mul_add] at key,
    exfalso, apply h,
    rw is_unit_iff_exists_inv,
    exact ⟨_, key.symm⟩ },
  { rintro ⟨c, rfl⟩,
    apply eq_zero_of_zero_dvd,
    use p,
    rw [zero_mul, helper (p*c), ideal.quotient.eq_zero_iff_mem, nat.cast_mul],
    exact ideal.mul_mem_right _ (ideal.subset_span $ set.mem_singleton p) }
end⟩
.

open ideal.quotient

def modp := mk_hom (ideal.span ({p} : set α))

lemma add_pow (a b : α) :
  ((a + b)^p modₑ (p : α)) = (a^p modₑ (p : α)) + (b^p modₑ (p : α)) :=
begin
  classical,
  by_cases H : is_unit (p : α),
  { haveI := modp.char_one_of_is_unit H, exact char_one.elim _ _ },
  { haveI := modp.char_p hp H, simpa using add_pow_char _ hp _ _, apply_instance }
end

end modp

section
open multiplicity

-- use `lift` instead
lemma integral_of_denom_eq_one (r : ℚ) (h : r.denom = 1) : (r.num : ℚ) = r :=
begin
  lift r to ℤ using h,
  rw rat.coe_int_num
end

end

-- ### end FOR_MATHLIB

-- proper start of this file
