/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import number_theory.weight_space
import number_theory.bernoulli_polynomials

/-!
# Special values of the p-adic L-function

This file determines the special values the p-adic L-function takes at negative integers, in terms
of generalized Bernoulli numbers. We first define Dirichlet characters over ℤ and then relate them
to multiplicative homomorphisms over ℤ/nℤ for any n divisible by the conductor. We then define the
generalized Bernoulli numbers related to Dirichlet characters.

## Main definitions
 * `dir_char`
 * `general_bernoulli_number`

## Implementation notes
TODO (optional)

## References
Introduction to Cyclotomic Fields, Washington (Chapter 12, Section 2)

## Tags
p-adic, L-function, Bernoulli measure, Dirichlet character
-/

/-- A Dirichlet character is defined as a multiplicative homomorphism which is periodic. -/
structure dir_char (R : Type*) [has_mul R] :=
(to_hom : mul_hom ℤ R)
(periodic : ∃ n : ℕ, ∀ a : ℤ, to_hom (a + n) = to_hom a)

instance (R : Type*) [has_mul R] : inhabited (dir_char R) := sorry

instance (R : Type*) [mul_one_class R] : has_one (dir_char R) :=
{ one := { to_hom := 1,
      periodic := ⟨1, λ a, rfl⟩, }, }

/-- The set of natural numbers for which a Dirichlet character is periodic. -/
def conductor_set {R : Type*} [has_mul R] (χ : dir_char R) : set ℕ :=
  {n : ℕ | ∀ a : ℤ, χ.to_hom (a + n) = χ.to_hom a}

variables {R : Type*} [has_mul R] (χ : dir_char R)

lemma mem_some : classical.some χ.periodic ∈ conductor_set χ := sorry

lemma mem_dvd {m n : ℕ} (h : n ∣ m) (mem : n ∈ conductor_set χ) : m ∈ conductor_set χ := sorry

/-- The minimum natural number n for which a Dirichlet character is periodic.
  The Dirichlet character χ can then alternatively be reformulated on ℤ/nℤ. -/
noncomputable def conductor : ℕ := Inf (conductor_set χ)

lemma mem_conductor : conductor χ ∈ conductor_set χ := sorry

lemma mem_lcm (m : ℕ) : lcm (conductor χ) m ∈ conductor_set χ := sorry

lemma map_mul' {m : ℕ} (x y : zmod m) : (χ.to_hom) ↑(x * y) = (χ.to_hom) ↑x * (χ.to_hom) ↑y := sorry

lemma conductor_one {S : Type*} [mul_one_class S] : conductor (1 : dir_char S) = 1 := sorry

lemma conductor_one_dvd_nat {S : Type*} [mul_one_class S] (n : ℕ) :
  conductor (1 : dir_char S) ∣ n := by {rw conductor_one, apply one_dvd _, }

/-- Reformulating a Dirichlet character modulo an element of the `conductor_set`. -/
abbreviation dir_char_to_zmod {m : ℕ} (mem : m ∈ conductor_set χ) : mul_hom (zmod m) R :=
{ to_fun := λ x, χ.to_hom (x : ℤ),
  map_mul' := map_mul' χ, }

/-- Using a multiplicative homomorphism ℤ/mℤ to construct a Dirichlet character having modulus m. -/
abbreviation zmod_to_dir_char {m : ℕ} (χ : mul_hom (zmod m) R) : dir_char R :=
{ to_hom := mul_hom.comp χ (int.cast_ring_hom (zmod m)).to_monoid_hom,
  periodic := ⟨m, λ a, by simp only [int.coe_cast_ring_hom, int.cast_coe_nat,
    monoid_hom.coe_eq_to_mul_hom, add_zero, int.cast_add, ring_hom.coe_monoid_hom,
    ring_hom.to_monoid_hom_eq_coe, function.comp_app, zmod.nat_cast_self,
    monoid_hom.to_mul_hom_coe, mul_hom.coe_comp]⟩, }

lemma mem_zmod_to_dir_char {m : ℕ} (χ : mul_hom (zmod m) R) :
  m ∈ conductor_set (zmod_to_dir_char χ) := sorry

noncomputable instance {R : Type*} [comm_semigroup R] : has_mul (dir_char R) :=
⟨λ f g, begin
    apply zmod_to_dir_char _,
    { exact lcm (conductor f) (conductor g), },
    have : (lcm (conductor f) (conductor g)) ∈ conductor_set g,
    { convert mem_lcm g (conductor f) using 1, rw lcm_comm, },
    refine ⟨λ x, dir_char_to_zmod f (mem_lcm f (conductor g)) x *
      dir_char_to_zmod g this x,
      λ x y, by {rw [mul_hom.map_mul, mul_hom.map_mul, mul_mul_mul_comm]}⟩,
  end,⟩
--should I find an equiv similar to zmod.lift?

open_locale big_operators
lemma sum_dir_char {S : Type*} [add_comm_monoid S] [has_mul S] (ψ : dir_char S) :
  ∑ i in finset.range (conductor ψ).succ, ψ.to_hom i = 0 := sorry

section general_bernoulli_number
variables {S : Type*} [semiring S] [algebra ℚ S] (ψ : dir_char S)

/-- The generalized Bernoulli number -/
noncomputable def general_bernoulli_number {F : ℕ} (n : ℕ) (dvd : conductor ψ ∣ F) : S :=
  F^(n - 1) * (∑ a in finset.range F.succ, ψ.to_hom a *
    algebra_map ℚ S ((bernoulli_poly n).eval (a/F : ℚ)))

namespace general_bernoulli_number

lemma general_bernoulli_number_one_eval_one :
general_bernoulli_number (1 : dir_char S) 1 (conductor_one_dvd_nat 1) =
  algebra_map ℚ S (1/2 : ℚ) := sorry

lemma general_bernoulli_number_one_eval {n : ℕ} (ne_one : n ≠ 1) :
general_bernoulli_number (1 : dir_char S) 1 (conductor_one_dvd_nat 1) =
  algebra_map ℚ S (bernoulli n) := sorry

end general_bernoulli_number
end general_bernoulli_number

--example {α β : Type*}

/-local attribute [instance] zmod.topological_space
noncomputable def p_adic_L_function' (p : ℕ) [fact (nat.prime p)] (d : ℕ) (R : Type*) [normed_comm_ring R]
[complete_space R] [char_zero R] (inj : ℤ_[p] → R) (m : ℕ)
{χ : mul_hom (zmod (d * p ^ m)) R} (hcond : conductor (zmod_to_dir_char χ) = d * p^m)
--(χ : mul_hom (units (zmod (d * p ^ m))) R)
(w : weight_space (units (zmod d) × units ℤ_[p]) R) {c : ℕ}
[fact (0 < d)] [semi_normed_algebra ℚ R] (hd : d.gcd p = 1) [fact (0 < m)]
  (h : function.injective inj) (cont : continuous inj) (hc : c.gcd p = 1) (hc' : c.gcd d = 1)
    (na : ∀ (n : ℕ) (f : ℕ → R), ∥∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
    --(hu : is_unit (f' p d R m hd hc hc' χ w))
    : R :=
  --(f p d R m χ w hd hc hc' hu) *
    (measure.integral (bernoulli_measure' p d R hc hc' hd na)
      ⟨(λ (a : (units (zmod d) × units ℤ_[p])), ((pri_dir_char_extend p d R m hd (mul_hom.comp (units.coe_hom R).to_mul_hom (units.map (is_mul_hom.to_is_monoid_hom χ)))) a) *
  (inj (teichmuller_character p a.snd))^(p - 2) * (w.to_fun a : R)), cont_paLf p d R inj m χ w hd cont⟩)-/
--is there not a way to go between mul_hom and is_mul_hom, similarly for monoid_hom?
