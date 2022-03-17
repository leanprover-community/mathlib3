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
 * `dirichlet_character`
 * `general_bernoulli_number`

## Implementation notes
TODO (optional)

## References
Introduction to Cyclotomic Fields, Washington (Chapter 12, Section 2)

## Tags
p-adic, L-function, Bernoulli measure, Dirichlet character
-/

-- this should be in a file called `dirichlet_character.lean`

/-- A Dirichlet character is defined as a multiplicative homomorphism which is periodic. -/
abbreviation dirichlet_character (R : Type*) [comm_monoid R] (n : ℕ) := zmod n →* R

namespace dirichlet_character

variables {R : Type*} [comm_monoid R] {n : ℕ} (χ : dirichlet_character R n)

lemma is_periodic (m : ℕ) (hm : n ∣ m) (a : ℤ) : χ (a + m) = χ a :=
begin
  rw ← zmod.nat_coe_zmod_eq_zero_iff_dvd at hm,
  simp [hm],
end

def change_level {m : ℕ} (hm : n ∣ m) (χ : dirichlet_character R n) : dirichlet_character R m :=
χ.comp (zmod.cast_hom hm (zmod n))

def mul {m : ℕ} (χ₁ : dirichlet_character R n) (χ₂ : dirichlet_character R m) :
  dirichlet_character R (lcm n m) :=
change_level (dvd_lcm_left n m) χ₁ * change_level (dvd_lcm_right n m) χ₂


def factors_through (χ : dirichlet_character R n) (d : ℕ) : Prop :=
d ∣ n ∧ ∃ χ₀ : dirichlet_character R d, ∀ a : ℤ, gcd a n = 1 → χ₀ d = χ d

/-- The set of natural numbers for which a Dirichlet character is periodic. -/
def conductor_set (χ : dirichlet_character R n) : set ℕ :=
  {d : ℕ | factors_through χ d}

lemma level_mem_conductor_set : n ∈ conductor_set χ :=
⟨dvd_rfl, χ, λ _ _, rfl⟩

-- do you need this?
lemma mem_dvd {d m : ℕ} (h₁ : d ∣ m) (h₂ : m ∣ n)
  (mem : d ∈ conductor_set χ) : m ∈ conductor_set χ :=
begin
  sorry
end

/-- The minimum natural number n for which a Dirichlet character is periodic.
  The Dirichlet character χ can then alternatively be reformulated on ℤ/nℤ. -/
noncomputable def conductor : ℕ := Inf (conductor_set χ)

lemma mem_conductor : conductor χ ∈ conductor_set χ :=
Inf_mem (set.nonempty_of_mem χ.level_mem_conductor_set)

-- false
lemma mem_lcm (m : ℕ) : lcm (conductor χ) m ∈ conductor_set χ := sorry

-- now not needed
--lemma map_mul' {m : ℕ} (x y : zmod m) : χ ↑(x * y) = χ ↑x * (χ.to_monoid_hom) ↑y := sorry

lemma conductor_one {S : Type*} [mul_one_class S] : conductor (1 : dirichlet_character R n) = 1 := sorry

--lemma conductor_one_dvd_nat {S : Type*} [mul_one_class S] (n : ℕ) :
--  conductor (1 : dirichlet_character S) ∣ n := by {rw conductor_one, apply one_dvd _, }

/-- Reformulating a Dirichlet character modulo an element of the `conductor_set`. -/
abbreviation dirichlet_character_to_zmod {m : ℕ} (mem : m ∈ conductor_set χ) : mul_hom (zmod m) R :=
{ to_fun := λ x, χ.to_monoid_hom (x : ℤ),
  map_mul' := map_mul' χ, }

/-- Using a multiplicative homomorphism ℤ/mℤ to construct a Dirichlet character having modulus m. -/
abbreviation zmod_to_dirichlet_character {m : ℕ} (χ : mul_hom (zmod m) R) : dirichlet_character R :=
{ to_monoid_hom := mul_hom.comp χ (int.cast_ring_hom (zmod m)).to_monoid_hom,
  periodic := ⟨m, λ a, by simp only [int.coe_cast_ring_hom, int.cast_coe_nat,
    monoid_hom.coe_eq_to_mul_hom, add_zero, int.cast_add, ring_hom.coe_monoid_hom,
    ring_hom.to_monoid_hom_eq_coe, function.comp_app, zmod.nat_cast_self,
    monoid_hom.to_mul_hom_coe, mul_hom.coe_comp]⟩, }

lemma mem_zmod_to_dirichlet_character {m : ℕ} (χ : mul_hom (zmod m) R) :
  m ∈ conductor_set (zmod_to_dirichlet_character χ) := sorry

noncomputable instance {R : Type*} [comm_semigroup R] : has_mul (dirichlet_character R) :=
⟨λ f g, begin
    apply zmod_to_dirichlet_character _,
    { exact lcm (conductor f) (conductor g), },
    have : (lcm (conductor f) (conductor g)) ∈ conductor_set g,
    { convert mem_lcm g (conductor f) using 1, rw lcm_comm, },
    refine ⟨λ x, dirichlet_character_to_zmod f (mem_lcm f (conductor g)) x *
      dirichlet_character_to_zmod g this x,
      λ x y, by {rw [mul_hom.map_mul, mul_hom.map_mul, mul_mul_mul_comm]}⟩,
  end,⟩
--should I find an equiv similar to zmod.lift?

open_locale big_operators
lemma sum_dirichlet_character {S : Type*} [add_comm_monoid S] [has_mul S] (ψ : dirichlet_character S) :
  ∑ i in finset.range (conductor ψ).succ, ψ.to_monoid_hom i = 0 := sorry

section general_bernoulli_number
variables {S : Type*} [semiring S] [algebra ℚ S] (ψ : dirichlet_character S)

/-- The generalized Bernoulli number -/
noncomputable def general_bernoulli_number {F : ℕ} (n : ℕ) (dvd : conductor ψ ∣ F) : S :=
  F^(n - 1) * (∑ a in finset.range F.succ, ψ.to_monoid_hom a *
    algebra_map ℚ S ((bernoulli_poly n).eval (a/F : ℚ)))

namespace general_bernoulli_number

lemma general_bernoulli_number_one_eval_one :
general_bernoulli_number (1 : dirichlet_character S) 1 (conductor_one_dvd_nat 1) =
  algebra_map ℚ S (1/2 : ℚ) := sorry

lemma general_bernoulli_number_one_eval {n : ℕ} (ne_one : n ≠ 1) :
general_bernoulli_number (1 : dirichlet_character S) 1 (conductor_one_dvd_nat 1) =
  algebra_map ℚ S (bernoulli n) := sorry

end general_bernoulli_number
end general_bernoulli_number

--example {α β : Type*}

/-local attribute [instance] zmod.topological_space
noncomputable def p_adic_L_function' (p : ℕ) [fact (nat.prime p)] (d : ℕ) (R : Type*) [normed_comm_ring R]
[complete_space R] [char_zero R] (inj : ℤ_[p] → R) (m : ℕ)
{χ : mul_hom (zmod (d * p ^ m)) R} (hcond : conductor (zmod_to_dirichlet_character χ) = d * p^m)
--(χ : mul_hom (units (zmod (d * p ^ m))) R)
(w : weight_space (units (zmod d) × units ℤ_[p]) R) {c : ℕ}
[fact (0 < d)] [semi_normed_algebra ℚ R] (hd : d.gcd p = 1) [fact (0 < m)]
  (h : function.injective inj) (cont : continuous inj) (hc : c.gcd p = 1) (hc' : c.gcd d = 1)
    (na : ∀ (n : ℕ) (f : ℕ → R), ∥∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
    --(hu : is_unit (f' p d R m hd hc hc' χ w))
    : R :=
  --(f p d R m χ w hd hc hc' hu) *
    (measure.integral (bernoulli_measure' p d R hc hc' hd na)
      ⟨(λ (a : (units (zmod d) × units ℤ_[p])), ((pri_dirichlet_character_extend p d R m hd (mul_hom.comp (units.coe_hom R).to_mul_hom (units.map (is_mul_hom.to_is_monoid_hom χ)))) a) *
  (inj (teichmuller_character p a.snd))^(p - 2) * (w.to_fun a : R)), cont_paLf p d R inj m χ w hd cont⟩)-/
--is there not a way to go between mul_hom and is_mul_hom, similarly for monoid_hom?
