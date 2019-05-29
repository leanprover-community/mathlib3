# 100 Theorems

In this file we collect information on how Lean is doing
on the 100 theorems challenge: http://www.cs.ru.nl/~freek/100/.

## 1. The Irrationality of the Square Root of 2

```lean
theorem irr_sqrt_two : irrational (sqrt 2) :=
```

* Author: Abhimanyu Pallavi Sudhir
* Link: https://github.com/leanprover-community/mathlib/blob/739d28a60f347e7357b76cd2d24e41460e49a456/src/data/real/irrational.lean#L63

## 2. Fundamental Theorem of Algebra

```lean
lemma exists_root {f : polynomial ℂ} (hf : 0 < degree f) : ∃ z : ℂ, is_root f z :=
```

* Author: Chris Hughes
* Link: https://github.com/leanprover-community/mathlib/blob/0b350228544244f2861ec8afc84dad0c27113a73/src/analysis/complex/polynomial.lean#L28

<!--
## 3. The Denumerability of the Rational Numbers

* Author:
* Link:

## 4. Pythagorean Theorem

* Author:
* Link:

## 5. Prime Number Theorem

* Author:
* Link:

## 6. Godel’s Incompleteness Theorem

* Author:
* Link:
-->

## 7. Law of Quadratic Reciprocity

```lean
theorem quadratic_reciprocity (hp : nat.prime p) (hq : nat.prime q) (hp1 : p % 2 = 1) (hq1 : q % 2 = 1) (hpq : p ≠ q) :
legendre_sym p q hq * legendre_sym q p hp = (-1) ^ ((p / 2) * (q / 2)) :=
```

* Author: Chris Hughes
* Link: https://github.com/leanprover-community/mathlib/blob/fb8001d6fd786a67e01d022241f01b7017ae0825/src/data/zmod/quadratic_reciprocity.lean#L503

<!--
## 8. The Impossibility of Trisecting the Angle and Doubling the Cube

* Author:
* Link:

## 9. The Area of a Circle

* Author:
* Link:

## 10. Euler’s Generalization of Fermat’s Little Theorem

* Author:
* Link:
-->

## 11. The Infinitude of Primes

```lean
theorem exists_infinite_primes (n : ℕ) : ∃ p, p ≥ n ∧ prime p :=
```

* Author: Jeremy Avigad
* Link: https://github.com/leanprover-community/mathlib/blob/d935bc312fac7eca7ef08b16ca06079145b437f2/src/data/nat/prime.lean#L231

<!--
## 12. The Independence of the Parallel Postulate

* Author:
* Link:

## 13. Polyhedron Formula

* Author:
* Link:

## 14. Euler’s Summation of 1 + (1/2)^2 + (1/3)^2 + ….

* Author:
* Link:

## 15. Fundamental Theorem of Integral Calculus

* Author:
* Link:

## 16. Insolvability of General Higher Degree Equations

* Author:
* Link: -->

## 17. De Moivre’s Theorem
```lean
theorem cos_add_sin_mul_I_pow (n : ℕ) (z : ℂ) :
  (cos z + sin z * I) ^ n = cos (↑n * z) + sin (↑n * z) * I
```
* Author: mathlib
* Link: https://github.com/leanprover-community/mathlib/blob/d4c7b7a6c26fed7f526234fa9c7f57eaf4f7b587/src/data/complex/exponential.lean#L678

<!-- ## 18. Liouville’s Theorem and the Construction of Trancendental Numbers

* Author:
* Link:

## 19. Four Squares Theorem

* Author:
* Link:

## 20. All Primes Equal the Sum of Two Squares

* Author:
* Link:

## 21. Green’s Theorem

* Author:
* Link:

## 22. The Non-Denumerability of the Continuum

* Author:
* Link:

## 23. Formula for Pythagorean Triples

* Author:
* Link:
-->

## 24. The Undecidability of the Continuum Hypothesis

* **Partial progress**: The unprovability of the continuum hypothesis. Caveat: ZFC is extended with a limited number of function symbols in this statement.
```lean
theorem CH_f_unprovable : ¬ (ZFC' ⊢' CH_f)
```
* Author: Floris van Doorn and Jesse Michael Han
* Link: [result](https://github.com/flypitch/flypitch/blob/ffd4ff5152a7ccb170accf7709be734e69c3d98d/src/zfc'.lean#L449), [website](https://flypitch.github.io/)


## 25. Schroeder-Bernstein Theorem
```lean
theorem schroeder_bernstein {f : α → β} {g : β → α}
  (hf : injective f) (hg : injective g) : ∃h:α→β, bijective h
```
* Author: Mario Carneiro
* Link: https://github.com/leanprover-community/mathlib/blob/024da4095269392369f0d818be5f0ada9b173e18/src/set_theory/schroeder_bernstein.lean#L21

<!--
## 26. Leibnitz’s Series for Pi

* Author:
* Link:

## 27. Sum of the Angles of a Triangle

* Author:
* Link:

## 28. Pascal’s Hexagon Theorem

* Author:
* Link:

## 29. Feuerbach’s Theorem

* Author:
* Link:

## 30. The Ballot Problem

* Author:
* Link:

## 31. Ramsey’s Theorem

* Author:
* Link:

## 32. The Four Color Problem

* Author:
* Link:

## 33. Fermat’s Last Theorem

* Author:
* Link:

## 34. Divergence of the Harmonic Series

* Author:
* Link:

## 35. Taylor’s Theorem

* Author:
* Link:

## 36. Brouwer Fixed Point Theorem

* Author:
* Link:

## 37. The Solution of a Cubic

* Author:
* Link:

## 38. Arithmetic Mean/Geometric Mean

* Author:
* Link:
-->

## 39. Solutions to Pell’s Equation
```lean
theorem eq_pell {x y : ℕ} (hp : x*x - d*y*y = 1) : ∃n, x = xn n ∧ y = yn n
```
* Remark: `d` is defined to be `a*a - 1` for an arbitrary `a > 1`.
* Author: Mario Carneiro
* Link: https://github.com/leanprover-community/mathlib/blob/d935bc312fac7eca7ef08b16ca06079145b437f2/src/number_theory/pell.lean#L161

<!--
## 40. Minkowski’s Fundamental Theorem

* Author:
* Link:

## 41. Puiseux’s Theorem

* Author:
* Link:

## 42. Sum of the Reciprocals of the Triangular Numbers

* Author:
* Link:

## 43. The Isoperimetric Theorem

* Author:
* Link:
-->

## 44. The Binomial Theorem

```lean
theorem add_pow :
∀ n : ℕ, (x + y) ^ n = (range (succ n)).sum (λ m, x ^ m * y ^ (n - m) * choose n m)
```

* Author: Chris Hughes
* Link: https://github.com/leanprover-community/mathlib/blob/22948763023aff7b0a9634b180e7838b39a3803d/src/data/nat/choose.lean#L25

<!--
## 45. The Partition Theorem

* Author:
* Link:

## 46. The Solution of the General Quartic Equation

* Author:
* Link:

## 47. The Central Limit Theorem

* Author:
* Link:

## 48. Dirichlet’s Theorem

* Author:
* Link:

## 49. The Cayley-Hamilton Thoerem

* Author:
* Link:

## 50. The Number of Platonic Solids

* Author:
* Link:

## 51. Wilson’s Theorem

* Author:
* Link:
-->
## 52. The Number of Subsets of a Set
```lean
theorem card_powerset (s : finset α) : card (powerset s) = 2 ^ card s
```
* Author: mathlib
* Link: https://github.com/leanprover-community/mathlib/blob/00aaf05a00b928ea9ac09721d87ae5d2ca1ae5a1/src/data/finset.lean#L1277
<!--
## 53. Pi is Trancendental

* Author:
* Link:

## 54. Konigsberg Bridges Problem

* Author:
* Link:

## 55. Product of Segments of Chords

* Author:
* Link:

## 56. The Hermite-Lindemann Transcendence Theorem

* Author:
* Link:

## 57. Heron’s Formula

* Author:
* Link:
-->
## 58. Formula for the Number of Combinations

```lean
theorem card_powerset_len (n : ℕ) (s : finset α) :
  card (powerset_len n s) = nat.choose (card s) n

theorem mem_powerset_len {n} {s t : finset α} :
  s ∈ powerset_len n t ↔ s ⊆ t ∧ card s = n
```
* Author: mathlib <!--Jeremy Avigad in lean 2-->
* Link: https://github.com/leanprover/lean2/blob/227fcad22ab2bc27bb7471be7911075d101ba3f9/library/theories/combinatorics/choose.lean#L208



<!--
## 59. The Laws of Large Numbers

* Author:
* Link:
-->
## 60. Bezout’s Theorem
```lean
theorem gcd_eq_gcd_ab (a b : α) : (gcd a b : α) = a * gcd_a a b + b * gcd_b a b
```
* Author: Chris Hughes
* Link: https://github.com/leanprover-community/mathlib/blob/4845b663c182704738868db5861ffb4c6056be23/src/algebra/euclidean_domain.lean#L233
<!--
## 61. Theorem of Ceva

* Author:
* Link:

## 62. Fair Games Theorem

* Author:
* Link:
-->
## 63. Cantor’s Theorem
```lean
theorem cantor : ∀(a : cardinal.{u}), a < 2 ^ a
```
* Author: mathlib <!-- Mario and/or Johannes -->
* Link: https://github.com/leanprover-community/mathlib/blob/e66e1f30d8a0a006ff93a309cc202ab4deaebf04/src/set_theory/cardinal.lean#L259
<!--
## 64. L’Hopital’s Rule

* Author:
* Link:

## 65. Isosceles Triangle Theorem

* Author:
* Link:
-->
## 66. Sum of a Geometric Series
```lean
theorem geom_sum [division_ring α] {x : α} (h : x ≠ 1) (n : ℕ) :
  (range n).sum (λ i, x^i) = (x^n-1)/(x-1)
```
* Author: Sander R. Dahmen
* Link: https://github.com/leanprover-community/mathlib/blob/d935bc312fac7eca7ef08b16ca06079145b437f2/src/algebra/big_operators.lean#L571

<!--
## 67. e is Transcendental

* Author:
* Link:
-->
## 68. Sum of an arithmetic series
```lean
lemma sum_range_id (n : ℕ) : (finset.range n).sum (λi, i) = (n * (n - 1)) / 2
```
* Author: Johannes Hölzl
* Link: https://github.com/leanprover-community/mathlib/blob/d935bc312fac7eca7ef08b16ca06079145b437f2/src/algebra/big_operators.lean#L607

## 69. Greatest Common Divisor Algorithm
```lean
def gcd : α → α → α
| a := λ b, if a0 : a = 0 then b else
  have h:_ := mod_lt b a0,
  gcd (b%a) a
using_well_founded {dec_tac := tactic.assumption,
  rel_tac := λ _ _, `[exact ⟨_, r_well_founded α⟩]}

theorem gcd_dvd (a b : α) : gcd a b ∣ a ∧ gcd a b ∣ b
theorem dvd_gcd {a b c : α} : c ∣ a → c ∣ b → c ∣ gcd a b
```
* Author: mathlib
* Link: https://github.com/leanprover-community/mathlib/blob/4845b663c182704738868db5861ffb4c6056be23/src/algebra/euclidean_domain.lean#L127

<!--
## 70. The Perfect Number Theorem

* Author:
* Link:
-->
## 71. Order of a Subgroup
```lean
lemma card_subgroup_dvd_card (s : set α) [is_subgroup s] [fintype s] :
  fintype.card s ∣ fintype.card α
```
* Author: Chris Hughes
* Link: https://github.com/leanprover-community/mathlib/blob/4845b663c182704738868db5861ffb4c6056be23/src/group_theory/order_of_element.lean#L56


## 72. Sylow’s Theorem

```lean
lemma exists_subgroup_card_pow_prime  {G : Type u} [group G] [fintype G] {p : ℕ} :
  ∀ {n : ℕ} (hp : nat.prime p) (hdvd : p ^ n ∣ card G),
  ∃ H : set G, is_subgroup H ∧ fintype.card H = p ^ n

lemma sylow_conjugate [fintype G] {p : ℕ} (hp : prime p)
  (H K : set G) [is_sylow H hp] [is_sylow K hp] :
  ∃ g : G, H = conjugate_set g K

lemma card_sylow_dvd [fintype G] {p : ℕ} (hp : prime p) :
  card {H : set G // is_sylow H hp} ∣ card G

lemma card_sylow_modeq_one [fintype G] {p : ℕ} (hp : prime p) :
  card {H : set G // is_sylow H hp} ≡ 1 [MOD p]
```

* Author: Chris Hughes
* Link: [1](https://github.com/leanprover-community/mathlib/blob/d935bc312fac7eca7ef08b16ca06079145b437f2/src/group_theory/sylow.lean#L184) [2](
https://github.com/ChrisHughes24/Sylow/blob/7185e33eeb6d28ea1a423492e7b4a8634aa9723d/src/sylow.lean#L885) [3.1](https://github.com/ChrisHughes24/Sylow/blob/7185e33eeb6d28ea1a423492e7b4a8634aa9723d/src/sylow.lean#L925) [3.2](https://github.com/ChrisHughes24/Sylow/blob/7185e33eeb6d28ea1a423492e7b4a8634aa9723d/src/sylow.lean#L944). Theorem 3.3 (number of Sylow sugroups is the cardinality of the normalizer of any of them) is not proven as a separate fact, but used in the other results [here](https://github.com/ChrisHughes24/Sylow/blob/7185e33eeb6d28ea1a423492e7b4a8634aa9723d/src/sylow.lean#L934).

<!--
## 73. Ascending or Descending Sequences

* Author:
* Link:
-->
## 74. The Principle of Mathematical Induction
* Automatically generated when defining the natural numbers
```lean
inductive nat
| zero : nat
| succ (n : nat) : nat

#print nat.rec
-- protected eliminator nat.rec : Π {C : ℕ → Sort l}, C 0 → (Π (n : ℕ), C n → C (nat.succ n)) → Π (n : ℕ), C n
```
* Author: Leonardo de Moura
* Link: https://github.com/leanprover/lean/blob/cbd2b6686ddb566028f5830490fe55c0b3a9a4cb/library/init/core.lean#L293

<!--
## 75. The Mean Value Theorem

* Author:
* Link:

## 76. Fourier Series

* Author:
* Link:

## 77. Sum of kth powers

* Author:
* Link:

## 78. The Cauchy-Schwarz Inequality

* Author:
* Link:
-->

## 79. The Intermediate Value Theorem
```lean
lemma real.intermediate_value {f : ℝ → ℝ} {a b t : ℝ}
  (hf : ∀ x, a ≤ x → x ≤ b → tendsto f (nhds x) (nhds (f x)))
  (ha : f a ≤ t) (hb : t ≤ f b) (hab : a ≤ b) : ∃ x : ℝ, a ≤ x ∧ x ≤ b ∧ f x = t
```
* Author: mathlib <!-- Rob Lewis and Chris Hughes -->
* Link: https://github.com/leanprover-community/mathlib/blob/4845b663c182704738868db5861ffb4c6056be23/src/topology/instances/real.lean#L340


## 80. The Fundamental Theorem of Arithmetic
The integers form a unique factorization domain by the first three declarations. A unique factorization domain gives most of the fundamental theorem of arithmetic, and the uniqueness is then proven for them.
```lean
instance int.euclidean_domain : euclidean_domain ℤ
instance euclidean_domain.to_principal_ideal_domain [euclidean_domain α] : principal_ideal_domain α
noncomputable def to_unique_factorization_domain [principal_ideal_domain α] : unique_factorization_domain α

class unique_factorization_domain (α : Type*) [integral_domain α] :=
(factors : α → multiset α)
(factors_prod : ∀{a : α}, a ≠ 0 → (factors a).prod ~ᵤ a)
(prime_factors : ∀{a : α}, a ≠ 0 → ∀x∈factors a, prime x)

lemma unique [integral_domain α] [unique_factorization_domain α] : ∀{f g : multiset α},
  (∀x∈f, irreducible x) → (∀x∈g, irreducible x) → f.prod ~ᵤ g.prod →
  multiset.rel associated f g
```
* Author: mathlib
* Link: [1](https://github.com/leanprover-community/mathlib/blob/4845b663c182704738868db5861ffb4c6056be23/src/algebra/euclidean_domain.lean#L320) [2](https://github.com/leanprover-community/mathlib/blob/4845b663c182704738868db5861ffb4c6056be23/src/ring_theory/principal_ideal_domain.lean#L71) [3](https://github.com/leanprover-community/mathlib/blob/4845b663c182704738868db5861ffb4c6056be23/src/ring_theory/principal_ideal_domain.lean#L158) [4](https://github.com/leanprover-community/mathlib/blob/4845b663c182704738868db5861ffb4c6056be23/src/ring_theory/unique_factorization_domain.lean#L29) [5](https://github.com/leanprover-community/mathlib/blob/master/src/ring_theory/unique_factorization_domain.lean#L90)

<!--
## 81. Divergence of the Prime Reciprocal Series

* Author:
* Link:
-->
## 82. Dissection of Cubes (J.E. Littlewood’s ‘elegant’ proof)
```lean
theorem cannot_cube_a_cube :
  ∀{n : ℕ}, n ≥ 3 →                              -- In ℝ^n for n ≥ 3
  ∀{ι : Type} [fintype ι] {cs : ι → cube n},     -- given a finite collection of (hyper)cubes
  2 ≤ cardinal.mk ι →                            -- containing at least two elements
  pairwise (disjoint on (cube.to_set ∘ cs)) →    -- which is pairwise disjoint
  (⋃(i : ι), (cs i).to_set) = unit_cube.to_set → -- whose union is the unit cube
  injective (cube.w ∘ cs) →                      -- such that the widths of all cubes are different
  false
```
* Author: Floris van Doorn
* Link: https://github.com/fpvandoorn/mathlib/blob/92f6874c49674f04b175637335bb21cf206bb74a/src/cube.lean#L586
<!--
## 83. The Friendship Theorem

* Author:
* Link:

## 84. Morley’s Theorem

* Author:
* Link:

## 85. Divisibility by 3 Rule

* Author:
* Link:
-->
## 86. Lebesgue Measure and Integration
```lean
instance : measure_space ℝ

def lintegral (f : α → ennreal) : ennreal :=
⨆ (s : α →ₛ ennreal) (hf : f ≥ s), s.integral
```
* Author: Johannes Hölzl
* Link: [measure](https://github.com/leanprover-community/mathlib/blob/f0f06ca1d07b441eda86342413b0088afb8aa875/src/measure_theory/lebesgue_measure.lean#L224) and [integral](https://github.com/leanprover-community/mathlib/blob/3461399615e4b2bee12f1bc5bbf0c337d669b7b5/src/measure_theory/integration.lean#L528)
<!--
## 87. Desargues’s Theorem

* Author:
* Link:

## 88. Derangements Formula

* Author:
* Link:

## 89. The Factor and Remainder Theorems

* Author:
* Link:

## 90. Stirling’s Formula

* Author:
* Link:

## 91. The Triangle Inequality

* Author:
* Link:

## 92. Pick’s Theorem

* Author:
* Link:

## 93. The Birthday Problem

* Author:
* Link:

## 94. The Law of Cosines

* Author:
* Link:

## 95. Ptolemy’s Theorem

* Author:
* Link: -->

## 96. Principle of Inclusion/Exclusion

```lean
lemma inclusion_exclusion {A : Type u} [fintype A] [decidable_eq A]
  {B : Type u} [fintype B] [decidable_eq B] (E : finset (A × B)) :
 ((clear_rows E).card : ℤ) =
  (@univ B _).powerset.sum (λ U, (card_sign U) * (card (col_inter E U)))
```
* Author: Neil Strickland
* Link: https://github.com/NeilStrickland/lean_lib/blob/f88d162da2f990b87c4d34f5f46bbca2bbc5948e/src/combinatorics/matching.lean#L304

<!-- ## 97. Cramer’s Rule

* Author:
* Link:

## 98. Bertrand’s Postulate

* Author:
* Link:

## 99. Buffon Needle Problem

* Author:
* Link:

## 100. Descartes Rule of Signs

* Author:
* Link:
-->
