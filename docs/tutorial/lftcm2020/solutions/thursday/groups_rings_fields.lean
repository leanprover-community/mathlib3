import linear_algebra.finite_dimensional
import ring_theory.algebraic
import data.zmod.basic
import data.real.basic
import tactic

/-!
```
  ____
 / ___|_ __ ___  _   _ _ __  ___
| |  _| '__/ _ \| | | | '_ \/ __|
| |_| | | | (_) | |_| | |_) \__ \_
 \____|_|  \___/ \__,_| .__/|___( )
                      |_|       |/


             _ __  (_)  _ __     __ _   ___
            | '__| | | | '_ \   / _` | / __|
            | |    | | | | | | | (_| | \__ \  _
            |_|    |_| |_| |_|  \__, | |___/ ( )
                                |___/        |/


                                         _      __   _          _       _
                      __ _   _ __     __| |    / _| (_)   ___  | |   __| |  ___
                     / _` | | '_ \   / _` |   | |_  | |  / _ \ | |  / _` | / __|
                    | (_| | | | | | | (_| |   |  _| | | |  __/ | | | (_| | \__ \
                     \__,_| |_| |_|  \__,_|   |_|   |_|  \___| |_|  \__,_| |___/

```
-/



/-! ## Reminder on updating the exercises

These instructions are now available at:
https://leanprover-community.github.io/lftcm2020/exercises.html

To get a new copy of the exercises,
run the following commands in your terminal:

```
leanproject get lftcm2020
cp -r lftcm2020/src/exercises_sources/ lftcm2020/src/my_exercises
code lftcm2020
```

To update your exercise files, run the following commands:

```
cd /path/to/lftcm2020
git pull
leanproject get-mathlib-cache
```

Don’t forget to copy the updated files to `src/my_exercises`.

-/



/-! ## What do we have?

Too much to cover in detail in 10 minutes.

Take a look at the “General algebra” section on
https://leanprover-community.github.io/mathlib-overview.html

All the basic concepts are there:
`group`, `ring`, `field`, `module`, etc...

Also versions that are compatible with an ordering, like `ordered_ring`

And versions that express compatibility with a topology: `topological_group`

Finally constructions, like `polynomial R`, or `mv_polynomial σ R`,
or `monoid_algebra K G`, or `ℤ_[p]`, or `zmod n`, or `localization R S`.
-/



/-! ## Morphisms

We are in the middle of a transition to “bundled” morphisms.
(Why? Long story... but they work better with `simp`)

* `X → Y`   -- ordinary function
* `X →+ Y`  -- function respects `0` and `+`
* `X →* Y`  -- function respects `1` and `*`
* `X →+* Y` -- function respects `0`, `1`, `+`, `*` (surprise!)

-/

section
variables {R S : Type*} [ring R] [ring S]

-- We used to write
example (f : R → S) [is_ring_hom f] : true := trivial

-- But now we write
example (f : R →+* S) : true := trivial

/-
This heavily relies on the “coercion to function”
that we have seen a couple of times this week.
-/
end


/-! ## Where are these things in the library?

`algebra/`         for basic definitions and properties; “algebraic hierarchy”

`group_theory/`  ⎫
`ring_theory/`   ⎬ “advanced” and “specialised” material
`field_theory/`  ⎭

`data/`            definitions and examples


To give an idea:

* `algebra/ordered_ring.lean`

* `ring_theory/noetherian.lean`

* `field_theory/chevalley_warning.lean`

* `data/nat/*.lean`, `data/real/*.lean`, `data/padics/*.lean`

-/



/-! ## How to find things (search tools)

* `library_search` -- it often helps to carve out
                      the exact lemma statement that you are looking for

* online documentation: https://leanprover-community.github.io/mathlib_docs/
  new search bar under construction

* Old-skool: `grep`

* Search in VS Code:

  - `Ctrl - Shift - F`
    -- don't forget to change settings, to search everywhere
    -- click the three dots (`…`) below the search bar
    -- disable the blue cogwheel

  - `Ctrl - P`        -- search for filenames
  - `Ctrl - P`, `#`   -- search for lemmas and definitions

-/



/-! ## How to find things (autocomplete)

Mathlib follows pretty strict naming conventions:

```
/-- The binomial theorem-/
theorem add_pow [comm_semiring α] (x y : α) (n : ℕ) :
  (x + y) ^ n = ∑ m in range (n + 1), x ^ m * y ^ (n - m) * choose n m :=
(commute.all x y).add_pow n
```

After a while, you get the hang of this,
and you can start guessing names.

-/

open_locale big_operators -- nice notation ∑, ∏
open finset -- `finset.range n` is the finite set `{0,1,..., n-1}`

-- Demonstrate autocompletion
example (f : ℕ → ℝ) (n : ℕ) :
  57 + ∑ i in range (n+1), f i = 57 + f n + ∑ i in range n, f i :=
begin
  sorry
end



/-! ## How to find things (jump to definition)

Another good strategy for finding useful results about `X`,
is to “jump to the definition” and scroll through the next 3 screens of lemmas.
If you are looking for a basic fact about `X`, you will usually find it there.

-/

-- demonstrate “jump to definition”
#check polynomial.coeff













/-! ## Exercise 1
We will warm up with a well-known result:
“Subgroups of abelian groups are normal.”

Hints for proving this result:
  * Notice that `normal` is a structure,
    which you can see by going to the definition.
    The `constructor` tactic will help you to get started.
-/

namespace add_subgroup
variables {A : Type*} [add_comm_group A]

lemma normal_of_add_comm_group (H : add_subgroup A) : normal H :=
begin
  -- sorry
  constructor,
  intros x hx y,
  simpa,
  -- sorry
end

end add_subgroup



/-! ## Exercise 2
The following exercise will show the classical fact:
“Finite field extensions are algebraic.”

Hints for proving this result:
  * Look up the definition of `finite_dimensional`.
  * Search the library for useful lemmas about `is_algebraic` and `is_integral`.
-/

namespace algebra
variables {K L : Type*} [field K] [field L] [algebra K L] [finite_dimensional K L]

lemma is_algebraic_of_finite_dimensional : is_algebraic K L :=
begin
  -- sorry
  intro x,
  rw is_algebraic_iff_is_integral,
  apply is_integral_of_noetherian',
  assumption,
  -- sorry
end

end algebra



/-! ## Exercise 3
In this exercise we will define the Frobenius morphism.
-/

section
variables (p : ℕ) [fact p.prime]
variables (K : Type*) [field K] [char_p K p]

/-! ### Subchallenge -/
lemma add_pow_char' (x y : K) : (x + y) ^ p = x ^ p + y ^ p :=
begin
  -- Hint: `add_pow_char` already exists.
  -- You can use it if you don't want to spend time on this.

  /- Hints if you do want to attempt this:
  * `finset.sum_range_succ`
  * `finset.sum_eq_single`
  * `nat.prime.ne_zero`
  * `char_p.cast_eq_zero_iff`
  * `nat.prime.dvd_choose_self`
  -/
  -- sorry
  rw add_pow,
  rw sum_range_succ,
  simp only [nat.choose_self, mul_one, nat.sub_self, nat.cast_one, add_right_inj, pow_zero],
  rw sum_eq_single 0,
  { simp only [mul_one, one_mul, nat.choose_zero_right, nat.sub_zero, nat.cast_one, pow_zero], },
  { intros i hi hi0,
    convert mul_zero _,
    rw char_p.cast_eq_zero_iff K p,
    apply nat.prime.dvd_choose_self _ _ (by assumption),
    { rwa nat.pos_iff_ne_zero, },
    { simpa using hi } },
  { intro h,
    simp only [le_zero_iff_eq, mem_range, not_lt] at h,
    exfalso,
    apply nat.prime.ne_zero _ h, assumption },
  -- sorry
end

def frobenius_hom : K →+* K :=
{ to_fun := λ x, x^p,
  map_zero' :=
  begin
    -- Hint: `zero_pow`, search for lemmas near `nat.prime`
    -- sorry
      rw zero_pow,
      apply nat.prime.pos,
      assumption,
    -- sorry
  end,
  map_one' :=
  begin
    -- sorry
      simp,
    -- sorry
  end,
  map_mul' :=
  begin
    -- sorry
      intros x y,
      rw mul_pow,
    -- sorry
  end,
  map_add' :=
  begin
    -- Hint: `add_pow_char` -- can you prove that one yourself?
    -- sorry
      intros x y,
      rw add_pow_char',
    -- sorry
  end }

end



/-! ## Exercise 4 [challenging]
The next exercise asks to show that a monic polynomial `f ∈ ℤ[X]` is irreducible
if it is irreducible modulo a prime `p`.
This fact is also not in mathlib.

Hint: prove the helper lemma that is stated first.

Follow-up question:
Can you generalise `irreducible_of_irreducible_mod_prime`?
-/

namespace polynomial
variables {R S : Type*} [semiring R] [integral_domain S] (φ : R →+* S)

/-
Useful library lemmas (in no particular order):

- `degree_eq_zero_of_is_unit`
- `eq_C_of_degree_eq_zero`
- `is_unit.map'`
- `leading_coeff_C`
- `degree_map_eq_of_leading_coeff_ne_zero`
- `is_unit.map'`
- `is_unit.ne_zero`
-/

lemma is_unit_of_is_unit_leading_coeff_of_is_unit_map
  (f : polynomial R) (hf : is_unit (leading_coeff f)) (H : is_unit (map φ f)) :
  is_unit f :=
begin
  -- sorry
  have key := degree_eq_zero_of_is_unit H,
  have hφ_lcf : φ (leading_coeff f) ≠ 0,
  { apply is_unit.ne_zero,
    apply is_unit.map',
    assumption, },
  rw degree_map_eq_of_leading_coeff_ne_zero _ hφ_lcf at key,
  rw eq_C_of_degree_eq_zero key,
  apply is_unit.map',
  rw [eq_C_of_degree_eq_zero key, leading_coeff_C] at hf,
  exact hf,
  -- sorry
end

/-
Useful library lemmas (in no particular order):

- `is_unit.map'`
- `is_unit_of_mul_is_unit_left` (also `_right`)
- `leading_coeff_mul`
- `is_unit_of_is_unit_leading_coeff_of_is_unit_map` (the helper lemma we just proved)
- `is_unit_one`
-/

lemma irreducible_of_irreducible_mod_prime (f : polynomial ℤ) (p : ℕ) [fact p.prime]
  (h_mon : monic f) (h_irr : irreducible (map (int.cast_ring_hom (zmod p)) f)) :
  irreducible f :=
begin
  -- sorry
  split,
  { intro hf,
    apply h_irr.1,
    apply is_unit.map',
    exact hf, },
  { intros g h Hf,
    have aux : is_unit (leading_coeff g * leading_coeff h),
    { rw [← leading_coeff_mul, ← Hf, h_mon.leading_coeff], exact is_unit_one, },
    have lc_g_unit : is_unit (leading_coeff g),
    { apply is_unit_of_mul_is_unit_left aux, },
    have lc_h_unit : is_unit (leading_coeff h),
    { apply is_unit_of_mul_is_unit_right aux, },
    rw Hf at h_irr,
    simp at h_irr,
    have key_fact := h_irr.2 _ _ rfl,
    cases key_fact with Hg Hh,
    { left,
      apply is_unit_of_is_unit_leading_coeff_of_is_unit_map _ g lc_g_unit Hg, },
    { right,
      apply is_unit_of_is_unit_leading_coeff_of_is_unit_map _ h lc_h_unit Hh, } }
  -- sorry
end

end polynomial





-- SCROLL DOWN FOR THE BONUS EXERCISE



















section
/-! ## Bonus exercise (wicked hard) -/

noncomputable theory       -- because `polynomial` is noncomputable (implementation detail)
open polynomial            -- we want to write `X`, instead of `polynomial.X`

/-
First we make some definitions
Scroll to the end for the actual exercise
-/

def partial_ramanujan_tau_polynomial (n : ℕ) : polynomial ℤ :=
X * ∏ k in finset.Ico 1 n, (1 - X^k)^24

def ramanujan_tau (n : ℕ) : ℤ :=
coeff (partial_ramanujan_tau_polynomial n) n

-- Some nice suggestive notation
prefix `τ`:300 := ramanujan_tau

/-
Some lemmas to warm up
Hint: unfold definitions, `simp`
-/

example : τ 0 = 0 :=
begin
  -- sorry
  simp [ramanujan_tau, partial_ramanujan_tau_polynomial],
  -- sorry
end

example : τ 1 = 1 :=
begin
  -- sorry
  simp [ramanujan_tau, partial_ramanujan_tau_polynomial],
  -- sorry
end

-- This one is nontrivial
-- Use `have : subresult,` or state helper lemmas and prove them first!

example : τ 2 = -24 :=
begin
  -- Really, we ought to have a tactic that makes this easy
  delta ramanujan_tau partial_ramanujan_tau_polynomial,
  rw [mul_comm, coeff_mul_X],
  suffices : ((1 - X) ^ 24 : polynomial ℤ).coeff 1 = -(24 : ℕ), by simpa,
  generalize : (24 : ℕ) = n,
  -- sorry
  induction n with n ih, { simp, },
  rw [pow_succ, sub_mul, one_mul, mul_comm X, coeff_sub, coeff_mul_X],
  rw ih,
  suffices : ((1 - X) ^ n : polynomial ℤ).coeff 0 = 1,
  { rw [this, sub_eq_add_neg, add_comm], simp, },
  clear ih,
  induction n with n ih, { simp, },
  rw [pow_succ, sub_mul, one_mul, coeff_sub],
  rw ih,
  rw coeff_mul,
  simp,
  -- sorry
end

/-
The actual exercise. Good luck (-;
-/

theorem deligne (p : ℕ) (hp : p.prime) : (abs (τ p) : ℝ) ≤ 2 * p^(11/2) :=
begin
  -- sorry
  -- I did not even start this proof
  sorry
  -- sorry
end

end
