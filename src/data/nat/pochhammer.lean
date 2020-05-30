import tactic.abel

/-!
# The rising and falling factorial functions

We define and prove some basic relations about
`rising_factorial x n = x * (x+1) * ... * (x + n - 1)`
and its cousin `falling_factorial`.

## TODO
There is lots more in this direction:
* Pochhammer symbols
* q-factorials, q-binomials

-/

variables {R : Type*}

section
variables [semiring R]

/--
The rising factorial function: `rising_factorial x n = x * (x+1) * ... * (x + n - 1)`.

It is also sometimes called the Pochhammer polynomial, or the upper factorial.
Notations in the mathematics literature vary considerably.
-/
@[simp]
def rising_factorial : R → ℕ → R
| r 0 := 1
| r (n+1) := r * rising_factorial (r+1) n

lemma rising_factorial_eq_mul_right {r : R} {n : ℕ} :
  rising_factorial r (n + 1) = rising_factorial r n * (r + n) :=
begin
  induction n with n ih generalizing r,
  { simp, },
  { rw [rising_factorial, ih, rising_factorial, nat.succ_eq_add_one],
    push_cast,
    rw [mul_assoc, add_comm (n : R) 1, add_assoc], }
end

lemma rising_factorial_mul_rising_factorial {r : R} {n m : ℕ} :
  rising_factorial r n * rising_factorial (r + n) m = rising_factorial r (n + m) :=
begin
  induction m with m ih,
  { simp, },
  { rw [rising_factorial_eq_mul_right, ←mul_assoc, ih, nat.add_succ, rising_factorial_eq_mul_right],
    push_cast,
    rw [add_assoc], }
end
end

section
variables [ring R]

/--
The falling factorial function: `falling_factorial x n = x * (x-1) * ... * (x - (n - 1))`.
-/
@[simp]
def falling_factorial : R → ℕ → R
| r 0 := 1
| r (n+1) := r * falling_factorial (r-1) n

lemma falling_factorial_eq_mul_right {r : R} {n : ℕ} :
  falling_factorial r (n + 1) = falling_factorial r n * (r - n) :=
begin
  induction n with n ih generalizing r,
  { simp, },
  { rw [falling_factorial, ih, falling_factorial, nat.succ_eq_add_one],
    push_cast,
    rw [mul_assoc, add_comm (n : R) 1, ←sub_sub], }
end

end

section
variables [comm_ring R]

lemma rising_factorial_eq_falling_factorial {r : R} {n : ℕ} :
  rising_factorial r n = falling_factorial (r + n - 1) n :=
begin
  induction n with n ih generalizing r,
  { refl, },
  { rw [rising_factorial, falling_factorial_eq_mul_right, ih, mul_comm, nat.succ_eq_add_one],
    push_cast,
    congr' 2; abel, }
end

end
section
lemma rising_factorial_eq_fact {n : ℕ} :
  rising_factorial 1 n = n.fact :=
begin
  induction n with n ih,
  { refl, },
  { rw [rising_factorial_eq_mul_right, nat.fact, ih, mul_comm, add_comm], push_cast, }
end

lemma fact_mul_rising_factorial {r n : ℕ} :
  r.fact * rising_factorial (r+1) n = (r + n).fact :=
begin
  rw [←rising_factorial_eq_fact, add_comm, ←rising_factorial_eq_fact],
  convert rising_factorial_mul_rising_factorial,
  simp,
end

lemma rising_factorial_eq_fact_div_fact {r n : ℕ} :
  rising_factorial (r+1) n = (r + n).fact / r.fact :=
(nat.div_eq_of_eq_mul_right (nat.fact_pos _) fact_mul_rising_factorial.symm).symm

lemma rising_factorial_eq_choose_mul_fact {r n : ℕ} :
  rising_factorial (r+1) n = (r + n).choose n * n.fact :=
begin
  rw rising_factorial_eq_fact_div_fact,
  -- TODO we need a `clear_denominators` tactic!
  apply nat.div_eq_of_eq_mul_right (nat.fact_pos _),
  rw [mul_comm],
  convert (nat.choose_mul_fact_mul_fact (nat.le_add_left n r)).symm,
  simp,
end

lemma choose_eq_rising_factorial_div_fact {r n : ℕ} :
  (r + n).choose n = rising_factorial (r+1) n / n.fact :=
begin
  symmetry,
  apply nat.div_eq_of_eq_mul_right (nat.fact_pos _),
  rw [mul_comm, rising_factorial_eq_choose_mul_fact],
end
end

namespace ring_hom
variables {S : Type*}

section
variables [semiring R] [semiring S]

lemma map_rising_factorial (f : R →+* S) {r : R} {n : ℕ} :
  f (rising_factorial r n) = rising_factorial (f r) n :=
begin
  induction n with n ih generalizing r,
  { simp, },
  { simp [ih], }
end

@[norm_cast]
lemma nat_coe_rising_factorial {r n : ℕ} : ((rising_factorial r n : ℕ) : R) = rising_factorial (r : R) n :=
by rw [←nat.coe_cast_ring_hom, map_rising_factorial]

end

section
variables [ring R] [ring S]

lemma map_falling_factorial (f : R →+* S) {r : R} {n : ℕ} :
  f (falling_factorial r n) = falling_factorial (f r) n :=
begin
  induction n with n ih generalizing r,
  { simp, },
  { simp [ih], }
end

@[norm_cast]
lemma int_coe_rising_factorial {r : ℤ} {n : ℕ} : ((rising_factorial r n : ℤ) : R) = rising_factorial (r : R) n :=
by rw [←int.coe_cast_ring_hom, map_rising_factorial]

@[norm_cast]
lemma int_coe_falling_factorial {r : ℤ} {n : ℕ} : ((falling_factorial r n : ℤ) : R) = falling_factorial (r : R) n :=
by rw [←int.coe_cast_ring_hom, map_falling_factorial]

end
end ring_hom
