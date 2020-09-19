import data.polynomial.derivative
import algebra.ring.basic
import data.polynomial.basic
import logic.function.iterate
import tactic.ring tactic.linarith

noncomputable theory

open finset nat polynomial
open_locale big_operators

namespace polynomial
universes u
variable {R : Type u}

section semiring

variables [semiring R] (f p q: polynomial R) (n k : ℕ)

/--Defining the n-th derivative of polynomial f-/
def deriv_n : polynomial R := derivative ^[n] f

@[simp] lemma zeroth_deriv : deriv_n f 0 = f := rfl


lemma deriv_n_succ : (deriv_n f n).derivative = (deriv_n f (n+1)) :=
by rw [deriv_n, deriv_n, function.iterate_succ']

lemma deriv_n_zero : deriv_n (0 : polynomial R) n = 0 :=
begin
  induction n with n hn;
  simp only [deriv_n, id.def, function.iterate_zero],
  rwa <-deriv_n
end

lemma deriv_n_add : (deriv_n (p+q) n) = (deriv_n p n) + (deriv_n q n) :=
begin
  induction n with n ih,
  { simp only [zeroth_deriv], },
  { rw [<-deriv_n_succ, ih, polynomial.derivative_add, deriv_n_succ, deriv_n_succ] }
end

end semiring

section comm_ring
variable [comm_ring R]
variables (f p q: polynomial R) (n k : ℕ)


lemma deriv_n_coeff : ∀ m : ℕ, (deriv_n f k).coeff m = (∏ i in finset.range k, (m+k-i)) * (f.coeff (m+k)) :=
begin
  induction k with k ih,
  { simp only [add_zero, forall_const, one_mul, range_zero, eq_self_iff_true,
      zeroth_deriv, prod_empty] },

  { intro m, rw <-deriv_n_succ,
    rw [polynomial.coeff_derivative, ih (m+1), prod_range_succ],
    simp only [nat.cast_succ, succ_eq_add_one],
    conv_rhs { rw [mul_assoc, mul_comm] },
    have triv : (∏ (i : ℕ) in range k, (m + 1 + k - i : R)) = ∏ (x : ℕ) in range k, (m + (k + 1) - x),
    { apply congr_arg, ext, ring },
    rw triv,
    replace triv : (m + 1 : R) = (m + (k+1) - k:R),
    { rw add_sub_assoc, simp only [add_sub_cancel'], }, rw <-triv,
      replace triv : f.coeff (m + 1 + k) = f.coeff (m + (k + 1)),
    { apply congr_arg, ring},
    rw triv }
end

end comm_ring

section integral_domain
variables [integral_domain R]
variables (f p q: polynomial R) (n k : ℕ)


lemma deriv_too_much : (deriv_n f (f.nat_degree + 1)) = 0 :=
begin
  ext,
  rw deriv_n_coeff,
  simp only [cast_one, cast_add, coeff_zero],

  rw mul_eq_zero, right,
  apply polynomial.coeff_eq_zero_of_nat_degree_lt, linarith,
end


lemma deriv_n_poly_prod :
  deriv_n (p * q) n = ∑ k in range n.succ, (C (n.choose k : R)) * (deriv_n p (n-k)) * (deriv_n q k) :=
begin
  induction n with n IH,
  { simp only [one_mul, cast_one, id.def, sum_singleton, C_eq_nat_cast, zeroth_deriv, choose_self, range_one]},

  { rw [<-deriv_n_succ, IH],
    simp only [derivative_mul, derivative_sum, derivative_C, zero_mul, zero_add, deriv_n_succ],
    conv_lhs {rw [sum_add_distrib]},
    conv {
      congr,
      { congr,
        { rw [sum_range_succ'],
          simp only [choose_zero_right, cast_one, C_1, one_mul, nat.sub_zero, zeroth_deriv] },
        { rw [sum_range_succ]}, },
      { rw [sum_range_succ'],
        simp only [choose_zero_right, cast_one, C_1, one_mul, nat.sub_zero, zeroth_deriv],
        congr,
        {rw [sum_range_succ]}, },
    },

    have lhs_eq :
      ∑ (i : ℕ) in range n,
        C ↑(n.choose (i + 1)) * p.deriv_n (n - (i + 1) + 1) * q.deriv_n (i + 1) +
      p.deriv_n (n + 1) * q +
      (C ↑(n.choose n) * p.deriv_n (n - n) * q.deriv_n (n + 1) +
        ∑ (x : ℕ) in range n, C ↑(n.choose x) * p.deriv_n (n - x) * q.deriv_n (x + 1)) =
      (∑ (i : ℕ) in range n,
        C ↑(n.choose (i + 1)) * p.deriv_n (n - (i + 1) + 1) * q.deriv_n (i + 1) +
        ∑ (x : ℕ) in range n, C ↑(n.choose x) * p.deriv_n (n - x) * q.deriv_n (x + 1)) +
      (p.deriv_n (n + 1) * q + C ↑(n.choose n) * p.deriv_n (n - n) * q.deriv_n (n + 1)) := by ring,
    rw lhs_eq,
    clear lhs_eq,

    have rhs_eq :
      C ↑(n.succ.choose (n + 1)) * p.deriv_n (n.succ - (n + 1)) * q.deriv_n (n + 1) +
      ∑ (x : ℕ) in range n,
        C ↑(n.succ.choose (x + 1)) * p.deriv_n (n.succ - (x + 1)) * q.deriv_n (x + 1) +
      p.deriv_n n.succ * q =
      ∑ (x : ℕ) in range n,
        C ↑(n.succ.choose (x + 1)) * p.deriv_n (n.succ - (x + 1)) * q.deriv_n (x + 1) +
      (C ↑(n.succ.choose (n + 1)) * p.deriv_n (n.succ - (n + 1)) * q.deriv_n (n + 1) +
        p.deriv_n n.succ * q) := by ring,
    rw rhs_eq,
    clear rhs_eq,

    apply congr_arg2,
    { rw <-sum_add_distrib,
      apply sum_congr rfl,
      intros x hx,
      simp only [mem_range, succ_sub_succ_eq_sub, C_eq_nat_cast, succ_eq_add_one, choose_succ_succ] at *,
      push_cast,
      have triv : (n - (x + 1) + 1)  = n - x,
      { rw <-nat.sub_add_comm,
        rw succ_sub_succ,
        exact succ_le_iff.mpr hx, },
        rw [triv, add_mul],
      ring},
      { simp only [one_mul, cast_one, nat.sub_self, ring_hom.map_one, zeroth_deriv, choose_self],
        ring,}
    }
end

end integral_domain

end polynomial
