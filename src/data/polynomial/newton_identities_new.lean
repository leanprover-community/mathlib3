/-
Copyright (c) 2022 Xialu Zheng, Bendit Chan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xialu Zheng, Bendit Chan, Kevin Buzzard
-/
import data.polynomial.degree.lemmas
import data.mv_polynomial.comm_ring
import algebra.polynomial.big_operators
import ring_theory.mv_polynomial.symmetric
import ring_theory.polynomial.vieta

/-

# Newton's Identities

TODO: write something nice here

https://en.wikipedia.org/wiki/Newton%27s_identities

## Main definitions

(in namespace `polynomial.symmetric`)

`e R n k` is the `k`th symmetric polynomial in `n` variables with
coefficients in the commutative ring `R`.

`s R n k` is (-1)^k * e n k

`p R n k` is the sum of the k'th powers of the n polynomial variables

-/

namespace polynomial
namespace symmetric

variables (R : Type*) [comm_ring R] (n: ℕ) (k : ℤ)


open_locale polynomial
open_locale big_operators
open finset polynomial

-- noncomputable def e : mv_polynomial (fin n) R :=
-- polynomial.coeff (∏ i : fin n, (X + C (mv_polynomial.X i))) k

noncomputable def s : mv_polynomial (fin n) R :=
if k ≤ n ∧ k ≥ 0 then polynomial.coeff (∏ i : fin n, (X - C (mv_polynomial.X i))) (int.to_nat k)
else 0

noncomputable def p : mv_polynomial (fin n) R :=
∑ i : fin n, (mv_polynomial.X i) ^ (int.to_nat k)

lemma s_symm : ∀ k : ℤ, k ≤ n → k ≥ 0 → s R n k = 
  (-1)^(n - k.to_nat) * mv_polynomial.esymm (fin n) R (n - k.to_nat) :=
begin
  intros k hk1 hk2,
  rw [s], 
  split_ifs,
  rw [finset.prod, multiset.prod_X_sub_C_coeff', finset.esymm_map_val],
  congr;
  exact finset.card_fin n,
  change k.to_nat ≤ finset.card _,
  rwa finset.card_fin n,
  sorry,
  sorry,
end


end symmetric
end polynomial