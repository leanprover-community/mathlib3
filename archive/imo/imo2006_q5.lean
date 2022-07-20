/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import data.polynomial.div
import dynamics.periodic_pts

/-!
# IMO 2006 Q5

Let $P(x)$ be a polynomial of degree $n>1$ with integer coefficients, and let $k$ be a positive
integer. Consider the polynomial $Q(x) = P( P ( \ldots P(P(x)) \ldots ))$, where $P$ occurs $k$
times. Prove that there are at most $n$ integers $t$ such that $Q(t)=t$.

## Sketch of solution

Let $P^k$ denote the polynomial $P$ composed with itself $k$ times. We rely on a key observation: if
$P^k(t)=t$, then $P(P(t))=t$. We prove this by building the cyclic list
$(P(t)-t,P^2(t)-P(t),\ldots)$, and showing that each entry divides the next, which by transitivity
implies they all divide each other, and thus have the same absolute value. If two successive entries
$P^{r+1}(t)-P^r(t)$ and $P^{r+2}(t)-P^{r+1}(t)$ have opposite signs, then $P^{r+2}(t)=P^r(t)$, which
implies $P(P(t))=t$. Otherwise, either all successive entries compare as `<` or they all compare as
`>`, which by transitivity implies the contradiction $P(t)-t < P(t)-t$  or $P(t)-t > P(t)-t$.

Knowing that $P(P(t))=t$, [FINISH WRITEUP]
-/

open function polynomial

/-- If every entry in a cyclic list of integers divides the next, then they all have the same
absolute value -/
theorem abs_eq_of_chain_dvd {l : cycle ℤ} {x y : ℤ} (hl : l.chain (∣)) (hx : x ∈ l) (hy : y ∈ l) :
  abs x = abs y :=
begin
haveI : @is_trans ℤ (∣) := by apply_instance,
  rw cycle.chain_iff_pairwise () at hl,
end

/-- The main lemma in the proof: if $P^k(t)=t$, then $P(P(t))=t$. -/
theorem periodic_lemma {p : polynomial ℤ} {k : ℕ} (hk : 1 ≤ k) {t : ℤ}
  (H : (p.comp^[k] X).eval t = t) : (p.comp p).eval t = t :=
begin
  -- The cycle [t, P(t), P(P(t)), ...].
  let C₁ : cycle ℤ := periodic_orbit (λ x, p.eval x) t,

  -- The cycle [P(t) - t, P(P(t)) - P(t), ...]
  let C₂ : cycle ℤ := C₁.map (λ x, p.eval x - x),
end
