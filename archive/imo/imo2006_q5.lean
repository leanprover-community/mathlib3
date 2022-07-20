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
$P^k(t)=t$, then $P(P(t))=t$. This is proven by observing that $P(t)-t$ divides $P(P(t))-P(t)$
divides... $P^{k+1}(t)-P^k(t)=P^k(t)-t$, which implies $P(P(t))-P(t)\mid P(t)-t$ and thus
$P(P(t))-P(t)=\pm(P(t)-t)$. Thi

Let `P` be a polynomial of degree `n > 1` and let `k : ℕ+`. Consider the polynomial `Q` equal to `P`
composed with itself `k` times. Prove that there's at most `n` integers `t` such that
`Q.eval t = t`.

The trick is proving that if `P` composed with itself `n` times applied
-/

open function polynomial


theorem periodic_lemma {p : polynomial ℤ} {k : ℕ} (hk : 1 ≤ n) {t : ℤ}
  (H : (p.comp^[n] X).eval t = t) : (p.comp p).eval t = t :=
begin
  have : p.comp p = (p.comp^[2] X) := by simp,
  rw this,
end
