/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import data.polynomial.eval
import dynamics.periodic_pts

/-!
# IMO 2006 Q5

Let `P` be a polynomial of degree `n > 1` and let `k : ℕ+`. Consider the polynomial `Q` equal to `P`
composed with itself `k` times. Prove that there's at most `n` integers `t` such that
`Q.eval t = t`.

The trick is proving
-/

open function polynomial

theorem periodic_lemma {p : polynomial ℤ} {n : ℕ} (hn : 1 ≤ n) {t : ℤ}
  (H : (p.comp^[n] X).eval t = t) : (p.comp p).eval t = t :=
begin
  have : p.comp p = (p.comp^[2] X) := by simp,
  rw this,
end
