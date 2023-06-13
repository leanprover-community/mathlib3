import data.mv_polynomial.basic
import data.polynomial.ring_division

structure test (K : Type) [inst : field K] :=
(n : ℕ)
(x : mv_polynomial ((n : polynomial K).root_set K) K)
