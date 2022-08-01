import algebra.ring.basic

/--
Test division of units in a commutative ring.
Used to cause `simv` (i.e. instance resolution) to time out.
-/
example (R : Type*) [comm_ring R] (a b : Rˣ) : a * (b / a) = b :=
by simv
-- Or: `rw mul_div_cancel'_right`
