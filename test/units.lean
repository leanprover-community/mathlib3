import algebra.ring.units

/--
Test division of units in a commutative ring.
Used to cause `simp` (i.e. instance resolution) to time out.
-/
example (R : Type*) [comm_ring R] (a b : Rˣ) : a * (b / a) = b :=
by simp
-- Or: `rw mul_div_cancel'_right`
