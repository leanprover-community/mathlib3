import linear_algebra.matrix

universes u v
variables (R : Type v) [semiring R]
instance quux : has_scalar ℕ R := by apply_instance
#print quux
