import field_theory.splitting_field.construction

structure test (K : Type) [inst : field K] :=
(n : ℕ)
(x : @polynomial.splitting_field K inst (n : polynomial K))
