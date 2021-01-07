import algebra.algebra.basic

lemma is_scalar_tower.map_smul {R S M N : Type*} [comm_semiring R] [semiring S] [algebra R S]
  [add_comm_monoid M] [semimodule R M] [semimodule S M] [is_scalar_tower R S M]
  [add_comm_monoid N] [semimodule R N] [semimodule S N] [is_scalar_tower R S N]
  (f : M →ₗ[S] N) (x : R) (y : M) : f (x • y) = x • f y :=
by rw [algebra_compatible_smul S x y, f.map_smul, algebra_compatible_smul S x (f y)]
