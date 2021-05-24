import topology.algebra.module

theorem continuous_linear_map.is_linear {R : Type*} [semiring R] {M : Type*} [topological_space M]
  [add_comm_monoid M] {M₂ : Type*} [topological_space M₂] [add_comm_monoid M₂] [module R M]
  [module R M₂] (f : M →L[R] M₂) :
  is_linear_map R ⇑f :=
f.to_linear_map.is_linear
