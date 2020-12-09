import m4r.tpow_to_talg linear_algebra.exterior_algebra

universe u
variables (R : Type u) [comm_ring R] (M : Type u) [add_comm_group M] [module R M]

local attribute [semireducible] exterior_algebra ring_quot

def epow_map (n : ℕ) : tpow R M n →ₗ[R] exterior_algebra R M :=
(((exterior_algebra.quot R M).comp (talg_equiv R M).to_alg_hom)).to_linear_map.comp
  $ (direct_sum.lof R ℕ (tpow R M) n : tpow R M n →ₗ[R] talg R M)

@[reducible] def epow (n : ℕ) := (epow_map R M n).ker.quotient

def epow.mk (n : ℕ) : multilinear_map R (λ i : fin n, M) (epow R M n) :=
linear_map.comp_multilinear_map (submodule.mkq (epow_map R M n).ker) (tpow.mk' R M n)

variables {R M} {N : Type u} [add_comm_group N] [module R N] {n : ℕ}

variables (R M N n)

#exit
def epow.lift (f : multilinear_map R (λ i : fin n, M) N) [is_alternating f] :
  epow R M n →ₗ[R] N :=
submodule.liftq (epow_map R M n).ker (tpow.lift R n N f) $ λ x hx,
