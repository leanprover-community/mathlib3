import m4r.tpow_to_talg linear_algebra.exterior_algebra

universe u
variables (R : Type u) [comm_ring R] (M : Type u) [add_comm_group M] [module R M]

instance tpow.ring : comm_ring (tpow R M 0) := by assumption
#exit
local attribute [semireducible] exterior_algebra ring_quot

def epow_map (n : ℕ) : tpow R M n →ₗ[R] exterior_algebra R M :=
(((exterior_algebra.quot R M).comp (talg_equiv R M).to_alg_hom)).to_linear_map.comp
  $ (@direct_sum2.lof R _ ℕ _ (tpow R M) (tpow_acm R M) (tpow_semimodule R M) n : tpow R M n →ₗ[R] talg R M)

def epow_map_ker (n : ℕ) := linear_map.ker (epow_map R M n)

def tpow_quotient (n : ℕ) (A : submodule R (tpow R M n)) :=
@submodule.quotient R A _ (@submodule.add_comm_group R (tpow R M n) _ (tpow.acg R M n) _ A) _

def epow (n : ℕ) := @submodule.quotient R (tpow R M n) _ sorry sorry (epow_map R M n).ker

def epow.mk (n : ℕ) : multilinear_map R (λ i : fin n, M) (epow R M n) :=
linear_map.comp_multilinear_map (submodule.mkq (epow_map R M n).ker) (tpow.mk' R M n)

variables {R M} {N : Type u} [add_comm_monoid N] [semimodule R N] {n : ℕ}

class is_alternating (f : multilinear_map R (λ i : fin n, M) N) :=
(cond : ∀ (g : fin n → M), (∃ (i j : fin n), i ≠ j → g i = g j) → f g = 0)

variables (R M N n)
def epow.lift (f : multilinear_map R (λ i : fin n, M) N) [is_alternating f] :
  epow R M n →ₗ[R] N :=
sorry
