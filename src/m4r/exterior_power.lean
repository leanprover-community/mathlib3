import m4r.tpow_to_talg linear_algebra.exterior_algebra

universe u
variables (R : Type u) [comm_ring R] (M : Type u) [add_comm_group M] [module R M]

instance tpow.ring : comm_ring (tpow R M 0) := by assumption

def tpow_aux.module (n : ℕ) :
  Σ (h : add_comm_group (tpow_aux R M n).1), @module R (tpow_aux R M n).1 _ h :=
nat.rec_on n ⟨ring.to_add_comm_group R, semiring.to_semimodule⟩ $ λ m h,
⟨sorry, sorry⟩ -- :/

instance tpow.acg (n : ℕ) : add_comm_group (tpow R M n) := (tpow_aux.module R M n).1

instance tpow.module (n : ℕ) : module R (tpow R M n) := (tpow_aux.module R M n).2

local attribute [semireducible] exterior_algebra ring_quot

def epow_map (n : ℕ) : tpow R M n →ₗ[R] exterior_algebra R M :=
(((exterior_algebra.quot R M).comp (talg_equiv R M).to_alg_hom)).to_linear_map.comp
  $ direct_sum2.lof R ℕ (tpow R M) n

-- non defeq instances -________-
def epow (n : ℕ) := @submodule.quotient R (tpow R M n) _ sorry sorry
$ @linear_map.ker R (tpow R M n) (exterior_algebra R M) _
  sorry _ sorry _ (epow_map R M n)

def epow.mk (n : ℕ) : multilinear_map R (λ i : fin n, M) (epow R M n) :=
linear_map.comp_multilinear_map (submodule.mkq (epow_map R M n).ker) (tpow.mk' R M n)

variables {R M} {N : Type u} [add_comm_monoid N] [semimodule R N] {n : ℕ}

class is_alternating (f : multilinear_map R (λ i : fin n, M) N) :=
(cond : ∀ (g : fin n → M), (∃ (i j : fin n), i ≠ j → g i = g j) → f g = 0)

variables (R M N n)
def epow.lift (f : multilinear_map R (λ i : fin n, M) N) [is_alternating f] :
  epow R M n →ₗ[R] N :=
sorry
