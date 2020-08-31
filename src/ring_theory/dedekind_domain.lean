import ring_theory.fractional_ideal
import ring_theory.ideal.over
import ring_theory.discrete_valuation_ring

/-- A ring `R` is (at most) one-dimensional if all nonzero prime ideals are maximal. -/
def ring.is_one_dimensional (R : Type*) [comm_ring R] :=
∀ p ≠ (⊥ : ideal R), p.is_prime → p.is_maximal

open ideal ring

lemma principal_ideal_ring.is_one_dimensional (R : Type*) [integral_domain R]
  [is_principal_ideal_ring R] :
  ring.is_one_dimensional R :=
λ p nonzero prime, by { haveI := prime, exact is_prime.to_maximal_ideal nonzero }

variables {R K : Type*}

lemma integral_closure.is_one_dimensional [comm_ring R] [nontrivial R] [integral_domain K] [algebra R K]
  (h : is_one_dimensional R) :
  is_one_dimensional (integral_closure R K) :=
begin
  intros p ne_bot prime,
  haveI := prime,
  refine integral_closure.is_maximal_of_is_maximal_comap p (h _ (integral_closure.comap_ne_bot ne_bot) _),
  apply is_prime.comap
end

/--Noetherian, integrally closed, Krull dimension 1-/
class is_dedekind_domain [comm_ring R] [comm_ring K] (f : fraction_map R K) :=
  (is_non_field : ∃(I : ideal R), ⊥ < I ∧ I < ⊤)
  (is_noetherian_ring : is_noetherian_ring R)
  (is_one_dimensional : is_one_dimensional R)
  (is_integrally_closed : integral_closure R f.codomain = ⊥)
/--Noetherian, localization at every maximal prime is a discrete valuation ring-/
class is_dedekind_domain_dvr [integral_domain R]: Prop :=
  (is_non_field : ∃(I : ideal R), ⊥ < I ∧ I < ⊤)
  (is_noetherian_ring : is_noetherian_ring R)
  (is_dvr_at_nonzero_prime : ∀ P ≠ (⊥ : ideal R), P.is_prime →
    @discrete_valuation_ring (localization.at_prime P) (by {exact localization_map.integral_domain_of_local_at_prime a}))
/--Every fractional ideal has an inverse-/
class is_dedekind_domain_inv [integral_domain R] [comm_ring K] (f : fraction_map R K) : Prop :=
  (is_non_field : ∃(I : ideal R), ⊥ < I ∧ I < ⊤)
  (is_invertible_ideal : ∀ I : ring.fractional_ideal f, ⊥ < I → (∃ J : ring.fractional_ideal f, I * J = 1))
