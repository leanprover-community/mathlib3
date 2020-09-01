import ring_theory.fractional_ideal
import ring_theory.ideal.over
import ring_theory.discrete_valuation_ring
import order.zorn

namespace ring

/-- A ring `R` is at most one-dimensional if all nonzero prime ideals are maximal. -/
def dimension_le_one (R : Type*) [comm_ring R] : Prop :=
∀ p ≠ (⊥ : ideal R), p.is_prime → p.is_maximal

variables {R : Type*} [comm_ring R]

lemma not_is_field_of_subsingleton {R : Type*} [ring R] [subsingleton R] : ¬ is_field R :=
λ ⟨⟨x, y, hxy⟩, _, _⟩, hxy (subsingleton.elim x y)

lemma exists_not_is_unit_of_not_is_field [nontrivial R] (hf : ¬ is_field R) :
  ∃ x ≠ (0 : R), ¬ is_unit x :=
begin
  have : ¬ _ := λ h, hf ⟨exists_pair_ne R, mul_comm, h⟩,
  simp_rw is_unit_iff_exists_inv,
  push_neg at ⊢ this,
  obtain ⟨x, hx, not_unit⟩ := this,
  exact ⟨x, hx, not_unit⟩
end

lemma not_is_field_iff_exists_ideal_bot_lt_and_lt_top [nontrivial R] :
  ¬ is_field R ↔ ∃ I : ideal R, ⊥ < I ∧ I < ⊤ :=
begin
  split,
  { intro h,
    obtain ⟨x, nz, nu⟩ := exists_not_is_unit_of_not_is_field h,
    use ideal.span {x},
    rw [bot_lt_iff_ne_bot, lt_top_iff_ne_top],
    exact ⟨mt ideal.span_singleton_eq_bot.mp nz, mt ideal.span_singleton_eq_top.mp nu⟩ },
  { rintros ⟨I, bot_lt, lt_top⟩ hf,
    obtain ⟨x, mem, ne_zero⟩ := submodule.exists_of_lt bot_lt,
    rw submodule.mem_bot at ne_zero,
    obtain ⟨y, hy⟩ := hf.mul_inv_cancel ne_zero,
    rw [lt_top_iff_ne_top, ne.def, ideal.eq_top_iff_one, ← hy] at lt_top,
    exact lt_top (ideal.mul_mem_right _ mem), }
end

lemma not_is_field_iff_exists_ideal_ne_bot_and_is_prime [nontrivial R] :
  ¬ is_field R ↔ ∃ p : ideal R, p ≠ ⊥ ∧ p.is_prime :=
not_is_field_iff_exists_ideal_bot_lt_and_lt_top.trans
  ⟨λ ⟨I, bot_lt, lt_top⟩, let ⟨p, hp, le_p⟩ := I.exists_le_maximal (lt_top_iff_ne_top.mp lt_top) in
    ⟨p, bot_lt_iff_ne_bot.mp (lt_of_lt_of_le bot_lt le_p), hp.is_prime⟩,
   λ ⟨p, ne_bot, prime⟩, ⟨p, bot_lt_iff_ne_bot.mpr ne_bot, lt_top_iff_ne_top.mpr prime.1⟩⟩

end ring

open ideal ring

lemma is_principal_ideal_ring.dimension_le_one (R : Type*) [integral_domain R]
  [is_principal_ideal_ring R] :
  ring.dimension_le_one R :=
λ p nonzero prime, by { haveI := prime, exact is_prime.to_maximal_ideal nonzero }

variables {R K : Type*}

lemma integral_closure.dimension_le_one [comm_ring R] [nontrivial R] [integral_domain K] [algebra R K]
  (h : dimension_le_one R) :
  dimension_le_one (integral_closure R K) :=
begin
  intros p ne_bot prime,
  haveI := prime,
  refine integral_closure.is_maximal_of_is_maximal_comap p (h _ (integral_closure.comap_ne_bot ne_bot) _),
  apply is_prime.comap
end

/--Noetherian, integrally closed, Krull dimension 1-/
class is_dedekind_domain [comm_ring R] [comm_ring K] (f : fraction_map R K) :=
  (not_is_field : ¬ is_field R)
  (is_noetherian_ring : is_noetherian_ring R)
  (dimension_le_one : dimension_le_one R)
  (is_integrally_closed : integral_closure R f.codomain = ⊥)
/--Noetherian, localization at every maximal prime is a discrete valuation ring-/
class is_dedekind_domain_dvr [integral_domain R]: Prop :=
  (not_is_field : ¬ is_field R)
  (is_noetherian_ring : is_noetherian_ring R)
  (is_dvr_at_nonzero_prime : ∀ P ≠ (⊥ : ideal R), P.is_prime →
    @discrete_valuation_ring (localization.at_prime P) (by {exact localization_map.integral_domain_of_local_at_prime a}))
/--Every fractional ideal has an inverse-/
class is_dedekind_domain_inv [integral_domain R] [comm_ring K] (f : fraction_map R K) : Prop :=
  (not_is_field : ¬ is_field R)
  (is_invertible_ideal : ∀ I : ring.fractional_ideal f, ⊥ < I → (∃ J : ring.fractional_ideal f, I * J = 1))
