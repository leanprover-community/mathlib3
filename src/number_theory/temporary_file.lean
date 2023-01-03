import ring_theory.adjoin_root
import field_theory.minpoly
import data.polynomial.div
import ring_theory.integrally_closed
import field_theory.splitting_field

open polynomial localization alg_hom


open_locale polynomial

variables {R S : Type*} [comm_ring R] [comm_ring S]


variables [algebra R S] {a : S} [is_domain S] [is_domain R] {φ : R →+* S} {f : R[X]}


local attribute [instance] frac_algebra_of_inj

open euclidean_domain

lemma polynomial.eq_zero_of_dvd_of_degree_lt {p q : R[X]} (h₁ : p ∣ q) (h₂ : degree q < degree p) :
  q = 0 :=
begin
  by_contradiction hc,
  exact (lt_iff_not_ge _ _ ).mp h₂ (degree_le_of_dvd h₁ hc),
end

lemma aeval_eq_zero_of_dvd_aeval_eq_zero {p q : R[X]} (h₁ : p ∣ q) {a : S} (h₂ : aeval a p = 0) :
  aeval a q = 0 :=
begin
  rw [aeval_def, ← eval_map] at h₂ ⊢,
  exact eval_eq_zero_of_dvd_of_eval_eq_zero (polynomial.map_dvd (algebra_map R S) h₁) h₂,
end

end preliminary_results

local attribute [instance] frac_algebra_of_inj

theorem algebra_map_minpoly_eq_minpoly [is_integrally_closed R]
  [h : fact (function.injective (algebra_map R S))] (ha : is_integral R a) :
  (map (algebra_map R (fraction_ring R)) (minpoly R a))
    = minpoly (fraction_ring R) (algebra_map S (fraction_ring S) a) :=
begin
  --a few "trivial" preliminary results to set up the proof
  have lem0 : minpoly (fraction_ring R) (algebra_map S (fraction_ring S) a) ∣
    (map (algebra_map R (fraction_ring R)) (minpoly R a)),
  { apply minpoly.dvd (fraction_ring R) (algebra_map S (fraction_ring S) a),
    rw [← aeval_commuting_diagram, minpoly.aeval, map_zero],
    exact fraction_algebra_commuting_diagram.symm },

  have lem1 : is_integral (fraction_ring R) (algebra_map S (fraction_ring S) a),
  { refine is_integral_of_commuting_diagram (algebra_map R (fraction_ring R)) _
    (fraction_algebra_commuting_diagram.symm) ha },

  obtain ⟨g, hg⟩ := eq_map_of_dvd (minpoly.monic ha) _ (minpoly.monic lem1) lem0,
  have lem2 : aeval a g = 0,
  { have := minpoly.aeval (fraction_ring R) (algebra_map S (fraction_ring S) a),
    rw [← hg, ← aeval_commuting_diagram, ← map_zero (algebra_map S (fraction_ring S))] at this,
    exact is_fraction_ring.injective S (fraction_ring S) this,
    refine fraction_algebra_commuting_diagram.symm },

  have lem3 : g.monic,
  { suffices : monic (map (algebra_map R (fraction_ring R)) g),
    { rwa ← monic_map_iff_of_injective at this,
      exact is_fraction_ring.injective R (fraction_ring R) },
    rw hg,
    exact minpoly.monic lem1 },

  --the idea of the proof is the following: since the minpoly of `a` over `Frac(R)` divides the
  --minpoly of `a` over `R`, it is itself in `R`. Hence its degree is greater or equal to that of
  --the minpoly of `a` over `R`. But the minpoly of `a` over `Frac(R)` divides the minpoly of a
  --over `R` in `R[X]` so we are done.
  suffices: minpoly R a = g,
  { rw [← hg, this] },
  refine polynomial.eq_of_monic_of_dvd_of_nat_degree_le lem3 (minpoly.monic ha) _ _,

  rwa [← map_dvd_map _ (is_fraction_ring.injective R (fraction_ring R)) lem3, hg],

  exact nat_degree_le_nat_degree (minpoly.min R a lem3 lem2),
end

theorem minpoly.dvd' [h : fact (function.injective (algebra_map R S))] [nontrivial R]
  [is_integrally_closed R] {a : S} (ha : is_integral R a) (p : R[X]) :
  aeval a p = 0 ↔ minpoly R a ∣ p :=
begin
  refine ⟨λ hp, _, λ hp, _⟩,

  { have : minpoly (fraction_ring R) (algebra_map S (fraction_ring S) a) ∣
      (map (algebra_map R (fraction_ring R)) (p %ₘ (minpoly R a))),
    { rw [map_mod_by_monic _ (minpoly.monic ha), mod_by_monic_eq_sub_mul_div],
      refine dvd_sub (minpoly.dvd (fraction_ring R) (algebra_map S (fraction_ring S) a) _) _,
      rw [← aeval_commuting_diagram, hp, map_zero],
      exact fraction_algebra_commuting_diagram.symm,

      apply dvd_mul_of_dvd_left,
      rw algebra_map_minpoly_eq_minpoly ha,

      exact monic_map_of_monic _ (minpoly.monic ha) },
    rw [← algebra_map_minpoly_eq_minpoly ha, map_dvd_map (algebra_map R (fraction_ring R))
      (is_fraction_ring.injective R (fraction_ring R)) (minpoly.monic ha)] at this,
    rw [← dvd_iff_mod_by_monic_eq_zero (minpoly.monic ha)],
    refine polynomial.eq_zero_of_dvd_of_degree_lt this
      (degree_mod_by_monic_lt p $ minpoly.monic ha) },

  { simpa only [ring_hom.mem_ker, ring_hom.coe_comp, coe_eval_ring_hom,
      coe_map_ring_hom, function.comp_app, eval_map, ← aeval_def] using
      aeval_eq_zero_of_dvd_aeval_eq_zero hp (minpoly.aeval R a) }
end

lemma ker_eval [h : fact (function.injective (algebra_map R S))] [nontrivial R]
  [is_integrally_closed R] (a : S) (ha : is_integral R a) :
    ((aeval a).to_ring_hom : R[X] →+* S).ker = ideal.span ({ minpoly R a} : set R[X] ):=
begin
  apply le_antisymm,
  { intros p hp,
    rwa [ring_hom.mem_ker, to_ring_hom_eq_coe, coe_to_ring_hom, minpoly.dvd' ha,
      ← ideal.mem_span_singleton] at hp },
  { intros p hp,
    rwa [ring_hom.mem_ker, alg_hom.to_ring_hom_eq_coe, alg_hom.coe_to_ring_hom, minpoly.dvd' ha,
      ← ideal.mem_span_singleton] }
end
