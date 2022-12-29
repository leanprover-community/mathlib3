import ring_theory.adjoin_root
import field_theory.minpoly
import data.polynomial.div
import ring_theory.integrally_closed
import field_theory.splitting_field

open polynomial localization


open_locale polynomial

variables {R S : Type*} [comm_ring R] [comm_ring S]

section move_me
/- The results in this section are useful (they are direct generalisations of results in
  `gauss_lemma.lean` but aren't necessary for this PR so will be shortly moved to another one) -/

theorem monic_map_of_monic [nontrivial S] (f : R →+* S) {p : R[X]} (hp : p.monic):
  monic (p.map f) :=
begin
  have : nat_degree p = nat_degree (p.map f),
  { refine le_antisymm (le_nat_degree_of_ne_zero _) (nat_degree_map_le _ _),
    rw [polynomial.coeff_map, coeff_nat_degree, monic.def.mp hp, ne.def,
      ← ring_hom.codomain_trivial_iff_map_one_eq_zero],
    exact zero_ne_one },
  rw [monic.def, leading_coeff, coeff_map, ← this, ← leading_coeff, monic.def.mp hp, map_one],
end

theorem monic_map_iff_of_injective [nontrivial S] (f : R →+* S) (hf : function.injective f)
  {p : R[X]} : p.monic ↔ (p.map f).monic :=
begin
  refine ⟨λ h, monic_map_of_monic f h, λ h, _⟩,
  have := nat_degree_map_eq_of_injective hf p,
  rw [monic.def, leading_coeff] at h ⊢,
  rw [this, coeff_map, ← map_one f] at h,
  exact hf h,
end

variables [algebra R S] {a : S} [is_domain S] [is_domain R] {φ : R →+* S} {f : R[X]}

theorem is_primitive.is_unit_iff_is_unit_map_of_injective' (hinj : function.injective φ)
  (hf : is_primitive f) : is_unit f ↔ is_unit (map φ f) :=
begin
  refine ⟨(map_ring_hom φ).is_unit_map, λ h, _⟩,
  rcases is_unit_iff.1 h with ⟨_, ⟨u, rfl⟩, hu⟩,
  have hdeg := degree_C u.ne_zero,
  rw [hu, degree_map_eq_of_injective hinj] at hdeg,
  rw [eq_C_of_degree_eq_zero hdeg] at hf,
  rw [eq_C_of_degree_eq_zero hdeg, is_unit_C],
  refine is_primitive_iff_is_unit_of_C_dvd.mp hf (f.coeff 0) (dvd_refl _),
end

lemma is_primitive_of_dvd' {p q : R[X]} (hp : is_primitive p) (hq : q ∣ p) : is_primitive q :=
λ a ha, is_primitive_iff_is_unit_of_C_dvd.mp hp a (dvd_trans ha hq)

lemma is_primitive.irreducible_of_irreducible_map_of_injective (hinj : function.injective φ)
  (hf : is_primitive f) (h_irr : irreducible (map φ f)) :
  irreducible f :=
begin
  refine ⟨λ h, h_irr.not_unit (is_unit.map (map_ring_hom φ) h), _⟩,
  intros a b h,
  rcases h_irr.is_unit_or_is_unit (by rw [h, polynomial.map_mul]) with hu | hu,
  { left,
    rwa is_primitive.is_unit_iff_is_unit_map_of_injective' hinj (is_primitive_of_dvd' hf
      (dvd.intro _ h.symm)) },
  right,
  rwa is_primitive.is_unit_iff_is_unit_map_of_injective' hinj
    (is_primitive_of_dvd' hf (dvd.intro_left _ h.symm))
end

end move_me

variables [algebra R S] {a : S} [is_domain S] [is_domain R]

section preliminary_results

theorem roots_mem_integral_closure {R A} [comm_ring R] [comm_ring A] [is_domain A] [algebra R A]
  {f : R[X]} (hf : f.monic) {a : A} (ha : a ∈ (f.map $ algebra_map R A).roots) :
  a ∈ integral_closure R A :=
⟨f, hf, (eval₂_eq_eval_map _).trans $ (mem_roots $ (hf.map _).ne_zero).1 ha⟩

theorem coeff_mem_subring_of_splits {K} [field K] {f : K[X]}
  (hs : f.splits (ring_hom.id K)) (hm : f.monic) (T : subring K)
  (hr : ∀ a ∈ f.roots, a ∈ T) (n : ℕ) : f.coeff n ∈ T :=
begin
  rw (_ : f = (f.roots.pmap (λ a h, X - C (⟨a, h⟩ : T)) hr).prod.map T.subtype),
  { rw coeff_map, apply set_like.coe_mem },
  conv_lhs { rw [eq_prod_roots_of_splits_id hs, hm.leading_coeff, C_1, one_mul] },
  rw [polynomial.map_multiset_prod, multiset.map_pmap],
  congr, convert (f.roots.pmap_eq_map _ _ hr).symm,
  ext1, ext1, rw [polynomial.map_sub, map_X, map_C], refl,
end

theorem frange_subset_integral_closure {R K} [comm_ring R] [field K] [algebra R K]
  {f : R[X]} (hf : f.monic) {g : K[X]} (hg : g.monic) (hd : g ∣ f.map (algebra_map R K)) :
  (g.frange : set K) ⊆ (integral_closure R K).to_subring :=
begin
  haveI : is_scalar_tower R K g.splitting_field := splitting_field_aux.is_scalar_tower _ _ _,
  have := coeff_mem_subring_of_splits ((splits_id_iff_splits _).2 $ splitting_field.splits g)
    (hg.map _) (integral_closure R _).to_subring (λ a ha, roots_mem_integral_closure hf _),
  { intros a ha, obtain ⟨n, -, rfl⟩ := mem_frange_iff.1 ha,
    obtain ⟨p, hp, he⟩ := this n, use [p, hp],
    rw [is_scalar_tower.algebra_map_eq R K, coeff_map, ← eval₂_map, eval₂_at_apply] at he,
    rw eval₂_eq_eval_map, apply (injective_iff_map_eq_zero _).1 _ _ he,
    { apply ring_hom.injective } },
  rw [is_scalar_tower.algebra_map_eq R K _, ← map_map],
  refine multiset.mem_of_le (roots.le_of_dvd ((hf.map _).map _).ne_zero _) ha,
  { apply_instance },
  { exact map_dvd (algebra_map K g.splitting_field) hd },
  { apply splitting_field_aux.is_scalar_tower },
end

theorem eq_map_of_dvd {R} [comm_ring R] [is_domain R] [is_integrally_closed R]
  {f : R[X]} (hf : f.monic) (g : (fraction_ring R)[X]) (hg : g.monic)
  (hd : g ∣ f.map (algebra_map R _)) : ∃ g' : R[X], g'.map (algebra_map R _) = g :=
begin
  let algeq := (subalgebra.equiv_of_eq _ _ $
    is_integrally_closed.integral_closure_eq_bot R _).trans
    (algebra.bot_equiv_of_injective $ is_fraction_ring.injective R $ fraction_ring R),
  have : (algebra_map R _).comp algeq.to_alg_hom.to_ring_hom =
    (integral_closure R _).to_subring.subtype,
  { ext, conv_rhs { rw ← algeq.symm_apply_apply x }, refl },
  refine ⟨map algeq.to_alg_hom.to_ring_hom _, _⟩,
  use g.to_subring _ (frange_subset_integral_closure hf hg hd),
  rw [map_map, this], apply g.map_to_subring,
end

noncomputable def frac_algebra_of_inj [h : fact (function.injective (algebra_map R S))] :
  algebra (fraction_ring R) (fraction_ring S) :=
ring_hom.to_algebra (is_fraction_ring.map (fact_iff.mp h))

local attribute [instance] frac_algebra_of_inj

open euclidean_domain

lemma aeval_commuting_diagram {R S T U : Type*}[comm_ring R] [comm_ring S] [comm_ring T]
  [comm_ring U] [algebra R S] [algebra T U] (φ : R →+* T) (ψ : S →+* U)
  (h : (algebra_map T U).comp φ = ψ.comp (algebra_map R S)) (p : R[X]) (a : S):
  ψ (aeval a p) = aeval (ψ a) (p.map φ) :=
begin
  conv_rhs {rw [aeval_def, ← eval_map]},
  rw [map_map, h, ← map_map, eval_map, eval₂_at_apply, aeval_def, eval_map],
end

lemma is_integral_of_commuting_diagram {R S T U : Type*} [nontrivial S] [nontrivial T]
  [comm_ring R] [comm_ring S] [comm_ring T] [comm_ring U] [algebra R S] [algebra T U]
  (φ : R →+* T) (ψ : S →+* U) (h : (algebra_map T U).comp φ = ψ.comp (algebra_map R S))
  {a : S} (ha : is_integral R a) : is_integral T (ψ a) :=
begin
  rw [is_integral, ring_hom.is_integral_elem] at ⊢ ha,
  obtain ⟨p, hp⟩ := ha,
  use p.map φ,
  refine ⟨monic_map_of_monic _ hp.left ,_⟩,
  rw [← eval_map, map_map, h, ← map_map, eval_map, eval₂_at_apply,
    eval_map, hp.right, map_zero],
end

lemma fraction_algebra_commuting_diagram [h : fact (function.injective (algebra_map R S))] :
  ((algebra_map S (fraction_ring S)).comp (algebra_map R S)) = ((algebra_map (fraction_ring R)
        (fraction_ring S)).comp (algebra_map R (fraction_ring R))) :=
begin
  ext x,
  rw [ring_hom.comp_apply, ring_hom.comp_apply, ring_hom.algebra_map_to_algebra,
   is_fraction_ring.map, is_localization.map_eq],
end

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
    rw [ring_hom.mem_ker, alg_hom.to_ring_hom_eq_coe, alg_hom.coe_to_ring_hom] at hp,
    rwa [ideal.mem_span_singleton, ← minpoly.dvd' ha] },
  { intros p hp,
    rwa [ring_hom.mem_ker, alg_hom.to_ring_hom_eq_coe, alg_hom.coe_to_ring_hom, minpoly.dvd' ha,
      ← ideal.mem_span_singleton] }
end
