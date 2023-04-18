import topology.algebra.star_subalgebra
import topology.continuous_function.polynomial
import topology.continuous_function.stone_weierstrass -- only needed for last two decls

open polynomial

theorem polynomial_functions.eq_adjoin_X {R : Type*} [comm_semiring R] [topological_space R]
  [topological_semiring R] (s : set R) :
  polynomial_functions s = algebra.adjoin R {to_continuous_map_on_alg_hom s X} :=
begin
  refine le_antisymm _ (algebra.adjoin_le (λ _ h, ⟨X, trivial, (set.mem_singleton_iff.1 h).symm⟩)),
  rintro _ ⟨p, -, rfl⟩,
  rw [alg_hom.coe_to_ring_hom],
  refine p.induction_on (λ r, _) (λ f g hf hg, _) (λ n r hn, _),
  { rw [polynomial.C_eq_algebra_map, alg_hom_class.commutes],
    exact subalgebra.algebra_map_mem _ r },
  { rw map_add,
    exact add_mem hf hg },
  { rw [pow_succ', ←mul_assoc, map_mul],
    refine mul_mem hn (algebra.subset_adjoin $ set.mem_singleton _) }
end

theorem polynomial_functions.le_equalizer {R A : Type*} [comm_semiring R] [topological_space R]
  [topological_semiring R] [semiring A] [algebra R A] (s : set R) (φ ψ : C(s, R) →ₐ[R] A)
  (h : φ (to_continuous_map_on_alg_hom s X) = ψ (to_continuous_map_on_alg_hom s X)) :
  polynomial_functions s ≤ φ.equalizer ψ :=
begin
  rw polynomial_functions.eq_adjoin_X s,
  exact φ.adjoin_le_equalizer ψ (λ x hx, (set.mem_singleton_iff.1 hx).symm ▸ h),
end

open star_subalgebra

theorem polynomial_functions.star_closure_eq_adjoin_X {R : Type*} [comm_semiring R]
  [topological_space R] [topological_semiring R] [star_ring R] [has_continuous_star R] (s : set R) :
  (polynomial_functions s).star_closure = adjoin R {(to_continuous_map_on_alg_hom s X)} :=
by rw [polynomial_functions.eq_adjoin_X s, adjoin_eq_star_closure_adjoin]


theorem polynomial_functions.le_equalizer_star {R A : Type*} [comm_semiring R] [topological_space R]
  [topological_semiring R] [star_ring R] [has_continuous_star R] [semiring A] [star_ring A]
  [algebra R A] [star_module R A] (s : set R) (φ ψ : C(s, R) →⋆ₐ[R] A)
  (h : φ (to_continuous_map_on_alg_hom s X) = ψ (to_continuous_map_on_alg_hom s X)) :
  (polynomial_functions s).star_closure ≤ φ.equalizer ψ :=
begin
  rw polynomial_functions.star_closure_eq_adjoin_X s,
  exact φ.adjoin_le_equalizer ψ (λ x hx, (set.mem_singleton_iff.1 hx).symm ▸ h),
end

lemma subalgebra.topological_closure_star_comm {R A : Type*} [comm_semiring R]
  [star_ring R] [topological_space A] [semiring A] [algebra R A] [topological_semiring A]
  [star_ring A] [has_continuous_star A] [star_module R A] (S : subalgebra R A) :
  (star S).topological_closure = star S.topological_closure :=
begin
  suffices : ∀ (s : subalgebra R A), (star s).topological_closure ≤ star s.topological_closure,
  { exact le_antisymm (this S)
      (by simpa only [star_star] using subalgebra.star_mono (this (star S))) },
  exact λ s, (star s).topological_closure_minimal (subalgebra.star_mono subset_closure)
    (is_closed_closure.preimage continuous_star),
end

lemma subalgebra.star_closure_to_subalgebra {R A : Type*} [comm_semiring R]
  [star_ring R] [topological_space A] [semiring A] [algebra R A] [topological_semiring A]
  [star_ring A] [has_continuous_star A] [star_module R A] (S : subalgebra R A) :
  S.star_closure.to_subalgebra = S ⊔ star S :=
rfl

lemma star_subalgebra.topological_closure_to_subalgebra_comm {R A : Type*} [comm_semiring R]
  [star_ring R] [topological_space A] [semiring A] [algebra R A] [topological_semiring A]
  [star_ring A] [has_continuous_star A] [star_module R A] (S : star_subalgebra R A) :
  S.topological_closure.to_subalgebra = S.to_subalgebra.topological_closure :=
set_like.coe_injective rfl

theorem polynomial_functions.star_closure_topological_closure {𝕜 : Type*} [is_R_or_C 𝕜] (s : set 𝕜)
  [compact_space s] : (polynomial_functions s).star_closure.topological_closure = ⊤ :=
begin
  rw [←to_subalgebra_inj, star_subalgebra.topological_closure_to_subalgebra_comm],
  refine continuous_map.subalgebra_is_R_or_C_topological_closure_eq_top_of_separates_points _
    (subalgebra.separates_points_monotone le_sup_left (polynomial_functions_separates_points s)) _,
  rintros _ ⟨f, hf, rfl⟩,
  simp only [alg_equiv.to_alg_hom_eq_coe, alg_hom.to_ring_hom_eq_coe, ring_hom.to_monoid_hom_eq_coe,
    ring_hom.coe_monoid_hom, alg_hom.coe_to_ring_hom, alg_equiv.coe_alg_hom, is_R_or_C.conj_ae_coe,
    alg_hom.comp_left_continuous_apply, ring_hom.to_fun_eq_coe, ring_hom.comp_left_continuous_apply,
    monoid_hom.to_fun_eq_coe, monoid_hom.comp_left_continuous_apply,
    subalgebra.mem_restrict_scalars, mem_to_subalgebra],
  exact star_mem (hf : f ∈ (polynomial_functions s).star_closure),
end

@[ext]
theorem continuous_map.star_alg_hom_ext_map_X {𝕜 A : Type*} [is_R_or_C 𝕜] [ring A] [star_ring A]
  [algebra 𝕜 A] [topological_space A] [t2_space A] [star_module 𝕜 A] {s : set 𝕜} [compact_space s]
  (φ ψ : C(s, 𝕜) →⋆ₐ[𝕜] A) (hφ : continuous φ) (hψ : continuous ψ)
  (h : φ (to_continuous_map_on_alg_hom s X) = ψ (to_continuous_map_on_alg_hom s X)) :
  φ = ψ :=
begin
  have : (⊤ : star_subalgebra 𝕜 C(s, 𝕜)) ≤ φ.equalizer ψ,
  rw ←polynomial_functions.star_closure_topological_closure s,
  refine star_subalgebra.topological_closure_minimal
    (polynomial_functions.le_equalizer_star s φ ψ h) (is_closed_eq hφ hψ),
  exact star_alg_hom.ext (λ x, this mem_top),
end
