import field_theory.normal
import field_theory.primitive_element
import field_theory.fixed

section

variables (F : Type*) [field F] (E : Type*) [field E] [algebra F E]

/-- A field extension E/F is galois if it is both separable and normal -/
@[class] def is_galois : Prop := is_separable F E ∧ normal F E

lemma lem1 [finite_dimensional F E] (h : is_galois F E) :
  ∃ p : polynomial F, p.separable ∧ p.is_splitting_field F E :=
begin
  haveI : decidable_eq E := classical.dec_eq E,
  cases field.exists_primitive_element h.1 with α h1,
  cases h.1 α with h2 h3,
  cases h.2 α with _ h4,
  use minimal_polynomial h2,
  split,
  { exact h3 },
  { split,
    { exact h4 },
    { rw [eq_top_iff, ←intermediate_field.top_to_subalgebra, ←h1],
      rw intermediate_field.adjoin_simple_to_subalgebra_of_integral F α h2,
      apply algebra.adjoin_mono,
      rw [set.singleton_subset_iff, finset.mem_coe, multiset.mem_to_finset, polynomial.mem_roots],
      { dsimp only [polynomial.is_root],
        rw [polynomial.eval_map, ←polynomial.aeval_def],
        exact minimal_polynomial.aeval h2 },
      { exact polynomial.map_ne_zero (minimal_polynomial.ne_zero h2) } } }
end

instance aut : group (E ≃ₐ[F] E) := {
    mul := λ ϕ ψ, ψ.trans ϕ,
    mul_assoc := λ ϕ ψ χ, rfl,
    one := 1,
    one_mul := λ ϕ, by {ext,refl},
    mul_one := λ ϕ, by {ext,refl},
    inv := alg_equiv.symm,
    mul_left_inv := λ ϕ, by {ext,exact alg_equiv.symm_apply_apply ϕ a},
}

instance aut_action : faithful_mul_semiring_action (E ≃ₐ[F] E) E := {
    smul := alg_equiv.to_fun,
    smul_zero := alg_equiv.map_zero,
    smul_one := alg_equiv.map_one,
    one_smul := λ _, rfl,
    smul_add := alg_equiv.map_add,
    smul_mul := alg_equiv.map_mul,
    mul_smul := λ _ _ _, rfl,
    eq_of_smul_eq_smul' := λ _ _, alg_equiv.ext,
}

end

section

variables {F : Type*} [field F] {E : Type*} [field E] [algebra F E]

instance subgroup_action (H : subgroup (E ≃ₐ[F] E)) : faithful_mul_semiring_action H E :=
  mul_action.submonoid_action E H

def fixed_field (H : subgroup (E ≃ₐ[F] E)) : intermediate_field F E := {
  carrier := mul_action.fixed_points H E,
}

end

/-instance aut_action : faithful_mul_semiring_action (E ≃ₐ[F] E) E := {
    smul := alg_equiv.to_fun,
    smul_zero := alg_equiv.map_zero,
    smul_one := alg_equiv.map_one,
    one_smul := λ _, rfl,
    smul_add := alg_equiv.map_add,
    smul_mul := alg_equiv.map_mul,
    mul_smul := λ _ _ _, rfl,
    eq_of_smul_eq_smul' := λ _ _, alg_equiv.ext,
}

instance : is_scalar_tower F (E ≃ₐ[F] E) E := {

}

lemma card_aut_le_dim [finite_dimensional F E] :
  fintype.card (E ≃ₐ[F] E) ≤ finite_dimensional.findim F E :=
begin
  haveI := fixed_points.finite_dimensional (E ≃ₐ[F] E) E,
  have key := fixed_points.findim_eq_card (E ≃ₐ[F] E) E,
  rw ← key,
end

lemma lem2 (h : ∃ p : polynomial F, p.separable ∧ p.is_splitting_field F E) :
  (mul_action.fixed_points (E ≃ₐ[F] E) E) = (⊥ : intermediate_field F E) :=
begin
  cases h with p hp,
  haveI := hp.2,
  haveI := polynomial.is_splitting_field.finite_dimensional E p,
  haveI := alg_hom.fintype F E,
  haveI := fintype.of_injective (@alg_equiv.to_alg_hom F E E _ _ _ _ _)
    (λ _ _ h, alg_equiv.ext (alg_hom.ext_iff.mp h)),
  haveI := fixed_points.finite_dimensional (E ≃ₐ[F] E) E,
  have key := fixed_points.findim_eq_card (E ≃ₐ[F] E) E,
end -/
