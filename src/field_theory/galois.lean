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
    one_mul := λ ϕ, by {ext, refl},
    mul_one := λ ϕ, by {ext, refl},
    inv := alg_equiv.symm,
    mul_left_inv := λ ϕ, by {ext, exact alg_equiv.symm_apply_apply ϕ a},
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

def aut_fixed_field : intermediate_field F E := {
  carrier := mul_action.fixed_points (E ≃ₐ[F] E) E,
  zero_mem' := smul_zero,
  add_mem' := λ _ _ hx hy _, by rw [smul_add, hx, hy],
  neg_mem' := λ _ hx _, by rw [smul_neg, hx],
  one_mem' := smul_one,
  mul_mem' := λ _ _ hx hy _, by rw [smul_mul', hx, hy],
  inv_mem' := λ _ hx _, by rw [smul_inv, hx],
  algebra_map_mem' := λ _ _, alg_equiv.commutes _ _,
}

lemma aut_fixed_field_findim_eq_card [finite_dimensional F E] :
  finite_dimensional.findim (aut_fixed_field F E) E = fintype.card (E ≃ₐ[F] E) :=
fixed_points.findim_eq_card (E ≃ₐ[F] E) E

lemma card_aut_le_dim [finite_dimensional F E] :
  fintype.card (E ≃ₐ[F] E) ≤ finite_dimensional.findim F E :=
begin
  rw ← aut_fixed_field_findim_eq_card F E,
  rw ← finite_dimensional.findim_mul_findim F (aut_fixed_field F E) E,
  exact nat.le_mul_of_pos_left finite_dimensional.findim_pos,
end

end

section

variables {F : Type*} [field F] {E : Type*} [field E] [algebra F E] (H : subgroup (E ≃ₐ[F] E))

instance subgroup_action : faithful_mul_semiring_action H E := {
  smul := λ h x, (↑h : (E ≃ₐ[F] E)) • x,
  smul_zero := λ _, alg_equiv.map_zero _,
  smul_add := λ _, alg_equiv.map_add _,
  one_smul := λ _, rfl,
  smul_one := λ _, alg_equiv.map_one _,
  mul_smul := λ _ _ _, rfl,
  smul_mul := λ _, alg_equiv.map_mul _,
  eq_of_smul_eq_smul' := λ x y z, subtype.ext (alg_equiv.ext z),
}

def subgroup_fixed_field : intermediate_field F E := {
  carrier := mul_action.fixed_points H E,
  zero_mem' := smul_zero,
  add_mem' := λ _ _ hx hy _, by rw [smul_add, hx, hy],
  neg_mem' := λ _ hx _, by rw [smul_neg, hx],
  one_mem' := smul_one,
  mul_mem' := λ _ _ hx hy _, by rw [smul_mul', hx, hy],
  inv_mem' := λ _ hx _, by rw [smul_inv, hx],
  algebra_map_mem' := λ _ _, alg_equiv.commutes _ _,
}

lemma subgroup_fixed_field_findim_eq_card [finite_dimensional F E] :
  finite_dimensional.findim (subgroup_fixed_field H) E = fintype.card H :=
fixed_points.findim_eq_card H E

lemma lem2 (h : ∃ p : polynomial F, p.separable ∧ p.is_splitting_field F E) :
  aut_fixed_field F E = ⊥ :=
begin
  cases h with p hp,
  haveI := hp.2,
  haveI := polynomial.is_splitting_field.finite_dimensional E p,
  have key := aut_fixed_field_findim_eq_card F E,
end

end
