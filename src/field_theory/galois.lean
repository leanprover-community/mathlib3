import field_theory.normal
import field_theory.primitive_element
import field_theory.fixed

section

variables (F : Type*) [field F] (E : Type*) [field E] [algebra F E]

/-- A field extension E/F is galois if it is both separable and normal -/
@[class] def is_galois : Prop := is_separable F E ∧ normal F E

instance is_galois_of_fixed_field (G : Type*) [group G] [fintype G] [mul_semiring_action G E] :
  is_galois (mul_action.fixed_points G E) E :=
⟨fixed_points.separable G E, fixed_points.normal G E⟩

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

end

section galois_correspondence

variables {F : Type*} [field F] {E : Type*} [field E] [algebra F E]
variables (H : subgroup (E ≃ₐ[F] E)) (K : intermediate_field F E)

instance subgroup_action : faithful_mul_semiring_action H E := {
  smul := λ h x, h x,
  smul_zero := λ _, alg_equiv.map_zero _,
  smul_add := λ _, alg_equiv.map_add _,
  one_smul := λ _, rfl,
  smul_one := λ _, alg_equiv.map_one _,
  mul_smul := λ _ _ _, rfl,
  smul_mul := λ _, alg_equiv.map_mul _,
  eq_of_smul_eq_smul' := λ x y z, subtype.ext (alg_equiv.ext z),
}

def fixed_field : intermediate_field F E := {
  carrier := mul_action.fixed_points H E,
  zero_mem' := smul_zero,
  add_mem' := λ _ _ hx hy _, by rw [smul_add, hx, hy],
  neg_mem' := λ _ hx _, by rw [smul_neg, hx],
  one_mem' := smul_one,
  mul_mem' := λ _ _ hx hy _, by rw [smul_mul', hx, hy],
  inv_mem' := λ _ hx _, by rw [smul_inv, hx],
  algebra_map_mem' := λ _ _, alg_equiv.commutes _ _,
}

def fixing_subgroup : subgroup (E ≃ₐ[F] E) := {
  carrier := λ ϕ, ∀ x : K, ϕ x = x,
  one_mem' := λ _, rfl,
  mul_mem' := λ _ _ hx hy _, (congr_arg _ (hy _)).trans (hx _),
  inv_mem' := λ _ hx _, (equiv.symm_apply_eq (alg_equiv.to_equiv _)).mpr (hx _).symm,
}

noncomputable def fixing_subgroup_equiv : fixing_subgroup K ≃ (E ≃ₐ[K] E) := {
  to_fun := λ ϕ, alg_equiv.of_bijective (alg_hom.mk ϕ (alg_equiv.map_one ϕ) (alg_equiv.map_mul ϕ)
    (alg_equiv.map_zero ϕ) (alg_equiv.map_add ϕ) (ϕ.mem)) (alg_equiv.bijective ϕ),
  inv_fun := λ ϕ, ⟨alg_equiv.of_bijective (alg_hom.mk ϕ (alg_equiv.map_one ϕ) (alg_equiv.map_mul ϕ)
    (alg_equiv.map_zero ϕ) (alg_equiv.map_add ϕ) (λ r, ϕ.commutes (algebra_map F K r)))
      (alg_equiv.bijective ϕ), ϕ.commutes⟩,
  left_inv := λ _, by {ext, refl},
  right_inv := λ _, by {ext, refl},
}

lemma finite_dimensional.bijective {F : Type*} [field F] {E : Type*} [field E] [algebra F E]
  [finite_dimensional F E] (ϕ : E →ₐ[F] E) : function.bijective ϕ :=
begin
  have inj : function.injective ϕ.to_linear_map := ϕ.to_ring_hom.injective,
  have rank_nullity := linear_map.findim_range_add_findim_ker ϕ.to_linear_map,
  rw [linear_map.ker_eq_bot_of_injective inj, findim_bot, add_zero] at rank_nullity,
  rw ← @findim_top F E _ _ _ at rank_nullity,
  split,
  { exact inj },
  { exact linear_map.range_eq_top.mp (finite_dimensional.eq_of_le_of_findim_eq
    (@le_top (submodule F E) _ ϕ.to_linear_map.range) rank_nullity) },
end

theorem fixing_subgroup_of_fixed_field [finite_dimensional F E] :
  fixing_subgroup (fixed_field H) = H :=
begin
  have H_le : H ≤ (fixing_subgroup (fixed_field H)) :=
    λ ϕ ϕh x, (mul_action.mem_fixed_points E).mp (subtype.mem x) ⟨ϕ, ϕh⟩,
  have key1 := fixing_subgroup_equiv (fixed_field H),
  have key2 := fixed_points.to_alg_hom_equiv H E,
  have key3 : (E ≃ₐ[fixed_field H] E) ≃ (E →ₐ[mul_action.fixed_points H E] E) := {
    to_fun := λ ϕ, alg_hom.mk ϕ ϕ.map_one ϕ.map_mul ϕ.map_zero ϕ.map_add ϕ.commutes,
    inv_fun := λ ϕ, alg_equiv.of_bijective
      (alg_hom.mk ϕ ϕ.map_one ϕ.map_mul ϕ.map_zero ϕ.map_add ϕ.commutes) begin
        have inj : function.injective ϕ.to_linear_map := ϕ.to_ring_hom.injective,
        have rank_nullity := linear_map.findim_range_add_findim_ker (ϕ.to_linear_map),
        rw [linear_map.ker_eq_bot_of_injective inj, findim_bot, add_zero] at rank_nullity,
        have key : finite_dimensional.findim (mul_action.fixed_points H E)
          (ϕ.to_linear_map.range) =
          finite_dimensional.findim (mul_action.fixed_points H E)
          (⊤ : submodule (mul_action.fixed_points H E) E),
          { rw rank_nullity,
            library_search,},
        have tada := finite_dimensional.eq_of_le_of_findim_eq,
      sorry,
    end,
    left_inv := λ _, by {ext, refl},
    right_inv := λ _, by {ext, refl},
  },
  have key4 : (fixing_subgroup (fixed_field H)) ≃ H := equiv.trans (equiv.trans key1 key3) key2.trans,
  have key5 := (fintype.bijective_iff_injective_and_card (set.inclusion H_le)).mpr,
  sorry,
end

/-lemma findim_fixed_field_eq_card [finite_dimensional F E] :
  finite_dimensional.findim (fixed_field H) E = fintype.card H :=
fixed_points.findim_eq_card H E-/


end galois_correspondence
