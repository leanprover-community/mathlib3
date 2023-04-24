import number_theory.number_field.norm
import field_theory.is_alg_closed.basic
import ring_theory.norm
import ring_theory.trace

/- section instances

local attribute [-instance] algebraic_closure.algebra

variables {K : Type*} [field K] [number_field K]

instance : char_zero (algebraic_closure K) := sorry

noncomputable instance i1 : algebra ℚ (algebraic_closure K) := algebra_rat

noncomputable instance i2 : algebra K (algebraic_closure K) := algebraic_closure.algebra K

instance : char_zero (normal_closure ℚ K (algebraic_closure K)) := sorry

noncomputable instance : algebra ℚ (normal_closure ℚ K (algebraic_closure K)) := algebra_rat

instance : number_field (normal_closure ℚ K (algebraic_closure K)) := sorry

instance : is_galois ℚ (normal_closure ℚ K (algebraic_closure K)) := sorry

instance i3 : is_galois K  (normal_closure ℚ K (algebraic_closure K)) := sorry

end instances -/

-- open_locale number_field big_operators

section norm

namespace trace

open algebra

variables {R S T : Type*} [comm_ring R] [comm_ring S] [comm_ring T]
variables [algebra R S] [algebra R T]

lemma norm_norm_of_basis [algebra S T] [is_scalar_tower R S T] {ι κ : Type*} [finite ι] [finite κ]
  (b : basis ι R S) (c : basis κ S T) (x : T) :
  norm R (norm S x) = norm R x :=
begin
  haveI := classical.dec_eq ι,
  haveI := classical.dec_eq κ,
  casesI nonempty_fintype ι,
  casesI nonempty_fintype κ,
  rw norm_eq_matrix_det (b.smul c),
  rw norm_eq_matrix_det b,
  rw norm_eq_matrix_det c,
  rw matrix.det,
  -- trace_eq_matrix_trace b, trace_eq_matrix_trace c,
  --    matrix.trace, matrix.trace, matrix.trace,
  --    ← finset.univ_product_univ, finset.sum_product],

end


end trace

namespace algebra

variables (F K L : Type*) [field F] [field K] [field L] [algebra F K] [algebra F L]
  [algebra K L] [is_scalar_tower F K L] [finite_dimensional F L] [is_separable F L]

lemma norm_norm (x : L) :
  norm F (norm K x) = norm F x :=
begin
  let A := algebraic_closure F,
  apply (algebra_map F A).injective,
  haveI : finite_dimensional K L := finite_dimensional.right F K L,
  haveI : finite_dimensional F K := finite_dimensional.left F K L,
  haveI : is_separable F K := is_separable_tower_bot_of_is_separable F K L,
  haveI : is_separable K L := is_separable_tower_top_of_is_separable F K L,
  letI : ∀ (σ : K →ₐ[F] A), fintype (@alg_hom K L A _ _ _ _ σ.to_ring_hom.to_algebra) :=
    λ _, infer_instance,
  rw [@norm_eq_prod_embeddings F L _ _ _ A _ _ _ _ _ _, fintype.prod_equiv alg_hom_equiv_sigma
    (λ σ : L →ₐ[F] A, σ x) (λ π : (Σ (f : K →ₐ[F] A), _), (π.2 : L → A) x)
    (λ _, rfl)],
  suffices : ∀ σ : K →ₐ[F] A, finset.univ.prod
    (λ (π : @alg_hom K L A _ _ _ _ σ.to_ring_hom.to_algebra), π x) = σ (norm K x),
  { simp_rw [← finset.univ_sigma_univ, finset.prod_sigma, this, norm_eq_prod_embeddings], },
  { intro σ,
    letI : algebra K A := σ.to_ring_hom.to_algebra,
    rw ← norm_eq_prod_embeddings K A,
    refl,
    apply_instance, },
end

#exit

lemma norm_norm0 (x : L) {A : Type*} [field A] [is_alg_closed A] [algebra F A] :
  norm F (norm K x) = norm F x :=
begin
--  let A := algebraic_closure L,
  haveI : finite_dimensional F K := sorry,
  haveI : is_separable F K := sorry,
  haveI : finite_dimensional K L := sorry,
  have : function.injective (algebra_map F A) := (algebra_map F A).injective,
  apply this,
  nth_rewrite 1 norm_eq_prod_embeddings F A,
  letI : ∀ (σ : K →ₐ[F] A), fintype (@alg_hom K L A _ _ _ _ σ.to_ring_hom.to_algebra) :=
  begin
    intro σ,
    apply_instance,
  end,
  rw fintype.prod_equiv alg_hom_equiv_sigma (λ σ : L →ₐ[F] A, σ x)
    (λ π : (Σ (f : K →ₐ[F] A), @alg_hom K L A _ _ _ _ f.to_ring_hom.to_algebra), (π.2 : L → A) x) _,
  { dsimp,
    rw ← finset.univ_sigma_univ,
    rw finset.prod_sigma,
    simp_rw alg_hom_equiv_sigma_apply x,
    have : ∀ σ : K →ₐ[F] A, finset.univ.prod
      (λ (π : @alg_hom K L A _ _ _ _ σ.to_ring_hom.to_algebra), π x) = σ (norm K x) :=
    begin
      intro σ,
      letI : algebra K A := σ.to_ring_hom.to_algebra,
      rw ← norm_eq_prod_embeddings K A,
      refl,
      sorry,
    end,
    simp_rw this,
    rw norm_eq_prod_embeddings, },
  { exact λ σ, (alg_hom_equiv_sigma_apply x).symm, },
end

#exit




  let T : (K →ₐ[F] A) → (A →+* A) := sorry,
/-  begin
    intro τ,
    have t1 : algebra K A := ring_hom.to_algebra τ,
    refine @is_alg_closed.lift A _ _ K _ A _ _ _ t1 _ _ _,
    sorry,
  end -/
  let R : (L →ₐ[F] A) → (K →ₐ[F] A) :=
  begin
    intro σ,
    use σ ∘ algebra_map K L,
    { simp only [function.comp_app, map_one], },
    { simp only [function.comp_app, map_mul, eq_self_iff_true, forall_const], },
    { simp only [function.comp_app, map_zero], },
    { simp only [function.comp_app, map_add, eq_self_iff_true, forall_const], },
    { simp only [function.comp_app, ←is_scalar_tower.algebra_map_apply, alg_hom.commutes,
        eq_self_iff_true, forall_const], },
  end,

  have prop1 : ∀ (τ : K →ₐ[F] A) (k : K), τ k = (T τ) (algebra_map K A k) :=
  begin
    intros τ k,
    sorry,
  end,

  -- have prop2 : ∀ τ : K →ₐ[F] A, finset.prod {σ : L →ₐ[F] A | σ ∘ algebra_map K L = τ}.to_finset
  --   (λ σ, σ x) = finset.univ.prod (λ π : L →ₐ[K] A, (T τ) (π x)) := sorry,


  have prop2 :  ∀ τ : K →ₐ[F] A,
    (finset.filter (λ (σ : L →ₐ[F] A), R σ = τ) finset.univ).prod (λ σ, σ x) =
    finset.prod finset.univ (λ π : L →ₐ[K] A, (T τ) (π x)) :=
  begin
    intro τ,
    rw ← finset.prod_subtype_eq_prod_filter,
    let e : { σ : L →ₐ[F] A // R σ = τ } ≃ (L →ₐ[K] A) := sorry,
    have := equiv.prod_comp' e _ _ _,
    convert this,
    {
      ext,
      refine ⟨λ σ, _, λ σ, _⟩,
      { exact finset.mem_univ _, },
      { simp only [finset.mem_subtype, finset.mem_univ], }},

--
    sorry,
--    refine fintype.prod_bijective _ _ _ _ _,

  end,

  have h : ∀ σ : L →ₐ[F] A, σ ∈ @finset.univ(L →ₐ[F] A) _ → R σ ∈ @finset.univ (K →ₐ[F] A) _ := sorry,
  rw ← finset.prod_fiberwise finset.univ R _,
  congr,
  dsimp,
  simp_rw prop2,
  simp_rw ← map_prod,
  simp_rw ← norm_eq_prod_embeddings,
  simp_rw ← prop1,
end

end algebra

end norm

#exit

section normal_closure

variables (F K A : Type*) [field F] [field K] [field A] [algebra F K] [algebra F A] [algebra K A]
[is_scalar_tower F K A]

-- instance [char_zero F] : char_zero (normal_closure F K A) :=
--  char_zero_of_injective_algebra_map (algebra_map F _).injective

instance normal_closure_alg_closure.is_scalar_tower : is_scalar_tower F (normal_closure F K A) A :=
is_scalar_tower.subalgebra' F A A _

-- TODO. [is_separable F K] should be enough
instance [is_separable F A] : is_separable F (normal_closure F K A) :=
is_separable_tower_bot_of_is_separable F _ A

noncomputable instance [char_zero F] : char_zero (normal_closure F K A) := sorry

lemma normal_algebra_closure_of_is_algebraic [is_alg_closure K A] (h : algebra.is_algebraic F K) :
  normal F A := sorry

instance normal_closure.is_galois [normal F A] [is_separable F A] :
  is_galois F (normal_closure F K A) := { }

variables [number_field F] [number_field K]

instance : number_field (normal_closure F K A) :=
{ to_finite_dimensional :=
  begin
    haveI : finite_dimensional F K := finite_dimensional.right ℚ F K,
    exact finite_dimensional.trans ℚ F (normal_closure F K A),
  end, }



end normal_closure

#exit

open_locale number_field

/- section galois_closure

variables (F K L : Type*) [field F] [field K] [number_field F] [number_field K] [field L]
  [algebra K L] [is_alg_closure K L] [algebra F K] [algebra F L] [is_scalar_tower F K L]

instance : number_field (normal_closure F K L) :=
{ to_char_zero :=
    char_zero_of_injective_algebra_map (algebra_map F _).injective,
  to_finite_dimensional :=
  begin
    haveI : finite_dimensional F K := sorry,
    have := normal_closure.is_finite_dimensional F K L,
  end,
}

end galois_closure -/

-- section normal

-- variables {F K L : Type*} [field F] [field K] [field L] [algebra F K] [algebra F L]
--   [algebra K L] [is_scalar_tower F K L] [is_alg_closure K L]

-- lemma is_alg_closed.normal.of_algebraic (h : algebra.is_algebraic F K) : normal F L :=
-- normal.of_alg_equiv (is_alg_closure.equiv_of_algebraic F K L (algebraic_closure F) h).symm

-- end normal

section norm

variables (F K L : Type*) [field F] [field K] [field L] [algebra F K] [algebra F L]
  [algebra K L] [is_scalar_tower F K L] [is_separable F L]

example (x : L) :
  algebra.norm F (algebra.norm K x) = algebra.norm F x := sorry

end norm

#exit



namespace ring_of_integers

variables {L : Type*} (F K : Type*) [field K] [field L] [field F]
  [algebra K L] [algebra F K] [algebra F L] [is_scalar_tower F K L]
  [is_separable F K] [finite_dimensional F K] [is_separable K L]
  [finite_dimensional K L] [is_separable F L] [finite_dimensional F L]

lemma norm_composition (x : 𝓞 L) :
  norm F (norm K x) = norm F x :=
begin
  sorry
end

end ring_of_integers

end norm
