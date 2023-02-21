import number_theory.number_field.norm
import ring_theory.norm

open_locale number_field big_operators

section norm

variables (F K L : Type*) [field F] [field K] [field L] [algebra F K] [algebra F L]
  [algebra K L] [is_scalar_tower F K L] [finite_dimensional F L] [is_separable F L]

lemma algebra.norm_norm (x : L) :
  algebra.norm F (algebra.norm K x) = algebra.norm F x :=
begin
  haveI : finite_dimensional F K := sorry,
  haveI : is_separable F K := sorry,
  let A := algebraic_closure L,
  have : function.injective (algebra_map F A) := sorry,
  rw ← this.eq_iff,
  rw algebra.norm_eq_prod_embeddings,
  rw algebra.norm_eq_prod_embeddings,
  let T : (K →ₐ[F] A) → (L →ₐ[F] A) := sorry,
  haveI :  ∀ σ : K →ₐ[F] A, fintype { τ : L →ₐ[F] A // τ ∘ (algebra_map K L) = σ} := sorry,
  have : ∀ σ : K →ₐ[F] A, σ ((algebra.norm K) x) =
    ∏ τ : { τ : L →ₐ[F] A // τ ∘ (algebra_map K L) = σ}, τ x := sorry,
  sorry,
end

end norm

namespace ring_of_integers

variables {L : Type*} (F K : Type*) [field K] [field L] [field F]
  [algebra K L] [algebra F K] [algebra F L] [is_scalar_tower F K L]
  [is_separable F K] [finite_dimensional F K] [is_separable K L]
  [finite_dimensional K L] [is_separable F L] [finite_dimensional F L]

lemma norm_norm (x : 𝓞 L) :
  norm F (norm K x) = norm F x :=
begin
  sorry
end

end ring_of_integers

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
