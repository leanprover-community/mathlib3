/-
Copyright (c) 2022 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import topology.algebra.module.weak_dual
import algebra.algebra.spectrum

/-!
# Character space of a topological algebra

The character space of a topological algebra is the subset of elements of the weak dual that
are also algebra homomorphisms. This space is used in the Gelfand transform, which gives an
isomorphism between a commutative C⋆-algebra and continuous functions on the character space
of the algebra. This, in turn, is used to construct the continuous functional calculus on
C⋆-algebras.


## Implementation notes

We define `character_space 𝕜 A` as a subset of the weak dual, which automatically puts the
correct topology on the space. We then define `to_alg_hom` which provides the algebra homomorphism
corresponding to any element. We also provide `to_clm` which provides the element as a
continuous linear map. (Even though `weak_dual 𝕜 A` is a type copy of `A →L[𝕜] 𝕜`, this is
often more convenient.)

## Tags

character space, Gelfand transform, functional calculus

-/

namespace weak_dual

/-- The character space of a topological algebra is the subset of elements of the weak dual that
are also algebra homomorphisms. -/
def character_space (𝕜 : Type*) (A : Type*) [comm_semiring 𝕜] [topological_space 𝕜]
  [has_continuous_add 𝕜] [has_continuous_const_smul 𝕜 𝕜]
  [non_unital_non_assoc_semiring A] [topological_space A] [module 𝕜 A] :=
  {φ : weak_dual 𝕜 A | (φ ≠ 0) ∧ (∀ (x y : A), φ (x * y) = (φ x) * (φ y))}

variables {𝕜 : Type*} {A : Type*}

namespace character_space

section non_unital_non_assoc_semiring

variables [comm_semiring 𝕜] [topological_space 𝕜] [has_continuous_add 𝕜]
  [has_continuous_const_smul 𝕜 𝕜] [non_unital_non_assoc_semiring A] [topological_space A]
  [module 𝕜 A]

lemma coe_apply (φ : character_space 𝕜 A) (x : A) : (φ : weak_dual 𝕜 A) x = φ x := rfl

/-- An element of the character space, as a continuous linear map. -/
def to_clm (φ : character_space 𝕜 A) : A →L[𝕜] 𝕜 := (φ : weak_dual 𝕜 A)

lemma to_clm_apply (φ : character_space 𝕜 A) (x : A) : φ x = to_clm φ x := rfl

/-- An element of the character space, as an non-unital algebra homomorphism. -/
@[simps] def to_non_unital_alg_hom (φ : character_space 𝕜 A) : A →ₙₐ[𝕜] 𝕜 :=
{ to_fun := (φ : A → 𝕜),
  map_mul' := φ.prop.2,
  map_smul' := (to_clm φ).map_smul,
  map_zero' := continuous_linear_map.map_zero _,
  map_add' := continuous_linear_map.map_add _ }

lemma map_zero (φ : character_space 𝕜 A) : φ 0 = 0 := (to_non_unital_alg_hom φ).map_zero
lemma map_add (φ : character_space 𝕜 A) (x y : A) : φ (x + y) = φ x + φ y :=
  (to_non_unital_alg_hom φ).map_add _ _
lemma map_smul (φ : character_space 𝕜 A) (r : 𝕜) (x : A) : φ (r • x) = r • (φ x) :=
  (to_clm φ).map_smul _ _
lemma map_mul (φ : character_space 𝕜 A) (x y : A) : φ (x * y) = φ x * φ y :=
  (to_non_unital_alg_hom φ).map_mul _ _
lemma continuous (φ : character_space 𝕜 A) : continuous φ := (to_clm φ).continuous

end non_unital_non_assoc_semiring

section unital

variables [comm_ring 𝕜] [no_zero_divisors 𝕜] [topological_space 𝕜] [has_continuous_add 𝕜]
  [has_continuous_const_smul 𝕜 𝕜] [topological_space A] [semiring A] [algebra 𝕜 A]

lemma map_one (φ : character_space 𝕜 A) : φ 1 = 1 :=
begin
  have h₁ : (φ 1) * (1 - φ 1) = 0 := by rw [mul_sub, sub_eq_zero, mul_one, ←map_mul φ, one_mul],
  rcases mul_eq_zero.mp h₁ with h₂|h₂,
  { exfalso,
    apply φ.prop.1,
    ext,
    rw [continuous_linear_map.zero_apply, ←one_mul x, coe_apply, map_mul φ, h₂, zero_mul] },
  { rw [sub_eq_zero] at h₂,
    exact h₂.symm },
end

/-- An element of the character space, as an algebra homomorphism. -/
@[simps] def to_alg_hom (φ : character_space 𝕜 A) : A →ₐ[𝕜] 𝕜 :=
{ map_one' := map_one φ,
  commutes' := λ r, by
  { rw [algebra.algebra_map_eq_smul_one, algebra.id.map_eq_id, ring_hom.id_apply],
    change ((φ : weak_dual 𝕜 A) : A →L[𝕜] 𝕜) (r • 1) = r,
    rw [continuous_linear_map.map_smul, algebra.id.smul_eq_mul, coe_apply, map_one φ, mul_one] },
  ..to_non_unital_alg_hom φ }

lemma eq_set_map_one_map_mul [nontrivial 𝕜] : character_space 𝕜 A =
  {φ : weak_dual 𝕜 A | (φ 1 = 1) ∧ (∀ (x y : A), φ (x * y) = (φ x) * (φ y))} :=
begin
  ext x,
  refine ⟨λ h, ⟨map_one ⟨x, h⟩, h.2⟩, λ h, ⟨_, h.2⟩⟩,
  rintro rfl,
  simpa using h.1,
end

lemma is_closed [nontrivial 𝕜] [t2_space 𝕜] [has_continuous_mul 𝕜] :
  is_closed (character_space 𝕜 A) :=
begin
  rw [eq_set_map_one_map_mul],
  refine is_closed.inter (is_closed_eq (eval_continuous _) continuous_const) _,
  change is_closed {φ : weak_dual 𝕜 A | ∀ x y : A, φ (x * y) = φ x * φ y},
  rw [set.set_of_forall],
  refine is_closed_Inter (λ a, _),
  rw [set.set_of_forall],
  exact is_closed_Inter (λ _, is_closed_eq (eval_continuous _)
    ((eval_continuous _).mul (eval_continuous _)))
end

end unital

section ring

variables [comm_ring 𝕜] [no_zero_divisors 𝕜] [topological_space 𝕜] [has_continuous_add 𝕜]
  [has_continuous_const_smul 𝕜 𝕜] [topological_space A] [ring A] [algebra 𝕜 A]

lemma apply_mem_spectrum [nontrivial 𝕜] (φ : character_space 𝕜 A) (a : A) : φ a ∈ spectrum 𝕜 a :=
(to_alg_hom φ).apply_mem_spectrum a

end ring

end character_space

end weak_dual
