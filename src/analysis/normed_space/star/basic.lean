/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import analysis.normed.group.hom
import analysis.normed_space.basic
import analysis.normed_space.linear_isometry
import algebra.star.self_adjoint
import algebra.star.unitary

/-!
# Normed star rings and algebras

A normed star monoid is a `star_add_monoid` endowed with a norm such that the star operation is
isometric.

A C⋆-ring is a normed star monoid that is also a ring and that verifies the stronger
condition `∥x⋆ * x∥ = ∥x∥^2` for all `x`.  If a C⋆-ring is also a star algebra, then it is a
C⋆-algebra.

To get a C⋆-algebra `E` over field `𝕜`, use
`[normed_field 𝕜] [star_ring 𝕜] [normed_ring E] [star_ring E] [cstar_ring E]
 [normed_algebra 𝕜 E] [star_module 𝕜 E]`.

## TODO

- Show that `∥x⋆ * x∥ = ∥x∥^2` is equivalent to `∥x⋆ * x∥ = ∥x⋆∥ * ∥x∥`, which is used as the
  definition of C*-algebras in some sources (e.g. Wikipedia).

-/

open_locale topological_space

local postfix `⋆`:std.prec.max_plus := star

/-- A normed star monoid is an additive monoid with a star,
endowed with a norm such that `star` is isometric. -/
class normed_star_monoid (E : Type*) [normed_group E] [star_add_monoid E] : Prop :=
(norm_star : ∀ {x : E}, ∥x⋆∥ = ∥x∥)

export normed_star_monoid (norm_star)
attribute [simp] norm_star

/-- A C*-ring is a normed star ring that satifies the stronger condition `∥x⋆ * x∥ = ∥x∥^2`
for every `x`. -/
class cstar_ring (E : Type*) [normed_ring E] [star_ring E] : Prop :=
(norm_star_mul_self : ∀ {x : E}, ∥x⋆ * x∥ = ∥x∥ * ∥x∥)

instance : cstar_ring ℝ :=
{ norm_star_mul_self := λ x, by simp only [star, id.def, norm_mul] }

variables {𝕜 E α : Type*}

section normed_star_monoid
variables [normed_group E] [star_add_monoid E] [normed_star_monoid E]

/-- The `star` map in a normed star group is a normed group homomorphism. -/
def star_normed_group_hom : normed_group_hom E E :=
{ bound' := ⟨1, λ v, le_trans (norm_star.le) (one_mul _).symm.le⟩,
  .. star_add_equiv }

/-- The `star` map in a normed star group is an isometry -/
lemma star_isometry : isometry (star : E → E) :=
star_add_equiv.to_add_monoid_hom.isometry_of_norm (λ _, norm_star)

lemma continuous_star : continuous (star : E → E) := star_isometry.continuous

lemma continuous_on_star {s : set E} : continuous_on star s := continuous_star.continuous_on

lemma continuous_at_star {x : E} : continuous_at star x := continuous_star.continuous_at

lemma continuous_within_at_star {s : set E} {x : E} : continuous_within_at star s x :=
continuous_star.continuous_within_at

lemma tendsto_star (x : E) : filter.tendsto star (𝓝 x) (𝓝 x⋆) := continuous_star.tendsto x

lemma filter.tendsto.star {f : α → E} {l : filter α} {y : E} (h : filter.tendsto f l (𝓝 y)) :
  filter.tendsto (λ x, (f x)⋆) l (𝓝 y⋆) :=
(continuous_star.tendsto y).comp h

variables [topological_space α]

lemma continuous.star {f : α → E} (hf : continuous f) : continuous (λ y, star (f y)) :=
continuous_star.comp hf

lemma continuous_at.star {f : α → E} {x : α} (hf : continuous_at f x) :
  continuous_at (λ x, (f x)⋆) x :=
continuous_at_star.comp hf

lemma continuous_on.star {f : α → E} {s : set α} (hf : continuous_on f s) :
  continuous_on (λ x, (f x)⋆) s :=
continuous_star.comp_continuous_on hf

lemma continuous_within_at.star {f : α → E} {s : set α} {x : α}
  (hf : continuous_within_at f s x) : continuous_within_at (λ x, (f x)⋆) s x := hf.star

end normed_star_monoid

instance ring_hom_isometric.star_ring_end [normed_comm_ring E] [star_ring E]
   [normed_star_monoid E] : ring_hom_isometric (star_ring_end E) :=
⟨λ _, norm_star⟩

namespace cstar_ring
variables [normed_ring E] [star_ring E] [cstar_ring E]

/-- In a C*-ring, star preserves the norm. -/
@[priority 100] -- see Note [lower instance priority]
instance to_normed_star_monoid : normed_star_monoid E :=
⟨λ x, begin
  have n_le : ∀ {y : E}, ∥y∥ ≤ ∥y⋆∥,
  { intros y,
    by_cases y0 : y = 0,
    { rw [y0, star_zero] },
    { refine le_of_mul_le_mul_right _ (norm_pos_iff.mpr y0),
      exact (norm_star_mul_self.symm.trans_le $ norm_mul_le _ _) } },
  exact (n_le.trans_eq $ congr_arg _ $ star_star _).antisymm n_le,
end⟩

lemma norm_self_mul_star {x : E} : ∥x * x⋆∥ = ∥x∥ * ∥x∥ :=
by { nth_rewrite 0 [←star_star x], simp only [norm_star_mul_self, norm_star] }

lemma norm_star_mul_self' {x : E} : ∥x⋆ * x∥ = ∥x⋆∥ * ∥x∥ :=
by rw [norm_star_mul_self, norm_star]

lemma nnnorm_star_mul_self {x : E} : ∥x⋆ * x∥₊ = ∥x∥₊ * ∥x∥₊ :=
subtype.ext norm_star_mul_self

@[simp] lemma norm_one [nontrivial E] : ∥(1 : E)∥ = 1 :=
begin
  have : 0 < ∥(1 : E)∥ := norm_pos_iff.mpr one_ne_zero,
  rw [←mul_left_inj' this.ne', ←norm_star_mul_self, mul_one, star_one, one_mul],
end

@[priority 100] -- see Note [lower instance priority]
instance [nontrivial E] : norm_one_class E := ⟨norm_one⟩

lemma norm_coe_unitary [nontrivial E] (U : unitary E) : ∥(U : E)∥ = 1 :=
begin
  rw [←sq_eq_sq (norm_nonneg _) zero_le_one, one_pow 2, sq, ←cstar_ring.norm_star_mul_self,
    unitary.coe_star_mul_self, cstar_ring.norm_one],
end

@[simp] lemma norm_of_mem_unitary [nontrivial E] {U : E} (hU : U ∈ unitary E) : ∥U∥ = 1 :=
norm_coe_unitary ⟨U, hU⟩

@[simp] lemma norm_coe_unitary_mul (U : unitary E) (A : E) : ∥(U : E) * A∥ = ∥A∥ :=
begin
  nontriviality E,
  refine le_antisymm _ _,
  { calc _  ≤ ∥(U : E)∥ * ∥A∥     : norm_mul_le _ _
        ... = ∥A∥                 : by rw [norm_coe_unitary, one_mul] },
  { calc _ = ∥(U : E)⋆ * U * A∥         : by rw [unitary.coe_star_mul_self U, one_mul]
       ... ≤ ∥(U : E)⋆∥ * ∥(U : E) * A∥ : by { rw [mul_assoc], exact norm_mul_le _ _ }
       ... = ∥(U : E) * A∥              : by rw [norm_star, norm_coe_unitary, one_mul] },
end

@[simp] lemma norm_unitary_smul (U : unitary E) (A : E) : ∥U • A∥ = ∥A∥ :=
norm_coe_unitary_mul U A

lemma norm_mem_unitary_mul {U : E} (A : E) (hU : U ∈ unitary E) : ∥U * A∥ = ∥A∥ :=
norm_coe_unitary_mul ⟨U, hU⟩ A

@[simp] lemma norm_mul_coe_unitary (A : E) (U : unitary E) : ∥A * U∥ = ∥A∥ :=
calc _ = ∥((U : E)⋆ * A⋆)⋆∥ : by simp only [star_star, star_mul]
  ...  = ∥(U : E)⋆ * A⋆∥    : by rw [norm_star]
  ...  = ∥A⋆∥               : norm_mem_unitary_mul (star A) (unitary.star_mem U.prop)
  ...  = ∥A∥                : norm_star

lemma norm_mul_mem_unitary (A : E) {U : E} (hU : U ∈ unitary E) : ∥A * U∥ = ∥A∥ :=
norm_mul_coe_unitary A ⟨U, hU⟩

end cstar_ring

lemma nnnorm_pow_two_pow_of_self_adjoint [normed_ring E] [star_ring E] [cstar_ring E]
  {x : E} (hx : x ∈ self_adjoint E) (n : ℕ) : ∥x ^ 2 ^ n∥₊ = ∥x∥₊ ^ (2 ^ n) :=
begin
  induction n with k hk,
  { simp only [pow_zero, pow_one] },
  { rw [pow_succ, pow_mul', sq],
    nth_rewrite 0 ←(self_adjoint.mem_iff.mp hx),
    rw [←star_pow, cstar_ring.nnnorm_star_mul_self, ←sq, hk, pow_mul'] },
end

lemma self_adjoint.nnnorm_pow_two_pow [normed_ring E] [star_ring E] [cstar_ring E]
  (x : self_adjoint E) (n : ℕ) : ∥x ^ 2 ^ n∥₊ = ∥x∥₊ ^ (2 ^ n) :=
nnnorm_pow_two_pow_of_self_adjoint x.property _

section starₗᵢ

variables [comm_semiring 𝕜] [star_ring 𝕜] [normed_ring E] [star_ring E] [normed_star_monoid E]
variables [module 𝕜 E] [star_module 𝕜 E]

variables (𝕜)
/-- `star` bundled as a linear isometric equivalence -/
def starₗᵢ : E ≃ₗᵢ⋆[𝕜] E :=
{ map_smul' := star_smul,
  norm_map' := λ x, norm_star,
  .. star_add_equiv }

variables {𝕜}

@[simp] lemma coe_starₗᵢ : (starₗᵢ 𝕜 : E → E) = star := rfl

lemma starₗᵢ_apply {x : E} : starₗᵢ 𝕜 x = star x := rfl

end starₗᵢ
