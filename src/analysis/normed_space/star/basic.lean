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
import topology.algebra.star_subalgebra

/-!
# Normed star rings and algebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A normed star group is a normed group with a compatible `star` which is isometric.

A C⋆-ring is a normed star group that is also a ring and that verifies the stronger
condition `‖x⋆ * x‖ = ‖x‖^2` for all `x`.  If a C⋆-ring is also a star algebra, then it is a
C⋆-algebra.

To get a C⋆-algebra `E` over field `𝕜`, use
`[normed_field 𝕜] [star_ring 𝕜] [normed_ring E] [star_ring E] [cstar_ring E]
 [normed_algebra 𝕜 E] [star_module 𝕜 E]`.

## TODO

- Show that `‖x⋆ * x‖ = ‖x‖^2` is equivalent to `‖x⋆ * x‖ = ‖x⋆‖ * ‖x‖`, which is used as the
  definition of C*-algebras in some sources (e.g. Wikipedia).

-/

open_locale topology

local postfix `⋆`:std.prec.max_plus := star

/-- A normed star group is a normed group with a compatible `star` which is isometric. -/
class normed_star_group (E : Type*) [seminormed_add_comm_group E] [star_add_monoid E] : Prop :=
(norm_star : ∀ x : E, ‖x⋆‖ = ‖x‖)

export normed_star_group (norm_star)
attribute [simp] norm_star

variables {𝕜 E α : Type*}

section normed_star_group
variables [seminormed_add_comm_group E] [star_add_monoid E] [normed_star_group E]

@[simp] lemma nnnorm_star (x : E) : ‖star x‖₊ = ‖x‖₊ := subtype.ext $ norm_star _

/-- The `star` map in a normed star group is a normed group homomorphism. -/
def star_normed_add_group_hom : normed_add_group_hom E E :=
{ bound' := ⟨1, λ v, le_trans (norm_star _).le (one_mul _).symm.le⟩,
  .. star_add_equiv }

/-- The `star` map in a normed star group is an isometry -/
lemma star_isometry : isometry (star : E → E) :=
show isometry star_add_equiv,
by exact add_monoid_hom_class.isometry_of_norm star_add_equiv
    (show ∀ x, ‖x⋆‖ = ‖x‖, from norm_star)

@[priority 100]
instance normed_star_group.to_has_continuous_star : has_continuous_star E :=
⟨star_isometry.continuous⟩

end normed_star_group

instance ring_hom_isometric.star_ring_end [normed_comm_ring E] [star_ring E]
  [normed_star_group E] : ring_hom_isometric (star_ring_end E) :=
⟨norm_star⟩

/-- A C*-ring is a normed star ring that satifies the stronger condition `‖x⋆ * x‖ = ‖x‖^2`
for every `x`. -/
class cstar_ring (E : Type*) [non_unital_normed_ring E] [star_ring E] : Prop :=
(norm_star_mul_self : ∀ {x : E}, ‖x⋆ * x‖ = ‖x‖ * ‖x‖)

instance : cstar_ring ℝ :=
{ norm_star_mul_self := λ x, by simp only [star, id.def, norm_mul] }

namespace cstar_ring
section non_unital

variables [non_unital_normed_ring E] [star_ring E] [cstar_ring E]

/-- In a C*-ring, star preserves the norm. -/
@[priority 100] -- see Note [lower instance priority]
instance to_normed_star_group : normed_star_group E :=
⟨begin
  intro x,
  by_cases htriv : x = 0,
  { simp only [htriv, star_zero] },
  { have hnt : 0 < ‖x‖ := norm_pos_iff.mpr htriv,
    have hnt_star : 0 < ‖x⋆‖ :=
      norm_pos_iff.mpr ((add_equiv.map_ne_zero_iff star_add_equiv).mpr htriv),
    have h₁ := calc
      ‖x‖ * ‖x‖ = ‖x⋆ * x‖        : norm_star_mul_self.symm
            ... ≤ ‖x⋆‖ * ‖x‖      : norm_mul_le _ _,
    have h₂ := calc
      ‖x⋆‖ * ‖x⋆‖ = ‖x * x⋆‖      : by rw [←norm_star_mul_self, star_star]
             ... ≤ ‖x‖ * ‖x⋆‖     : norm_mul_le _ _,
    exact le_antisymm (le_of_mul_le_mul_right h₂ hnt_star) (le_of_mul_le_mul_right h₁ hnt) },
end⟩

lemma norm_self_mul_star {x : E} : ‖x * x⋆‖ = ‖x‖ * ‖x‖ :=
by { nth_rewrite 0 [←star_star x], simp only [norm_star_mul_self, norm_star] }

lemma norm_star_mul_self' {x : E} : ‖x⋆ * x‖ = ‖x⋆‖ * ‖x‖ :=
by rw [norm_star_mul_self, norm_star]

lemma nnnorm_self_mul_star {x : E} : ‖x * star x‖₊ = ‖x‖₊ * ‖x‖₊ :=
subtype.ext norm_self_mul_star

lemma nnnorm_star_mul_self {x : E} : ‖x⋆ * x‖₊ = ‖x‖₊ * ‖x‖₊ :=
subtype.ext norm_star_mul_self

@[simp]
lemma star_mul_self_eq_zero_iff (x : E) : star x * x = 0 ↔ x = 0 :=
by { rw [←norm_eq_zero, norm_star_mul_self], exact mul_self_eq_zero.trans norm_eq_zero }

lemma star_mul_self_ne_zero_iff (x : E) : star x * x ≠ 0 ↔ x ≠ 0 :=
by simp only [ne.def, star_mul_self_eq_zero_iff]

@[simp]
lemma mul_star_self_eq_zero_iff (x : E) : x * star x = 0 ↔ x = 0 :=
by simpa only [star_eq_zero, star_star] using @star_mul_self_eq_zero_iff _ _ _ _ (star x)

lemma mul_star_self_ne_zero_iff (x : E) : x * star x ≠ 0 ↔ x ≠ 0 :=
by simp only [ne.def, mul_star_self_eq_zero_iff]

end non_unital

section prod_pi

variables {ι R₁ R₂ : Type*} {R : ι → Type*}
variables [non_unital_normed_ring R₁] [star_ring R₁] [cstar_ring R₁]
variables [non_unital_normed_ring R₂] [star_ring R₂] [cstar_ring R₂]
variables [Π i, non_unital_normed_ring (R i)] [Π i, star_ring (R i)]

/-- This instance exists to short circuit type class resolution because of problems with
inference involving Π-types. -/
instance _root_.pi.star_ring' : star_ring (Π i, R i) := infer_instance

variables [fintype ι] [Π i, cstar_ring (R i)]

instance _root_.prod.cstar_ring : cstar_ring (R₁ × R₂) :=
{ norm_star_mul_self := λ x,
  begin
    unfold norm,
    simp only [prod.fst_mul, prod.fst_star, prod.snd_mul, prod.snd_star, norm_star_mul_self, ←sq],
    refine le_antisymm _ _,
    { refine max_le _ _;
      rw [sq_le_sq, abs_of_nonneg (norm_nonneg _)],
      exact (le_max_left _ _).trans (le_abs_self _),
      exact (le_max_right _ _).trans (le_abs_self _) },
    { rw le_sup_iff,
      rcases le_total (‖x.fst‖) (‖x.snd‖) with (h | h);
      simp [h] }
  end }

instance _root_.pi.cstar_ring : cstar_ring (Π i, R i) :=
{ norm_star_mul_self := λ x,
  begin
    simp only [norm, pi.mul_apply, pi.star_apply, nnnorm_star_mul_self, ←sq],
    norm_cast,
    exact (finset.comp_sup_eq_sup_comp_of_is_total (λ x : nnreal, x ^ 2)
      (λ x y h, by simpa only [sq] using mul_le_mul' h h) (by simp)).symm,
  end }

instance _root_.pi.cstar_ring' : cstar_ring (ι → R₁) := pi.cstar_ring

end prod_pi

section unital
variables [normed_ring E] [star_ring E] [cstar_ring E]

@[simp] lemma norm_one [nontrivial E] : ‖(1 : E)‖ = 1 :=
begin
  have : 0 < ‖(1 : E)‖ := norm_pos_iff.mpr one_ne_zero,
  rw [←mul_left_inj' this.ne', ←norm_star_mul_self, mul_one, star_one, one_mul],
end

@[priority 100] -- see Note [lower instance priority]
instance [nontrivial E] : norm_one_class E := ⟨norm_one⟩

lemma norm_coe_unitary [nontrivial E] (U : unitary E) : ‖(U : E)‖ = 1 :=
begin
  rw [←sq_eq_sq (norm_nonneg _) zero_le_one, one_pow 2, sq, ←cstar_ring.norm_star_mul_self,
    unitary.coe_star_mul_self, cstar_ring.norm_one],
end

@[simp] lemma norm_of_mem_unitary [nontrivial E] {U : E} (hU : U ∈ unitary E) : ‖U‖ = 1 :=
norm_coe_unitary ⟨U, hU⟩

@[simp] lemma norm_coe_unitary_mul (U : unitary E) (A : E) : ‖(U : E) * A‖ = ‖A‖ :=
begin
  nontriviality E,
  refine le_antisymm _ _,
  { calc _  ≤ ‖(U : E)‖ * ‖A‖     : norm_mul_le _ _
        ... = ‖A‖                 : by rw [norm_coe_unitary, one_mul] },
  { calc _ = ‖(U : E)⋆ * U * A‖         : by rw [unitary.coe_star_mul_self U, one_mul]
       ... ≤ ‖(U : E)⋆‖ * ‖(U : E) * A‖ : by { rw [mul_assoc], exact norm_mul_le _ _ }
       ... = ‖(U : E) * A‖              : by rw [norm_star, norm_coe_unitary, one_mul] },
end

@[simp] lemma norm_unitary_smul (U : unitary E) (A : E) : ‖U • A‖ = ‖A‖ :=
norm_coe_unitary_mul U A

lemma norm_mem_unitary_mul {U : E} (A : E) (hU : U ∈ unitary E) : ‖U * A‖ = ‖A‖ :=
norm_coe_unitary_mul ⟨U, hU⟩ A

@[simp] lemma norm_mul_coe_unitary (A : E) (U : unitary E) : ‖A * U‖ = ‖A‖ :=
calc _ = ‖((U : E)⋆ * A⋆)⋆‖ : by simp only [star_star, star_mul]
  ...  = ‖(U : E)⋆ * A⋆‖    : by rw [norm_star]
  ...  = ‖A⋆‖               : norm_mem_unitary_mul (star A) (unitary.star_mem U.prop)
  ...  = ‖A‖                : norm_star _

lemma norm_mul_mem_unitary (A : E) {U : E} (hU : U ∈ unitary E) : ‖A * U‖ = ‖A‖ :=
norm_mul_coe_unitary A ⟨U, hU⟩

end unital
end cstar_ring

lemma is_self_adjoint.nnnorm_pow_two_pow [normed_ring E] [star_ring E]
  [cstar_ring E] {x : E} (hx : is_self_adjoint x) (n : ℕ) : ‖x ^ 2 ^ n‖₊ = ‖x‖₊ ^ (2 ^ n) :=
begin
  induction n with k hk,
  { simp only [pow_zero, pow_one] },
  { rw [pow_succ, pow_mul', sq],
    nth_rewrite 0 ←(self_adjoint.mem_iff.mp hx),
    rw [←star_pow, cstar_ring.nnnorm_star_mul_self, ←sq, hk, pow_mul'] },
end

lemma self_adjoint.nnnorm_pow_two_pow [normed_ring E] [star_ring E] [cstar_ring E]
  (x : self_adjoint E) (n : ℕ) : ‖x ^ 2 ^ n‖₊ = ‖x‖₊ ^ (2 ^ n) :=
x.prop.nnnorm_pow_two_pow _

section starₗᵢ

variables [comm_semiring 𝕜] [star_ring 𝕜]
variables [seminormed_add_comm_group E] [star_add_monoid E] [normed_star_group E]
variables [module 𝕜 E] [star_module 𝕜 E]

variables (𝕜)
/-- `star` bundled as a linear isometric equivalence -/
def starₗᵢ : E ≃ₗᵢ⋆[𝕜] E :=
{ map_smul' := star_smul,
  norm_map' := norm_star,
  .. star_add_equiv }

variables {𝕜}

@[simp] lemma coe_starₗᵢ : (starₗᵢ 𝕜 : E → E) = star := rfl

lemma starₗᵢ_apply {x : E} : starₗᵢ 𝕜 x = star x := rfl

end starₗᵢ

namespace star_subalgebra

instance to_normed_algebra {𝕜 A : Type*} [normed_field 𝕜] [star_ring 𝕜]
  [semi_normed_ring A] [star_ring A] [normed_algebra 𝕜 A] [star_module 𝕜 A]
  (S : star_subalgebra 𝕜 A) : normed_algebra 𝕜 S :=
@normed_algebra.induced _ 𝕜 S A _ (subring_class.to_ring S) S.algebra _ _ _ S.subtype

instance to_cstar_ring {R A} [comm_ring R] [star_ring R] [normed_ring A]
  [star_ring A] [cstar_ring A] [algebra R A] [star_module R A] (S : star_subalgebra R A) :
  cstar_ring S :=
{ norm_star_mul_self := λ x, @cstar_ring.norm_star_mul_self A _ _ _ x }

end star_subalgebra
