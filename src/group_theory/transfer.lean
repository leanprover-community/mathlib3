/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import group_theory.complement
import group_theory.group_action.basic
import group_theory.index

/-!
# The Transfer Homomorphism

In this file we construct the transfer homomorphism.

## Main definitions

- `transfer ϕ : G →* A` for `ϕ : H →* A` from `H : subgroup G` to a commutative group `A`.
-/

open_locale big_operators

open subgroup

variables {G : Type*} [group G] {H : subgroup G}
variables {A : Type*} [comm_group A] (ϕ : H →* A) (R S T : left_transversals (H : set G))

namespace subgroup

namespace left_transversals

/-- The left action of `G` on left transversals of `H : subgroup G`. -/
@[to_additive "The left action of `G` on left transversals of `H : add_subgroup G`."]
instance left_action : mul_action G (left_transversals (H : set G)) :=
{ smul := λ g T, ⟨left_coset g T, mem_left_transversals_iff_exists_unique_inv_mul_mem.mpr (λ g', by
  { obtain ⟨t, ht1, ht2⟩ := mem_left_transversals_iff_exists_unique_inv_mul_mem.mp T.2 (g⁻¹ * g'),
    simp_rw [←mul_assoc, ←mul_inv_rev] at ht1 ht2,
    refine ⟨⟨g * t, mem_left_coset g t.2⟩, ht1, _⟩,
    rintros ⟨-, t', ht', rfl⟩ h,
    exact subtype.ext ((mul_right_inj g).mpr (subtype.ext_iff.mp (ht2 ⟨t', ht'⟩ h))) })⟩,
  one_smul := λ T, subtype.ext (one_left_coset T),
  mul_smul := λ g g' T, subtype.ext (left_coset_assoc ↑T g g').symm }

@[to_additive] lemma smul_apply_eq_mul_apply_inv_smul (g : G) (q : G ⧸ H) :
  ↑(mem_left_transversals.to_equiv (g • T).2 q) =
    g * mem_left_transversals.to_equiv T.2 (g⁻¹ • q) :=
begin
  let w := mem_left_transversals.to_equiv T.2,
  let y := (mem_left_transversals.to_equiv (g • T).2).symm,
  change ↑(y.symm q) = ↑(⟨_, mem_left_coset g (subtype.mem _)⟩ : (g • T).1),
  refine subtype.ext_iff.mp (y.symm_apply_eq.mpr _),
  change q = g • (w.symm (w (g⁻¹ • q))),
  rw [equiv.symm_apply_apply, ←mul_smul, mul_inv_self, one_smul],
end

-- for mathlib:
@[to_additive] lemma mem_normalizer_iff' {g : G} : g ∈ normalizer H ↔ ∀ n, n * g ∈ H ↔ g * n ∈ H :=
begin
  refine ⟨λ h n, _, λ h n, _⟩,
  { specialize h (n * g),
    rwa [mul_assoc, mul_inv_cancel_right] at h },
  { specialize h (n * g⁻¹),
    rwa [inv_mul_cancel_right, ←mul_assoc] at h },
end

/-- The right action of `H.normalizer` on left transversals of `H : subgroup G`. -/
@[to_additive "The right action of `H.normalizer` on left transversals of `H : add_subgroup G`."]
instance right_action : mul_action H.normalizerᵐᵒᵖ (left_transversals (H : set G)) :=
{ smul := λ g T, ⟨right_coset T g.unop, mem_left_transversals_iff_exists_unique_inv_mul_mem.mpr
  (λ g', by
  { obtain ⟨t, ht1, ht2⟩ :=
    mem_left_transversals_iff_exists_unique_inv_mul_mem.mp T.2 (g' * g.unop⁻¹),
    simp_rw [set_like.mem_coe, ←mul_assoc, mem_normalizer_iff'.mp (H.normalizer.inv_mem
      (show ↑g.unop ∈ H.normalizer, from g.unop.2)), ←mul_assoc, ←mul_inv_rev] at ht1 ht2,
    refine ⟨⟨t * g.unop, mem_right_coset g.unop t.2⟩, ht1, _⟩,
    rintros ⟨-, t', ht', rfl⟩ h,
    exact subtype.ext ((mul_left_inj ↑g.unop).mpr (subtype.ext_iff.mp (ht2 ⟨t', ht'⟩ h))) })⟩,
  one_smul := λ T, subtype.ext (right_coset_one T),
  mul_smul := λ g g' T, subtype.ext (right_coset_assoc ↑T ↑g'.unop ↑g.unop).symm }

-- for mathlib:
@[to_additive] instance : mul_action H.normalizerᵐᵒᵖ (G ⧸ H) :=
{ smul := λ g, quotient.map' (* g.unop) (λ a b h, by
  { have := (g.unop⁻¹.2 (a⁻¹ * b)).mp h,
    rwa [subtype.val_eq_coe, coe_inv, inv_inv, ←mul_assoc, ←mul_inv_rev, mul_assoc] at this }),
  one_smul := λ q, q.induction_on' (by exact λ g, congr_arg quotient.mk' (mul_one g)),
  mul_smul := λ a b q, q.induction_on'
    (by exact λ g, congr_arg quotient.mk' (mul_assoc g b.unop a.unop).symm) }

@[to_additive] lemma smul_apply_eq_apply_inv_smul_mul (g : H.normalizerᵐᵒᵖ) (q : G ⧸ H) :
  (mem_left_transversals.to_equiv (g • T).2 q : G) =
    mem_left_transversals.to_equiv T.2 (g⁻¹ • q) * g.unop :=
begin
  let w := (mem_left_transversals.to_equiv T.2).symm,
  let y := (mem_left_transversals.to_equiv (g • T).2).symm,
  change ↑(y.symm q) = ↑(⟨_, mem_right_coset (g.unop : G) (subtype.mem _)⟩ : (g • T).1),
  refine subtype.ext_iff.mp (y.symm_apply_eq.mpr _),
  change q = y ⟨w.symm _ * _, _⟩,
  have key : q = (g.unop : G) • w (w.symm ((↑g.unop)⁻¹ • q)),
  { rw [equiv.apply_symm_apply, ←mul_smul, mul_inv_self, one_smul] },
  refine key.trans _,
  let x : T.1 := w.symm ((↑g.unop)⁻¹ • q),
  change ↑g.unop • w x = y _,
  refine y.symm_apply_eq.mp _,
  have key : ∀ S : left_transversals (H : set G), ∀ a b : S.1, a = b ↔ (quotient.mk' (a : G) : G ⧸ H) = (quotient.mk' (b : G) : G ⧸ H) :=
  begin
    intros S a b,
    have key := mem_left_transversals_iff_bijective.mp S.2,
    exact key.injective.eq_iff.symm,
  end,
  change y.symm (↑g.unop • w x) = _,
  rw key,
  refine (mem_left_transversals.mk'_to_equiv _ _).trans _,
  symmetry,
  refine inv_smul_eq_iff.mp _,
  refine w.symm_apply_eq.mp _,
  rw key,
  refine (mem_left_transversals.mk'_to_equiv _ _).trans _,
  change (g.unop : G)⁻¹ • (g • quotient.mk' ↑(mem_left_transversals.to_equiv T.2 _)) = _,
  rw mem_left_transversals.mk'_to_equiv,
  rw smul_inv_smul,
  symmetry,
  refine mem_left_transversals.mk'_to_equiv _ _,
end

variables [fintype (G ⧸ H)]

/-- The difference of two left transversals -/
@[to_additive "The difference of two left transversals"]
noncomputable def diff : A :=
let α' := mem_left_transversals.to_equiv S.2, β' := mem_left_transversals.to_equiv T.2 in
∏ q, ϕ ⟨(α' q)⁻¹ * (β' q),
  quotient.exact' ((α'.symm_apply_apply q).trans (β'.symm_apply_apply q).symm)⟩

@[to_additive] lemma diff_mul_diff : diff ϕ R S * diff ϕ S T = diff ϕ R T :=
finset.prod_mul_distrib.symm.trans (finset.prod_congr rfl (λ q hq, (ϕ.map_mul _ _).symm.trans
  (congr_arg ϕ (subtype.ext (by simp_rw [coe_mul, coe_mk, mul_assoc, mul_inv_cancel_left])))))

@[to_additive] lemma diff_self : diff ϕ T T = 1 :=
mul_right_eq_self.mp (diff_mul_diff ϕ T T T)

@[to_additive] lemma diff_inv : (diff ϕ S T)⁻¹ = diff ϕ T S :=
inv_eq_of_mul_eq_one ((diff_mul_diff ϕ S T S).trans (diff_self ϕ S))

@[to_additive] lemma smul_diff_smul (g : G) : diff ϕ (g • S) (g • T) = diff ϕ S T :=
finset.prod_bij' (λ q _, g⁻¹ • q) (λ _ _, finset.mem_univ _) (λ _ _, congr_arg ϕ $ subtype.ext $ by
  simp_rw [coe_mk, smul_apply_eq_mul_apply_inv_smul, mul_inv_rev, mul_assoc, inv_mul_cancel_left])
  (λ q _, g • q) (λ _ _, finset.mem_univ _) (λ q _, smul_inv_smul g q) (λ q _, inv_smul_smul g q)

lemma smul_diff_smul' [is_commutative H] (g : H.normalizerᵐᵒᵖ) :
  diff (monoid_hom.id H) (g • S) (g • T) = ⟨(g.unop : G)⁻¹ * ((diff (monoid_hom.id H) S T : H) : G) * (g.unop : G),
    sorry⟩ :=
begin
  /-let ϕ : H →* H :=
  { to_fun := λ h, ⟨g * h * g⁻¹, hH.conj_mem h.1 h.2 g⟩,
    map_one' := subtype.ext (by rw [coe_mk, coe_one, mul_one, mul_inv_self]),
    map_mul' := λ h₁ h₂, subtype.ext (by rw [coe_mk, coe_mul, coe_mul, coe_mk, coe_mk, mul_assoc,
      mul_assoc, mul_assoc, mul_assoc, mul_assoc, inv_mul_cancel_left]) },-/
  let ϕ : H →* H :=
  { to_fun := λ h, ⟨g.unop⁻¹ * h * g.unop, sorry⟩,
    map_one' := sorry,
    map_mul' := sorry },
  refine eq.trans (finset.prod_bij' (λ q _, g⁻¹ • q) (λ _ _, finset.mem_univ _)
    (λ q _, subtype.ext _) (λ q _, g • q) (λ _ _, finset.mem_univ _)
    (λ q _, smul_inv_smul _ q) (λ q _, inv_smul_smul _ q)) (ϕ.map_prod _ _).symm,
  change _ * _ = (g.unop : G)⁻¹ * (_ * _) * (g.unop : G),
  simp_rw [smul_apply_eq_apply_inv_smul_mul, mul_inv_rev, mul_assoc],
end

end left_transversals

end subgroup

namespace monoid_hom

variables [fintype (G ⧸ H)]

open subgroup.left_transversals

/-- Given `ϕ : H →* A` from `H : subgroup G` to a commutative group `A`,
the transfer homomorphism is `transfer ϕ : H →* A`. -/
@[to_additive "Given `ϕ : H →+ A` from `H : add_subgroup G` to an additive commutative group `A`,
the transfer homomorphism is `transfer ϕ : H →+ A`."]
noncomputable def transfer (ϕ : H →* A) : G →* A :=
let T : left_transversals (H : set G) := left_transversals.inhabited.default in
{ to_fun := λ g, diff ϕ T (g • T),
  map_one' := by rw [one_smul, diff_self],
  map_mul' := λ g h, by rw [mul_smul, ←diff_mul_diff, smul_diff_smul] }

@[to_additive] lemma transfer_def (g : G) : transfer ϕ g = diff ϕ T (g • T) :=
by rw [transfer, ←diff_mul_diff, ←smul_diff_smul, mul_comm, diff_mul_diff]; refl

end monoid_hom
