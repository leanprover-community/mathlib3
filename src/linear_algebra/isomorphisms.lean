/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov
-/
import linear_algebra.quotient

/-!
# Isomorphism theorems for modules.

* The Noether's first, second, and third isomorphism theorems for modules are proved as
  `linear_map.quot_ker_equiv_range`, `linear_map.quotient_inf_equiv_sup_quotient` and
  `submodule.quotient_quotient_equiv_quotient`.

-/

universes u v

variables {R M M₂ M₃ : Type*}
variables [ring R] [add_comm_group M] [add_comm_group M₂] [add_comm_group M₃]
variables [module R M] [module R M₂] [module R M₃]
variables (f : M →ₗ[R] M₂)

/-! The first and second isomorphism theorems for modules. -/
namespace linear_map

open submodule

section isomorphism_laws

/-- The first isomorphism law for modules. The quotient of `M` by the kernel of `f` is linearly
equivalent to the range of `f`. -/
noncomputable def quot_ker_equiv_range : f.ker.quotient ≃ₗ[R] f.range :=
(linear_equiv.of_injective (f.ker.liftq f $ le_refl _) $
  ker_eq_bot.mp $ submodule.ker_liftq_eq_bot _ _ _ (le_refl f.ker)).trans
  (linear_equiv.of_eq _ _ $ submodule.range_liftq _ _ _)

/-- The first isomorphism theorem for surjective linear maps. -/
noncomputable def quot_ker_equiv_of_surjective
  (f : M →ₗ[R] M₂) (hf : function.surjective f) : f.ker.quotient ≃ₗ[R] M₂ :=
f.quot_ker_equiv_range.trans
  (linear_equiv.of_top f.range (linear_map.range_eq_top.2 hf))

@[simp] lemma quot_ker_equiv_range_apply_mk (x : M) :
  (f.quot_ker_equiv_range (submodule.quotient.mk x) : M₂) = f x :=
rfl

@[simp] lemma quot_ker_equiv_range_symm_apply_image (x : M) (h : f x ∈ f.range) :
  f.quot_ker_equiv_range.symm ⟨f x, h⟩ = f.ker.mkq x :=
f.quot_ker_equiv_range.symm_apply_apply (f.ker.mkq x)

/--
Canonical linear map from the quotient `p/(p ∩ p')` to `(p+p')/p'`, mapping `x + (p ∩ p')`
to `x + p'`, where `p` and `p'` are submodules of an ambient module.
-/
def quotient_inf_to_sup_quotient (p p' : submodule R M) :
  (comap p.subtype (p ⊓ p')).quotient →ₗ[R] (comap (p ⊔ p').subtype p').quotient :=
(comap p.subtype (p ⊓ p')).liftq
  ((comap (p ⊔ p').subtype p').mkq.comp (of_le le_sup_left)) begin
rw [ker_comp, of_le, comap_cod_restrict, ker_mkq, map_comap_subtype],
exact comap_mono (inf_le_inf_right _ le_sup_left) end

/--
Second Isomorphism Law : the canonical map from `p/(p ∩ p')` to `(p+p')/p'` as a linear isomorphism.
-/
noncomputable def quotient_inf_equiv_sup_quotient (p p' : submodule R M) :
  (comap p.subtype (p ⊓ p')).quotient ≃ₗ[R] (comap (p ⊔ p').subtype p').quotient :=
linear_equiv.of_bijective (quotient_inf_to_sup_quotient p p')
  begin
    rw [← ker_eq_bot, quotient_inf_to_sup_quotient, ker_liftq_eq_bot],
    rw [ker_comp, ker_mkq],
    exact λ ⟨x, hx1⟩ hx2, ⟨hx1, hx2⟩
  end
  begin
    rw [← range_eq_top, quotient_inf_to_sup_quotient, range_liftq, eq_top_iff'],
    rintros ⟨x, hx⟩, rcases mem_sup.1 hx with ⟨y, hy, z, hz, rfl⟩,
    use [⟨y, hy⟩], apply (submodule.quotient.eq _).2,
    change y - (y + z) ∈ p',
    rwa [sub_add_eq_sub_sub, sub_self, zero_sub, neg_mem_iff]
  end

@[simp] lemma coe_quotient_inf_to_sup_quotient (p p' : submodule R M) :
  ⇑(quotient_inf_to_sup_quotient p p') = quotient_inf_equiv_sup_quotient p p' := rfl

@[simp] lemma quotient_inf_equiv_sup_quotient_apply_mk (p p' : submodule R M) (x : p) :
  quotient_inf_equiv_sup_quotient p p' (submodule.quotient.mk x) =
    submodule.quotient.mk (of_le (le_sup_left : p ≤ p ⊔ p') x) :=
rfl

lemma quotient_inf_equiv_sup_quotient_symm_apply_left (p p' : submodule R M)
  (x : p ⊔ p') (hx : (x:M) ∈ p) :
  (quotient_inf_equiv_sup_quotient p p').symm (submodule.quotient.mk x) =
    submodule.quotient.mk ⟨x, hx⟩ :=
(linear_equiv.symm_apply_eq _).2 $ by simp [of_le_apply]

@[simp] lemma quotient_inf_equiv_sup_quotient_symm_apply_eq_zero_iff {p p' : submodule R M}
  {x : p ⊔ p'} :
  (quotient_inf_equiv_sup_quotient p p').symm (submodule.quotient.mk x) = 0 ↔ (x:M) ∈ p' :=
(linear_equiv.symm_apply_eq _).trans $ by simp [of_le_apply]

lemma quotient_inf_equiv_sup_quotient_symm_apply_right (p p' : submodule R M) {x : p ⊔ p'}
  (hx : (x:M) ∈ p') :
  (quotient_inf_equiv_sup_quotient p p').symm (submodule.quotient.mk x) = 0 :=
quotient_inf_equiv_sup_quotient_symm_apply_eq_zero_iff.2 hx

end isomorphism_laws

end linear_map

/-! The third isomorphism theorem for modules. -/
namespace submodule

variables (S T : submodule R M) (h : S ≤ T)

/-- The map from the third isomorphism theorem for modules: `(M / S) / (T / S) → M / T`. -/
def quotient_quotient_equiv_quotient_aux :
  quotient (T.map S.mkq) →ₗ[R] quotient T :=
liftq _ (mapq S T linear_map.id h)
  (by { rintro _ ⟨x, hx, rfl⟩, rw [linear_map.mem_ker, mkq_apply, mapq_apply],
        exact (quotient.mk_eq_zero _).mpr hx })

@[simp] lemma quotient_quotient_equiv_quotient_aux_mk (x : S.quotient) :
  quotient_quotient_equiv_quotient_aux S T h (quotient.mk x) = mapq S T linear_map.id h x :=
liftq_apply _ _ _

@[simp] lemma quotient_quotient_equiv_quotient_aux_mk_mk (x : M) :
  quotient_quotient_equiv_quotient_aux S T h (quotient.mk (quotient.mk x)) = quotient.mk x :=
by rw [quotient_quotient_equiv_quotient_aux_mk, mapq_apply, linear_map.id_apply]

/-- **Noether's third isomorphism theorem** for modules: `(M / S) / (T / S) ≃ M / T`. -/
def quotient_quotient_equiv_quotient :
  quotient (T.map S.mkq) ≃ₗ[R] quotient T :=
{ to_fun := quotient_quotient_equiv_quotient_aux S T h,
  inv_fun := mapq _ _ (mkq S) (le_comap_map _ _),
  left_inv := λ x, quotient.induction_on' x $ λ x, quotient.induction_on' x $ λ x, by simp,
  right_inv := λ x, quotient.induction_on' x $ λ x, by simp,
  .. quotient_quotient_equiv_quotient_aux S T h }

end submodule
