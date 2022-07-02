/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import analysis.normed_space.operator_norm

/-!
# Compact operators

## Main definitions

* `foo_bar`

## Main statements

* `foo_bar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open function set filter bornology metric

structure compact_operator {R S} [semiring R] [semiring S] (σ₁₂ : R →+* S) (M₁ M₂ : Type*)
  [metric_space M₁] [add_comm_monoid M₁] [topological_space M₂] [add_comm_monoid M₂]
  [module R M₁] [module S M₂] extends M₁ →SL[σ₁₂] M₂ :=
(image_in_compact' : ∃ K, is_compact K ∧ to_fun '' (closed_ball 0 1) ⊆ K)

set_option old_structure_cmd true

class compact_operator_class (F : Type*) {R S : out_param Type*} [semiring R] [semiring S]
  (σ₁₂ : out_param $ R →+* S) (M₁ : out_param Type*) [metric_space M₁] [add_comm_monoid M₁]
  (M₂ : out_param Type*) [topological_space M₂] [add_comm_monoid M₂] [module R M₁] [module S M₂]
  extends continuous_semilinear_map_class F σ₁₂ M₁ M₂ :=
(image_in_compact : ∀ f : F, ∃ K, is_compact K ∧ f '' (closed_ball 0 1) ⊆ K)

set_option old_structure_cmd false

namespace compact_operator

section boilerplate

variables {R S : Type*} [semiring R] [semiring S] {σ₁₂ : R →+* S} {M₁ M₂ : Type*}
  [metric_space M₁] [add_comm_monoid M₁] [topological_space M₂] [add_comm_monoid M₂]
  [module R M₁] [module S M₂]

/-- Coerce compact operators to continuous linear maps. -/
instance : has_coe (compact_operator σ₁₂ M₁ M₂) (M₁ →SL[σ₁₂] M₂) := ⟨to_continuous_linear_map⟩

-- make the coercion the preferred form
@[simp] lemma to_continuous_linear_map_eq_coe (f : compact_operator σ₁₂ M₁ M₂) :
  f.to_continuous_linear_map = f := rfl

theorem coe_injective :
  function.injective (coe : (compact_operator σ₁₂ M₁ M₂) → (M₁ →SL[σ₁₂] M₂)) :=
by { intros f g H, cases f, cases g, congr' }

instance : compact_operator_class (compact_operator σ₁₂ M₁ M₂) σ₁₂ M₁ M₂ :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, coe_injective (fun_like.coe_injective h),
  map_add := λ f, map_add f.to_linear_map,
  map_continuous := λ f, f.1.2,
  map_smulₛₗ := λ f, f.to_linear_map.map_smul',
  image_in_compact := λ f, f.image_in_compact' }

/-- Coerce continuous linear maps to functions. -/
-- see Note [function coercion]
instance to_fun : has_coe_to_fun (compact_operator σ₁₂ M₁ M₂) (λ _, M₁ → M₂) := ⟨λ f, f.to_fun⟩

@[simp] lemma coe_mk (f : M₁ →SL[σ₁₂] M₂) (h) : (mk f h : M₁ →SL[σ₁₂] M₂) = f := rfl
@[simp] lemma coe_mk' (f : M₁ →SL[σ₁₂] M₂) (h) : (mk f h : M₁ → M₂) = f := rfl

@[continuity]
protected lemma continuous (f : compact_operator σ₁₂ M₁ M₂) : continuous f := f.1.2

@[simp, norm_cast] lemma coe_inj {f g : compact_operator σ₁₂ M₁ M₂} :
  (f : M₁ →SL[σ₁₂] M₂) = g ↔ f = g :=
coe_injective.eq_iff

theorem coe_fn_injective : @function.injective (compact_operator σ₁₂ M₁ M₂) (M₁ → M₂) coe_fn :=
fun_like.coe_injective

end boilerplate

end compact_operator
