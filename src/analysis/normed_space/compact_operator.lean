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

open_locale pointwise big_operators

structure compact_operator {R₁ R₂} [semiring R₁] [semiring R₂] (σ₁₂ : R₁ →+* R₂) (M₁ M₂ : Type*)
  [metric_space M₁] [add_comm_monoid M₁] [topological_space M₂] [add_comm_monoid M₂]
  [module R₁ M₁] [module R₂ M₂] extends M₁ →SL[σ₁₂] M₂ :=
(ball_subset_preimage_compact' : ∃ K, is_compact K ∧ (closed_ball 0 1) ⊆ to_fun ⁻¹' K)

set_option old_structure_cmd true

class compact_operator_class (F : Type*) {R₁ R₂ : out_param Type*} [semiring R₁] [semiring R₂]
  (σ₁₂ : out_param $ R₁ →+* R₂) (M₁ : out_param Type*) [metric_space M₁] [add_comm_monoid M₁]
  (M₂ : out_param Type*) [topological_space M₂] [add_comm_monoid M₂] [module R₁ M₁] [module R₂ M₂]
  extends continuous_semilinear_map_class F σ₁₂ M₁ M₂ :=
(ball_subset_preimage_compact : ∀ f : F, ∃ K, is_compact K ∧ (closed_ball 0 1) ⊆ f ⁻¹' K)

export compact_operator_class (ball_subset_preimage_compact)

set_option old_structure_cmd false

namespace compact_operator

section boilerplate

variables {R₁ R₂ : Type*} [semiring R₁] [semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ M₂ : Type*}
  [metric_space M₁] [add_comm_monoid M₁] [topological_space M₂] [add_comm_monoid M₂]
  [module R₁ M₁] [module R₂ M₂]

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
  ball_subset_preimage_compact := λ f, f.ball_subset_preimage_compact' }

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

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def simps.apply (h : compact_operator σ₁₂ M₁ M₂) : M₁ → M₂ := h

/-- See Note [custom simps projection]. -/
def simps.coe (h : compact_operator σ₁₂ M₁ M₂) : M₁ →SL[σ₁₂] M₂ := h

initialize_simps_projections compact_operator
  (to_continuous_linear_map_to_linear_map_to_fun → apply, to_continuous_linear_map → coe)

@[ext] theorem ext {f g : compact_operator σ₁₂ M₁ M₂} (h : ∀ x, f x = g x) : f = g :=
fun_like.ext f g h

theorem ext_iff {f g : compact_operator σ₁₂ M₁ M₂} : f = g ↔ ∀ x, f x = g x :=
fun_like.ext_iff

/-- Copy of a `compact_operator` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : compact_operator σ₁₂ M₁ M₂) (f' : M₁ → M₂) (h : f' = ⇑f) :
  compact_operator σ₁₂ M₁ M₂ :=
{ to_continuous_linear_map := f.to_continuous_linear_map.copy f' h,
  ball_subset_preimage_compact' := show ∃ K, is_compact K ∧ closed_ball 0 1 ⊆ f' ⁻¹' K,
    from h.symm ▸ f.ball_subset_preimage_compact' }

@[simp, norm_cast] lemma coe_coe (f :compact_operator σ₁₂ M₁ M₂) : ⇑(f : M₁ →SL[σ₁₂] M₂) = f := rfl

end boilerplate

section semiring

variables {R₁ R₂ : Type*} [semiring R₁] [semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ M₂ : Type*}
  [metric_space M₁] [add_comm_monoid M₁] [topological_space M₂] [add_comm_monoid M₂]
  [module R₁ M₁] [module R₂ M₂]

section smul_monoid

variables {S₂ T₂ : Type*} [monoid S₂] [monoid T₂]
variables [distrib_mul_action S₂ M₂] [smul_comm_class R₂ S₂ M₂] [has_continuous_const_smul S₂ M₂]
variables [distrib_mul_action T₂ M₂] [smul_comm_class R₂ T₂ M₂] [has_continuous_const_smul T₂ M₂]

instance : mul_action S₂ (compact_operator σ₁₂ M₁ M₂) :=
{ smul := λ c f, ⟨c • f, let ⟨K, hK, hKf⟩ := ball_subset_preimage_compact f in
    ⟨c • K, hK.image $ continuous_id.const_smul c, λ x hx, smul_mem_smul_set (hKf hx)⟩⟩,
  one_smul := λ f, ext $ λ x, one_smul _ _,
  mul_smul := λ a b f, ext $ λ x, mul_smul _ _ _ }

lemma smul_apply (c : S₂) (f : compact_operator σ₁₂ M₁ M₂) (x : M₁) : (c • f) x = c • (f x) := rfl
@[simp, norm_cast]
lemma coe_smul (c : S₂) (f : compact_operator σ₁₂ M₁ M₂) :
  (↑(c • f) : M₁ →SL[σ₁₂] M₂) = c • f := rfl
@[simp, norm_cast] lemma coe_smul' (c : S₂) (f : compact_operator σ₁₂ M₁ M₂) :
  ⇑(c • f) = c • f := rfl

instance [has_smul S₂ T₂] [is_scalar_tower S₂ T₂ M₂] :
  is_scalar_tower S₂ T₂ (compact_operator σ₁₂ M₁ M₂) :=
⟨λ a b f, ext $ λ x, smul_assoc a b (f x)⟩

instance [smul_comm_class S₂ T₂ M₂] : smul_comm_class S₂ T₂ (compact_operator σ₁₂ M₁ M₂) :=
⟨λ a b f, ext $ λ x, smul_comm a b (f x)⟩

end smul_monoid

/-- The zero function is compact. -/
instance : has_zero (compact_operator σ₁₂ M₁ M₂) :=
  ⟨⟨0, ⟨{0}, is_compact_singleton, λ _ _, rfl⟩⟩⟩
instance : inhabited (compact_operator σ₁₂ M₁ M₂) := ⟨0⟩

@[simp] lemma default_def : (default : compact_operator σ₁₂ M₁ M₂) = 0 := rfl
@[simp] lemma zero_apply (x : M₁) : (0 : compact_operator σ₁₂ M₁ M₂) x = 0 := rfl
@[simp, norm_cast] lemma coe_zero : ((0 : compact_operator σ₁₂ M₁ M₂) : M₁ →SL[σ₁₂] M₂) = 0 := rfl
/- no simp attribute on the next line as simp does not always simplify `0 x` to `0`
when `0` is the zero function, while it does for the zero compact operator,
and this is the most important property we care about. -/
@[norm_cast] lemma coe_zero' : ⇑(0 : compact_operator σ₁₂ M₁ M₂) = 0 := rfl

section add
variables [has_continuous_add M₂]

instance : has_add (compact_operator σ₁₂ M₁ M₂) :=
⟨λ f g, ⟨f + g,
  let ⟨A, hA, hAf⟩ := ball_subset_preimage_compact f,
      ⟨B, hB, hBg⟩ := ball_subset_preimage_compact g in
  ⟨A + B, hA.add hB, λ x hx, set.add_mem_add (hAf hx) (hBg hx)⟩⟩⟩

@[simp] lemma add_apply (f g : compact_operator σ₁₂ M₁ M₂)  (x : M₁) : (f + g) x = f x + g x := rfl
@[simp, norm_cast] lemma coe_add (f g : compact_operator σ₁₂ M₁ M₂) : (↑(f + g) : M₁ →ₛₗ[σ₁₂] M₂) = f + g := rfl
@[norm_cast] lemma coe_add' (f g : compact_operator σ₁₂ M₁ M₂) : ⇑(f + g) = f + g := rfl

instance : add_comm_monoid (compact_operator σ₁₂ M₁ M₂) :=
{ zero := (0 : compact_operator σ₁₂ M₁ M₂),
  add := (+),
  zero_add := by intros; ext; apply_rules [zero_add, add_assoc, add_zero, add_left_neg, add_comm],
  add_zero := by intros; ext; apply_rules [zero_add, add_assoc, add_zero, add_left_neg, add_comm],
  add_comm := by intros; ext; apply_rules [zero_add, add_assoc, add_zero, add_left_neg, add_comm],
  add_assoc := by intros; ext; apply_rules [zero_add, add_assoc, add_zero, add_left_neg, add_comm],
  nsmul := (•),
  nsmul_zero' := λ f, by { ext, simp },
  nsmul_succ' := λ n f, by { ext, simp [nat.succ_eq_one_add, add_smul] } }

@[simp, norm_cast] lemma coe_sum {ι : Type*} (t : finset ι) (f : ι → compact_operator σ₁₂ M₁ M₂) :
  ↑(∑ d in t, f d) = (∑ d in t, f d : M₁ →SL[σ₁₂] M₂) :=
(add_monoid_hom.mk (coe : (compact_operator σ₁₂ M₁ M₂) → (M₁ →SL[σ₁₂] M₂))
  rfl (λ _ _, rfl)).map_sum _ _

@[simp, norm_cast] lemma coe_sum' {ι : Type*} (t : finset ι) (f : ι → compact_operator σ₁₂ M₁ M₂) :
  ⇑(∑ d in t, f d) = ∑ d in t, f d :=
by simp only [← coe_coe, coe_sum, continuous_linear_map.coe_sum']

lemma sum_apply {ι : Type*} (t : finset ι) (f : ι → compact_operator σ₁₂ M₁ M₂) (b : M₁) :
  (∑ d in t, f d) b = ∑ d in t, f d b :=
by simp only [coe_sum', finset.sum_apply]

end add

end semiring

end compact_operator
