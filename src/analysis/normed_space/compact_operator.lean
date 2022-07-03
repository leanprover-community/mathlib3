/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import analysis.normed_space.operator_norm
import analysis.locally_convex.bounded

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

open_locale pointwise big_operators topological_space

/-namespace continuous_linear_map

def is_compact_map {R₁ R₂ M₁ M₂ : Type*} [semiring R₁] [semiring R₂] {σ₁₂ : R₁ →+* R₂}
  [metric_space M₁] [add_comm_monoid M₁] [topological_space M₂] [add_comm_monoid M₂]
  [module R₁ M₁] [module R₂ M₂] (f : M₁ →SL[σ₁₂] M₂) : Prop :=
∃ K, is_compact K ∧ (closed_ball 0 1) ⊆ f ⁻¹' K

namespace is_compact_map

section semiring

variables {R₁ R₂ M₁ M₂ : Type*} [semiring R₁] [semiring R₂] {σ₁₂ : R₁ →+* R₂}
  [metric_space M₁] [add_comm_monoid M₁] [topological_space M₂] [add_comm_monoid M₂]
  [module R₁ M₁] [module R₂ M₂] {f g : M₁ →SL[σ₁₂] M₂}

protected lemma zero : (0 : M₁ →SL[σ₁₂] M₂).is_compact_map :=
⟨{0}, is_compact_singleton, λ _ _, rfl⟩

protected lemma add [has_continuous_add M₂] (hf : f.is_compact_map) (hg : g.is_compact_map) :
  (f + g).is_compact_map :=
let ⟨A, hA, hAf⟩ := hf, ⟨B, hB, hBg⟩ := hg in
⟨A + B, hA.add hB, λ x hx, set.add_mem_add (hAf hx) (hBg hx)⟩

protected lemma const_smul {S₂ : Type*} [monoid S₂]
  [distrib_mul_action S₂ M₂] [smul_comm_class R₂ S₂ M₂] [has_continuous_const_smul S₂ M₂]
  (hf : f.is_compact_map) (c : S₂) :
  (c • f).is_compact_map :=
let ⟨K, hK, hKf⟩ := hf in ⟨c • K, hK.image $ continuous_id.const_smul c,
  λ x hx, smul_mem_smul_set (hKf hx)⟩

#lint

end semiring

end is_compact_map

end continuous_linear_map-/

structure compact_operator {R₁ R₂} [semiring R₁] [semiring R₂] (σ₁₂ : R₁ →+* R₂) (M₁ M₂ : Type*)
  [topological_space M₁] [add_comm_monoid M₁] [topological_space M₂] [add_comm_monoid M₂]
  [module R₁ M₁] [module R₂ M₂] extends M₁ →ₛₗ[σ₁₂] M₂ :=
(exists_compact_preimage_mem_nhds' : ∃ K, is_compact K ∧ to_fun ⁻¹' K ∈ (𝓝 0 : filter M₁))

localized "notation M ` →SLᶜ[`:25 σ `] ` M₂ := compact_operator σ M M₂" in compact_operator
localized "notation M ` →Lᶜ[`:25 R `] ` M₂ := compact_operator (ring_hom.id R) M M₂"
  in compact_operator
localized "notation M ` →L⋆ᶜ[`:25 R `] ` M₂ := compact_operator (star_ring_end R) M M₂"
  in compact_operator

set_option old_structure_cmd true

class compact_operator_class (F : Type*) {R₁ R₂ : out_param Type*} [semiring R₁] [semiring R₂]
  (σ₁₂ : out_param $ R₁ →+* R₂) (M₁ : out_param Type*) [topological_space M₁] [add_comm_monoid M₁]
  (M₂ : out_param Type*) [topological_space M₂] [add_comm_monoid M₂] [module R₁ M₁] [module R₂ M₂]
  extends semilinear_map_class F σ₁₂ M₁ M₂ :=
(exists_compact_preimage_mem_nhds : ∀ f : F, ∃ K, is_compact K ∧ f ⁻¹' K ∈ (𝓝 0 : filter M₁))

export compact_operator_class (exists_compact_preimage_mem_nhds)

set_option old_structure_cmd false

namespace compact_operator

section boilerplate

variables {R₁ R₂ : Type*} [semiring R₁] [semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ M₂ : Type*}
  [topological_space M₁] [add_comm_monoid M₁] [topological_space M₂] [add_comm_monoid M₂]
  [module R₁ M₁] [module R₂ M₂]

/-- Coerce compact operators to linear maps. -/
instance : has_coe (M₁ →SLᶜ[σ₁₂] M₂) (M₁ →ₛₗ[σ₁₂] M₂) := ⟨to_linear_map⟩

-- make the coercion the preferred form
@[simp] lemma to_linear_map_eq_coe (f : M₁ →SLᶜ[σ₁₂] M₂) :
  f.to_linear_map = f := rfl

theorem coe_injective :
  function.injective (coe : (M₁ →SLᶜ[σ₁₂] M₂) → (M₁ →ₛₗ[σ₁₂] M₂)) :=
by { intros f g H, cases f, cases g, congr' }

instance : compact_operator_class (M₁ →SLᶜ[σ₁₂] M₂) σ₁₂ M₁ M₂ :=
{ coe := λ f, f,
  coe_injective' := λ f g h, coe_injective (fun_like.coe_injective h),
  map_add := λ f, map_add f.to_linear_map,
  map_smulₛₗ := λ f, f.to_linear_map.map_smul',
  exists_compact_preimage_mem_nhds := λ f, f.exists_compact_preimage_mem_nhds' }

/-- Coerce continuous linear maps to functions. -/
-- see Note [function coercion]
instance to_fun : has_coe_to_fun (M₁ →SLᶜ[σ₁₂] M₂) (λ _, M₁ → M₂) := ⟨λ f, f.to_fun⟩

@[simp] lemma coe_mk (f : M₁ →ₛₗ[σ₁₂] M₂) (h) : (mk f h : M₁ →ₛₗ[σ₁₂] M₂) = f := rfl
@[simp] lemma coe_mk' (f : M₁ →ₛₗ[σ₁₂] M₂) (h) : (mk f h : M₁ → M₂) = f := rfl

@[simp, norm_cast] lemma coe_inj {f g : M₁ →SLᶜ[σ₁₂] M₂} :
  (f : M₁ →ₛₗ[σ₁₂] M₂) = g ↔ f = g :=
coe_injective.eq_iff

theorem coe_fn_injective : @function.injective (M₁ →SLᶜ[σ₁₂] M₂) (M₁ → M₂) coe_fn :=
fun_like.coe_injective

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def simps.apply (h : M₁ →SLᶜ[σ₁₂] M₂) : M₁ → M₂ := h

/-- See Note [custom simps projection]. -/
def simps.coe (h : M₁ →SLᶜ[σ₁₂] M₂) : M₁ →ₛₗ[σ₁₂] M₂ := h

initialize_simps_projections compact_operator
  (to_linear_map_to_fun → apply, to_linear_map → coe)

@[ext] theorem ext {f g : M₁ →SLᶜ[σ₁₂] M₂} (h : ∀ x, f x = g x) : f = g :=
fun_like.ext f g h

theorem ext_iff {f g : M₁ →SLᶜ[σ₁₂] M₂} : f = g ↔ ∀ x, f x = g x :=
fun_like.ext_iff

/-- Copy of a `compact_operator` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : M₁ →SLᶜ[σ₁₂] M₂) (f' : M₁ → M₂) (h : f' = ⇑f) :
  M₁ →SLᶜ[σ₁₂] M₂ :=
{ to_linear_map := f.to_linear_map.copy f' h,
  exists_compact_preimage_mem_nhds' := show ∃ K, is_compact K ∧ f' ⁻¹' K ∈ (𝓝 0 : filter M₁),
    from h.symm ▸ f.exists_compact_preimage_mem_nhds' }

@[simp, norm_cast] lemma coe_coe (f : M₁ →SLᶜ[σ₁₂] M₂) : ⇑(f : M₁ →ₛₗ[σ₁₂] M₂) = f := rfl

end boilerplate

section to_continuous

variables {𝕜₁ 𝕜₂ : Type*} [nondiscrete_normed_field 𝕜₁] [nondiscrete_normed_field 𝕜₂]
  {σ₁₂ : 𝕜₁ →+* 𝕜₂} [ring_hom_isometric σ₁₂] {M₁ M₂ : Type*} [topological_space M₁]
  [add_comm_group M₁] [topological_space M₂] [add_comm_group M₂] [module 𝕜₁ M₁] [module 𝕜₂ M₂]
  [topological_add_group M₁] [has_continuous_const_smul 𝕜₁ M₁]
  [topological_add_group M₂] [has_continuous_smul 𝕜₂ M₂]

instance {F : Type*} [h : compact_operator_class F σ₁₂ M₁ M₂] :
  continuous_semilinear_map_class F σ₁₂ M₁ M₂ :=
{ map_continuous :=
  begin
    letI : uniform_space M₂ := topological_add_group.to_uniform_space _,
    haveI : uniform_add_group M₂ := topological_add_group_is_uniform,
    refine λ f, continuous_of_continuous_at_zero f (λ U hU, _),
    rw map_zero at hU,
    rcases exists_compact_preimage_mem_nhds f with ⟨K, hK, hKf⟩,
    rcases hK.totally_bounded.is_vonN_bounded 𝕜₂ hU with ⟨r, hr, hrU⟩,
    rcases normed_field.exists_lt_norm 𝕜₁ r with ⟨c, hc⟩,
    have hcnz : c ≠ 0 := ne_zero_of_norm_ne_zero (hr.trans hc).ne.symm,
    suffices : (σ₁₂ $ c⁻¹) • K ⊆ U,
    { refine mem_of_superset _ this,
      have : is_unit c⁻¹ := hcnz.is_unit.inv,
      rwa [mem_map, preimage_smul_setₛₗ f this, set_smul_mem_nhds_zero_iff (inv_ne_zero hcnz)],
      apply_instance },
    rw [σ₁₂.map_inv, ← subset_set_smul_iff₀ (σ₁₂.map_ne_zero.mpr hcnz)],
    refine hrU (σ₁₂ c) _,
    rw ring_hom_isometric.is_iso,
    exact hc.le
  end,
  ..h }

/-- Coerce compact operators to continuous linear maps. -/
instance : has_coe (M₁ →SLᶜ[σ₁₂] M₂) (M₁ →SL[σ₁₂] M₂) := ⟨λ f, ⟨f, map_continuous f⟩⟩

theorem coe_clm_injective :
  function.injective (coe : (M₁ →SLᶜ[σ₁₂] M₂) → (M₁ →SL[σ₁₂] M₂)) :=
by { intros f g, rw [continuous_linear_map.ext_iff, ext_iff], exact id }

@[simp] lemma coe_clm_mk (f : M₁ →SL[σ₁₂] M₂) (h) :
  (mk (f : M₁ →ₛₗ[σ₁₂] M₂) h : M₁ →SL[σ₁₂] M₂) = f :=
by ext; refl

@[simp, norm_cast] lemma coe_clm_inj {f g : M₁ →SLᶜ[σ₁₂] M₂} :
  (f : M₁ →SL[σ₁₂] M₂) = g ↔ f = g :=
coe_clm_injective.eq_iff

end to_continuous

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
