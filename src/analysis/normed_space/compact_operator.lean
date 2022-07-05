/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import analysis.normed_space.operator_norm
import analysis.locally_convex.with_seminorms

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

section characterizations

section

variables {R₁ R₂ : Type*} [semiring R₁] [semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ M₂ : Type*}
  [topological_space M₁] [add_comm_monoid M₁] [topological_space M₂] [add_comm_monoid M₂]
  [module R₁ M₁] [module R₂ M₂]

lemma exists_mem_nhds_image_in_compact (f : M₁ →SLᶜ[σ₁₂] M₂) :
  ∃ V ∈ (𝓝 0 : filter M₁), ∃ (K : set M₂), is_compact K ∧ f '' V ⊆ K :=
let ⟨K, hK, hKf⟩ := exists_compact_preimage_mem_nhds f in
⟨f ⁻¹' K, hKf, K, hK, image_preimage_subset _ _⟩

lemma exists_mem_nhds_image_relatively_compact [t2_space M₂] (f : M₁ →SLᶜ[σ₁₂] M₂) :
  ∃ V ∈ (𝓝 0 : filter M₁), is_compact (closure $ f '' V) :=
let ⟨V, hV, K, hK, hKV⟩ := f.exists_mem_nhds_image_in_compact in
⟨V, hV, compact_closure_of_subset_compact hK hKV⟩

def mk_of_image_in_compact (f : M₁ →ₛₗ[σ₁₂] M₂) {V} (hV : V ∈ (𝓝 0 : filter M₁)) {K}
  (hK : is_compact K) (hVK : f '' V ⊆ K) : M₁ →SLᶜ[σ₁₂] M₂ :=
⟨f, ⟨K, hK, mem_of_superset hV (image_subset_iff.mp hVK)⟩⟩

def mk_of_image_relatively_compact (f : M₁ →ₛₗ[σ₁₂] M₂) {V} (hV : V ∈ (𝓝 0 : filter M₁))
  (hVc : is_compact (closure $ f '' V)) : M₁ →SLᶜ[σ₁₂] M₂ :=
mk_of_image_in_compact f hV hVc subset_closure

end

section bounded

variables {𝕜₁ 𝕜₂ : Type*} [nondiscrete_normed_field 𝕜₁] [semi_normed_ring 𝕜₂] {σ₁₂ : 𝕜₁ →+* 𝕜₂}
  {M₁ M₂ : Type*} [topological_space M₁] [add_comm_monoid M₁] [topological_space M₂]
  [add_comm_monoid M₂] [module 𝕜₁ M₁] [module 𝕜₂ M₂] [has_continuous_const_smul 𝕜₂ M₂]

lemma image_in_compact_of_vonN_bounded (f : M₁ →SLᶜ[σ₁₂] M₂) {S : set M₁}
  (hS : is_vonN_bounded 𝕜₁ S) :
  ∃ (K : set M₂), is_compact K ∧ f '' S ⊆ K :=
let ⟨K, hK, hKf⟩ := exists_compact_preimage_mem_nhds f,
    ⟨r, hr, hrS⟩ := hS hKf,
    ⟨c, hc⟩ := normed_field.exists_lt_norm 𝕜₁ r,
    this := ne_zero_of_norm_ne_zero (hr.trans hc).ne.symm in
⟨σ₁₂ c • K, hK.image $ continuous_id.const_smul (σ₁₂ c),
  by rw [image_subset_iff, preimage_smul_setₛₗ f this.is_unit]; exact hrS c hc.le⟩

lemma image_relatively_compact_of_vonN_bounded [t2_space M₂] (f : M₁ →SLᶜ[σ₁₂] M₂) {S : set M₁}
  (hS : is_vonN_bounded 𝕜₁ S) : is_compact (closure $ f '' S) :=
let ⟨K, hK, hKf⟩ := f.image_in_compact_of_vonN_bounded hS in
compact_closure_of_subset_compact hK hKf

end bounded

section normed_space

variables {𝕜₁ 𝕜₂ : Type*} [nondiscrete_normed_field 𝕜₁] [semi_normed_ring 𝕜₂] {σ₁₂ : 𝕜₁ →+* 𝕜₂}
  {M₁ M₂ : Type*} [semi_normed_group M₁] [topological_space M₂]
  [add_comm_monoid M₂] [normed_space 𝕜₁ M₁] [module 𝕜₂ M₂]

lemma image_ball_in_compact [has_continuous_const_smul 𝕜₂ M₂] (f : M₁ →SLᶜ[σ₁₂] M₂) (r : ℝ) :
  ∃ (K : set M₂), is_compact K ∧ f '' metric.ball 0 r ⊆ K :=
image_in_compact_of_vonN_bounded f (normed_space.is_vonN_bounded_ball 𝕜₁ M₁ r)

lemma image_closed_ball_in_compact [has_continuous_const_smul 𝕜₂ M₂] (f : M₁ →SLᶜ[σ₁₂] M₂)
  (r : ℝ) : ∃ (K : set M₂), is_compact K ∧ f '' metric.closed_ball 0 r ⊆ K :=
image_in_compact_of_vonN_bounded f (normed_space.is_vonN_bounded_closed_ball 𝕜₁ M₁ r)

lemma image_ball_relatively_compact [has_continuous_const_smul 𝕜₂ M₂] [t2_space M₂]
  (f : M₁ →SLᶜ[σ₁₂] M₂) (r : ℝ) : is_compact (closure $ f '' metric.ball 0 r) :=
image_relatively_compact_of_vonN_bounded f (normed_space.is_vonN_bounded_ball 𝕜₁ M₁ r)

lemma image_closed_ball_relatively_compact [has_continuous_const_smul 𝕜₂ M₂] [t2_space M₂]
  (f : M₁ →SLᶜ[σ₁₂] M₂) (r : ℝ) : is_compact (closure $ f '' metric.closed_ball 0 r) :=
image_relatively_compact_of_vonN_bounded f (normed_space.is_vonN_bounded_closed_ball 𝕜₁ M₁ r)

def mk_of_image_ball_in_compact (f : M₁ →ₛₗ[σ₁₂] M₂) {r : ℝ} (hr : 0 < r)
  {K : set M₂} (hK : is_compact K) (hrK : f '' metric.ball 0 r ⊆ K) :
  M₁ →SLᶜ[σ₁₂] M₂ :=
mk_of_image_in_compact f (ball_mem_nhds (0 : M₁) hr) hK hrK

def mk_of_image_closed_ball_in_compact (f : M₁ →ₛₗ[σ₁₂] M₂) {r : ℝ} (hr : 0 < r)
  {K : set M₂} (hK : is_compact K) (hrK : f '' metric.closed_ball 0 r ⊆ K) :
  M₁ →SLᶜ[σ₁₂] M₂ :=
mk_of_image_in_compact f (closed_ball_mem_nhds (0 : M₁) hr) hK hrK

def mk_of_image_ball_relatively_compact (f : M₁ →ₛₗ[σ₁₂] M₂) {r : ℝ} (hr : 0 < r)
  (hrf : is_compact $ closure $ f '' metric.ball 0 r) :
  M₁ →SLᶜ[σ₁₂] M₂ :=
mk_of_image_relatively_compact f (ball_mem_nhds (0 : M₁) hr) hrf

def mk_of_image_closed_ball_relatively_compact (f : M₁ →ₛₗ[σ₁₂] M₂) {r : ℝ} (hr : 0 < r)
  (hrf : is_compact $ closure $ f '' metric.closed_ball 0 r) :
  M₁ →SLᶜ[σ₁₂] M₂ :=
mk_of_image_relatively_compact f (closed_ball_mem_nhds (0 : M₁) hr) hrf

end normed_space

end characterizations

section operations

variables {R₁ R₂ R₃ R₄ : Type*} [semiring R₁] [semiring R₂] [comm_semiring R₃] [comm_semiring R₄]
  {σ₁₂ : R₁ →+* R₂} {σ₃₄ : R₃ →+* R₄} {M₁ M₂ M₃ M₄ : Type*} [topological_space M₁]
  [add_comm_monoid M₁] [topological_space M₂] [add_comm_monoid M₂] [topological_space M₃]
  [add_comm_group M₃] [topological_space M₄] [add_comm_group M₄] [module R₁ M₁] [module R₂ M₂]
  [module R₃ M₃] [module R₄ M₄]

section smul_monoid

variables {S₂ T₂ : Type*} [monoid S₂] [monoid T₂]
variables [distrib_mul_action S₂ M₂] [smul_comm_class R₂ S₂ M₂] [has_continuous_const_smul S₂ M₂]
variables [distrib_mul_action T₂ M₂] [smul_comm_class R₂ T₂ M₂] [has_continuous_const_smul T₂ M₂]

instance : mul_action S₂ (M₁ →SLᶜ[σ₁₂] M₂) :=
{ smul := λ c f, ⟨c • f, let ⟨K, hK, hKf⟩ := exists_compact_preimage_mem_nhds f in ⟨c • K,
    hK.image $ continuous_id.const_smul c, mem_of_superset hKf (λ x hx, smul_mem_smul_set hx)⟩⟩,
  one_smul := λ f, ext $ λ x, one_smul _ _,
  mul_smul := λ a b f, ext $ λ x, mul_smul _ _ _ }

lemma smul_apply (c : S₂) (f : M₁ →SLᶜ[σ₁₂] M₂) (x : M₁) : (c • f) x = c • (f x) := rfl
@[simp, norm_cast]
lemma coe_smul (c : S₂) (f : M₁ →SLᶜ[σ₁₂] M₂) :
  (↑(c • f) : M₁ →ₛₗ[σ₁₂] M₂) = c • f := rfl
@[simp, norm_cast] lemma coe_smul' (c : S₂) (f : M₁ →SLᶜ[σ₁₂] M₂) :
  ⇑(c • f) = c • f := rfl

instance [has_smul S₂ T₂] [is_scalar_tower S₂ T₂ M₂] :
  is_scalar_tower S₂ T₂ (M₁ →SLᶜ[σ₁₂] M₂) :=
⟨λ a b f, ext $ λ x, smul_assoc a b (f x)⟩

instance [smul_comm_class S₂ T₂ M₂] : smul_comm_class S₂ T₂ (M₁ →SLᶜ[σ₁₂] M₂) :=
⟨λ a b f, ext $ λ x, smul_comm a b (f x)⟩

end smul_monoid

/-- The zero function is compact. -/
instance : has_zero (M₁ →SLᶜ[σ₁₂] M₂) :=
  ⟨⟨0, ⟨{0}, is_compact_singleton, mem_of_superset univ_mem (λ x _, rfl)⟩⟩⟩
instance : inhabited (M₁ →SLᶜ[σ₁₂] M₂) := ⟨0⟩

@[simp] lemma default_def : (default : M₁ →SLᶜ[σ₁₂] M₂) = 0 := rfl
@[simp] lemma zero_apply (x : M₁) : (0 : M₁ →SLᶜ[σ₁₂] M₂) x = 0 := rfl
@[simp, norm_cast] lemma coe_zero : ((0 : M₁ →SLᶜ[σ₁₂] M₂) : M₁ →ₛₗ[σ₁₂] M₂) = 0 := rfl
/- no simp attribute on the next line as simp does not always simplify `0 x` to `0`
when `0` is the zero function, while it does for the zero compact operator,
and this is the most important property we care about. -/
@[norm_cast] lemma coe_zero' : ⇑(0 : M₁ →SLᶜ[σ₁₂] M₂) = 0 := rfl

section add
variables [has_continuous_add M₂]

instance : has_add (M₁ →SLᶜ[σ₁₂] M₂) :=
⟨λ f g, ⟨f + g,
  let ⟨A, hA, hAf⟩ := exists_compact_preimage_mem_nhds f,
      ⟨B, hB, hBg⟩ := exists_compact_preimage_mem_nhds g in
  ⟨A + B, hA.add hB, mem_of_superset (inter_mem hAf hBg)
    (λ x ⟨hxA, hxB⟩, set.add_mem_add hxA hxB)⟩⟩⟩

@[simp] lemma add_apply (f g : M₁ →SLᶜ[σ₁₂] M₂)  (x : M₁) : (f + g) x = f x + g x := rfl
@[simp, norm_cast] lemma coe_add (f g : M₁ →SLᶜ[σ₁₂] M₂) :
  (↑(f + g) : M₁ →ₛₗ[σ₁₂] M₂) = f + g := rfl
@[norm_cast] lemma coe_add' (f g : M₁ →SLᶜ[σ₁₂] M₂) : ⇑(f + g) = f + g := rfl

instance : add_comm_monoid (M₁ →SLᶜ[σ₁₂] M₂) :=
{ zero := (0 : M₁ →SLᶜ[σ₁₂] M₂),
  add := (+),
  zero_add := by intros; ext; apply_rules [zero_add, add_assoc, add_zero, add_left_neg, add_comm],
  add_zero := by intros; ext; apply_rules [zero_add, add_assoc, add_zero, add_left_neg, add_comm],
  add_comm := by intros; ext; apply_rules [zero_add, add_assoc, add_zero, add_left_neg, add_comm],
  add_assoc := by intros; ext; apply_rules [zero_add, add_assoc, add_zero, add_left_neg, add_comm],
  nsmul := (•),
  nsmul_zero' := λ f, by { ext, simp },
  nsmul_succ' := λ n f, by { ext, simp [nat.succ_eq_one_add, add_smul] } }

@[simp, norm_cast] lemma coe_sum {ι : Type*} (t : finset ι) (f : ι → M₁ →SLᶜ[σ₁₂] M₂) :
  ↑(∑ d in t, f d) = (∑ d in t, f d : M₁ →ₛₗ[σ₁₂] M₂) :=
(add_monoid_hom.mk (coe : (M₁ →SLᶜ[σ₁₂] M₂) → (M₁ →ₛₗ[σ₁₂] M₂))
  rfl (λ _ _, rfl)).map_sum _ _

@[simp, norm_cast] lemma coe_sum' {ι : Type*} (t : finset ι) (f : ι → M₁ →SLᶜ[σ₁₂] M₂) :
  ⇑(∑ d in t, f d) = ∑ d in t, f d :=
by simp only [← coe_coe, coe_sum, linear_map.coe_fn_sum]

lemma sum_apply {ι : Type*} (t : finset ι) (f : ι → M₁ →SLᶜ[σ₁₂] M₂) (b : M₁) :
  (∑ d in t, f d) b = ∑ d in t, f d b :=
by simp only [coe_sum', finset.sum_apply]

instance {S : Type*} [monoid S] [distrib_mul_action S M₂] [smul_comm_class R₂ S M₂]
  [has_continuous_const_smul S M₂] :
  distrib_mul_action S (M₁ →SLᶜ[σ₁₂] M₂) :=
{ smul_add := λ a f g, by ext; exact smul_add _ _ _,
  smul_zero := λ a, by ext; exact smul_zero _ }

end add

section sub

variables [module R₁ M₃] [module R₂ M₄] [topological_add_group M₄]

instance : has_neg (M₃ →SLᶜ[σ₁₂] M₄) :=
⟨λ f, ⟨-f, let ⟨K, hK, hKf⟩ := exists_compact_preimage_mem_nhds f in
  ⟨-K, hK.neg, mem_of_superset hKf $ λ x (hx : f x ∈ K), set.neg_mem_neg.mpr hx⟩⟩⟩

@[simp] lemma neg_apply (f : M₃ →SLᶜ[σ₁₂] M₄) (x : M₃) : (-f) x = - (f x) := rfl
@[simp, norm_cast] lemma coe_neg (f : M₃ →SLᶜ[σ₁₂] M₄) : (↑(-f) : M₃ →ₛₗ[σ₁₂] M₄) = -f := rfl
@[norm_cast] lemma coe_neg' (f : M₃ →SLᶜ[σ₁₂] M₄) : ⇑(-f) = -f := rfl

instance : has_sub (M₃ →SLᶜ[σ₁₂] M₄) := ⟨λ f g, (f + (-g)).copy (f - g) (sub_eq_add_neg _ _)⟩

instance : add_comm_group (M₃ →SLᶜ[σ₁₂] M₄) :=
by refine
{ zero := 0,
  add := (+),
  neg := has_neg.neg,
  sub := has_sub.sub,
  sub_eq_add_neg := _,
  nsmul := (•),
  zsmul := (•),
  zsmul_zero' := λ f, by { ext, simp },
  zsmul_succ' := λ n f, by { ext, simp [add_smul, add_comm] },
  zsmul_neg' := λ n f, by { ext, simp [nat.succ_eq_add_one, add_smul] },
  .. compact_operator.add_comm_monoid, .. };
intros; ext; apply_rules [zero_add, add_assoc, add_zero, add_left_neg, add_comm, sub_eq_add_neg]

lemma sub_apply (f g : M₃ →SLᶜ[σ₁₂] M₄) (x : M₃) : (f - g) x = f x - g x := rfl
@[simp, norm_cast] lemma coe_sub (f g : M₃ →SLᶜ[σ₁₂] M₄) :
  (↑(f - g) : M₃ →ₛₗ[σ₁₂] M₄) = f - g := rfl
@[simp, norm_cast] lemma coe_sub' (f g : M₃ →SLᶜ[σ₁₂] M₄) : ⇑(f - g) = f - g := rfl

end sub

section module

variables [topological_add_group M₄] [has_continuous_const_smul R₄ M₄]

instance : module R₄ (M₃ →SLᶜ[σ₃₄] M₄) :=
{ zero_smul := λ _, ext $ λ _, zero_smul _ _,
  add_smul  := λ _ _ _, ext $ λ _, add_smul _ _ _ }

end module

end operations

section to_continuous

variables {𝕜₁ 𝕜₂ : Type*} [nondiscrete_normed_field 𝕜₁] [nondiscrete_normed_field 𝕜₂]
  {σ₁₂ : 𝕜₁ →+* 𝕜₂} [ring_hom_isometric σ₁₂] {M₁ M₂ : Type*} [topological_space M₁]
  [add_comm_group M₁] [topological_space M₂] [add_comm_group M₂] [module 𝕜₁ M₁] [module 𝕜₂ M₂]
  [topological_add_group M₁] [has_continuous_const_smul 𝕜₁ M₁]
  [topological_add_group M₂] [has_continuous_smul 𝕜₂ M₂]

@[priority 100] instance {F : Type*} [h : compact_operator_class F σ₁₂ M₁ M₂] :
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

@[simp, norm_cast]
lemma coe_clm_smul {S : Type*} [monoid S] [distrib_mul_action S M₂] [smul_comm_class 𝕜₂ S M₂]
  [has_continuous_const_smul S M₂](c : S) (f : M₁ →SLᶜ[σ₁₂] M₂) :
  (↑(c • f) : M₁ →SL[σ₁₂] M₂) = c • f := rfl

@[simp, norm_cast] lemma coe_clm_zero : ((0 : M₁ →SLᶜ[σ₁₂] M₂) : M₁ →SL[σ₁₂] M₂) = 0 := rfl

@[simp, norm_cast] lemma coe_clm_add (f g : M₁ →SLᶜ[σ₁₂] M₂) :
  (↑(f + g) : M₁ →SL[σ₁₂] M₂) = f + g := rfl

variables (σ₁₂ M₁ M₂)

def coe_clmₗ : (M₁ →SLᶜ[σ₁₂] M₂) →ₗ[𝕜₂] (M₁ →SL[σ₁₂] M₂) :=
⟨coe, coe_clm_add, coe_clm_smul⟩

end to_continuous

section topology

variables {𝕜₁ 𝕜₂ : Type*} [nondiscrete_normed_field 𝕜₁] [nondiscrete_normed_field 𝕜₂]
  {σ₁₂ : 𝕜₁ →+* 𝕜₂} [ring_hom_isometric σ₁₂] {M₁ M₂ M₃ M₄ : Type*} [semi_normed_group M₁]
  [semi_normed_group M₂] [normed_group M₃] [normed_group M₄] [normed_space 𝕜₁ M₁]
  [normed_space 𝕜₂ M₂] [normed_space 𝕜₁ M₃] [normed_space 𝕜₂ M₄]

noncomputable instance : semi_normed_group (M₁ →SLᶜ[σ₁₂] M₂) :=
semi_normed_group.induced ((coe_clmₗ σ₁₂ M₁ M₂) : (M₁ →SLᶜ[σ₁₂] M₂) →+ (M₁ →SL[σ₁₂] M₂))

noncomputable instance : normed_group (M₃ →SLᶜ[σ₁₂] M₄) :=
normed_group.induced ((coe_clmₗ σ₁₂ M₃ M₄) : (M₃ →SLᶜ[σ₁₂] M₄) →+ (M₃ →SL[σ₁₂] M₄))
  coe_clm_injective

variables (σ₁₂ M₁ M₂)

def coe_clmL : (M₁ →SLᶜ[σ₁₂] M₂) →L[𝕜₂] (M₁ →SL[σ₁₂] M₂) :=
⟨coe_clmₗ σ₁₂ M₁ M₂, continuous_induced_dom⟩

variables {σ₁₂ M₁ M₂}

lemma is_closed_range_coe_clmL [complete_space M₄] : is_closed (range $ coe_clmL σ₁₂ M₁ M₄) :=
begin
  refine is_closed_of_closure_subset _,
  rintros u hu,
  rw metric.mem_closure_iff at hu,
  suffices : totally_bounded (u '' metric.closed_ball 0 1),
  from ⟨mk_of_image_closed_ball_relatively_compact (u : M₁ →ₛₗ[σ₁₂] M₄) zero_lt_one $
        compact_of_totally_bounded_is_closed this.closure is_closed_closure, by ext; refl⟩,
  rw metric.totally_bounded_iff,
  intros ε hε,
  rcases hu (ε/2) (by linarith) with ⟨_, ⟨v, rfl⟩, huv⟩,
  rcases (v.image_closed_ball_relatively_compact 1).finite_cover_balls
    (show 0 < ε/2, by linarith) with ⟨T, -, hT, hTv⟩,
  have hTv : v '' closed_ball 0 1 ⊆ _ := subset_closure.trans hTv,
  refine ⟨T, hT, _⟩,
  rw image_subset_iff at ⊢ hTv,
  intros x hx,
  specialize hTv hx,
  rw [mem_preimage, mem_Union₂] at ⊢ hTv,
  rcases hTv with ⟨t, ht, htx⟩,
  refine ⟨t, ht, _⟩,
  suffices : dist (u x) (v x) < ε/2,
  { rw mem_ball at *,
    linarith [dist_triangle (u x) (v x) t] },
  rw mem_closed_ball_zero_iff at hx,
  calc dist (u x) (v x)
      = ∥u x - v x∥ : dist_eq_norm _ _
  ... = ∥(u - v) x∥ : by rw continuous_linear_map.sub_apply; refl
  ... ≤ ∥u - v∥ : (u - v).unit_le_op_norm x hx
  ... = dist u v : (dist_eq_norm _ _).symm
  ... < ε/2 : huv
end

lemma closed_embedding_coe_clmL [complete_space M₄] : closed_embedding (coe_clmL σ₁₂ M₁ M₄) :=
{ induced := rfl,
  inj := coe_clm_injective,
  closed_range := is_closed_range_coe_clmL }

lemma uniform_embedding_coe_clmL : uniform_embedding (coe_clmL σ₁₂ M₁ M₄) :=
{ comap_uniformity := rfl,
  inj := coe_clm_injective }

instance [complete_space M₄] : complete_space (M₁ →SLᶜ[σ₁₂] M₄) :=
begin
  rw complete_space_iff_is_complete_range uniform_embedding_coe_clmL.to_uniform_inducing,
  exact is_closed_range_coe_clmL.is_complete
end

end topology

end compact_operator

#lint
