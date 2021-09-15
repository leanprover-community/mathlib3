/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov, Sébastien Gouëzel, Rémy Degenne
-/
import measure_theory.integral.set_to_l1
import measure_theory.group.basic
import analysis.normed_space.bounded_linear_maps
import topology.sequences

/-!
# Bochner integral

The Bochner integral extends the definition of the Lebesgue integral to functions that map from a
measure space into a Banach space (complete normed vector space). It is constructed here by
extending the integral on simple functions.

## Main definitions

The Bochner integral is defined through the extension process described in the file `set_to_L1`,
which follows these steps:

1. Define the integral of the indicator of a set. This is `weighted_smul μ s x = (μ s).to_real * x`.
  `weighted_smul μ` is shown to be linear in the value `x` and `dominated_fin_meas_additive`
  (defined in the file `set_to_L1`) with respect to the set `s`.

2. Define the integral on simple functions of the type `simple_func α E` (notation : `α →ₛ E`)
  where `E` is a real normed space. (See `simple_func.integral` for details.)

3. Transfer this definition to define the integral on `L1.simple_func α E` (notation :
  `α →₁ₛ[μ] E`), see `L1.simple_func.integral`. Show that this integral is a continuous linear
  map from `α →₁ₛ[μ] E` to `E`.

4. Define the Bochner integral on L1 functions by extending the integral on integrable simple
  functions `α →₁ₛ[μ] E` using `continuous_linear_map.extend` and the fact that the embedding of
  `α →₁ₛ[μ] E` into `α →₁[μ] E` is dense.

5. Define the Bochner integral on functions as the Bochner integral of its equivalence class in L1
  space, if it is in L1, and 0 otherwise.

The result of that construction is `∫ a, f a ∂μ`, which is definitionally equal to
`set_to_fun (dominated_fin_meas_additive_weighted_smul μ) f`. Some basic properties of the integral
(like linearity) are particular cases of the properties of `set_to_fun` (which are described in the
file `set_to_L1`).

## Main statements

1. Basic properties of the Bochner integral on functions of type `α → E`, where `α` is a measure
   space and `E` is a real normed space.

  * `integral_zero`                  : `∫ 0 ∂μ = 0`
  * `integral_add`                   : `∫ x, f x + g x ∂μ = ∫ x, f ∂μ + ∫ x, g x ∂μ`
  * `integral_neg`                   : `∫ x, - f x ∂μ = - ∫ x, f x ∂μ`
  * `integral_sub`                   : `∫ x, f x - g x ∂μ = ∫ x, f x ∂μ - ∫ x, g x ∂μ`
  * `integral_smul`                  : `∫ x, r • f x ∂μ = r • ∫ x, f x ∂μ`
  * `integral_congr_ae`              : `f =ᵐ[μ] g → ∫ x, f x ∂μ = ∫ x, g x ∂μ`
  * `norm_integral_le_integral_norm` : `∥∫ x, f x ∂μ∥ ≤ ∫ x, ∥f x∥ ∂μ`

2. Basic properties of the Bochner integral on functions of type `α → ℝ`, where `α` is a measure
  space.

  * `integral_nonneg_of_ae` : `0 ≤ᵐ[μ] f → 0 ≤ ∫ x, f x ∂μ`
  * `integral_nonpos_of_ae` : `f ≤ᵐ[μ] 0 → ∫ x, f x ∂μ ≤ 0`
  * `integral_mono_ae`      : `f ≤ᵐ[μ] g → ∫ x, f x ∂μ ≤ ∫ x, g x ∂μ`
  * `integral_nonneg`       : `0 ≤ f → 0 ≤ ∫ x, f x ∂μ`
  * `integral_nonpos`       : `f ≤ 0 → ∫ x, f x ∂μ ≤ 0`
  * `integral_mono`         : `f ≤ᵐ[μ] g → ∫ x, f x ∂μ ≤ ∫ x, g x ∂μ`

3. Propositions connecting the Bochner integral with the integral on `ℝ≥0∞`-valued functions,
   which is called `lintegral` and has the notation `∫⁻`.

  * `integral_eq_lintegral_max_sub_lintegral_min` : `∫ x, f x ∂μ = ∫⁻ x, f⁺ x ∂μ - ∫⁻ x, f⁻ x ∂μ`,
    where `f⁺` is the positive part of `f` and `f⁻` is the negative part of `f`.
  * `integral_eq_lintegral_of_nonneg_ae`          : `0 ≤ᵐ[μ] f → ∫ x, f x ∂μ = ∫⁻ x, f x ∂μ`

4. `tendsto_integral_of_dominated_convergence` : the Lebesgue dominated convergence theorem

5. (In the file `set_integral`) integration commutes with continuous linear maps.

  * `continuous_linear_map.integral_comp_comm`
  * `linear_isometry.integral_comp_comm`


## Notes

Some tips on how to prove a proposition if the API for the Bochner integral is not enough so that
you need to unfold the definition of the Bochner integral and go back to simple functions.

One method is to use the theorem `integrable.induction` in the file `simple_func_dense` (or one of
the related results, like `Lp.induction` for functions in `Lp`), which allows you to prove something
for an arbitrary measurable + integrable function.

Another method is using the following steps.
See `integral_eq_lintegral_max_sub_lintegral_min` for a complicated example, which proves that
`∫ f = ∫⁻ f⁺ - ∫⁻ f⁻`, with the first integral sign being the Bochner integral of a real-valued
function `f : α → ℝ`, and second and third integral sign being the integral on `ℝ≥0∞`-valued
functions (called `lintegral`). The proof of `integral_eq_lintegral_max_sub_lintegral_min` is
scattered in sections with the name `pos_part`.

Here are the usual steps of proving that a property `p`, say `∫ f = ∫⁻ f⁺ - ∫⁻ f⁻`, holds for all
functions :

1. First go to the `L¹` space.

   For example, if you see `ennreal.to_real (∫⁻ a, ennreal.of_real $ ∥f a∥)`, that is the norm of
   `f` in `L¹` space. Rewrite using `L1.norm_of_fun_eq_lintegral_norm`.

2. Show that the set `{f ∈ L¹ | ∫ f = ∫⁻ f⁺ - ∫⁻ f⁻}` is closed in `L¹` using `is_closed_eq`.

3. Show that the property holds for all simple functions `s` in `L¹` space.

   Typically, you need to convert various notions to their `simple_func` counterpart, using lemmas
   like `L1.integral_coe_eq_integral`.

4. Since simple functions are dense in `L¹`,
```
univ = closure {s simple}
     = closure {s simple | ∫ s = ∫⁻ s⁺ - ∫⁻ s⁻} : the property holds for all simple functions
     ⊆ closure {f | ∫ f = ∫⁻ f⁺ - ∫⁻ f⁻}
     = {f | ∫ f = ∫⁻ f⁺ - ∫⁻ f⁻} : closure of a closed set is itself
```
Use `is_closed_property` or `dense_range.induction_on` for this argument.

## Notations

* `α →ₛ E`  : simple functions (defined in `measure_theory/integration`)
* `α →₁[μ] E` : functions in L1 space, i.e., equivalence classes of integrable functions (defined in
                `measure_theory/lp_space`)
* `α →₁ₛ[μ] E` : simple functions in L1 space, i.e., equivalence classes of integrable simple
                 functions (defined in `measure_theory/simple_func_dense`)
* `∫ a, f a ∂μ` : integral of `f` with respect to a measure `μ`
* `∫ a, f a` : integral of `f` with respect to `volume`, the default measure on the ambient type

We also define notations for integral on a set, which are described in the file
`measure_theory/set_integral`.

Note : `ₛ` is typed using `\_s`. Sometimes it shows as a box if the font is missing.

## Tags

Bochner integral, simple function, function space, Lebesgue dominated convergence theorem

-/

noncomputable theory
open_locale classical topological_space big_operators nnreal ennreal measure_theory
open set filter topological_space ennreal emetric

local attribute [instance] fact_one_le_one_ennreal

namespace measure_theory

variables {α E F 𝕜 : Type*}

section weighted_smul

open continuous_linear_map

variables [normed_group F] [normed_space ℝ F] {m : measurable_space α} {μ : measure α}

/-- Given a set `s`, return the continuous linear map `λ x, (μ s).to_real • x`. The extension of
that set function through `set_to_L1` gives the Bochner integral of L1 functions. -/
def weighted_smul {m : measurable_space α} (μ : measure α) (s : set α) : F →L[ℝ] F :=
(μ s).to_real • (continuous_linear_map.id ℝ F)

lemma weighted_smul_apply {m : measurable_space α} (μ : measure α) (s : set α) (x : F) :
  weighted_smul μ s x = (μ s).to_real • x :=
by simp [weighted_smul]

@[simp] lemma weighted_smul_zero_measure {m : measurable_space α} :
  weighted_smul (0 : measure α) = (0 : set α → F →L[ℝ] F) :=
by { ext1, simp [weighted_smul], }

@[simp] lemma weighted_smul_empty {m : measurable_space α} (μ : measure α) :
  weighted_smul μ ∅ = (0 : F →L[ℝ] F) :=
by { ext1 x, rw [weighted_smul_apply], simp, }

lemma weighted_smul_add_measure {m : measurable_space α} (μ ν : measure α) {s : set α}
  (hμs : μ s ≠ ∞) (hνs : ν s ≠ ∞) :
  (weighted_smul (μ + ν) s : F →L[ℝ] F) = weighted_smul μ s + weighted_smul ν s :=
begin
  ext1 x,
  push_cast,
  simp_rw [pi.add_apply, weighted_smul_apply],
  push_cast,
  rw [pi.add_apply, ennreal.to_real_add hμs hνs, add_smul],
end

lemma weighted_smul_congr (s t : set α) (hst : μ s = μ t) :
  (weighted_smul μ s : F →L[ℝ] F) = weighted_smul μ t :=
by { ext1 x, simp_rw weighted_smul_apply, congr' 2, }

lemma weighted_smul_null {s : set α} (h_zero : μ s = 0) : (weighted_smul μ s : F →L[ℝ] F) = 0 :=
by { ext1 x, rw [weighted_smul_apply, h_zero], simp, }

lemma weighted_smul_union (s t : set α) (hs : measurable_set s) (ht : measurable_set t)
  (hs_finite : μ s ≠ ∞) (ht_finite : μ t ≠ ∞) (h_inter : s ∩ t = ∅) :
  (weighted_smul μ (s ∪ t) : F →L[ℝ] F) = weighted_smul μ s + weighted_smul μ t :=
begin
  ext1 x,
  simp_rw [add_apply, weighted_smul_apply,
    measure_union (set.disjoint_iff_inter_eq_empty.mpr h_inter) hs ht,
    ennreal.to_real_add hs_finite ht_finite, add_smul],
end

lemma weighted_smul_smul [normed_field 𝕜] [normed_space 𝕜 F] [smul_comm_class ℝ 𝕜 F]
  (c : 𝕜) (s : set α) (x : F) :
  weighted_smul μ s (c • x) = c • weighted_smul μ s x :=
by { simp_rw [weighted_smul_apply, smul_comm], }

lemma norm_weighted_smul_le (s : set α) : ∥(weighted_smul μ s : F →L[ℝ] F)∥ ≤ (μ s).to_real :=
calc ∥(weighted_smul μ s : F →L[ℝ] F)∥ = ∥(μ s).to_real∥ * ∥continuous_linear_map.id ℝ F∥ :
  norm_smul _ _
... ≤ ∥(μ s).to_real∥ : (mul_le_mul_of_nonneg_left norm_id_le (norm_nonneg _)).trans (mul_one _).le
... = abs (μ s).to_real : real.norm_eq_abs _
... = (μ s).to_real : abs_eq_self.mpr ennreal.to_real_nonneg

lemma dominated_fin_meas_additive_weighted_smul {m : measurable_space α} (μ : measure α) :
  dominated_fin_meas_additive μ (weighted_smul μ : set α → F →L[ℝ] F) 1 :=
⟨weighted_smul_union, λ s, (norm_weighted_smul_le s).trans (one_mul _).symm.le⟩

end weighted_smul

local infixr ` →ₛ `:25 := simple_func

namespace simple_func

section pos_part
variables [linear_order E] [has_zero E] [measurable_space α]

/-- Positive part of a simple function. -/
def pos_part (f : α →ₛ E) : α →ₛ E := f.map (λ b, max b 0)

/-- Negative part of a simple function. -/
def neg_part [has_neg E] (f : α →ₛ E) : α →ₛ E := pos_part (-f)

lemma pos_part_map_norm (f : α →ₛ ℝ) : (pos_part f).map norm = pos_part f :=
by { ext, rw [map_apply, real.norm_eq_abs, abs_of_nonneg], exact le_max_right _ _ }

lemma neg_part_map_norm (f : α →ₛ ℝ) : (neg_part f).map norm = neg_part f :=
by { rw neg_part, exact pos_part_map_norm _ }

lemma pos_part_sub_neg_part (f : α →ₛ ℝ) : f.pos_part - f.neg_part = f :=
begin
  simp only [pos_part, neg_part],
  ext a,
  rw coe_sub,
  exact max_zero_sub_eq_self (f a)
end

end pos_part

section integral
/-!
### The Bochner integral of simple functions

Define the Bochner integral of simple functions of the type `α →ₛ β` where `β` is a normed group,
and prove basic property of this integral.
-/
open finset

variables [normed_group E] [measurable_space E] [normed_group F] [normed_space ℝ F] {p : ℝ≥0∞}
  {G F' : Type*} [normed_group G] [normed_group F'] [normed_space ℝ F']
  {m : measurable_space α} {μ : measure α}

/-- Bochner integral of simple functions whose codomain is a real `normed_space`.
This is equal to `∑ x in f.range, (μ (f ⁻¹' {x})).to_real • x` (see `integral_eq`). -/
def integral {m : measurable_space α} (μ : measure α) (f : α →ₛ F) : F :=
f.set_to_simple_func (weighted_smul μ)

lemma integral_def {m : measurable_space α} (μ : measure α) (f : α →ₛ F) :
  f.integral μ = f.set_to_simple_func (weighted_smul μ) := rfl

lemma integral_eq {m : measurable_space α} (μ : measure α) (f : α →ₛ F) :
  f.integral μ = ∑ x in f.range, (μ (f ⁻¹' {x})).to_real • x :=
by simp [integral, set_to_simple_func, weighted_smul_apply]

lemma integral_eq_sum_filter {m : measurable_space α} (f : α →ₛ F) (μ : measure α) :
  f.integral μ = ∑ x in f.range.filter (λ x, x ≠ 0), (μ (f ⁻¹' {x})).to_real • x :=
by { rw [integral_def, set_to_simple_func_eq_sum_filter], simp_rw weighted_smul_apply, }

/-- The Bochner integral is equal to a sum over any set that includes `f.range` (except `0`). -/
lemma integral_eq_sum_of_subset {f : α →ₛ F} {s : finset F}
  (hs : f.range.filter (λ x, x ≠ 0) ⊆ s) : f.integral μ = ∑ x in s, (μ (f ⁻¹' {x})).to_real • x :=
begin
  rw [simple_func.integral_eq_sum_filter, finset.sum_subset hs],
  rintro x - hx, rw [finset.mem_filter, not_and_distrib, ne.def, not_not] at hx,
  rcases hx with hx|rfl; [skip, simp],
  rw [simple_func.mem_range] at hx, rw [preimage_eq_empty]; simp [disjoint_singleton_left, hx]
end

/-- Calculate the integral of `g ∘ f : α →ₛ F`, where `f` is an integrable function from `α` to `E`
    and `g` is a function from `E` to `F`. We require `g 0 = 0` so that `g ∘ f` is integrable. -/
lemma map_integral (f : α →ₛ E) (g : E → F) (hf : integrable f μ) (hg : g 0 = 0) :
  (f.map g).integral μ = ∑ x in f.range, (ennreal.to_real (μ (f ⁻¹' {x}))) • (g x) :=
map_set_to_simple_func _ weighted_smul_union hf hg

/-- `simple_func.integral` and `simple_func.lintegral` agree when the integrand has type
    `α →ₛ ℝ≥0∞`. But since `ℝ≥0∞` is not a `normed_space`, we need some form of coercion.
    See `integral_eq_lintegral` for a simpler version. -/
lemma integral_eq_lintegral' {f : α →ₛ E} {g : E → ℝ≥0∞} (hf : integrable f μ) (hg0 : g 0 = 0)
  (hgt : ∀b, g b < ∞) :
  (f.map (ennreal.to_real ∘ g)).integral μ = ennreal.to_real (∫⁻ a, g (f a) ∂μ) :=
begin
  have hf' : f.fin_meas_supp μ := integrable_iff_fin_meas_supp.1 hf,
  simp only [← map_apply g f, lintegral_eq_lintegral],
  rw [map_integral f _ hf, map_lintegral, ennreal.to_real_sum],
  { refine finset.sum_congr rfl (λb hb, _),
    rw [smul_eq_mul, to_real_mul, mul_comm] },
  { assume a ha,
    by_cases a0 : a = 0,
    { rw [a0, hg0, zero_mul], exact with_top.zero_lt_top },
    { apply mul_lt_top (hgt a) (hf'.meas_preimage_singleton_ne_zero a0) } },
  { simp [hg0] }
end

variables [normed_field 𝕜] [normed_space 𝕜 E] [normed_space ℝ E] [smul_comm_class ℝ 𝕜 E]

lemma integral_congr {f g : α →ₛ E} (hf : integrable f μ) (h : f =ᵐ[μ] g) :
  f.integral μ = g.integral μ :=
set_to_simple_func_congr (weighted_smul μ) (λ s hs, weighted_smul_null) weighted_smul_union hf h

/-- `simple_func.bintegral` and `simple_func.integral` agree when the integrand has type
    `α →ₛ ℝ≥0∞`. But since `ℝ≥0∞` is not a `normed_space`, we need some form of coercion. -/
lemma integral_eq_lintegral {f : α →ₛ ℝ} (hf : integrable f μ) (h_pos : 0 ≤ᵐ[μ] f) :
  f.integral μ = ennreal.to_real (∫⁻ a, ennreal.of_real (f a) ∂μ) :=
begin
  have : f =ᵐ[μ] f.map (ennreal.to_real ∘ ennreal.of_real) :=
    h_pos.mono (λ a h, (ennreal.to_real_of_real h).symm),
  rw [← integral_eq_lintegral' hf],
  { exact integral_congr hf this },
  { exact ennreal.of_real_zero },
  { assume b, rw ennreal.lt_top_iff_ne_top, exact ennreal.of_real_ne_top }
end

lemma integral_add {f g : α →ₛ E} (hf : integrable f μ) (hg : integrable g μ) :
  integral μ (f + g) = integral μ f + integral μ g :=
set_to_simple_func_add _ weighted_smul_union hf hg

lemma integral_neg {f : α →ₛ E} (hf : integrable f μ) : integral μ (-f) = - integral μ f :=
set_to_simple_func_neg _ weighted_smul_union hf

lemma integral_sub {f g : α →ₛ E} (hf : integrable f μ) (hg : integrable g μ) :
  integral μ (f - g) = integral μ f - integral μ g :=
set_to_simple_func_sub _ weighted_smul_union hf hg

lemma integral_smul (c : 𝕜) {f : α →ₛ E} (hf : integrable f μ) :
  integral μ (c • f) = c • integral μ f :=
set_to_simple_func_smul _ weighted_smul_union weighted_smul_smul c hf

lemma norm_set_to_simple_func_le_integral_norm (T : set α → E →L[ℝ] F) {C : ℝ}
  (hT_norm : ∀ s, ∥T s∥ ≤ C * (μ s).to_real) {f : α →ₛ E} (hf : integrable f μ) :
  ∥f.set_to_simple_func T∥ ≤ C * (f.map norm).integral μ :=
calc ∥f.set_to_simple_func T∥
    ≤ C * ∑ x in f.range, ennreal.to_real (μ (f ⁻¹' {x})) * ∥x∥ :
  norm_set_to_simple_func_le_sum_mul_norm T hT_norm f
... = C * (f.map norm).integral μ : by { rw map_integral f norm hf norm_zero, simp_rw smul_eq_mul, }

lemma norm_integral_le_integral_norm (f : α →ₛ E) (hf : integrable f μ) :
  ∥f.integral μ∥ ≤ (f.map norm).integral μ :=
begin
  refine (norm_set_to_simple_func_le_integral_norm _ (λ s, _) hf).trans (one_mul _).le,
  exact (norm_weighted_smul_le s).trans (one_mul _).symm.le,
end

lemma integral_add_measure {ν} (f : α →ₛ E) (hf : integrable f (μ + ν)) :
  f.integral (μ + ν) = f.integral μ + f.integral ν :=
begin
  simp_rw [integral_def],
  refine set_to_simple_func_add_left' (weighted_smul μ) (weighted_smul ν) (weighted_smul (μ + ν))
    (λ s hs hμνs, _) hf,
  rw [measure.coe_add, pi.add_apply, ennreal.add_ne_top] at hμνs,
  rw weighted_smul_add_measure _ _ hμνs.1 hμνs.2,
end

end integral

end simple_func

namespace L1

open ae_eq_fun Lp.simple_func Lp

variables
  [normed_group E] [second_countable_topology E] [measurable_space E] [borel_space E]
  [normed_group F] [second_countable_topology F] [measurable_space F] [borel_space F]
  {m : measurable_space α} {μ : measure α}

variables {α E μ}

namespace simple_func

lemma norm_eq_integral (f : α →₁ₛ[μ] E) : ∥f∥ = ((to_simple_func f).map norm).integral μ :=
begin
  rw [norm_eq_sum_mul f, (to_simple_func f).map_integral norm (simple_func.integrable f) norm_zero],
  simp_rw smul_eq_mul,
end

section pos_part

/-- Positive part of a simple function in L1 space.  -/
def pos_part (f : α →₁ₛ[μ] ℝ) : α →₁ₛ[μ] ℝ := ⟨Lp.pos_part (f : α →₁[μ] ℝ),
begin
  rcases f with ⟨f, s, hsf⟩,
  use s.pos_part,
  simp only [subtype.coe_mk, Lp.coe_pos_part, ← hsf, ae_eq_fun.pos_part_mk, simple_func.pos_part,
    simple_func.coe_map]
end ⟩

/-- Negative part of a simple function in L1 space. -/
def neg_part (f : α →₁ₛ[μ] ℝ) : α →₁ₛ[μ] ℝ := pos_part (-f)

@[norm_cast]
lemma coe_pos_part (f : α →₁ₛ[μ] ℝ) : (pos_part f : α →₁[μ] ℝ) = Lp.pos_part (f : α →₁[μ] ℝ) := rfl

@[norm_cast]
lemma coe_neg_part (f : α →₁ₛ[μ] ℝ) : (neg_part f : α →₁[μ] ℝ) = Lp.neg_part (f : α →₁[μ] ℝ) := rfl

end pos_part

section simple_func_integral
/-!
### The Bochner integral of `L1`

Define the Bochner integral on `α →₁ₛ[μ] E` by extension from the simple functions `α →₁ₛ[μ] E`,
and prove basic properties of this integral. -/

variables [normed_field 𝕜] [normed_space 𝕜 E] [normed_space ℝ E] [smul_comm_class ℝ 𝕜 E]
  {F' : Type*} [normed_group F'] [normed_space ℝ F']

local attribute [instance] simple_func.normed_space

/-- The Bochner integral over simple functions in L1 space. -/
def integral (f : α →₁ₛ[μ] E) : E := ((to_simple_func f)).integral μ

lemma integral_eq_integral (f : α →₁ₛ[μ] E) : integral f = ((to_simple_func f)).integral μ := rfl

lemma integral_eq_lintegral {f : α →₁ₛ[μ] ℝ} (h_pos : 0 ≤ᵐ[μ] (to_simple_func f)) :
  integral f = ennreal.to_real (∫⁻ a, ennreal.of_real ((to_simple_func f) a) ∂μ) :=
by rw [integral, simple_func.integral_eq_lintegral (simple_func.integrable f) h_pos]

lemma integral_eq_set_to_L1s (f : α →₁ₛ[μ] E) : integral f = set_to_L1s (weighted_smul μ) f := rfl

lemma integral_congr {f g : α →₁ₛ[μ] E} (h : to_simple_func f =ᵐ[μ] to_simple_func g) :
  integral f = integral g :=
simple_func.integral_congr (simple_func.integrable f) h

lemma integral_add (f g : α →₁ₛ[μ] E) : integral (f + g) = integral f + integral g :=
set_to_L1s_add _ (λ _ _, weighted_smul_null) weighted_smul_union _ _

lemma integral_smul [measurable_space 𝕜] [opens_measurable_space 𝕜] (c : 𝕜) (f : α →₁ₛ[μ] E) :
  integral (c • f) = c • integral f :=
set_to_L1s_smul _ (λ _ _, weighted_smul_null) weighted_smul_union weighted_smul_smul c f

lemma norm_integral_le_norm (f : α →₁ₛ[μ] E) : ∥integral f∥ ≤ ∥f∥ :=
begin
  rw [integral, norm_eq_integral],
  exact (to_simple_func f).norm_integral_le_integral_norm (simple_func.integrable f)
end

variables {E' : Type*} [normed_group E'] [second_countable_topology E'] [measurable_space E']
  [borel_space E'] [normed_space ℝ E'] [normed_space 𝕜 E']
  [measurable_space 𝕜] [opens_measurable_space 𝕜]

variables (α E μ 𝕜)
/-- The Bochner integral over simple functions in L1 space as a continuous linear map. -/
def integral_clm' : (α →₁ₛ[μ] E) →L[𝕜] E :=
linear_map.mk_continuous ⟨integral, integral_add, integral_smul⟩
  1 (λf, le_trans (norm_integral_le_norm _) $ by rw one_mul)

/-- The Bochner integral over simple functions in L1 space as a continuous linear map over ℝ. -/
def integral_clm : (α →₁ₛ[μ] E) →L[ℝ] E := integral_clm' α E ℝ μ

variables {α E μ 𝕜}

local notation `Integral` := integral_clm α E μ

open continuous_linear_map

lemma norm_Integral_le_one : ∥Integral∥ ≤ 1 :=
linear_map.mk_continuous_norm_le _ (zero_le_one) _

section pos_part

lemma pos_part_to_simple_func (f : α →₁ₛ[μ] ℝ) :
  to_simple_func (pos_part f) =ᵐ[μ] (to_simple_func f).pos_part :=
begin
  have eq : ∀ a, (to_simple_func f).pos_part a = max ((to_simple_func f) a) 0 := λa, rfl,
  have ae_eq : ∀ᵐ a ∂μ, to_simple_func (pos_part f) a = max ((to_simple_func f) a) 0,
  { filter_upwards [to_simple_func_eq_to_fun (pos_part f), Lp.coe_fn_pos_part (f : α →₁[μ] ℝ),
      to_simple_func_eq_to_fun f],
    assume a h₁ h₂ h₃,
    convert h₂ },
  refine ae_eq.mono (assume a h, _),
  rw [h, eq]
end

lemma neg_part_to_simple_func (f : α →₁ₛ[μ] ℝ) :
  to_simple_func (neg_part f) =ᵐ[μ] (to_simple_func f).neg_part :=
begin
  rw [simple_func.neg_part, measure_theory.simple_func.neg_part],
  filter_upwards [pos_part_to_simple_func (-f), neg_to_simple_func f],
  assume a h₁ h₂,
  rw h₁,
  show max _ _ = max _ _,
  rw h₂,
  refl
end

lemma integral_eq_norm_pos_part_sub (f : α →₁ₛ[μ] ℝ) :
  integral f = ∥pos_part f∥ - ∥neg_part f∥ :=
begin
  -- Convert things in `L¹` to their `simple_func` counterpart
  have ae_eq₁ : (to_simple_func f).pos_part =ᵐ[μ] (to_simple_func (pos_part f)).map norm,
  { filter_upwards [pos_part_to_simple_func f],
    assume a h,
    rw [simple_func.map_apply, h],
    conv_lhs { rw [← simple_func.pos_part_map_norm, simple_func.map_apply] } },
  -- Convert things in `L¹` to their `simple_func` counterpart
  have ae_eq₂ : (to_simple_func f).neg_part =ᵐ[μ] (to_simple_func (neg_part f)).map norm,
  { filter_upwards [neg_part_to_simple_func f],
    assume a h,
    rw [simple_func.map_apply, h],
    conv_lhs { rw [← simple_func.neg_part_map_norm, simple_func.map_apply] } },
  -- Convert things in `L¹` to their `simple_func` counterpart
  have ae_eq : ∀ᵐ a ∂μ, (to_simple_func f).pos_part a - (to_simple_func f).neg_part a =
     (to_simple_func (pos_part f)).map norm a -  (to_simple_func (neg_part f)).map norm a,
  { filter_upwards [ae_eq₁, ae_eq₂],
    assume a h₁ h₂,
    rw [h₁, h₂] },
  rw [integral, norm_eq_integral, norm_eq_integral, ← simple_func.integral_sub],
  { show (to_simple_func f).integral μ =
      ((to_simple_func (pos_part f)).map norm - (to_simple_func (neg_part f)).map norm).integral μ,
    apply measure_theory.simple_func.integral_congr (simple_func.integrable f),
    filter_upwards [ae_eq₁, ae_eq₂],
    assume a h₁ h₂, show _ = _ - _,
    rw [← h₁, ← h₂],
    have := (to_simple_func f).pos_part_sub_neg_part,
    conv_lhs {rw ← this},
    refl },
  { exact (simple_func.integrable f).max_zero.congr ae_eq₁ },
  { exact (simple_func.integrable f).neg.max_zero.congr ae_eq₂ }
end

end pos_part

end simple_func_integral

end simple_func

open simple_func
local notation `Integral` := @integral_clm α E _ _ _ _ _ μ _


variables [normed_space ℝ E] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E]
  [smul_comm_class ℝ 𝕜 E] [normed_space ℝ F] [complete_space E]

section integration_in_L1

local attribute [instance] simple_func.normed_space

open continuous_linear_map

variables (𝕜) [measurable_space 𝕜] [opens_measurable_space 𝕜]

/-- The Bochner integral in L1 space as a continuous linear map. -/
def integral_clm' : (α →₁[μ] E) →L[𝕜] E :=
(integral_clm' α E 𝕜 μ).extend
  (coe_to_Lp α E 𝕜) (simple_func.dense_range one_ne_top) simple_func.uniform_inducing

variables {𝕜}

/-- The Bochner integral in L1 space as a continuous linear map over ℝ. -/
def integral_clm : (α →₁[μ] E) →L[ℝ] E := integral_clm' ℝ

/-- The Bochner integral in L1 space -/
def integral (f : α →₁[μ] E) : E := integral_clm f

lemma integral_eq (f : α →₁[μ] E) : integral f = integral_clm f := rfl

lemma integral_eq_set_to_L1 (f : α →₁[μ] E) :
  integral f = set_to_L1 (dominated_fin_meas_additive_weighted_smul μ) f :=
rfl

@[norm_cast] lemma simple_func.integral_L1_eq_integral (f : α →₁ₛ[μ] E) :
  integral (f : α →₁[μ] E) = (simple_func.integral f) :=
set_to_L1_eq_set_to_L1s_clm (dominated_fin_meas_additive_weighted_smul μ) f

variables (α E)
@[simp] lemma integral_zero : integral (0 : α →₁[μ] E) = 0 :=
map_zero integral_clm
variables {α E}

lemma integral_add (f g : α →₁[μ] E) : integral (f + g) = integral f + integral g :=
map_add integral_clm f g

lemma integral_neg (f : α →₁[μ] E) : integral (-f) = - integral f :=
map_neg integral_clm f

lemma integral_sub (f g : α →₁[μ] E) : integral (f - g) = integral f - integral g :=
map_sub integral_clm f g

lemma integral_smul (c : 𝕜) (f : α →₁[μ] E) : integral (c • f) = c • integral f :=
map_smul (integral_clm' 𝕜) c f

local notation `Integral` := @integral_clm α E _ _ _ _ _ μ _ _
local notation `sIntegral` := @simple_func.integral_clm α E _ _ _ _ _ μ _

lemma norm_Integral_le_one : ∥Integral∥ ≤ 1 :=
calc ∥Integral∥ ≤ (1 : ℝ≥0) * ∥sIntegral∥ :
  op_norm_extend_le _ _ _ $ λs, by {rw [nnreal.coe_one, one_mul], refl}
  ... = ∥sIntegral∥ : one_mul _
  ... ≤ 1 : norm_Integral_le_one

lemma norm_integral_le (f : α →₁[μ] E) : ∥integral f∥ ≤ ∥f∥ :=
calc ∥integral f∥ = ∥Integral f∥ : rfl
  ... ≤ ∥Integral∥ * ∥f∥ : le_op_norm _ _
  ... ≤ 1 * ∥f∥ : mul_le_mul_of_nonneg_right norm_Integral_le_one $ norm_nonneg _
  ... = ∥f∥ : one_mul _

@[continuity]
lemma continuous_integral : continuous (λ (f : α →₁[μ] E), integral f) :=
L1.integral_clm.continuous

section pos_part

local attribute [instance] fact_one_le_one_ennreal

lemma integral_eq_norm_pos_part_sub (f : α →₁[μ] ℝ) :
  integral f = ∥Lp.pos_part f∥ - ∥Lp.neg_part f∥ :=
begin
  -- Use `is_closed_property` and `is_closed_eq`
  refine @is_closed_property _ _ _ (coe : (α →₁ₛ[μ] ℝ) → (α →₁[μ] ℝ))
    (λ f : α →₁[μ] ℝ, integral f = ∥Lp.pos_part f∥ - ∥Lp.neg_part f∥)
    (simple_func.dense_range one_ne_top) (is_closed_eq _ _) _ f,
  { exact cont _ },
  { refine continuous.sub (continuous_norm.comp Lp.continuous_pos_part)
      (continuous_norm.comp Lp.continuous_neg_part) },
  -- Show that the property holds for all simple functions in the `L¹` space.
  { assume s,
    norm_cast,
    exact simple_func.integral_eq_norm_pos_part_sub _ }
end

end pos_part

end integration_in_L1

end L1

/-!
### The Bochner integral on functions

Define the Bochner integral on functions generally to be the `L1` Bochner integral, for integrable
functions, and 0 otherwise; prove its basic properties.

-/

variables [normed_group E] [second_countable_topology E] [normed_space ℝ E] [complete_space E]
  [measurable_space E] [borel_space E]
          [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [smul_comm_class ℝ 𝕜 E]
          [normed_group F] [second_countable_topology F] [normed_space ℝ F] [complete_space F]
  [measurable_space F] [borel_space F]

/-- The Bochner integral -/
def integral {m : measurable_space α} (μ : measure α) (f : α → E) : E :=
if hf : integrable f μ then L1.integral (hf.to_L1 f) else 0

/-! In the notation for integrals, an expression like `∫ x, g ∥x∥ ∂μ` will not be parsed correctly,
  and needs parentheses. We do not set the binding power of `r` to `0`, because then
  `∫ x, f x = 0` will be parsed incorrectly. -/
notation `∫` binders `, ` r:(scoped:60 f, f) ` ∂` μ:70 := integral μ r
notation `∫` binders `, ` r:(scoped:60 f, integral volume f) := r
notation `∫` binders ` in ` s `, ` r:(scoped:60 f, f) ` ∂` μ:70 := integral (measure.restrict μ s) r
notation `∫` binders ` in ` s `, ` r:(scoped:60 f, integral (measure.restrict volume s) f) := r

section properties

open continuous_linear_map measure_theory.simple_func

variables {f g : α → E} {m : measurable_space α} {μ : measure α}

lemma integral_eq (f : α → E) (hf : integrable f μ) :
  ∫ a, f a ∂μ = L1.integral (hf.to_L1 f) :=
dif_pos hf

lemma integral_eq_set_to_fun (f : α → E) :
  ∫ a, f a ∂μ = set_to_fun (dominated_fin_meas_additive_weighted_smul μ) f :=
rfl

lemma L1.integral_eq_integral (f : α →₁[μ] E) : L1.integral f = ∫ a, f a ∂μ :=
(L1.set_to_fun_eq_set_to_L1 (dominated_fin_meas_additive_weighted_smul μ) f).symm

lemma integral_undef (h : ¬ integrable f μ) : ∫ a, f a ∂μ = 0 :=
dif_neg h

lemma integral_non_ae_measurable (h : ¬ ae_measurable f μ) : ∫ a, f a ∂μ = 0 :=
integral_undef $ not_and_of_not_left _ h

variables (α E)

lemma integral_zero : ∫ a : α, (0:E) ∂μ = 0 :=
set_to_fun_zero (dominated_fin_meas_additive_weighted_smul μ)

@[simp] lemma integral_zero' : integral μ (0 : α → E) = 0 :=
integral_zero α E

variables {α E}

lemma integral_add (hf : integrable f μ) (hg : integrable g μ) :
  ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ :=
set_to_fun_add (dominated_fin_meas_additive_weighted_smul μ) hf hg

lemma integral_add' (hf : integrable f μ) (hg : integrable g μ) :
  ∫ a, (f + g) a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ :=
integral_add hf hg

lemma integral_neg (f : α → E) : ∫ a, -f a ∂μ = - ∫ a, f a ∂μ :=
set_to_fun_neg (dominated_fin_meas_additive_weighted_smul μ) f

lemma integral_neg' (f : α → E) : ∫ a, (-f) a ∂μ = - ∫ a, f a ∂μ :=
integral_neg f

lemma integral_sub (hf : integrable f μ) (hg : integrable g μ) :
  ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ :=
set_to_fun_sub (dominated_fin_meas_additive_weighted_smul μ) hf hg

lemma integral_sub' (hf : integrable f μ) (hg : integrable g μ) :
  ∫ a, (f - g) a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ :=
integral_sub hf hg

lemma integral_smul [measurable_space 𝕜] [opens_measurable_space 𝕜] (c : 𝕜) (f : α → E) :
  ∫ a, c • (f a) ∂μ = c • ∫ a, f a ∂μ :=
set_to_fun_smul (dominated_fin_meas_additive_weighted_smul μ) weighted_smul_smul c f

lemma integral_mul_left (r : ℝ) (f : α → ℝ) : ∫ a, r * (f a) ∂μ = r * ∫ a, f a ∂μ :=
integral_smul r f

lemma integral_mul_right (r : ℝ) (f : α → ℝ) : ∫ a, (f a) * r ∂μ = ∫ a, f a ∂μ * r :=
by { simp only [mul_comm], exact integral_mul_left r f }

lemma integral_div (r : ℝ) (f : α → ℝ) : ∫ a, (f a) / r ∂μ = ∫ a, f a ∂μ / r :=
integral_mul_right r⁻¹ f

lemma integral_congr_ae (h : f =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ :=
set_to_fun_congr_ae (dominated_fin_meas_additive_weighted_smul μ) h

@[simp] lemma L1.integral_of_fun_eq_integral {f : α → E} (hf : integrable f μ) :
  ∫ a, (hf.to_L1 f) a ∂μ = ∫ a, f a ∂μ :=
integral_congr_ae $ by simp [integrable.coe_fn_to_L1]

@[continuity]
lemma continuous_integral : continuous (λ (f : α →₁[μ] E), ∫ a, f a ∂μ) :=
by { simp only [← L1.integral_eq_integral], exact L1.continuous_integral }

lemma norm_integral_le_lintegral_norm (f : α → E) :
  ∥∫ a, f a ∂μ∥ ≤ ennreal.to_real (∫⁻ a, (ennreal.of_real ∥f a∥) ∂μ) :=
begin
  by_cases hf : integrable f μ,
  { rw [integral_eq f hf, ← integrable.norm_to_L1_eq_lintegral_norm f hf],
    exact L1.norm_integral_le _ },
  { rw [integral_undef hf, norm_zero], exact to_real_nonneg }
end

lemma ennnorm_integral_le_lintegral_ennnorm (f : α → E) :
  (nnnorm (∫ a, f a ∂μ) : ℝ≥0∞) ≤ ∫⁻ a, (nnnorm (f a)) ∂μ :=
by { simp_rw [← of_real_norm_eq_coe_nnnorm], apply ennreal.of_real_le_of_le_to_real,
  exact norm_integral_le_lintegral_norm f }

lemma integral_eq_zero_of_ae {f : α → E} (hf : f =ᵐ[μ] 0) : ∫ a, f a ∂μ = 0 :=
by simp [integral_congr_ae hf, integral_zero]

/-- If `f` has finite integral, then `∫ x in s, f x ∂μ` is absolutely continuous in `s`: it tends
to zero as `μ s` tends to zero. -/
lemma has_finite_integral.tendsto_set_integral_nhds_zero {ι} {f : α → E}
  (hf : has_finite_integral f μ) {l : filter ι} {s : ι → set α}
  (hs : tendsto (μ ∘ s) l (𝓝 0)) :
  tendsto (λ i, ∫ x in s i, f x ∂μ) l (𝓝 0) :=
begin
  rw [tendsto_zero_iff_norm_tendsto_zero],
  simp_rw [← coe_nnnorm, ← nnreal.coe_zero, nnreal.tendsto_coe, ← ennreal.tendsto_coe,
    ennreal.coe_zero],
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_set_lintegral_zero hf hs) (λ i, zero_le _)
    (λ i, ennnorm_integral_le_lintegral_ennnorm _)
end

/-- If `f` is integrable, then `∫ x in s, f x ∂μ` is absolutely continuous in `s`: it tends
to zero as `μ s` tends to zero. -/
lemma integrable.tendsto_set_integral_nhds_zero {ι} {f : α → E}
  (hf : integrable f μ) {l : filter ι} {s : ι → set α} (hs : tendsto (μ ∘ s) l (𝓝 0)) :
  tendsto (λ i, ∫ x in s i, f x ∂μ) l (𝓝 0) :=
hf.2.tendsto_set_integral_nhds_zero hs

/-- If `F i → f` in `L1`, then `∫ x, F i x ∂μ → ∫ x, f x∂μ`. -/
lemma tendsto_integral_of_L1 {ι} (f : α → E) (hfi : integrable f μ)
  {F : ι → α → E} {l : filter ι} (hFi : ∀ᶠ i in l, integrable (F i) μ)
  (hF : tendsto (λ i, ∫⁻ x, ∥F i x - f x∥₊ ∂μ) l (𝓝 0)) :
  tendsto (λ i, ∫ x, F i x ∂μ) l (𝓝 $ ∫ x, f x ∂μ) :=
begin
  rw [tendsto_iff_norm_tendsto_zero],
  replace hF : tendsto (λ i, ennreal.to_real $ ∫⁻ x, ∥F i x - f x∥₊ ∂μ) l (𝓝 0) :=
    (ennreal.tendsto_to_real zero_ne_top).comp hF,
  refine squeeze_zero_norm' (hFi.mp $ hFi.mono $ λ i hFi hFm, _) hF,
  simp only [norm_norm, ← integral_sub hFi hfi],
  convert norm_integral_le_lintegral_norm (λ x, F i x - f x),
  ext1 x,
  exact coe_nnreal_eq _
end

/-- Lebesgue dominated convergence theorem provides sufficient conditions under which almost
  everywhere convergence of a sequence of functions implies the convergence of their integrals. -/
theorem tendsto_integral_of_dominated_convergence {F : ℕ → α → E} {f : α → E} (bound : α → ℝ)
  (F_measurable : ∀ n, ae_measurable (F n) μ)
  (f_measurable : ae_measurable f μ)
  (bound_integrable : integrable bound μ)
  (h_bound : ∀ n, ∀ᵐ a ∂μ, ∥F n a∥ ≤ bound a)
  (h_lim : ∀ᵐ a ∂μ, tendsto (λ n, F n a) at_top (𝓝 (f a))) :
  tendsto (λn, ∫ a, F n a ∂μ) at_top (𝓝 $ ∫ a, f a ∂μ) :=
begin
  /- To show `(∫ a, F n a) --> (∫ f)`, suffices to show `∥∫ a, F n a - ∫ f∥ --> 0` -/
  rw tendsto_iff_norm_tendsto_zero,
  /- But `0 ≤ ∥∫ a, F n a - ∫ f∥ = ∥∫ a, (F n a - f a) ∥ ≤ ∫ a, ∥F n a - f a∥, and thus we apply the
    sandwich theorem and prove that `∫ a, ∥F n a - f a∥ --> 0` -/
  have lintegral_norm_tendsto_zero :
    tendsto (λn, ennreal.to_real $ ∫⁻ a, (ennreal.of_real ∥F n a - f a∥) ∂μ) at_top (𝓝 0) :=
  (tendsto_to_real zero_ne_top).comp
    (tendsto_lintegral_norm_of_dominated_convergence
      F_measurable f_measurable bound_integrable.has_finite_integral h_bound h_lim),
  -- Use the sandwich theorem
  refine squeeze_zero (λ n, norm_nonneg _) _ lintegral_norm_tendsto_zero,
  -- Show `∥∫ a, F n a - ∫ f∥ ≤ ∫ a, ∥F n a - f a∥` for all `n`
  { assume n,
    have h₁ : integrable (F n) μ := bound_integrable.mono' (F_measurable n) (h_bound _),
    have h₂ : integrable f μ :=
    ⟨f_measurable, has_finite_integral_of_dominated_convergence
      bound_integrable.has_finite_integral h_bound h_lim⟩,
    rw ← integral_sub h₁ h₂,
    exact norm_integral_le_lintegral_norm _ }
end

/-- Lebesgue dominated convergence theorem for filters with a countable basis -/
lemma tendsto_integral_filter_of_dominated_convergence {ι} {l : filter ι}
  {F : ι → α → E} {f : α → E} (bound : α → ℝ)
  (hl_cb : l.is_countably_generated)
  (hF_meas : ∀ᶠ n in l, ae_measurable (F n) μ)
  (f_measurable : ae_measurable f μ)
  (h_bound : ∀ᶠ n in l, ∀ᵐ a ∂μ, ∥F n a∥ ≤ bound a)
  (bound_integrable : integrable bound μ)
  (h_lim : ∀ᵐ a ∂μ, tendsto (λ n, F n a) l (𝓝 (f a))) :
  tendsto (λn, ∫ a, F n a ∂μ) l (𝓝 $ ∫ a, f a ∂μ) :=
begin
  rw hl_cb.tendsto_iff_seq_tendsto,
  { intros x xl,
    have hxl, { rw tendsto_at_top' at xl, exact xl },
    have h := inter_mem hF_meas h_bound,
    replace h := hxl _ h,
    rcases h with ⟨k, h⟩,
    rw ← tendsto_add_at_top_iff_nat k,
    refine tendsto_integral_of_dominated_convergence _ _ _ _ _ _,
    { exact bound },
    { intro, refine (h _ _).1, exact nat.le_add_left _ _ },
    { assumption },
    { assumption },
    { intro, refine (h _ _).2, exact nat.le_add_left _ _ },
    { filter_upwards [h_lim],
      assume a h_lim,
      apply @tendsto.comp _ _ _ (λn, x (n + k)) (λn, F n a),
      { assumption },
      rw tendsto_add_at_top_iff_nat,
      assumption } },
end

variables {X : Type*} [topological_space X] [first_countable_topology X]

lemma continuous_at_of_dominated {F : X → α → E} {x₀ : X} {bound : α → ℝ}
  (hF_meas : ∀ᶠ x in 𝓝 x₀, ae_measurable (F x) μ)
  (h_bound : ∀ᶠ x in 𝓝 x₀, ∀ᵐ a ∂μ, ∥F x a∥ ≤ bound a)
  (bound_integrable : integrable bound μ) (h_cont : ∀ᵐ a ∂μ, continuous_at (λ x, F x a) x₀) :
  continuous_at (λ x, ∫ a, F x a ∂μ) x₀ :=
tendsto_integral_filter_of_dominated_convergence bound
  (first_countable_topology.nhds_generated_countable x₀) ‹_›
    (mem_of_mem_nhds hF_meas : _) ‹_› ‹_› ‹_›

lemma continuous_of_dominated {F : X → α → E} {bound : α → ℝ}
  (hF_meas : ∀ x, ae_measurable (F x) μ) (h_bound : ∀ x, ∀ᵐ a ∂μ, ∥F x a∥ ≤ bound a)
  (bound_integrable : integrable bound μ) (h_cont : ∀ᵐ a ∂μ, continuous (λ x, F x a)) :
  continuous (λ x, ∫ a, F x a ∂μ) :=
continuous_iff_continuous_at.mpr (λ x₀, continuous_at_of_dominated (eventually_of_forall hF_meas)
  (eventually_of_forall h_bound) ‹_› $ h_cont.mono $ λ _, continuous.continuous_at)

/-- The Bochner integral of a real-valued function `f : α → ℝ` is the difference between the
  integral of the positive part of `f` and the integral of the negative part of `f`.  -/
lemma integral_eq_lintegral_pos_part_sub_lintegral_neg_part {f : α → ℝ} (hf : integrable f μ) :
  ∫ a, f a ∂μ =
  ennreal.to_real (∫⁻ a, (ennreal.of_real $ f a) ∂μ) -
  ennreal.to_real (∫⁻ a, (ennreal.of_real $ - f a) ∂μ) :=
let f₁ := hf.to_L1 f in
-- Go to the `L¹` space
have eq₁ : ennreal.to_real (∫⁻ a, (ennreal.of_real $ f a) ∂μ) = ∥Lp.pos_part f₁∥ :=
begin
  rw L1.norm_def,
  congr' 1,
  apply lintegral_congr_ae,
  filter_upwards [Lp.coe_fn_pos_part f₁, hf.coe_fn_to_L1],
  assume a h₁ h₂,
  rw [h₁, h₂, ennreal.of_real],
  congr' 1,
  apply nnreal.eq,
  simp [real.norm_of_nonneg, le_max_right, real.coe_to_nnreal]
end,
-- Go to the `L¹` space
have eq₂ : ennreal.to_real (∫⁻ a, (ennreal.of_real $ - f a) ∂μ)  = ∥Lp.neg_part f₁∥ :=
begin
  rw L1.norm_def,
  congr' 1,
  apply lintegral_congr_ae,
  filter_upwards [Lp.coe_fn_neg_part f₁, hf.coe_fn_to_L1],
  assume a h₁ h₂,
  rw [h₁, h₂, ennreal.of_real],
  congr' 1,
  apply nnreal.eq,
  simp only [real.norm_of_nonneg, min_le_right, neg_nonneg, real.coe_to_nnreal', subtype.coe_mk],
  rw [← max_neg_neg, coe_nnnorm, neg_zero, real.norm_of_nonneg (le_max_right (-f a) 0)]
end,
begin
  rw [eq₁, eq₂, integral, dif_pos],
  exact L1.integral_eq_norm_pos_part_sub _
end

lemma integral_eq_lintegral_of_nonneg_ae {f : α → ℝ} (hf : 0 ≤ᵐ[μ] f) (hfm : ae_measurable f μ) :
  ∫ a, f a ∂μ = ennreal.to_real (∫⁻ a, (ennreal.of_real $ f a) ∂μ) :=
begin
  by_cases hfi : integrable f μ,
  { rw integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfi,
    have h_min : ∫⁻ a, ennreal.of_real (-f a) ∂μ = 0,
    { rw lintegral_eq_zero_iff',
      { refine hf.mono _,
        simp only [pi.zero_apply],
        assume a h,
        simp only [h, neg_nonpos, of_real_eq_zero], },
      { exact measurable_of_real.comp_ae_measurable hfm.neg } },
    rw [h_min, zero_to_real, _root_.sub_zero] },
  { rw integral_undef hfi,
    simp_rw [integrable, hfm, has_finite_integral_iff_norm, lt_top_iff_ne_top, ne.def, true_and,
      not_not] at hfi,
    have : ∫⁻ (a : α), ennreal.of_real (f a) ∂μ = ∫⁻ a, (ennreal.of_real ∥f a∥) ∂μ,
    { refine lintegral_congr_ae (hf.mono $ assume a h, _),
      rw [real.norm_eq_abs, abs_of_nonneg h] },
    rw [this, hfi], refl }
end

lemma of_real_integral_norm_eq_lintegral_nnnorm {G} [normed_group G] [measurable_space G]
  [opens_measurable_space G] {f : α → G} (hf : integrable f μ) :
  ennreal.of_real ∫ x, ∥f x∥ ∂μ = ∫⁻ x, ∥f x∥₊ ∂μ :=
begin
  rw integral_eq_lintegral_of_nonneg_ae _ hf.1.norm,
  { simp_rw [of_real_norm_eq_coe_nnnorm, ennreal.of_real_to_real (lt_top_iff_ne_top.mp hf.2)], },
  { refine ae_of_all _ _, simp, },
end

lemma integral_eq_integral_pos_part_sub_integral_neg_part {f : α → ℝ} (hf : integrable f μ) :
  ∫ a, f a ∂μ = (∫ a, real.to_nnreal (f a) ∂μ) - (∫ a, real.to_nnreal (-f a) ∂μ) :=
begin
  rw [← integral_sub hf.real_to_nnreal],
  { simp },
  { exact hf.neg.real_to_nnreal }
end

lemma integral_nonneg_of_ae {f : α → ℝ} (hf : 0 ≤ᵐ[μ] f) : 0 ≤ ∫ a, f a ∂μ :=
begin
  by_cases hfm : ae_measurable f μ,
  { rw integral_eq_lintegral_of_nonneg_ae hf hfm, exact to_real_nonneg },
  { rw integral_non_ae_measurable hfm }
end

lemma lintegral_coe_eq_integral (f : α → ℝ≥0) (hfi : integrable (λ x, (f x : ℝ)) μ) :
  ∫⁻ a, f a ∂μ = ennreal.of_real ∫ a, f a ∂μ :=
begin
  simp_rw [integral_eq_lintegral_of_nonneg_ae (eventually_of_forall (λ x, (f x).coe_nonneg))
    hfi.ae_measurable, ← ennreal.coe_nnreal_eq], rw [ennreal.of_real_to_real],
  rw [← lt_top_iff_ne_top], convert hfi.has_finite_integral, ext1 x, rw [nnreal.nnnorm_eq]
end

lemma integral_to_real {f : α → ℝ≥0∞} (hfm : ae_measurable f μ) (hf : ∀ᵐ x ∂μ, f x < ∞) :
  ∫ a, (f a).to_real ∂μ = (∫⁻ a, f a ∂μ).to_real :=
begin
  rw [integral_eq_lintegral_of_nonneg_ae _ hfm.ennreal_to_real],
  { rw lintegral_congr_ae, refine hf.mp (eventually_of_forall _),
    intros x hx, rw [lt_top_iff_ne_top] at hx, simp [hx] },
  { exact (eventually_of_forall $ λ x, ennreal.to_real_nonneg) }
end

lemma integral_nonneg {f : α → ℝ} (hf : 0 ≤ f) : 0 ≤ ∫ a, f a ∂μ :=
integral_nonneg_of_ae $ eventually_of_forall hf

lemma integral_nonpos_of_ae {f : α → ℝ} (hf : f ≤ᵐ[μ] 0) : ∫ a, f a ∂μ ≤ 0 :=
begin
  have hf : 0 ≤ᵐ[μ] (-f) := hf.mono (assume a h, by rwa [pi.neg_apply, pi.zero_apply, neg_nonneg]),
  have : 0 ≤ ∫ a, -f a ∂μ := integral_nonneg_of_ae hf,
  rwa [integral_neg, neg_nonneg] at this,
end

lemma integral_nonpos {f : α → ℝ} (hf : f ≤ 0) : ∫ a, f a ∂μ ≤ 0 :=
integral_nonpos_of_ae $ eventually_of_forall hf

lemma integral_eq_zero_iff_of_nonneg_ae {f : α → ℝ} (hf : 0 ≤ᵐ[μ] f) (hfi : integrable f μ) :
  ∫ x, f x ∂μ = 0 ↔ f =ᵐ[μ] 0 :=
by simp_rw [integral_eq_lintegral_of_nonneg_ae hf hfi.1, ennreal.to_real_eq_zero_iff,
  lintegral_eq_zero_iff' (ennreal.measurable_of_real.comp_ae_measurable hfi.1),
  ← ennreal.not_lt_top, ← has_finite_integral_iff_of_real hf, hfi.2, not_true, or_false,
  ← hf.le_iff_eq, filter.eventually_eq, filter.eventually_le, (∘), pi.zero_apply,
  ennreal.of_real_eq_zero]

lemma integral_eq_zero_iff_of_nonneg {f : α → ℝ} (hf : 0 ≤ f) (hfi : integrable f μ) :
  ∫ x, f x ∂μ = 0 ↔ f =ᵐ[μ] 0 :=
integral_eq_zero_iff_of_nonneg_ae (eventually_of_forall hf) hfi

lemma integral_pos_iff_support_of_nonneg_ae {f : α → ℝ} (hf : 0 ≤ᵐ[μ] f) (hfi : integrable f μ) :
  (0 < ∫ x, f x ∂μ) ↔ 0 < μ (function.support f) :=
by simp_rw [(integral_nonneg_of_ae hf).lt_iff_ne, pos_iff_ne_zero, ne.def, @eq_comm ℝ 0,
  integral_eq_zero_iff_of_nonneg_ae hf hfi, filter.eventually_eq, ae_iff, pi.zero_apply,
  function.support]

lemma integral_pos_iff_support_of_nonneg {f : α → ℝ} (hf : 0 ≤ f) (hfi : integrable f μ) :
  (0 < ∫ x, f x ∂μ) ↔ 0 < μ (function.support f) :=
integral_pos_iff_support_of_nonneg_ae (eventually_of_forall hf) hfi

section normed_group
variables {H : Type*} [normed_group H] [second_countable_topology H] [measurable_space H]
          [borel_space H]

lemma L1.norm_eq_integral_norm (f : α →₁[μ] H) : ∥f∥ = ∫ a, ∥f a∥ ∂μ :=
begin
  simp only [snorm, snorm', ennreal.one_to_real, ennreal.rpow_one, Lp.norm_def,
    if_false, ennreal.one_ne_top, one_ne_zero, _root_.div_one],
  rw integral_eq_lintegral_of_nonneg_ae (eventually_of_forall (by simp [norm_nonneg]))
    (continuous_norm.measurable.comp_ae_measurable (Lp.ae_measurable f)),
  simp [of_real_norm_eq_coe_nnnorm]
end

lemma L1.norm_of_fun_eq_integral_norm {f : α → H} (hf : integrable f μ) :
  ∥hf.to_L1 f∥ = ∫ a, ∥f a∥ ∂μ :=
begin
  rw L1.norm_eq_integral_norm,
  refine integral_congr_ae _,
  apply hf.coe_fn_to_L1.mono,
  intros a ha,
  simp [ha]
end

end normed_group

lemma integral_mono_ae {f g : α → ℝ} (hf : integrable f μ) (hg : integrable g μ) (h : f ≤ᵐ[μ] g) :
  ∫ a, f a ∂μ ≤ ∫ a, g a ∂μ :=
le_of_sub_nonneg $ integral_sub hg hf ▸ integral_nonneg_of_ae $ h.mono (λ a, sub_nonneg_of_le)

@[mono] lemma integral_mono {f g : α → ℝ} (hf : integrable f μ) (hg : integrable g μ) (h : f ≤ g) :
  ∫ a, f a ∂μ ≤ ∫ a, g a ∂μ :=
integral_mono_ae hf hg $ eventually_of_forall h

lemma integral_mono_of_nonneg {f g : α → ℝ} (hf : 0 ≤ᵐ[μ] f) (hgi : integrable g μ)
  (h : f ≤ᵐ[μ] g) : ∫ a, f a ∂μ ≤ ∫ a, g a ∂μ :=
begin
  by_cases hfm : ae_measurable f μ,
  { refine integral_mono_ae ⟨hfm, _⟩ hgi h,
    refine (hgi.has_finite_integral.mono $ h.mp $ hf.mono $ λ x hf hfg, _),
    simpa [real.norm_eq_abs, abs_of_nonneg hf, abs_of_nonneg (le_trans hf hfg)] },
  { rw [integral_non_ae_measurable hfm],
    exact integral_nonneg_of_ae (hf.trans h) }
end

lemma norm_integral_le_integral_norm (f : α → E) : ∥(∫ a, f a ∂μ)∥ ≤ ∫ a, ∥f a∥ ∂μ :=
have le_ae : ∀ᵐ a ∂μ, 0 ≤ ∥f a∥ := eventually_of_forall (λa, norm_nonneg _),
classical.by_cases
( λh : ae_measurable f μ,
  calc ∥∫ a, f a ∂μ∥ ≤ ennreal.to_real (∫⁻ a, (ennreal.of_real ∥f a∥) ∂μ) :
      norm_integral_le_lintegral_norm _
    ... = ∫ a, ∥f a∥ ∂μ : (integral_eq_lintegral_of_nonneg_ae le_ae $ ae_measurable.norm h).symm )
( λh : ¬ae_measurable f μ,
  begin
    rw [integral_non_ae_measurable h, norm_zero],
    exact integral_nonneg_of_ae le_ae
  end )

lemma norm_integral_le_of_norm_le {f : α → E} {g : α → ℝ} (hg : integrable g μ)
  (h : ∀ᵐ x ∂μ, ∥f x∥ ≤ g x) : ∥∫ x, f x ∂μ∥ ≤ ∫ x, g x ∂μ :=
calc ∥∫ x, f x ∂μ∥ ≤ ∫ x, ∥f x∥ ∂μ : norm_integral_le_integral_norm f
               ... ≤ ∫ x, g x ∂μ   :
  integral_mono_of_nonneg (eventually_of_forall $ λ x, norm_nonneg _) hg h

lemma integral_finset_sum {ι} (s : finset ι) {f : ι → α → E} (hf : ∀ i, integrable (f i) μ) :
  ∫ a, ∑ i in s, f i a ∂μ = ∑ i in s, ∫ a, f i a ∂μ :=
begin
  refine finset.induction_on s _ _,
  { simp only [integral_zero, finset.sum_empty] },
  { assume i s his ih,
    simp only [his, finset.sum_insert, not_false_iff],
    rw [integral_add (hf _) (integrable_finset_sum s hf), ih] }
end

lemma simple_func.integral_eq_integral (f : α →ₛ E) (hfi : integrable f μ) :
  f.integral μ = ∫ x, f x ∂μ :=
begin
  rw [integral_eq f hfi, ← L1.simple_func.to_Lp_one_eq_to_L1,
    L1.simple_func.integral_L1_eq_integral, L1.simple_func.integral_eq_integral],
  exact simple_func.integral_congr hfi (Lp.simple_func.to_simple_func_to_Lp _ _).symm
end

lemma simple_func.integral_eq_sum (f : α →ₛ E) (hfi : integrable f μ) :
  ∫ x, f x ∂μ = ∑ x in f.range, (ennreal.to_real (μ (f ⁻¹' {x}))) • x :=
by { rw [← f.integral_eq_integral hfi, simple_func.integral, ← simple_func.integral_eq], refl, }

@[simp] lemma integral_const (c : E) : ∫ x : α, c ∂μ = (μ univ).to_real • c :=
begin
  cases (@le_top _ _ (μ univ)).lt_or_eq with hμ hμ,
  { haveI : is_finite_measure μ := ⟨hμ⟩,
    calc ∫ x : α, c ∂μ = (simple_func.const α c).integral μ :
      ((simple_func.const α c).integral_eq_integral (integrable_const _)).symm
    ... = _ : _,
    casesI is_empty_or_nonempty α,
    { rw simple_func.integral,
      simp [μ.eq_zero_of_is_empty], },
    { rw simple_func.integral_eq,
      simp [preimage_const_of_mem], } },
  { by_cases hc : c = 0,
    { simp [hc, integral_zero] },
    { have : ¬integrable (λ x : α, c) μ,
      { simp only [integrable_const_iff, not_or_distrib],
        exact ⟨hc, hμ.not_lt⟩ },
      simp [integral_undef, *] } }
end

lemma norm_integral_le_of_norm_le_const [is_finite_measure μ] {f : α → E} {C : ℝ}
  (h : ∀ᵐ x ∂μ, ∥f x∥ ≤ C) :
  ∥∫ x, f x ∂μ∥ ≤ C * (μ univ).to_real :=
calc ∥∫ x, f x ∂μ∥ ≤ ∫ x, C ∂μ : norm_integral_le_of_norm_le (integrable_const C) h
               ... = C * (μ univ).to_real : by rw [integral_const, smul_eq_mul, mul_comm]

lemma tendsto_integral_approx_on_univ_of_measurable
  {f : α → E} (fmeas : measurable f) (hf : integrable f μ) :
  tendsto (λ n, (simple_func.approx_on f fmeas univ 0 trivial n).integral μ) at_top
    (𝓝 $ ∫ x, f x ∂μ) :=
begin
  have : tendsto (λ n, ∫ x, simple_func.approx_on f fmeas univ 0 trivial n x ∂μ)
    at_top (𝓝 $ ∫ x, f x ∂μ) :=
    tendsto_integral_of_L1 _ hf
      (eventually_of_forall $ simple_func.integrable_approx_on_univ fmeas hf)
      (simple_func.tendsto_approx_on_univ_L1_nnnorm fmeas hf),
  simpa only [simple_func.integral_eq_integral, simple_func.integrable_approx_on_univ fmeas hf]
end

variable {ν : measure α}

private lemma integral_add_measure_of_measurable
  {f : α → E} (fmeas : measurable f) (hμ : integrable f μ) (hν : integrable f ν) :
  ∫ x, f x ∂(μ + ν) = ∫ x, f x ∂μ + ∫ x, f x ∂ν :=
begin
  have hfi := hμ.add_measure hν,
  refine tendsto_nhds_unique (tendsto_integral_approx_on_univ_of_measurable fmeas hfi) _,
  simpa only [simple_func.integral_add_measure _
    (simple_func.integrable_approx_on_univ fmeas hfi _)]
    using (tendsto_integral_approx_on_univ_of_measurable fmeas hμ).add
      (tendsto_integral_approx_on_univ_of_measurable fmeas hν)
end

lemma integral_add_measure {f : α → E} (hμ : integrable f μ) (hν : integrable f ν) :
  ∫ x, f x ∂(μ + ν) = ∫ x, f x ∂μ + ∫ x, f x ∂ν :=
begin
  have h : ae_measurable f (μ + ν) := hμ.ae_measurable.add_measure hν.ae_measurable,
  let g := h.mk f,
  have A : f =ᵐ[μ + ν] g := h.ae_eq_mk,
  have B : f =ᵐ[μ] g := A.filter_mono (ae_mono (measure.le_add_right (le_refl μ))),
  have C : f =ᵐ[ν] g := A.filter_mono (ae_mono (measure.le_add_left (le_refl ν))),
  calc ∫ x, f x ∂(μ + ν) = ∫ x, g x ∂(μ + ν) : integral_congr_ae A
  ... = ∫ x, g x ∂μ + ∫ x, g x ∂ν :
    integral_add_measure_of_measurable h.measurable_mk ((integrable_congr B).1 hμ)
      ((integrable_congr C).1 hν)
  ... = ∫ x, f x ∂μ + ∫ x, f x ∂ν :
    by { congr' 1, { exact integral_congr_ae B.symm }, { exact integral_congr_ae C.symm } }
end

@[simp] lemma integral_zero_measure {m : measurable_space α} (f : α → E) :
  ∫ x, f x ∂(0 : measure α) = 0 :=
norm_le_zero_iff.1 $ le_trans (norm_integral_le_lintegral_norm f) $ by simp

private lemma integral_smul_measure_aux {f : α → E} {c : ℝ≥0∞}
  (h0 : 0 < c) (hc : c < ∞) (fmeas : measurable f) (hfi : integrable f μ) :
  ∫ x, f x ∂(c • μ) = c.to_real • ∫ x, f x ∂μ :=
begin
  refine tendsto_nhds_unique _
    (tendsto_const_nhds.smul (tendsto_integral_approx_on_univ_of_measurable fmeas hfi)),
  convert tendsto_integral_approx_on_univ_of_measurable fmeas (hfi.smul_measure hc),
  simp only [simple_func.integral_eq, measure.smul_apply, finset.smul_sum, smul_smul,
    ennreal.to_real_mul]
end

@[simp] lemma integral_smul_measure (f : α → E) (c : ℝ≥0∞) :
  ∫ x, f x ∂(c • μ) = c.to_real • ∫ x, f x ∂μ :=
begin
  -- First we consider “degenerate” cases:
  -- `c = 0`
  rcases (zero_le c).eq_or_lt with rfl|h0, { simp },
  -- `f` is not almost everywhere measurable
  by_cases hfm : ae_measurable f μ, swap,
  { have : ¬ (ae_measurable f (c • μ)), by simpa [ne_of_gt h0] using hfm,
    simp [integral_non_ae_measurable, hfm, this] },
  -- `c = ∞`
  rcases (le_top : c ≤ ∞).eq_or_lt with rfl|hc,
  { rw [ennreal.top_to_real, zero_smul],
    by_cases hf : f =ᵐ[μ] 0,
    { have : f =ᵐ[∞ • μ] 0 := ae_smul_measure hf ∞,
      exact integral_eq_zero_of_ae this },
    { apply integral_undef,
      rw [integrable, has_finite_integral, iff_true_intro (hfm.smul_measure ∞), true_and,
          lintegral_smul_measure, top_mul, if_neg],
      { apply lt_irrefl },
      { rw [lintegral_eq_zero_iff' hfm.ennnorm],
        refine λ h, hf (h.mono $ λ x, _),
        simp } } },
  -- `f` is not integrable and `0 < c < ∞`
  by_cases hfi : integrable f μ, swap,
  { rw [integral_undef hfi, smul_zero],
    refine integral_undef (mt (λ h, _) hfi),
    convert h.smul_measure (ennreal.inv_lt_top.2 h0),
    rw [smul_smul, ennreal.inv_mul_cancel (ne_of_gt h0) (ne_of_lt hc), one_smul] },
  -- Main case: `0 < c < ∞`, `f` is almost everywhere measurable and integrable
  let g := hfm.mk f,
  calc ∫ x, f x ∂(c • μ) = ∫ x, g x ∂(c • μ) : integral_congr_ae $ ae_smul_measure hfm.ae_eq_mk c
  ... = c.to_real • ∫ x, g x ∂μ :
    integral_smul_measure_aux h0 hc hfm.measurable_mk $ hfi.congr hfm.ae_eq_mk
  ... = c.to_real • ∫ x, f x ∂μ :
    by { congr' 1, exact integral_congr_ae (hfm.ae_eq_mk.symm) }
end

lemma integral_map_of_measurable {β} [measurable_space β] {φ : α → β} (hφ : measurable φ)
  {f : β → E} (hfm : measurable f) :
  ∫ y, f y ∂(measure.map φ μ) = ∫ x, f (φ x) ∂μ :=
begin
  by_cases hfi : integrable f (measure.map φ μ), swap,
  { rw [integral_undef hfi, integral_undef],
    rwa [← integrable_map_measure hfm.ae_measurable hφ] },
  refine tendsto_nhds_unique (tendsto_integral_approx_on_univ_of_measurable hfm hfi) _,
  convert tendsto_integral_approx_on_univ_of_measurable (hfm.comp hφ)
    ((integrable_map_measure hfm.ae_measurable hφ).1 hfi),
  ext1 i,
  simp only [simple_func.approx_on_comp, simple_func.integral_eq, measure.map_apply, hφ,
    simple_func.measurable_set_preimage, ← preimage_comp, simple_func.coe_comp],
  refine (finset.sum_subset (simple_func.range_comp_subset_range _ hφ) (λ y _ hy, _)).symm,
  rw [simple_func.mem_range, ← set.preimage_singleton_eq_empty, simple_func.coe_comp] at hy,
  simp [hy]
end

lemma integral_map {β} [measurable_space β] {φ : α → β} (hφ : measurable φ)
  {f : β → E} (hfm : ae_measurable f (measure.map φ μ)) :
  ∫ y, f y ∂(measure.map φ μ) = ∫ x, f (φ x) ∂μ :=
let g := hfm.mk f in calc
∫ y, f y ∂(measure.map φ μ) = ∫ y, g y ∂(measure.map φ μ) : integral_congr_ae hfm.ae_eq_mk
... = ∫ x, g (φ x) ∂μ : integral_map_of_measurable hφ hfm.measurable_mk
... = ∫ x, f (φ x) ∂μ : integral_congr_ae $ ae_eq_comp hφ (hfm.ae_eq_mk).symm

lemma integral_map_of_closed_embedding {β} [topological_space α] [borel_space α]
  [topological_space β] [measurable_space β] [borel_space β]
  {φ : α → β} (hφ : closed_embedding φ) (f : β → E) :
  ∫ y, f y ∂(measure.map φ μ) = ∫ x, f (φ x) ∂μ :=
begin
  by_cases hfm : ae_measurable f (measure.map φ μ),
  { exact integral_map hφ.continuous.measurable hfm },
  { rw [integral_non_ae_measurable hfm, integral_non_ae_measurable],
    rwa ae_measurable_comp_right_iff_of_closed_embedding hφ }
end

lemma integral_dirac' [measurable_space α] (f : α → E) (a : α) (hfm : measurable f) :
  ∫ x, f x ∂(measure.dirac a) = f a :=
calc ∫ x, f x ∂(measure.dirac a) = ∫ x, f a ∂(measure.dirac a) :
  integral_congr_ae $ ae_eq_dirac' hfm
... = f a : by simp [measure.dirac_apply_of_mem]

lemma integral_dirac [measurable_space α] [measurable_singleton_class α] (f : α → E) (a : α) :
  ∫ x, f x ∂(measure.dirac a) = f a :=
calc ∫ x, f x ∂(measure.dirac a) = ∫ x, f a ∂(measure.dirac a) :
  integral_congr_ae $ ae_eq_dirac f
... = f a : by simp [measure.dirac_apply_of_mem]

end properties

section group

variables {G : Type*} [measurable_space G] [topological_space G] [group G] [has_continuous_mul G]
  [borel_space G]
variables {μ : measure G}

open measure

/-- Translating a function by left-multiplication does not change its integral with respect to a
left-invariant measure. -/
@[to_additive]
lemma integral_mul_left_eq_self (hμ : is_mul_left_invariant μ) {f : G → E} (g : G) :
  ∫ x, f (g * x) ∂μ = ∫ x, f x ∂μ :=
begin
  have hgμ : measure.map (has_mul.mul g) μ = μ,
  { rw ← map_mul_left_eq_self at hμ,
    exact hμ g },
  have h_mul : closed_embedding (λ x, g * x) := (homeomorph.mul_left g).closed_embedding,
  rw [← integral_map_of_closed_embedding h_mul, hgμ],
  apply_instance,
end

/-- Translating a function by right-multiplication does not change its integral with respect to a
right-invariant measure. -/
@[to_additive]
lemma integral_mul_right_eq_self (hμ : is_mul_right_invariant μ) {f : G → E} (g : G) :
  ∫ x, f (x * g) ∂μ = ∫ x, f x ∂μ :=
begin
  have hgμ : measure.map (λ x, x * g) μ = μ,
  { rw ← map_mul_right_eq_self at hμ,
    exact hμ g },
  have h_mul : closed_embedding (λ x, x * g) := (homeomorph.mul_right g).closed_embedding,
  rw [← integral_map_of_closed_embedding h_mul, hgμ],
  apply_instance,
end

/-- If some left-translate of a function negates it, then the integral of the function with respect
to a left-invariant measure is 0. -/
@[to_additive]
lemma integral_zero_of_mul_left_eq_neg (hμ : is_mul_left_invariant μ) {f : G → E} {g : G}
  (hf' : ∀ x, f (g * x) = - f x) :
  ∫ x, f x ∂μ = 0 :=
begin
  refine eq_zero_of_eq_neg ℝ (eq.symm _),
  have : ∫ x, f (g * x) ∂μ = ∫ x, - f x ∂μ,
  { congr,
    ext x,
    exact hf' x },
  convert integral_mul_left_eq_self hμ g using 1,
  rw [this, integral_neg]
end

/-- If some right-translate of a function negates it, then the integral of the function with respect
to a right-invariant measure is 0. -/
@[to_additive]
lemma integral_zero_of_mul_right_eq_neg (hμ : is_mul_right_invariant μ) {f : G → E} {g : G}
  (hf' : ∀ x, f (x * g) = - f x) :
  ∫ x, f x ∂μ = 0 :=
begin
  refine eq_zero_of_eq_neg ℝ (eq.symm _),
  have : ∫ x, f (x * g) ∂μ = ∫ x, - f x ∂μ,
  { congr,
    ext x,
    exact hf' x },
  convert integral_mul_right_eq_self hμ g using 1,
  rw [this, integral_neg]
end

end group

mk_simp_attribute integral_simps "Simp set for integral rules."

attribute [integral_simps] integral_neg integral_smul L1.integral_add L1.integral_sub
  L1.integral_smul L1.integral_neg

attribute [irreducible] integral L1.integral

section integral_trim

variables {H β γ : Type*} [normed_group H] [measurable_space H]
  {m m0 : measurable_space β} {μ : measure β}

/-- Simple function seen as simple function of a larger `measurable_space`. -/
def simple_func.to_larger_space (hm : m ≤ m0) (f : @simple_func β m γ) : simple_func β γ :=
⟨@simple_func.to_fun β m γ f, λ x, hm _ (@simple_func.measurable_set_fiber β γ m f x),
  @simple_func.finite_range β γ m f⟩

lemma simple_func.coe_to_larger_space_eq (hm : m ≤ m0) (f : @simple_func β m γ) :
  ⇑(f.to_larger_space hm) = f :=
rfl

lemma integral_simple_func_larger_space (hm : m ≤ m0) (f : @simple_func β m F)
  (hf_int : integrable f μ) :
  ∫ x, f x ∂μ = ∑ x in (@simple_func.range β F m f), (ennreal.to_real (μ (f ⁻¹' {x}))) • x :=
begin
  simp_rw ← f.coe_to_larger_space_eq hm,
  have hf_int : integrable (f.to_larger_space hm) μ, by rwa simple_func.coe_to_larger_space_eq,
  rw simple_func.integral_eq_sum _ hf_int,
  congr,
end

lemma integral_trim_simple_func (hm : m ≤ m0) (f : @simple_func β m F) (hf_int : integrable f μ) :
  ∫ x, f x ∂μ = ∫ x, f x ∂(μ.trim hm) :=
begin
  have hf : @measurable _ _ m _ f, from @simple_func.measurable β F m _ f,
  have hf_int_m := hf_int.trim hm hf,
  rw [integral_simple_func_larger_space le_rfl f hf_int_m,
    integral_simple_func_larger_space hm f hf_int],
  congr,
  ext1 x,
  congr,
  exact (trim_measurable_set_eq hm (@simple_func.measurable_set_fiber β F m f x)).symm,
end

lemma integral_trim (hm : m ≤ m0) {f : β → F} (hf : @measurable β F m _ f) :
  ∫ x, f x ∂μ = ∫ x, f x ∂(μ.trim hm) :=
begin
  by_cases hf_int : integrable f μ,
  swap,
  { have hf_int_m : ¬ integrable f (μ.trim hm),
      from λ hf_int_m, hf_int (integrable_of_integrable_trim hm hf_int_m),
    rw [integral_undef hf_int, integral_undef hf_int_m], },
  let f_seq := @simple_func.approx_on F β _ _ _ m _ hf set.univ 0 (set.mem_univ 0) _,
  have hf_seq_meas : ∀ n, @measurable _ _ m _ (f_seq n),
    from λ n, @simple_func.measurable β F m _ (f_seq n),
  have hf_seq_int : ∀ n, integrable (f_seq n) μ,
    from simple_func.integrable_approx_on_univ (hf.mono hm le_rfl) hf_int,
  have hf_seq_int_m : ∀ n, integrable (f_seq n) (μ.trim hm),
    from λ n, (hf_seq_int n).trim hm (hf_seq_meas n) ,
  have hf_seq_eq : ∀ n, ∫ x, f_seq n x ∂μ = ∫ x, f_seq n x ∂(μ.trim hm),
    from λ n, integral_trim_simple_func hm (f_seq n) (hf_seq_int n),
  have h_lim_1 : at_top.tendsto (λ n, ∫ x, f_seq n x ∂μ) (𝓝 (∫ x, f x ∂μ)),
  { refine tendsto_integral_of_L1 f hf_int (eventually_of_forall hf_seq_int) _,
    exact simple_func.tendsto_approx_on_univ_L1_nnnorm (hf.mono hm le_rfl) hf_int, },
  have h_lim_2 :  at_top.tendsto (λ n, ∫ x, f_seq n x ∂μ) (𝓝 (∫ x, f x ∂(μ.trim hm))),
  { simp_rw hf_seq_eq,
    refine @tendsto_integral_of_L1 β F _ _ _ _ _ _ m (μ.trim hm) _ f
      (hf_int.trim hm hf) _ _ (eventually_of_forall hf_seq_int_m) _,
    exact @simple_func.tendsto_approx_on_univ_L1_nnnorm β F m _ _ _ _ f _ hf (hf_int.trim hm hf), },
  exact tendsto_nhds_unique h_lim_1 h_lim_2,
end

lemma integral_trim_ae (hm : m ≤ m0) {f : β → F} (hf : ae_measurable f (μ.trim hm)) :
  ∫ x, f x ∂μ = ∫ x, f x ∂(μ.trim hm) :=
begin
  rw [integral_congr_ae (ae_eq_of_ae_eq_trim hf.ae_eq_mk), integral_congr_ae hf.ae_eq_mk],
  exact integral_trim hm hf.measurable_mk,
end

lemma ae_eq_trim_of_measurable [measurable_space γ] [add_group γ] [measurable_singleton_class γ]
  [has_measurable_sub₂ γ] (hm : m ≤ m0) {f g : β → γ} (hf : @measurable _ _ m _ f)
  (hg : @measurable _ _ m _ g) (hfg : f =ᵐ[μ] g) :
  f =ᵐ[μ.trim hm] g :=
begin
  rwa [eventually_eq, ae_iff, trim_measurable_set_eq hm _],
  exact (@measurable_set.compl β _ m (@measurable_set_eq_fun β m γ _ _ _ _ _ _ hf hg)),
end

lemma ae_eq_trim_iff [measurable_space γ] [add_group γ] [measurable_singleton_class γ]
  [has_measurable_sub₂ γ]
  (hm : m ≤ m0) {f g : β → γ} (hf : @measurable _ _ m _ f) (hg : @measurable _ _ m _ g) :
  f =ᵐ[μ.trim hm] g ↔ f =ᵐ[μ] g :=
⟨ae_eq_of_ae_eq_trim, ae_eq_trim_of_measurable hm hf hg⟩

end integral_trim

end measure_theory
