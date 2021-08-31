/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov, Sébastien Gouëzel
-/
import measure_theory.function.simple_func_dense
import measure_theory.function.l1_space
import measure_theory.group.basic
import analysis.normed_space.bounded_linear_maps
import topology.sequences

/-!
# Bochner integral

The Bochner integral extends the definition of the Lebesgue integral to functions that map from a
measure space into a Banach space (complete normed vector space). It is constructed here by
extending the integral on simple functions.

## Main definitions

The Bochner integral is defined following these steps:

1. Define the integral on simple functions of the type `simple_func α E` (notation : `α →ₛ E`)
  where `E` is a real normed space.

  (See `simple_func.bintegral` and section `bintegral` for details. Also see `simple_func.integral`
  for the integral on simple functions of the type `simple_func α ℝ≥0∞`.)

2. Transfer this definition to define the integral on `L1.simple_func α E` (notation :
  `α →₁ₛ[μ] E`), see `L1.simple_func.integral`. Show that this integral is a continuous linear
  map from `α →₁ₛ[μ] E` to `E`.

3. Define the Bochner integral on L1 functions by extending the integral on integrable simple
  functions `α →₁ₛ[μ] E` using `continuous_linear_map.extend` and the fact that the embedding of
  `α →₁ₛ[μ] E` into `α →₁[μ] E` is dense.

4. Define the Bochner integral on functions as the Bochner integral of its equivalence class in L1
  space, if it is in L1, and 0 otherwise.

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

One method is to use the theorem `integrable.induction` in the file `simple_func_dense`, which
allows you to prove something for an arbitrary measurable + integrable function.

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
* `∫ a, f a` : integral of `f` with respect to `volume`, the default measure on the
                    ambient type

We also define notations for integral on a set, which are described in the file
`measure_theory/set_integral`.

Note : `ₛ` is typed using `\_s`. Sometimes it shows as a box if font is missing.

## Tags

Bochner integral, simple function, function space, Lebesgue dominated convergence theorem

-/

noncomputable theory
open_locale classical topological_space big_operators nnreal ennreal measure_theory pointwise
open set filter topological_space ennreal emetric

local attribute [instance] fact_one_le_one_ennreal

namespace measure_theory

variables {α E F 𝕜 : Type*}

section weighted_smul

variables [normed_group F] [normed_space ℝ F] {m : measurable_space α} {μ : measure α}

def weighted_smul {m : measurable_space α} (μ : measure α) (s : set α) : F →L[ℝ] F :=
{ to_fun := λ x, (μ s).to_real • x, map_add' := by simp, map_smul' := λ c x, by rw smul_comm, }

@[simp] lemma weighted_smul_zero {m : measurable_space α} (μ : measure α) (s : set α) :
  weighted_smul μ s (0 : F) = 0 :=
by simp [weighted_smul]

lemma weighted_smul_apply {m : measurable_space α} (μ : measure α) (s : set α) (x : F) :
  weighted_smul μ s x = (μ s).to_real • x :=
rfl

@[simp] lemma weighted_smul_empty {m : measurable_space α} (μ : measure α) :
  weighted_smul μ ∅ = (0 : F →L[ℝ] F) :=
by { ext1 x, rw [weighted_smul_apply, measure_empty], simp, }

lemma weighted_smul_congr (s t : set α) (hst : μ s = μ t) :
  (weighted_smul μ s : F →L[ℝ] F) = weighted_smul μ t :=
by { ext1 x, simp_rw weighted_smul_apply, congr' 2, }

lemma weighted_smul_null {s : set α} (h_zero : μ s = 0) :
  (weighted_smul μ s : F →L[ℝ] F) = 0 :=
by { ext1 x, rw [weighted_smul_apply, h_zero], simp, }

lemma weighted_smul_union (s t : set α) (hs : measurable_set s) (ht : measurable_set t)
  (hs_finite : μ s ≠ ∞) (ht_finite : μ t ≠ ∞) (h_inter : s ∩ t = ∅) :
  (weighted_smul μ (s ∪ t) : F →L[ℝ] F) = weighted_smul μ s + weighted_smul μ t :=
begin
  ext1 x,
  simp_rw [continuous_linear_map.add_apply, weighted_smul_apply,
    measure_union (set.disjoint_iff_inter_eq_empty.mpr h_inter) hs ht,
    ennreal.to_real_add hs_finite ht_finite, add_smul],
end

lemma norm_weighted_smul (s : set α) :
  ∥(weighted_smul μ s : F →L[ℝ] F)∥ ≤ (μ s).to_real :=
begin
  refine continuous_linear_map.op_norm_le_bound _ ennreal.to_real_nonneg (λ x, le_of_eq _),
  rw [weighted_smul_apply, norm_smul, real.norm_eq_abs, abs_of_nonneg ennreal.to_real_nonneg],
end

end weighted_smul

section to_be_moved

variables {m : measurable_space α} {μ : measure α} {s t : set α}

lemma measure_union_lt_top (hs : μ s < ∞) (ht : μ t < ∞) : μ (s ∪ t) < ∞ :=
(measure_union_le s t).trans_lt (ennreal.add_lt_top.mpr ⟨hs, ht⟩)

lemma measure_union_lt_top_iff : μ (s ∪ t) < ∞ ↔ μ s < ∞ ∧ μ t < ∞ :=
begin
  refine ⟨λ h, ⟨_, _⟩, λ h, measure_union_lt_top h.1 h.2⟩,
  { exact (measure_mono (set.subset_union_left s t)).trans_lt h, },
  { exact (measure_mono (set.subset_union_right s t)).trans_lt h, },
end

lemma measure_union_ne_top (hs : μ s ≠ ∞) (ht : μ t ≠ ∞) : μ (s ∪ t) ≠ ∞ :=
((measure_union_le s t).trans_lt (lt_top_iff_ne_top.mpr (ennreal.add_ne_top.mpr ⟨hs, ht⟩))).ne

lemma measure_inter_lt_top (hs_finite : μ s < ∞) : μ (s ∩ t) < ∞ :=
(measure_mono (set.inter_subset_left s t)).trans_lt hs_finite

lemma measure_inter_ne_top (hs_finite : μ s ≠ ∞) : μ (s ∩ t) ≠ ∞ :=
(measure_inter_lt_top (lt_top_iff_ne_top.mpr hs_finite)).ne

lemma set_finset_union_bUnion {α ι} (S : ι → set α) (s : finset ι) (a : ι) :
  (⋃ (i : ι) (H : i ∈ insert a s), S i) = S a ∪ ⋃ (i : ι) (H : i ∈ s), S i :=
begin
  ext1 x,
  simp_rw [set.mem_union, set.mem_Union],
  split; intro h,
  { obtain ⟨i, hi, hxi⟩ := h,
    rw finset.mem_insert at hi,
    cases hi,
    { rw ← hi,
      exact or.inl hxi, },
    { exact or.inr ⟨i, hi, hxi⟩, }, },
  { cases h,
    { use [a, finset.mem_insert_self a s, h], },
    { obtain ⟨i, hi, hxi⟩ := h,
      use [i, finset.mem_insert_of_mem hi, hxi], }, },
end

end to_be_moved

local infixr ` →ₛ `:25 := simple_func

namespace simple_func

section pos_part
variables [linear_order E] [has_zero E] [measurable_space α]

/-- Positive part of a simple function. -/
def pos_part (f : α →ₛ E) : α →ₛ E := f.map (λb, max b 0)

/-- Negative part of a simple function. -/
def neg_part [has_neg E] (f : α →ₛ E) : α →ₛ E := pos_part (-f)

lemma pos_part_map_norm (f : α →ₛ ℝ) : (pos_part f).map norm = pos_part f :=
begin
  ext,
  rw [map_apply, real.norm_eq_abs, abs_of_nonneg],
  rw [pos_part, map_apply],
  exact le_max_right _ _
end

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
  {G G' F' : Type*} [normed_group G] [normed_group G'] [normed_group F'] [normed_space ℝ F']
  {m : measurable_space α} {μ : measure α}

def extend_op [normed_space ℝ G] {m : measurable_space α}
  (T : set α → (F →L[ℝ] G)) (f : α →ₛ F) : G :=
∑ x in f.range, T (f ⁻¹' {x}) x

/-- Bochner integral of simple functions whose codomain is a real `normed_space`. -/
def integral {m : measurable_space α} (μ : measure α) (f : α →ₛ F) : F :=
∑ x in f.range, (μ (f ⁻¹' {x})).to_real • x

lemma integral_eq_extend_op {m : measurable_space α} (μ : measure α) (f : α →ₛ F) :
  f.integral μ = f.extend_op (weighted_smul μ) :=
by simp [integral, extend_op, weighted_smul]

lemma integral_eq_sum_filter {m : measurable_space α} (f : α →ₛ F) (μ : measure α) :
  f.integral μ = ∑ x in f.range.filter (λ x, x ≠ 0),  (μ (f ⁻¹' {x})).to_real • x :=
eq.symm $ sum_filter_of_ne $ λ x _, mt $ λ h0, h0.symm ▸ smul_zero _

/-- The Bochner integral is equal to a sum over any set that includes `f.range` (except `0`). -/
lemma integral_eq_sum_of_subset {f : α →ₛ F} {s : finset F}
  (hs : f.range.filter (λ x, x ≠ 0) ⊆ s) : f.integral μ = ∑ x in s, (μ (f ⁻¹' {x})).to_real • x :=
begin
  rw [simple_func.integral_eq_sum_filter, finset.sum_subset hs],
  rintro x - hx, rw [finset.mem_filter, not_and_distrib, ne.def, not_not] at hx,
  rcases hx with hx|rfl; [skip, simp],
  rw [simple_func.mem_range] at hx, rw [preimage_eq_empty]; simp [disjoint_singleton_left, hx]
end

lemma T_Union_fin_meas_set {β} [add_comm_monoid β] (T : set α → β) (T_empty : T ∅ = 0)
  (h_add : ∀ (s t : set α) (hs : measurable_set s) (ht : measurable_set t)
    (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞) (h : s ∩ t = ∅), T (s ∪ t) = T s + T t)
  {ι} (S : ι → set α) (sι : finset ι) (hS_meas : ∀ i, measurable_set (S i))
  (hSp : ∀ i ∈ sι, μ (S i) ≠ ∞) (h_disj : ∀ i j ∈ sι, i ≠ j → disjoint (S i) (S j)) :
  T (⋃ i ∈ sι, S i) = ∑ i in sι, T (S i) :=
begin
  revert hSp h_disj,
  refine finset.induction_on sι _ _,
  { simp only [finset.not_mem_empty, forall_false_left, Union_false, Union_empty, sum_empty,
    forall_2_true_iff, implies_true_iff, forall_true_left, not_false_iff, T_empty], },
  intros a s has h hps h_disj,
  rw finset.sum_insert has,
  rw ← h,
  swap, { exact λ i hi, hps i (finset.mem_insert_of_mem hi), },
  swap, { exact λ i j hi hj hij,
    h_disj i j (finset.mem_insert_of_mem hi) (finset.mem_insert_of_mem hj) hij, },
  rw ← h_add (S a) (⋃ i ∈ s, S i) (hS_meas a) (measurable_set_bUnion _ (λ i _, hS_meas i))
    (hps a (finset.mem_insert_self a s)),
  { congr, rw set_finset_union_bUnion, },
  { exact ((measure_bUnion_finset_le _ _).trans_lt
      (ennreal.sum_lt_top (λ i hi, lt_top_iff_ne_top.mpr
      (hps i (finset.mem_insert_of_mem hi))))).ne, },
  { simp_rw set.inter_Union,
    rw Union_eq_empty,
    intro i,
    rw Union_eq_empty,
    intro hi,
    rw ← set.disjoint_iff_inter_eq_empty,
    refine h_disj a i (finset.mem_insert_self a s) (finset.mem_insert_of_mem hi) (λ hai, _),
    rw ← hai at hi,
    exact has hi, },
end

lemma map_extend_op (T : set α → (F →L[ℝ] F')) (T_empty : T ∅ = 0)
  (h_add : ∀ (s t : set α) (hs : measurable_set s) (ht : measurable_set t)
    (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞) (h : s ∩ t = ∅), T (s ∪ t) = T s + T t)
  {f : α →ₛ E} (hf : integrable f μ) {g : E → F} (hg : g 0 = 0) :
  (f.map g).extend_op T = ∑ x in f.range, T (f ⁻¹' {x}) (g x) :=
begin
  have hfp : ∀ x ∈ f.range, x ≠ 0 → μ (f ⁻¹' {x}) ≠ ∞,
    from λ x hx hx0, (measure_preimage_lt_top_of_integrable f hf hx0).ne,
  simp only [extend_op, range_map],
  refine finset.sum_image' _ (assume b hb, _),
  rcases mem_range.1 hb with ⟨a, rfl⟩,
  by_cases h0 : g (f a) = 0,
  { simp_rw h0,
    rw [continuous_linear_map.map_zero, finset.sum_eq_zero (λ x hx, _)],
    rw mem_filter at hx,
    rw [hx.2, continuous_linear_map.map_zero], },
  have h_left_eq : T ((map g f) ⁻¹' {g (f a)}) (g (f a))
    = T (f ⁻¹' ↑(f.range.filter (λ b, g b = g (f a)))) (g (f a)),
  { congr, rw map_preimage_singleton, },
  rw h_left_eq,
  have h_left_eq' : T (f ⁻¹' ↑(filter (λ (b : E), g b = g (f a)) f.range)) (g (f a))
    = T (⋃ y ∈ (filter (λ (b : E), g b = g (f a)) f.range), f ⁻¹' {y}) (g (f a)),
  { congr, rw ← finset.set_bUnion_preimage_singleton, },
  rw h_left_eq',
  rw T_Union_fin_meas_set T T_empty h_add,
  { simp only [filter_congr_decidable, sum_apply, continuous_linear_map.coe_sum'],
    refine finset.sum_congr rfl (λ x hx, _),
    rw mem_filter at hx,
    rw hx.2, },
  { exact λ i, measurable_set_fiber _ _, },
  { intros i hi,
    rw mem_filter at hi,
    refine hfp i hi.1 (λ hi0, _),
    rw [hi0, hg] at hi,
    exact h0 hi.2.symm, },
  { intros i j hi hj hij,
    rw set.disjoint_iff,
    intros x hx,
    rw [set.mem_inter_iff, set.mem_preimage, set.mem_preimage, set.mem_singleton_iff,
      set.mem_singleton_iff] at hx,
    rw [← hx.1, ← hx.2] at hij,
    exact absurd rfl hij, },
end

/-- Calculate the integral of `g ∘ f : α →ₛ F`, where `f` is an integrable function from `α` to `E`
    and `g` is a function from `E` to `F`. We require `g 0 = 0` so that `g ∘ f` is integrable. -/
lemma map_integral (f : α →ₛ E) (g : E → F) (hf : integrable f μ) (hg : g 0 = 0) :
  (f.map g).integral μ = ∑ x in f.range, (ennreal.to_real (μ (f ⁻¹' {x}))) • (g x) :=
begin
  rw integral_eq_extend_op,
  exact map_extend_op (weighted_smul μ) (weighted_smul_empty μ) weighted_smul_union hf hg,
end

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

lemma extend_op_congr' (T : set α → (E →L[ℝ] F)) (T_empty : T ∅ = 0)
  (h_add : ∀ (s t : set α) (hs : measurable_set s) (ht : measurable_set t)
    (hμs : μ s ≠ ∞) (hpt : μ t ≠ ∞) (h : s ∩ t = ∅), T (s ∪ t) = T s + T t)
  {f g : α →ₛ E} (hf : integrable f μ) (hg : integrable g μ)
  (h : ∀ x y, x ≠ y → T ((f ⁻¹' {x}) ∩ (g ⁻¹' {y})) = 0) :
  f.extend_op T = g.extend_op T :=
show ((pair f g).map prod.fst).extend_op T = ((pair f g).map prod.snd).extend_op T, from
begin
  have h_pair : integrable (f.pair g) μ, from integrable_pair hf hg,
  rw map_extend_op T T_empty h_add h_pair prod.fst_zero,
  rw map_extend_op T T_empty h_add h_pair prod.snd_zero,
  refine finset.sum_congr rfl (λ p hp, _),
  rcases mem_range.1 hp with ⟨a, rfl⟩,
  by_cases eq : f a = g a,
  { dsimp only [pair_apply], rw eq },
  { have : T ((pair f g) ⁻¹' {(f a, g a)}) = 0,
    { have h_eq : T (⇑(f.pair g) ⁻¹' {(f a, g a)}) = T ((f ⁻¹' {f a}) ∩ (g ⁻¹' {g a})),
      { congr, rw pair_preimage_singleton f g, },
      rw h_eq,
      exact h (f a) (g a) eq, },
    simp only [this, continuous_linear_map.zero_apply, pair_apply], },
end

lemma extend_op_congr {m : measurable_space α} (μ : measure α)
  (T : set α → (E →L[ℝ] F)) (h_zero : ∀ s (hs : measurable_set s) (hs_zero : μ s = 0), T s = 0)
  (h_add : ∀ (s t : set α) (hs : measurable_set s) (ht : measurable_set t)
    (hps : μ s ≠ ∞) (hpt : μ t ≠ ∞) (h : s ∩ t = ∅), T (s ∪ t) = T s + T t)
  {f g : α →ₛ E} (hf : integrable f μ) (h : f =ᵐ[μ] g) :
  f.extend_op T = g.extend_op T :=
begin
  refine extend_op_congr' T (h_zero ∅ measurable_set.empty measure_empty)
    h_add hf ((integrable_congr h).mp hf) _,
  refine λ x y hxy, h_zero _ ((measurable_set_fiber f x).inter (measurable_set_fiber g y)) _,
  rw [eventually_eq, ae_iff] at h,
  refine measure_mono_null (λ z, _) h,
  simp_rw [set.mem_inter_iff, set.mem_set_of_eq, set.mem_preimage, set.mem_singleton_iff],
  intro h,
  rwa [h.1, h.2],
end

lemma congr_hyp_of_le_measure (T : set α → (F' →L[ℝ] F)) {C : ℝ}
  (hT_norm : ∀ s, ∥T s∥ ≤ C * (μ s).to_real) {f g : α →ₛ F'} (hfg : f =ᵐ[μ] g)
  (x y : F') (hxy : x ≠ y) :
  T ((f ⁻¹' {x}) ∩ (g ⁻¹' {y})) = 0 :=
begin
  have : μ ((pair f g) ⁻¹' {(x, y)}) = 0,
  { refine measure_mono_null (λ a' ha', _) hfg,
    simp only [set.mem_preimage, mem_singleton_iff, pair_apply, prod.mk.inj_iff] at ha',
    show f a' ≠ g a',
    rwa [ha'.1, ha'.2], },
  rw ← norm_eq_zero,
  refine le_antisymm ((hT_norm _).trans (le_of_eq _)) (norm_nonneg _),
  rw pair_preimage_singleton at this,
  rw this,
  simp,
end

lemma map_fst_pair [measurable_space α] {β} (f g : α →ₛ β) : map prod.fst (f.pair g) = f :=
by { ext, simp only [pair_apply, function.comp_app, coe_map], }

lemma map_snd_pair [measurable_space α] {β} (f g : α →ₛ β) : map prod.snd (f.pair g) = g :=
by { ext, simp only [pair_apply, function.comp_app, coe_map], }

lemma integral_congr {f g : α →ₛ E} (hf : integrable f μ) (h : f =ᵐ[μ] g) :
  f.integral μ = g.integral μ :=
show ((pair f g).map prod.fst).integral μ = ((pair f g).map prod.snd).integral μ, from
extend_op_congr μ (weighted_smul μ) (λ s hs, weighted_smul_null) weighted_smul_union hf
  (by rwa map_snd_pair)

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

lemma extend_op_add (T : set α → (E →L[ℝ] F)) (T_empty : T ∅ = 0)
  (h_add : ∀ (s t : set α) (hs : measurable_set s) (ht : measurable_set t)
    (hps : μ s ≠ ∞) (hpt : μ t ≠ ∞) (h : s ∩ t = ∅), T (s ∪ t) = T s + T t)
  {f g : α →ₛ E} (hf : integrable f μ) (hg : integrable g μ) :
  extend_op T (f + g) = extend_op T f + extend_op T g :=
have hp_pair : integrable (f.pair g) μ, from integrable_pair hf hg,
calc extend_op T (f + g) = ∑ x in (pair f g).range,
       T ((pair f g) ⁻¹' {x}) (x.fst + x.snd) :
  by { rw [add_eq_map₂, map_extend_op T T_empty h_add hp_pair], simp, }
... = ∑ x in (pair f g).range, (T ((pair f g) ⁻¹' {x}) x.fst + T ((pair f g) ⁻¹' {x}) x.snd) :
  finset.sum_congr rfl $ assume a ha, continuous_linear_map.map_add _ _ _
... = ∑ x in (pair f g).range, T ((pair f g) ⁻¹' {x}) x.fst +
      ∑ x in (pair f g).range, T ((pair f g) ⁻¹' {x}) x.snd :
  by rw finset.sum_add_distrib
... = ((pair f g).map prod.fst).extend_op T + ((pair f g).map prod.snd).extend_op T :
  by rw [map_extend_op T T_empty h_add hp_pair prod.snd_zero,
    map_extend_op T T_empty h_add hp_pair prod.fst_zero]


lemma integral_add {f g : α →ₛ E} (hf : integrable f μ) (hg : integrable g μ) :
  integral μ (f + g) = integral μ f + integral μ g :=
begin
  rw integral_eq_extend_op,
  exact extend_op_add _ (weighted_smul_empty μ) weighted_smul_union hf hg,
end

lemma extend_op_neg (T : set α → (E →L[ℝ] F)) (T_empty : T ∅ = 0)
  (h_add : ∀ (s t : set α) (hs : measurable_set s) (ht : measurable_set t)
    (hps : μ s ≠ ∞) (hpt : μ t ≠ ∞) (h : s ∩ t = ∅), T (s ∪ t) = T s + T t)
  {f : α →ₛ E} (hf : integrable f μ) :
  extend_op T (-f) = - extend_op T f :=
calc extend_op T (-f) = extend_op T (f.map (has_neg.neg)) : rfl
  ... = - extend_op T f :
  begin
    rw [map_extend_op T T_empty h_add hf neg_zero, extend_op,
      ← sum_neg_distrib],
    exact finset.sum_congr rfl (λ x h, continuous_linear_map.map_neg _ _),
  end

lemma integral_neg {f : α →ₛ E} (hf : integrable f μ) : integral μ (-f) = - integral μ f :=
begin
  rw integral_eq_extend_op,
  exact extend_op_neg _ (weighted_smul_empty μ) weighted_smul_union hf,
end

lemma neg_singleton {β : Type*} [add_group β] (x : β) : -({x} : set β) = {-x} :=
by { ext1 y, rw [mem_neg, mem_singleton_iff, mem_singleton_iff, neg_eq_iff_neg_eq, eq_comm], }

lemma extend_op_sub (T : set α → (E →L[ℝ] F)) (T_empty : T ∅ = 0)
  (h_add : ∀ (s t : set α) (hs : measurable_set s) (ht : measurable_set t)
    (hps : μ s ≠ ∞) (hpt : μ t ≠ ∞) (h : s ∩ t = ∅), T (s ∪ t) = T s + T t) {f g : α →ₛ E}
  (hf : integrable f μ) (hg : integrable g μ) :
  extend_op T (f - g) = extend_op T f - extend_op T g :=
begin
  rw [sub_eq_add_neg, extend_op_add T T_empty h_add hf,
    extend_op_neg T T_empty h_add hg, sub_eq_add_neg],
  rw integrable_iff at hg ⊢,
  intros x hx_ne,
  change μ ((has_neg.neg ∘ g) ⁻¹' {x}) < ∞,
  rw [preimage_comp, neg_preimage, neg_singleton],
  refine hg (-x) _,
  simp [hx_ne],
end

lemma integral_sub [borel_space E] {f g : α →ₛ E} (hf : integrable f μ) (hg : integrable g μ) :
  integral μ (f - g) = integral μ f - integral μ g :=
by { rw [sub_eq_add_neg, integral_add hf, integral_neg hg, sub_eq_add_neg], exact hg.neg, }

/-- The extension to 𝕜 has to come from something else. -/
lemma extend_op_smul_ℝ (T : set α → (E →L[ℝ] F)) (T_empty : T ∅ = 0)
  (h_add : ∀ (s t : set α) (hs : measurable_set s) (ht : measurable_set t)
    (hps : μ s ≠ ∞) (hpt : μ t ≠ ∞) (h : s ∩ t = ∅), T (s ∪ t) = T s + T t)
  (c : ℝ) {f : α →ₛ E} (hf : integrable f μ) :
  extend_op T (c • f) = c • extend_op T f :=
calc extend_op T (c • f) = ∑ x in f.range, T (f ⁻¹' {x}) (c • x) :
  by { rw [smul_eq_map c f, map_extend_op T T_empty h_add hf], rw smul_zero, }
... = ∑ x in f.range, c • (T (f ⁻¹' {x}) x) :
  finset.sum_congr rfl $ λ b hb, by { rw continuous_linear_map.map_smul (T (f ⁻¹' {b})) c b, }
... = c • extend_op T f :
by simp only [extend_op, smul_sum, smul_smul, mul_comm]

lemma extend_op_smul  {E} [measurable_space E] [normed_group E] [normed_space 𝕜 E]
  [normed_space ℝ E] [normed_space 𝕜 F] (T : set α → (E →L[ℝ] F)) (T_empty : T ∅ = 0)
  (h_add : ∀ (s t : set α) (hs : measurable_set s) (ht : measurable_set t)
    (hps : μ s ≠ ∞) (hpt : μ t ≠ ∞) (h : s ∩ t = ∅), T (s ∪ t) = T s + T t)
  (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x)
  (c : 𝕜) {f : α →ₛ E} (hf : integrable f μ) :
  extend_op T (c • f) = c • extend_op T f :=
calc extend_op T (c • f) = ∑ x in f.range, T (f ⁻¹' {x}) (c • x) :
  by { rw [smul_eq_map c f, map_extend_op T T_empty h_add hf],
    rw smul_zero, }
... = ∑ x in f.range, c • (T (f ⁻¹' {x}) x) : finset.sum_congr rfl $ λ b hb, by { rw h_smul, }
... = c • extend_op T f : by simp only [extend_op, smul_sum, smul_smul, mul_comm]

lemma integral_smul (c : 𝕜) {f : α →ₛ E} (hf : integrable f μ) :
  integral μ (c • f) = c • integral μ f :=
begin
  rw integral_eq_extend_op,
  exact extend_op_smul (weighted_smul μ) (weighted_smul_empty μ)
    weighted_smul_union (λ c s x, by simp_rw [weighted_smul_apply, smul_comm]) c hf,
end

lemma norm_extend_op_le_sum_op_norm {m : measurable_space α}
  (T : set α → (F' →L[ℝ] F)) (f : α →ₛ F') :
  ∥f.extend_op T∥ ≤ ∑ x in f.range, ∥T (f ⁻¹' {x})∥ * ∥x∥ :=
calc ∥∑ x in f.range, T (f ⁻¹' {x}) x∥
    ≤ ∑ x in f.range, ∥T (f ⁻¹' {x}) x∥ : norm_sum_le _ _
... ≤ ∑ x in f.range, ∥T (f ⁻¹' {x})∥ * ∥x∥ :
  by { refine finset.sum_le_sum (λb hb, _), simp_rw continuous_linear_map.le_op_norm, }

lemma norm_extend_op_le_integral_norm (T : set α → (E →L[ℝ] F)) (C : ℝ) (hC : 0 ≤ C)
  (hT_norm : ∀ s, ∥T s∥ ≤ C * (μ s).to_real) {f : α →ₛ E} (hf : integrable f μ) :
  ∥f.extend_op T∥ ≤ C * (f.map norm).integral μ :=
calc ∥f.extend_op T∥
    ≤ ∑ x in f.range, ∥T (f ⁻¹' {x})∥ * ∥x∥ : norm_extend_op_le_sum_op_norm T f
... ≤ ∑ x in f.range, C * ennreal.to_real (μ (f ⁻¹' {x})) • ∥x∥ :
  begin
    refine finset.sum_le_sum (λb hb, _),
    rw [smul_eq_mul, ← mul_assoc],
    exact mul_le_mul (hT_norm _) le_rfl (norm_nonneg _) (mul_nonneg hC ennreal.to_real_nonneg),
  end
... = C * (f.map norm).integral μ : by rw [map_integral f norm hf norm_zero, finset.mul_sum]

lemma norm_integral_le_integral_norm (f : α →ₛ E) (hf : integrable f μ) :
  ∥f.integral μ∥ ≤ (f.map norm).integral μ :=
begin
  rw integral_eq_extend_op,
  refine (norm_extend_op_le_integral_norm _ 1 (by simp) (λ s, _) hf).trans (one_mul _).le,
  exact (norm_weighted_smul s).trans (one_mul _).symm.le,
end

lemma integral_add_measure {ν} (f : α →ₛ E) (hf : integrable f (μ + ν)) :
  f.integral (μ + ν) = f.integral μ + f.integral ν :=
begin
  simp only [integral_eq_sum_filter, ← sum_add_distrib, ← add_smul, measure.add_apply],
  refine sum_congr rfl (λ x hx, _),
  rw [to_real_add];
    refine ne_of_lt ((integrable_iff_fin_meas_supp.1 _).meas_preimage_singleton_ne_zero
      (mem_filter.1 hx).2),
  exacts [hf.left_of_add_measure, hf.right_of_add_measure]
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
  rw [norm_to_simple_func, simple_func.integral_eq_lintegral],
  { simp only [simple_func.map_apply, of_real_norm_eq_coe_nnnorm, snorm_one_eq_lintegral_nnnorm] },
  { exact (simple_func.integrable f).norm },
  { exact eventually_of_forall (λ x, norm_nonneg _) }
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

def indicator_to_L1s (T : set α → (E →L[ℝ] F')) (f : α →₁ₛ[μ] E) : F' :=
(to_simple_func f).extend_op T

local attribute [instance] simple_func.normed_space

/-- The Bochner integral over simple functions in L1 space. -/
def integral (f : α →₁ₛ[μ] E) : E := ((to_simple_func f)).integral μ

lemma indicator_to_L1s_eq_extend_op (T : set α → (E →L[ℝ] F')) (f : α →₁ₛ[μ] E) :
  indicator_to_L1s T f = (to_simple_func f).extend_op T :=
rfl

lemma integral_eq_integral (f : α →₁ₛ[μ] E) : integral f = ((to_simple_func f)).integral μ := rfl

lemma integral_eq_lintegral {f : α →₁ₛ[μ] ℝ} (h_pos : 0 ≤ᵐ[μ] (to_simple_func f)) :
  integral f = ennreal.to_real (∫⁻ a, ennreal.of_real ((to_simple_func f) a) ∂μ) :=
by rw [integral, simple_func.integral_eq_lintegral (simple_func.integrable f) h_pos]

lemma integral_eq_indicator_to_L1s (f : α →₁ₛ[μ] E) :
  integral f = indicator_to_L1s (weighted_smul μ) f :=
by rw [integral_eq_integral, indicator_to_L1s_eq_extend_op, simple_func.integral_eq_extend_op]

lemma indicator_to_L1s_congr (T : set α → (E →L[ℝ] F'))
  (h_zero : ∀ s (hs : measurable_set s) (hs_zero : μ s = 0), T s = 0)
  (h_add : ∀ (s t : set α) (hs : measurable_set s) (ht : measurable_set t)
    (hps : μ s ≠ ∞) (hpt : μ t ≠ ∞) (h : s ∩ t = ∅), T (s ∪ t) = T s + T t)
  {f g : α →₁ₛ[μ] E} (h : to_simple_func f =ᵐ[μ] to_simple_func g) :
  indicator_to_L1s T f = indicator_to_L1s T g :=
simple_func.extend_op_congr μ T h_zero h_add (simple_func.integrable f) h

lemma integral_congr {f g : α →₁ₛ[μ] E} (h : to_simple_func f =ᵐ[μ] to_simple_func g) :
  integral f = integral g :=
simple_func.integral_congr (simple_func.integrable f) h

lemma indicator_to_L1s_add (T : set α → (E →L[ℝ] F'))
  (h_zero : ∀ s (hs : measurable_set s) (hs_zero : μ s = 0), T s = 0)
  (h_add : ∀ (s t : set α) (hs : measurable_set s) (ht : measurable_set t)
    (hps : μ s ≠ ∞) (hpt : μ t ≠ ∞) (h : s ∩ t = ∅), T (s ∪ t) = T s + T t)
  (f g : α →₁ₛ[μ] E) :
  indicator_to_L1s T (f + g) = indicator_to_L1s T f + indicator_to_L1s T g :=
begin
  simp_rw indicator_to_L1s,
  rw ← simple_func.extend_op_add T (h_zero ∅ measurable_set.empty measure_empty) h_add
    (simple_func.integrable f) (simple_func.integrable g),
  exact simple_func.extend_op_congr μ T h_zero h_add (simple_func.integrable _)
    (add_to_simple_func f g),
end

lemma integral_add (f g : α →₁ₛ[μ] E) : integral (f + g) = integral f + integral g :=
begin
  rw integral_eq_indicator_to_L1s,
  exact indicator_to_L1s_add _ (λ _ _, weighted_smul_null) weighted_smul_union _ _,
end

lemma indicator_to_L1s_smul_ℝ (T : set α → (E →L[ℝ] F'))
  (h_zero : ∀ s (hs : measurable_set s) (hs_zero : μ s = 0), T s = 0)
  (h_add : ∀ (s t : set α) (hs : measurable_set s) (ht : measurable_set t)
    (hps : μ s ≠ ∞) (hpt : μ t ≠ ∞) (h : s ∩ t = ∅), T (s ∪ t) = T s + T t)
  (c : ℝ) (f : α →₁ₛ[μ] E) :
  indicator_to_L1s T (c • f) = c • indicator_to_L1s T f :=
begin
  have hT_empty : T ∅ = 0, from h_zero ∅ measurable_set.empty measure_empty,
  simp_rw indicator_to_L1s,
  rw ← simple_func.extend_op_smul_ℝ T hT_empty h_add c (simple_func.integrable f),
  refine simple_func.extend_op_congr μ T h_zero h_add (simple_func.integrable _) _,
  exact smul_to_simple_func c f,
end

lemma indicator_to_L1s_smul {E} [normed_group E] [measurable_space E] [normed_space ℝ E]
  [normed_space 𝕜 E] [second_countable_topology E] [borel_space E] [normed_space 𝕜 F']
  [measurable_space 𝕜] [opens_measurable_space 𝕜]
  (T : set α → (E →L[ℝ] F')) (h_zero : ∀ s (hs : measurable_set s) (hs_zero : μ s = 0), T s = 0)
  (h_add : ∀ (s t : set α) (hs : measurable_set s) (ht : measurable_set t)
    (hps : μ s ≠ ∞) (hpt : μ t ≠ ∞) (h : s ∩ t = ∅), T (s ∪ t) = T s + T t)
  (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x)
  (c : 𝕜) (f : α →₁ₛ[μ] E) :
  indicator_to_L1s T (c • f) = c • indicator_to_L1s T f :=
begin
  have hT_empty : T ∅ = 0, from h_zero ∅ measurable_set.empty measure_empty,
  simp_rw indicator_to_L1s,
  rw ← simple_func.extend_op_smul T hT_empty h_add h_smul c (simple_func.integrable f),
  refine simple_func.extend_op_congr μ T h_zero h_add (simple_func.integrable _) _,
  exact smul_to_simple_func c f,
end

lemma integral_smul [measurable_space 𝕜] [opens_measurable_space 𝕜] (c : 𝕜) (f : α →₁ₛ[μ] E) :
  integral (c • f) = c • integral f :=
begin
  rw integral_eq_indicator_to_L1s,
  exact indicator_to_L1s_smul _ (λ _ _, weighted_smul_null) weighted_smul_union
    (λ c s x, by simp_rw [weighted_smul_apply, smul_comm]) c f,
end

lemma norm_indicator_to_L1s_le (T : set α → (E →L[ℝ] F'))
  {C : ℝ} (hC : 0 ≤ C) (hT_norm : ∀ s, ∥T s∥ ≤ C * (μ s).to_real) (f : α →₁ₛ[μ] E) :
  ∥indicator_to_L1s T f∥ ≤ C * ∥f∥ :=
begin
  rw [indicator_to_L1s, norm_eq_integral],
  exact simple_func.norm_extend_op_le_integral_norm T C hC hT_norm (simple_func.integrable f),
end

lemma norm_integral_le_norm (f : α →₁ₛ[μ] E) : ∥integral f∥ ≤ ∥f∥ :=
begin
  rw [integral, norm_eq_integral],
  exact (to_simple_func f).norm_integral_le_integral_norm (simple_func.integrable f)
end

variables {E' : Type*} [normed_group E'] [second_countable_topology E'] [measurable_space E']
  [borel_space E'] [normed_space ℝ E'] [normed_space 𝕜 E']
  [measurable_space 𝕜] [opens_measurable_space 𝕜]

variables (α E' μ 𝕜)
def indicator_to_L1s_clm' [normed_space 𝕜 F'] (T : set α → (E' →L[ℝ] F'))
  (h_add : ∀ (s t : set α) (hs : measurable_set s) (ht : measurable_set t)
    (hps : μ s ≠ ∞) (hpt : μ t ≠ ∞) (h : s ∩ t = ∅), T (s ∪ t) = T s + T t)
  (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x)
  {C : ℝ} (hC : 0 ≤ C) (hT_norm : ∀ s, ∥T s∥ ≤ C * (μ s).to_real) :
  (α →₁ₛ[μ] E') →L[𝕜] F' :=
have h_zero : ∀ s (hs : measurable_set s) (hs_zero : μ s = 0), T s = 0,
{ refine λ s hs hs0, norm_eq_zero.mp _,
  refine le_antisymm ((hT_norm s).trans (le_of_eq _)) (norm_nonneg _),
  rw [hs0, ennreal.zero_to_real, mul_zero], },
linear_map.mk_continuous ⟨indicator_to_L1s T, indicator_to_L1s_add T h_zero h_add,
  indicator_to_L1s_smul T h_zero h_add h_smul⟩ C (λ f, norm_indicator_to_L1s_le T hC hT_norm f)

def indicator_to_L1s_clm (T : set α → (E' →L[ℝ] F'))
  (h_add : ∀ (s t : set α) (hs : measurable_set s) (ht : measurable_set t)
    (hps : μ s ≠ ∞) (hpt : μ t ≠ ∞) (h : s ∩ t = ∅), T (s ∪ t) = T s + T t)
  {C : ℝ} (hC : 0 ≤ C) (hT_norm : ∀ s, ∥T s∥ ≤ C * (μ s).to_real) :
  (α →₁ₛ[μ] E') →L[ℝ] F' :=
have h_zero : ∀ s (hs : measurable_set s) (hs_zero : μ s = 0), T s = 0,
{ refine λ s hs hs0, norm_eq_zero.mp _,
  refine le_antisymm ((hT_norm s).trans (le_of_eq _)) (norm_nonneg _),
  rw [hs0, ennreal.zero_to_real, mul_zero], },
linear_map.mk_continuous ⟨indicator_to_L1s T, indicator_to_L1s_add T h_zero h_add,
  indicator_to_L1s_smul_ℝ T h_zero h_add⟩ C (λ f, norm_indicator_to_L1s_le T hC hT_norm f)

variables {α E' μ 𝕜}

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
  {E' F' : Type*} [measurable_space E'] [normed_group E'] [normed_space ℝ E'] [normed_space 𝕜 E']
  [second_countable_topology E'] [borel_space E']
  [normed_group F'] [normed_space ℝ F'] [normed_space 𝕜 F'] [complete_space F']

def indicator_to_L1_clm' (T : set α → (E' →L[ℝ] F'))
  (h_add : ∀ (s t : set α) (hs : measurable_set s) (ht : measurable_set t)
    (hps : μ s ≠ ∞) (hpt : μ t ≠ ∞) (h : s ∩ t = ∅), T (s ∪ t) = T s + T t)
  (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x)
  {C : ℝ} (hC : 0 ≤ C) (hT_norm : ∀ s, ∥T s∥ ≤ C * (μ s).to_real) :
  (α →₁[μ] E') →L[𝕜] F' :=
(indicator_to_L1s_clm' α 𝕜 μ E' T h_add h_smul hC hT_norm).extend
  (coe_to_Lp α E' 𝕜) (simple_func.dense_range one_ne_top) simple_func.uniform_inducing

/-- The Bochner integral in L1 space as a continuous linear map. -/
def integral_clm' : (α →₁[μ] E) →L[𝕜] E :=
(integral_clm' α E 𝕜 μ).extend
  (coe_to_Lp α E 𝕜) (simple_func.dense_range one_ne_top) simple_func.uniform_inducing

variables {𝕜}

def indicator_to_L1_clm (T : set α → (E' →L[ℝ] F'))
  (h_add : ∀ (s t : set α) (hs : measurable_set s) (ht : measurable_set t)
    (hps : μ s ≠ ∞) (hpt : μ t ≠ ∞) (h : s ∩ t = ∅), T (s ∪ t) = T s + T t)
  {C : ℝ} (hC : 0 ≤ C) (hT_norm : ∀ s, ∥T s∥ ≤ C * (μ s).to_real) :
  (α →₁[μ] E') →L[ℝ] F' :=
(indicator_to_L1s_clm α μ E' T h_add hC hT_norm).extend
  (coe_to_Lp α E' ℝ) (simple_func.dense_range one_ne_top) simple_func.uniform_inducing

/-- The Bochner integral in L1 space as a continuous linear map over ℝ. -/
def integral_clm : (α →₁[μ] E) →L[ℝ] E := integral_clm' ℝ

/-- The Bochner integral in L1 space -/
def integral (f : α →₁[μ] E) : E := integral_clm f

lemma integral_eq (f : α →₁[μ] E) : integral f = integral_clm f := rfl

@[norm_cast] lemma simple_func.integral_L1_eq_integral (f : α →₁ₛ[μ] E) :
  integral (f : α →₁[μ] E) = (simple_func.integral f) :=
uniformly_extend_of_ind simple_func.uniform_inducing (simple_func.dense_range one_ne_top)
  (simple_func.integral_clm α E μ).uniform_continuous _

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
by simp [L1.integral, L1.integral_clm.continuous]

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
    rw [← coe_norm_subgroup, ← coe_norm_subgroup],
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

lemma L1.integral_eq_integral (f : α →₁[μ] E) : L1.integral f = ∫ a, f a ∂μ :=
by rw [integral_eq _ (L1.integrable_coe_fn f), integrable.to_L1_coe_fn]

lemma integral_undef (h : ¬ integrable f μ) : ∫ a, f a ∂μ = 0 :=
dif_neg h

lemma integral_non_ae_measurable (h : ¬ ae_measurable f μ) : ∫ a, f a ∂μ = 0 :=
integral_undef $ not_and_of_not_left _ h

variables (α E)

lemma integral_zero : ∫ a : α, (0:E) ∂μ = 0 :=
by { rw [integral_eq _ (integrable_zero α E μ)], exact L1.integral_zero _ _ }

@[simp] lemma integral_zero' : integral μ (0 : α → E) = 0 :=
integral_zero α E

variables {α E}

lemma integral_add (hf : integrable f μ) (hg : integrable g μ) :
  ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ :=
begin
  rw [integral_eq, integral_eq f hf, integral_eq g hg, ← L1.integral_add],
  { refl },
  { exact hf.add hg }
end

lemma integral_add' (hf : integrable f μ) (hg : integrable g μ) :
  ∫ a, (f + g) a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ :=
integral_add hf hg

lemma integral_neg (f : α → E) : ∫ a, -f a ∂μ = - ∫ a, f a ∂μ :=
begin
  by_cases hf : integrable f μ,
  { rw [integral_eq f hf, integral_eq (λa, - f a) hf.neg, ← L1.integral_neg],
    refl },
  { rw [integral_undef hf, integral_undef, neg_zero], rwa [← integrable_neg_iff] at hf }
end

lemma integral_neg' (f : α → E) : ∫ a, (-f) a ∂μ = - ∫ a, f a ∂μ :=
integral_neg f

lemma integral_sub (hf : integrable f μ) (hg : integrable g μ) :
  ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ :=
by { simp only [sub_eq_add_neg, ← integral_neg], exact integral_add hf hg.neg }

lemma integral_sub' (hf : integrable f μ) (hg : integrable g μ) :
  ∫ a, (f - g) a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ :=
integral_sub hf hg

lemma integral_smul [measurable_space 𝕜] [opens_measurable_space 𝕜] (c : 𝕜) (f : α → E) :
  ∫ a, c • (f a) ∂μ = c • ∫ a, f a ∂μ :=
begin
  by_cases hf : integrable f μ,
  { rw [integral_eq f hf, integral_eq (λa, c • (f a)), integrable.to_L1_smul, L1.integral_smul], },
  { by_cases hr : c = 0,
    { simp only [hr, measure_theory.integral_zero, zero_smul] },
    have hf' : ¬ integrable (λ x, c • f x) μ,
    { change ¬ integrable (c • f) μ, rwa [integrable_smul_iff hr f] },
    rw [integral_undef hf, integral_undef hf', smul_zero] }
end

lemma integral_mul_left (r : ℝ) (f : α → ℝ) : ∫ a, r * (f a) ∂μ = r * ∫ a, f a ∂μ :=
integral_smul r f

lemma integral_mul_right (r : ℝ) (f : α → ℝ) : ∫ a, (f a) * r ∂μ = ∫ a, f a ∂μ * r :=
by { simp only [mul_comm], exact integral_mul_left r f }

lemma integral_div (r : ℝ) (f : α → ℝ) : ∫ a, (f a) / r ∂μ = ∫ a, f a ∂μ / r :=
integral_mul_right r⁻¹ f

lemma integral_congr_ae (h : f =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ :=
begin
  by_cases hfi : integrable f μ,
  { have hgi : integrable g μ := hfi.congr h,
    rw [integral_eq f hfi, integral_eq g hgi, (integrable.to_L1_eq_to_L1_iff f g hfi hgi).2 h] },
  { have hgi : ¬ integrable g μ, { rw integrable_congr h at hfi, exact hfi },
    rw [integral_undef hfi, integral_undef hgi] },
end

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
by rw [← f.integral_eq_integral hfi, simple_func.integral]

@[simp] lemma integral_const (c : E) : ∫ x : α, c ∂μ = (μ univ).to_real • c :=
begin
  cases (@le_top _ _ (μ univ)).lt_or_eq with hμ hμ,
  { haveI : finite_measure μ := ⟨hμ⟩,
    calc ∫ x : α, c ∂μ = (simple_func.const α c).integral μ :
      ((simple_func.const α c).integral_eq_integral (integrable_const _)).symm
    ... = _ : _,
    rw [simple_func.integral],
    casesI is_empty_or_nonempty α,
    { simp [μ.eq_zero_of_is_empty] },
    { simp [preimage_const_of_mem] } },
  { by_cases hc : c = 0,
    { simp [hc, integral_zero] },
    { have : ¬integrable (λ x : α, c) μ,
      { simp only [integrable_const_iff, not_or_distrib],
        exact ⟨hc, hμ.not_lt⟩ },
      simp [integral_undef, *] } }
end

lemma norm_integral_le_of_norm_le_const [finite_measure μ] {f : α → E} {C : ℝ}
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
  simp only [simple_func.integral, measure.smul_apply, finset.smul_sum, smul_smul,
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
  simp only [simple_func.approx_on_comp, simple_func.integral, measure.map_apply, hφ,
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
