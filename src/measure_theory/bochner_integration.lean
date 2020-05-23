/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
import measure_theory.simple_func_dense
import analysis.normed_space.bounded_linear_maps

/-!
# Bochner integral

The Bochner integral extends the definition of the Lebesgue integral to functions that map from a
measure space into a Banach space (complete normed vector space). It is constructed here by
extending the integral on simple functions.

## Main definitions

The Bochner integral is defined following these steps:

1. Define the integral on simple functions of the type `simple_func α β` (notation : `α →ₛ β`)
  where `β` is a real normed space.

  (See `simple_func.bintegral` and section `bintegral` for details. Also see `simple_func.integral`
  for the integral on simple functions of the type `simple_func α ennreal`.)

2. Use `simple_func α β` to cut out the simple functions from L1 functions, and define integral
  on these. The type of simple functions in L1 space is written as `α →₁ₛ β`.

3. Show that the embedding of `α →₁ₛ β` into L1 is a dense and uniform one.

4. Show that the integral defined on `α →₁ₛ β` is a continuous linear map.

5. Define the Bochner integral on L1 functions by extending the integral on integrable simple
  functions `α →₁ₛ β` using `continuous_linear_map.extend`. Define the Bochner integral on functions
  as the Bochner integral of its equivalence class in L1 space.

## Main statements

1. Basic properties of the Bochner integral on functions of type `α → β`, where `α` is a measure
   space and `β` is a real normed space.

  * `integral_zero`                  : `∫ 0 = 0`
  * `integral_add`                   : `∫ f + g = ∫ f + ∫ g`
  * `integral_neg`                   : `∫ -f = - ∫ f`
  * `integral_sub`                   : `∫ f - g = ∫ f - ∫ g`
  * `integral_smul`                  : `∫ r • f = r • ∫ f`
  * `integral_congr_ae`              : `∀ₘ a, f a = g a → ∫ f = ∫ g`
  * `norm_integral_le_integral_norm` : `∥∫ f∥ ≤ ∫ ∥f∥`

2. Basic properties of the Bochner integral on functions of type `α → ℝ`, where `α` is a measure
  space.

  * `integral_nonneg_of_ae`         : `∀ₘ a, 0 ≤ f a → 0 ≤ ∫ f`
  * `integral_nonpos_of_nonpos_ae`  : `∀ₘ a, f a ≤ 0 → ∫ f ≤ 0`
  * `integral_le_integral_of_le_ae` : `∀ₘ a, f a ≤ g a → ∫ f ≤ ∫ g`

3. Propositions connecting the Bochner integral with the integral on `ennreal`-valued functions,
   which is called `lintegral` and has the notation `∫⁻`.

  * `integral_eq_lintegral_max_sub_lintegral_min` : `∫ f = ∫⁻ f⁺ - ∫⁻ f⁻`, where `f⁺` is the positive
  part of `f` and `f⁻` is the negative part of `f`.
  * `integral_eq_lintegral_of_nonneg_ae`          : `∀ₘ a, 0 ≤ f a → ∫ f = ∫⁻ f`

4. `tendsto_integral_of_dominated_convergence` : the Lebesgue dominated convergence theorem

## Notes

Some tips on how to prove a proposition if the API for the Bochner integral is not enough so that
you need to unfold the definition of the Bochner integral and go back to simple functions.

See `integral_eq_lintegral_max_sub_lintegral_min` for a complicated example, which proves that
`∫ f = ∫⁻ f⁺ - ∫⁻ f⁻`, with the first integral sign being the Bochner integral of a real-valued
function f : α → ℝ, and second and third integral sign being the integral on ennreal-valued
functions (called `lintegral`). The proof of `integral_eq_lintegral_max_sub_lintegral_min` is
scattered in sections with the name `pos_part`.

Here are the usual steps of proving that a property `p`, say `∫ f = ∫⁻ f⁺ - ∫⁻ f⁻`, holds for all
functions :

1. First go to the `L¹` space.

   For example, if you see `ennreal.to_real (∫⁻ a, ennreal.of_real $ ∥f a∥)`, that is the norm of `f` in
`L¹` space. Rewrite using `l1.norm_of_fun_eq_lintegral_norm`.

2. Show that the set `{f ∈ L¹ | ∫ f = ∫⁻ f⁺ - ∫⁻ f⁻}` is closed in `L¹` using `is_closed_eq`.

3. Show that the property holds for all simple functions `s` in `L¹` space.

   Typically, you need to convert various notions to their `simple_func` counterpart, using lemmas like
`l1.integral_coe_eq_integral`.

4. Since simple functions are dense in `L¹`,
```
univ = closure {s simple}
     = closure {s simple | ∫ s = ∫⁻ s⁺ - ∫⁻ s⁻} : the property holds for all simple functions
     ⊆ closure {f | ∫ f = ∫⁻ f⁺ - ∫⁻ f⁻}
     = {f | ∫ f = ∫⁻ f⁺ - ∫⁻ f⁻} : closure of a closed set is itself
```
Use `is_closed_property` or `dense_range.induction_on` for this argument.

## Notations

* `α →ₛ β`  : simple functions (defined in `measure_theory/integration`)
* `α →₁ β`  : functions in L1 space, i.e., equivalence classes of integrable functions (defined in
             `measure_theory/l1_space`)
* `α →₁ₛ β` : simple functions in L1 space, i.e., equivalence classes of integrable simple functions

Note : `ₛ` is typed using `\_s`. Sometimes it shows as a box if font is missing.

## Tags

Bochner integral, simple function, function space, Lebesgue dominated convergence theorem

-/

noncomputable theory
open_locale classical topological_space


-- Typeclass inference has difficulty finding `has_scalar ℝ β` where `β` is a `normed_space` on `ℝ`
local attribute [instance, priority 10000]
  mul_action.to_has_scalar distrib_mul_action.to_mul_action add_comm_group.to_add_comm_monoid
  normed_group.to_add_comm_group normed_space.to_module
  module.to_semimodule

namespace measure_theory

universes u v w
variables {α : Type u} [measurable_space α] {β : Type v} [decidable_linear_order β] [has_zero β]

local infixr ` →ₛ `:25 := simple_func

namespace simple_func

section pos_part

/-- Positive part of a simple function. -/
def pos_part (f : α →ₛ β) : α →ₛ β := f.map (λb, max b 0)

/-- Negative part of a simple function. -/
def neg_part [has_neg β] (f : α →ₛ β) : α →ₛ β := pos_part (-f)

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
  ext,
  exact max_zero_sub_eq_self (f a)
end

end pos_part

end simple_func

end measure_theory

namespace measure_theory
open set filter topological_space ennreal emetric

universes u v w
variables {α : Type u} [measure_space α] {β : Type v} {γ : Type w}

local infixr ` →ₛ `:25 := simple_func

namespace simple_func

section bintegral
/-!
### The Bochner integral of simple functions

Define the Bochner integral of simple functions of the type `α →ₛ β` where `β` is a normed group,
and prove basic property of this integral.
-/
open finset

variables [normed_group β] [normed_group γ]

lemma integrable_iff_integral_lt_top {f : α →ₛ β} :
  integrable f ↔ integral (f.map (coe ∘ nnnorm)) < ⊤ :=
by { rw [integrable, ← lintegral_eq_integral, lintegral_map] }

lemma fin_vol_supp_of_integrable {f : α →ₛ β} (hf : integrable f) : f.fin_vol_supp :=
begin
  rw [integrable_iff_integral_lt_top] at hf,
  have hf := fin_vol_supp_of_integral_lt_top hf,
  refine fin_vol_supp_of_fin_vol_supp_map f hf _,
  assume b, simp [nnnorm_eq_zero]
end

lemma integrable_of_fin_vol_supp {f : α →ₛ β} (h : f.fin_vol_supp) : integrable f :=
by { rw [integrable_iff_integral_lt_top], exact integral_map_coe_lt_top h nnnorm_zero }

/-- For simple functions with a `normed_group` as codomain, being integrable is the same as having
    finite volume support. -/
lemma integrable_iff_fin_vol_supp (f : α →ₛ β) : integrable f ↔ f.fin_vol_supp :=
iff.intro fin_vol_supp_of_integrable integrable_of_fin_vol_supp

lemma integrable_pair {f : α →ₛ β} {g : α →ₛ γ} (hf : integrable f) (hg : integrable g) :
  integrable (pair f g) :=
by { rw integrable_iff_fin_vol_supp at *, apply fin_vol_supp_pair; assumption }

variables [normed_space ℝ γ]

/-- Bochner integral of simple functions whose codomain is a real `normed_space`.
    The name `simple_func.integral` has been taken in the file `integration.lean`, which calculates
    the integral of a simple function with type `α → ennreal`.
    The name `bintegral` stands for Bochner integral. -/
def bintegral [normed_space ℝ β] (f : α →ₛ β) : β :=
f.range.sum (λ x, (ennreal.to_real (volume (f ⁻¹' {x}))) • x)

/-- Calculate the integral of `g ∘ f : α →ₛ γ`, where `f` is an integrable function from `α` to `β`
    and `g` is a function from `β` to `γ`. We require `g 0 = 0` so that `g ∘ f` is integrable. -/
lemma map_bintegral (f : α →ₛ β) (g : β → γ) (hf : integrable f) (hg : g 0 = 0) :
  (f.map g).bintegral = f.range.sum (λ x, (ennreal.to_real (volume (f ⁻¹' {x}))) • (g x)) :=
begin
  /- Just a complicated calculation with `finset.sum`. Real work is done by
     `map_preimage_singleton`, `simple_func.volume_bUnion_preimage` and `ennreal.to_real_sum`  -/
  rw integrable_iff_fin_vol_supp at hf,
  simp only [bintegral, range_map],
  refine finset.sum_image' _ (assume b hb, _),
  rcases mem_range.1 hb with ⟨a, rfl⟩,
  let s' := f.range.filter (λb, g b = g (f a)),
  calc (ennreal.to_real (volume ((f.map g) ⁻¹' {g (f a)}))) • (g (f a)) =
      (ennreal.to_real (volume (⋃b∈s', f ⁻¹' {b}))) • (g (f a)) : by rw map_preimage_singleton
  ... = (ennreal.to_real (s'.sum (λb, volume (f ⁻¹' {b})))) • (g (f a)) :
    by rw volume_bUnion_preimage
  ... = (s'.sum (λb, ennreal.to_real (volume (f ⁻¹' {b})))) • (g (f a)) :
  begin
    by_cases h : g (f a) = 0,
    { rw [h, smul_zero, smul_zero] },
    { rw ennreal.to_real_sum,
      simp only [mem_filter],
      rintros b ⟨_, hb⟩,
      have : b ≠ 0, { assume hb', rw [← hb, hb'] at h, contradiction },
      apply hf,
      assumption }
  end
  ... = s'.sum (λb, (ennreal.to_real (volume (f ⁻¹' {b}))) • (g (f a))) : finset.sum_smul
  ... = s'.sum (λb, (ennreal.to_real (volume (f ⁻¹' {b}))) • (g b)) :
    finset.sum_congr rfl $ by { assume x, simp only [mem_filter], rintro ⟨_, h⟩, rw h }
end

/-- `simple_func.bintegral` and `simple_func.integral` agree when the integrand has type
    `α →ₛ ennreal`. But since `ennreal` is not a `normed_space`, we need some form of coercion.
    See `bintegral_eq_integral'` for a simpler version. -/
lemma bintegral_eq_integral {f : α →ₛ β} {g : β → ennreal} (hf : integrable f) (hg0 : g 0 = 0)
  (hgt : ∀b, g b < ⊤):
  (f.map (ennreal.to_real ∘ g)).bintegral = ennreal.to_real (f.map g).integral :=
begin
  have hf' : f.fin_vol_supp, { rwa integrable_iff_fin_vol_supp at hf },
  rw [map_bintegral f _ hf, map_integral, ennreal.to_real_sum],
  { refine finset.sum_congr rfl (λb hb, _),
    rw [smul_eq_mul],
    rw [to_real_mul_to_real, mul_comm] },
  { assume a ha,
    by_cases a0 : a = 0,
    { rw [a0, hg0, zero_mul], exact with_top.zero_lt_top },
    apply mul_lt_top (hgt a) (hf' _ a0) },
  { simp [hg0] }
end

/-- `simple_func.bintegral` and `lintegral : (α → ennreal) → ennreal` are the same when the
    integrand has type `α →ₛ ennreal`. But since `ennreal` is not a `normed_space`, we need some
    form of coercion.
    See `bintegral_eq_lintegral'` for a simpler version. -/
lemma bintegral_eq_lintegral (f : α →ₛ β) (g : β → ennreal) (hf : integrable f) (hg0 : g 0 = 0)
  (hgt : ∀b, g b < ⊤):
  (f.map (ennreal.to_real ∘ g)).bintegral = ennreal.to_real (∫⁻ a, g (f a)) :=
by { rw [bintegral_eq_integral hf hg0 hgt, ← lintegral_eq_integral], refl }

variables [normed_space ℝ β]

lemma bintegral_congr {f g : α →ₛ β} (hf : integrable f) (hg : integrable g) (h : ∀ₘ a, f a = g a):
  bintegral f = bintegral g :=
show ((pair f g).map prod.fst).bintegral = ((pair f g).map prod.snd).bintegral, from
begin
  have inte := integrable_pair hf hg,
  rw [map_bintegral (pair f g) _ inte prod.fst_zero, map_bintegral (pair f g) _ inte prod.snd_zero],
  refine finset.sum_congr rfl (assume p hp, _),
  rcases mem_range.1 hp with ⟨a, rfl⟩,
  by_cases eq : f a = g a,
  { dsimp only [pair_apply], rw eq },
  { have : volume ((pair f g) ⁻¹' {(f a, g a)}) = 0,
    { refine volume_mono_null (assume a' ha', _) h,
      simp only [set.mem_preimage, mem_singleton_iff, pair_apply, prod.mk.inj_iff] at ha',
      show f a' ≠ g a',
      rwa [ha'.1, ha'.2] },
    simp only [this, pair_apply, zero_smul, ennreal.zero_to_real] },
end

/-- `simple_func.bintegral` and `simple_func.integral` agree when the integrand has type
    `α →ₛ ennreal`. But since `ennreal` is not a `normed_space`, we need some form of coercion. -/
lemma bintegral_eq_integral' {f : α →ₛ ℝ} (hf : integrable f) (h_pos : ∀ₘ a, 0 ≤ f a) :
  f.bintegral = ennreal.to_real (f.map ennreal.of_real).integral :=
begin
  have : ∀ₘ a, f a = (f.map (ennreal.to_real ∘ ennreal.of_real)) a,
  { filter_upwards [h_pos],
    assume a,
    simp only [mem_set_of_eq, map_apply, function.comp_apply],
    assume h,
    exact (ennreal.to_real_of_real h).symm },
  rw ← bintegral_eq_integral hf,
  { refine bintegral_congr hf _ this, exact integrable_of_ae_eq hf this },
  { exact ennreal.of_real_zero },
  { assume b, rw ennreal.lt_top_iff_ne_top, exact ennreal.of_real_ne_top  }
end

/-- `simple_func.bintegral` and `lintegral : (α → ennreal) → ennreal` agree when the integrand has
    type `α →ₛ ennreal`. But since `ennreal` is not a `normed_space`, we need some form of coercion. -/
lemma bintegral_eq_lintegral' {f : α →ₛ ℝ} (hf : integrable f) (h_pos : ∀ₘ a, 0 ≤ f a) :
  f.bintegral = ennreal.to_real (∫⁻ a, (f.map ennreal.of_real a)) :=
by rw [bintegral_eq_integral' hf h_pos, ← lintegral_eq_integral]

lemma bintegral_add {f g : α →ₛ β} (hf : integrable f) (hg : integrable g) :
  bintegral (f + g) = bintegral f + bintegral g :=
calc bintegral (f + g) = (pair f g).range.sum
       (λx, ennreal.to_real (volume ((pair f g) ⁻¹' {x})) • (x.fst + x.snd)) :
begin
  rw [add_eq_map₂, map_bintegral (pair f g)],
  { exact integrable_pair hf hg },
  { simp only [add_zero, prod.fst_zero, prod.snd_zero] }
end
... = (pair f g).range.sum
        (λx, ennreal.to_real (volume ((pair f g) ⁻¹' {x})) • x.fst +
             ennreal.to_real (volume ((pair f g) ⁻¹' {x})) • x.snd) :
  finset.sum_congr rfl $ assume a ha, smul_add _ _ _
... = (simple_func.range (pair f g)).sum
        (λ (x : β × β), ennreal.to_real (volume ((pair f g) ⁻¹' {x})) • x.fst) +
      (simple_func.range (pair f g)).sum
        (λ (x : β × β), ennreal.to_real (volume ((pair f g) ⁻¹' {x})) • x.snd) :
  by rw finset.sum_add_distrib
... = ((pair f g).map prod.fst).bintegral + ((pair f g).map prod.snd).bintegral :
begin
  rw [map_bintegral (pair f g), map_bintegral (pair f g)],
  { exact integrable_pair hf hg }, { refl },
  { exact integrable_pair hf hg }, { refl }
end
... = bintegral f + bintegral g : rfl

lemma bintegral_neg {f : α →ₛ β} (hf : integrable f) : bintegral (-f) = - bintegral f :=
calc bintegral (-f) = bintegral (f.map (has_neg.neg)) : rfl
  ... = - bintegral f :
  begin
    rw [map_bintegral f _ hf neg_zero, bintegral, ← sum_neg_distrib],
    refine finset.sum_congr rfl (λx h, smul_neg _ _),
  end

lemma bintegral_sub {f g : α →ₛ β} (hf : integrable f) (hg : integrable g) :
  bintegral (f - g) = bintegral f - bintegral g :=
begin
  have : f - g = f + (-g) := rfl,
  rw [this, bintegral_add hf _, bintegral_neg hg],
  { refl },
  exact hg.neg
end

lemma bintegral_smul (r : ℝ) {f : α →ₛ β} (hf : integrable f) :
  bintegral (r • f) = r • bintegral f :=
calc bintegral (r • f) = f.range.sum (λx, ennreal.to_real (volume (f ⁻¹' {x})) • r • x) :
  by rw [smul_eq_map r f, map_bintegral f _ hf (smul_zero _)]
... = f.range.sum (λ (x : β), ((ennreal.to_real (volume (f ⁻¹' {x}))) * r) • x) :
  finset.sum_congr rfl $ λb hb, by apply smul_smul
... = r • bintegral f :
begin
  rw [bintegral, smul_sum],
  refine finset.sum_congr rfl (λb hb, _),
  rw [smul_smul, mul_comm]
end

lemma norm_bintegral_le_bintegral_norm (f : α →ₛ β) (hf : integrable f) :
  ∥f.bintegral∥ ≤ (f.map norm).bintegral :=
begin
  rw map_bintegral f norm hf norm_zero,
  rw bintegral,
  calc ∥f.range.sum (λx, ennreal.to_real (volume (f ⁻¹' {x})) • x)∥ ≤
       f.range.sum (λx, ∥ennreal.to_real (volume (f ⁻¹' {x})) • x∥) :
    norm_sum_le _ _
    ... = f.range.sum (λx, ennreal.to_real (volume (f ⁻¹' {x})) • ∥x∥) :
    begin
      refine finset.sum_congr rfl (λb hb, _),
      rw [norm_smul, smul_eq_mul, real.norm_eq_abs, abs_of_nonneg to_real_nonneg]
    end
end

end bintegral

end simple_func

namespace l1

open ae_eq_fun

variables
  [normed_group β] [second_countable_topology β] [measurable_space β] [borel_space β]
  [normed_group γ] [second_countable_topology γ] [measurable_space γ] [borel_space γ]

variables (α β)
/-- `l1.simple_func` is a subspace of L1 consisting of equivalence classes of an integrable simple
    function. -/
def simple_func : Type (max u v) :=
{ f : α →₁ β // ∃ (s : α →ₛ β),  integrable s ∧ ae_eq_fun.mk s s.measurable = f}
-- TODO: it seems that `ae_eq_fun.mk s s.measurable = f` implies `integrable s`

variables {α β}

infixr ` →₁ₛ `:25 := measure_theory.l1.simple_func

namespace simple_func

section instances
/-! Simple functions in L1 space form a `normed_space`. -/

instance : has_coe (α →₁ₛ β) (α →₁ β) := ⟨subtype.val⟩

protected lemma eq {f g : α →₁ₛ β} : (f : α →₁ β) = (g : α →₁ β) → f = g := subtype.eq
protected lemma eq' {f g : α →₁ₛ β} : (f : α →ₘ β) = (g : α →ₘ β) → f = g := subtype.eq ∘ subtype.eq

@[norm_cast] protected lemma eq_iff {f g : α →₁ₛ β} : (f : α →₁ β) = (g : α →₁ β) ↔ f = g :=
iff.intro (subtype.eq) (congr_arg coe)

@[norm_cast] protected lemma eq_iff' {f g : α →₁ₛ β} : (f : α →ₘ β) = (g : α →ₘ β) ↔ f = g :=
iff.intro (simple_func.eq') (congr_arg _)

/-- L1 simple functions forms a `emetric_space`, with the emetric being inherited from L1 space,
  i.e., `edist f g = ∫⁻ a, edist (f a) (g a)`.
  Not declared as an instance as `α →₁ₛ β` will only be useful in the construction of the bochner
  integral. -/
protected def emetric_space  : emetric_space (α →₁ₛ β) := subtype.emetric_space

/-- L1 simple functions forms a `metric_space`, with the metric being inherited from L1 space,
  i.e., `dist f g = ennreal.to_real (∫⁻ a, edist (f a) (g a)`).
  Not declared as an instance as `α →₁ₛ β` will only be useful in the construction of the bochner
  integral. -/
protected def metric_space : metric_space (α →₁ₛ β) := subtype.metric_space

local attribute [instance] protected lemma is_add_subgroup : is_add_subgroup
  (λf:α →₁ β, ∃ (s : α →ₛ β), integrable s ∧ ae_eq_fun.mk s s.measurable = f) :=
{ zero_mem := ⟨0, integrable_zero _ _, rfl⟩,
  add_mem :=
  begin
    rintros f g ⟨s, hsi, hs⟩ ⟨t, hti, ht⟩,
    use s + t, split,
    { exact hsi.add s.measurable t.measurable hti },
    { rw [coe_add, ← hs, ← ht], refl }
  end,
  neg_mem :=
  begin
    rintros f ⟨s, hsi, hs⟩,
    use -s, split,
    { exact hsi.neg },
    { rw [coe_neg, ← hs], refl }
  end }

/-- Not declared as an instance as `α →₁ₛ β` will only be useful in the construction of the bochner
  integral. -/
protected def add_comm_group : add_comm_group (α →₁ₛ β) := subtype.add_comm_group

local attribute [instance] simple_func.add_comm_group simple_func.metric_space
  simple_func.emetric_space

instance : inhabited (α →₁ₛ β) := ⟨0⟩

@[simp, norm_cast] lemma coe_zero : ((0 : α →₁ₛ β) : α →₁ β) = 0 := rfl
@[simp, norm_cast] lemma coe_add (f g : α →₁ₛ β) : ((f + g : α →₁ₛ β) : α →₁ β) = f + g := rfl
@[simp, norm_cast] lemma coe_neg (f : α →₁ₛ β) : ((-f : α →₁ₛ β) : α →₁ β) = -f := rfl
@[simp, norm_cast] lemma coe_sub (f g : α →₁ₛ β) : ((f - g : α →₁ₛ β) : α →₁ β) = f - g := rfl

@[simp] lemma edist_eq (f g : α →₁ₛ β) : edist f g = edist (f : α →₁ β) (g : α →₁ β) := rfl
@[simp] lemma dist_eq (f g : α →₁ₛ β) : dist f g = dist (f : α →₁ β) (g : α →₁ β) := rfl

/-- The norm on `α →₁ₛ β` is inherited from L1 space. That is, `∥f∥ = ∫⁻ a, edist (f a) 0`.
  Not declared as an instance as `α →₁ₛ β` will only be useful in the construction of the bochner
  integral. -/
protected def has_norm : has_norm (α →₁ₛ β) := ⟨λf, ∥(f : α →₁ β)∥⟩

local attribute [instance] simple_func.has_norm

lemma norm_eq (f : α →₁ₛ β) : ∥f∥ = ∥(f : α →₁ β)∥ := rfl
lemma norm_eq' (f : α →₁ₛ β) : ∥f∥ = ennreal.to_real (edist (f : α →ₘ β) 0) := rfl

/-- Not declared as an instance as `α →₁ₛ β` will only be useful in the construction of the bochner
  integral. -/
protected def normed_group : normed_group (α →₁ₛ β) :=
normed_group.of_add_dist (λ x, rfl) $ by
  { intros, simp only [dist_eq, coe_add, l1.dist_eq, l1.coe_add], rw edist_eq_add_add }

variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 β]

/-- Not declared as an instance as `α →₁ₛ β` will only be useful in the construction of the bochner
  integral. -/
protected def has_scalar : has_scalar 𝕜 (α →₁ₛ β) := ⟨λk f, ⟨k • f,
begin
  rcases f with ⟨f, ⟨s, hsi, hs⟩⟩,
  use k • s, split,
  { exact integrable.smul _ hsi },
  { rw [coe_smul, subtype.coe_mk, ← hs], refl }
end ⟩⟩

local attribute [instance, priority 10000] simple_func.has_scalar

@[simp, norm_cast] lemma coe_smul (c : 𝕜) (f : α →₁ₛ β) :
  ((c • f : α →₁ₛ β) : α →₁ β) = c • (f : α →₁ β) := rfl

/-- Not declared as an instance as `α →₁ₛ β` will only be useful in the construction of the bochner
  integral. -/
protected def semimodule : semimodule 𝕜 (α →₁ₛ β) :=
{ one_smul  := λf, simple_func.eq (by { simp only [coe_smul], exact one_smul _ _ }),
  mul_smul  := λx y f, simple_func.eq (by { simp only [coe_smul], exact mul_smul _ _ _ }),
  smul_add  := λx f g, simple_func.eq (by { simp only [coe_smul, coe_add], exact smul_add _ _ _ }),
  smul_zero := λx, simple_func.eq (by { simp only [coe_zero, coe_smul], exact smul_zero _ }),
  add_smul  := λx y f, simple_func.eq (by { simp only [coe_smul], exact add_smul _ _ _ }),
  zero_smul := λf, simple_func.eq (by { simp only [coe_smul], exact zero_smul _ _ }) }

/-- Not declared as an instance as `α →₁ₛ β` will only be useful in the construction of the bochner
  integral. -/
protected def module : module 𝕜 (α →₁ₛ β) :=
{ .. simple_func.semimodule }

/-- Not declared as an instance as `α →₁ₛ β` will only be useful in the construction of the bochner
  integral. -/
protected def vector_space : vector_space 𝕜 (α →₁ₛ β) :=
{ .. simple_func.semimodule }

local attribute [instance] simple_func.vector_space simple_func.normed_group

/-- Not declared as an instance as `α →₁ₛ β` will only be useful in the construction of the bochner
  integral. -/
protected def normed_space : normed_space 𝕜 (α →₁ₛ β) :=
⟨ λc f, by { rw [norm_eq, norm_eq, coe_smul, norm_smul] } ⟩

end instances

local attribute [instance] simple_func.normed_group simple_func.normed_space

section of_simple_func

/-- Construct the equivalence class `[f]` of an integrable simple function `f`. -/
@[reducible] def of_simple_func (f : α →ₛ β) (hf : integrable f) : (α →₁ₛ β) :=
  ⟨l1.of_fun f f.measurable hf, ⟨f, ⟨hf, rfl⟩⟩⟩

lemma of_simple_func_eq_of_fun (f : α →ₛ β) (hf : integrable f) :
  (of_simple_func f hf : α →₁ β) = l1.of_fun f f.measurable hf := rfl

lemma of_simple_func_eq_mk (f : α →ₛ β) (hf : integrable f) :
  (of_simple_func f hf : α →ₘ β) = ae_eq_fun.mk f f.measurable := rfl

lemma of_simple_func_zero : of_simple_func (0 : α →ₛ β) (integrable_zero α β) = 0 := rfl

lemma of_simple_func_add (f g : α →ₛ β) (hf hg) :
  of_simple_func (f + g) (integrable.add f.measurable hf g.measurable hg) = of_simple_func f hf +
    of_simple_func g hg := rfl

lemma of_simple_func_neg (f : α →ₛ β) (hf) :
  of_simple_func (-f) (integrable.neg hf) = -of_simple_func f hf := rfl

lemma of_simple_func_sub (f g : α →ₛ β) (hf hg) :
  of_simple_func (f - g) (integrable.sub f.measurable hf g.measurable hg) = of_simple_func f hf -
    of_simple_func g hg := rfl

variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 β]

lemma of_simple_func_smul (f : α →ₛ β) (hf) (c : 𝕜) :
  of_simple_func (c • f) (integrable.smul _ hf) = c • of_simple_func f hf := rfl

lemma norm_of_simple_func (f : α →ₛ β) (hf) : ∥of_simple_func f hf∥ = ennreal.to_real (∫⁻ a, edist (f a) 0) :=
rfl

end of_simple_func

section to_simple_func

/-- Find a representative of a `l1.simple_func`. -/
def to_simple_func (f : α →₁ₛ β) : α →ₛ β := classical.some f.2

/-- `f.to_simple_func` is measurable. -/
protected lemma measurable (f : α →₁ₛ β) : measurable f.to_simple_func := f.to_simple_func.measurable

/-- `f.to_simple_func` is integrable. -/
protected lemma integrable (f : α →₁ₛ β) : integrable f.to_simple_func :=
let ⟨h, _⟩ := classical.some_spec f.2 in h

lemma of_simple_func_to_simple_func (f : α →₁ₛ β) :
  of_simple_func (f.to_simple_func) f.integrable = f :=
by { rw ← simple_func.eq_iff', exact (classical.some_spec f.2).2 }

lemma to_simple_func_of_simple_func (f : α →ₛ β) (hfi) :
  ∀ₘ a, (of_simple_func f hfi).to_simple_func a = f a :=
by { rw ← mk_eq_mk, exact (classical.some_spec (of_simple_func f hfi).2).2 }

lemma to_simple_func_eq_to_fun (f : α →₁ₛ β) : ∀ₘ a, (f.to_simple_func) a = (f : α →₁ β).to_fun a :=
begin
  rw [← of_fun_eq_of_fun (f.to_simple_func) (f : α →₁ β).to_fun f.measurable f.integrable
    (f:α→₁β).measurable (f:α→₁β).integrable, ← l1.eq_iff],
  simp only [of_fun_eq_mk],
  rcases classical.some_spec f.2 with ⟨_, h⟩, convert h, rw mk_to_fun, refl
end

variables (α β)
lemma zero_to_simple_func : ∀ₘ a, (0 : α →₁ₛ β).to_simple_func a = 0 :=
begin
  filter_upwards [to_simple_func_eq_to_fun (0 : α →₁ₛ β), l1.zero_to_fun α β],
  assume a,
  simp only [mem_set_of_eq],
  assume h,
  rw h,
  assume h,
  exact h
end
variables {α β}

lemma add_to_simple_func (f g : α →₁ₛ β) :
  ∀ₘ a, (f + g).to_simple_func a = f.to_simple_func a + g.to_simple_func a :=
begin
  filter_upwards [to_simple_func_eq_to_fun (f + g), to_simple_func_eq_to_fun f,
    to_simple_func_eq_to_fun g, l1.add_to_fun (f:α→₁β) g],
  assume a,
  simp only [mem_set_of_eq],
  repeat { assume h, rw h },
  assume h,
  rw ← h,
  refl
end

lemma neg_to_simple_func (f : α →₁ₛ β) : ∀ₘ a, (-f).to_simple_func a = - f.to_simple_func a :=
begin
  filter_upwards [to_simple_func_eq_to_fun (-f), to_simple_func_eq_to_fun f, l1.neg_to_fun (f:α→₁β)],
  assume a,
  simp only [mem_set_of_eq],
  repeat { assume h, rw h },
  assume h,
  rw ← h,
  refl
end

lemma sub_to_simple_func (f g : α →₁ₛ β) :
  ∀ₘ a, (f - g).to_simple_func a = f.to_simple_func a - g.to_simple_func a :=
begin
  filter_upwards [to_simple_func_eq_to_fun (f - g), to_simple_func_eq_to_fun f,
    to_simple_func_eq_to_fun g, l1.sub_to_fun (f:α→₁β) g],
  assume a,
  simp only [mem_set_of_eq],
  repeat { assume h, rw h },
  assume h,
  rw ← h,
  refl
end

variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 β]

lemma smul_to_simple_func (k : 𝕜) (f : α →₁ₛ β) :
  ∀ₘ a, (k • f).to_simple_func a = k • f.to_simple_func a :=
begin
  filter_upwards [to_simple_func_eq_to_fun (k • f), to_simple_func_eq_to_fun f,
    l1.smul_to_fun k (f:α→₁β)],
  assume a,
  simp only [mem_set_of_eq],
  repeat { assume h, rw h },
  assume h,
  rw ← h,
  refl
end

lemma lintegral_edist_to_simple_func_lt_top (f g : α →₁ₛ β) :
  (∫⁻ (x : α), edist ((to_simple_func f) x) ((to_simple_func g) x)) < ⊤ :=
begin
  rw lintegral_rw₂ (to_simple_func_eq_to_fun f) (to_simple_func_eq_to_fun g),
  exact lintegral_edist_to_fun_lt_top _ _
end

lemma dist_to_simple_func (f g : α →₁ₛ β) : dist f g =
  ennreal.to_real (∫⁻ x, edist (f.to_simple_func x) (g.to_simple_func x)) :=
begin
  rw [dist_eq, l1.dist_to_fun, ennreal.to_real_eq_to_real],
  { rw lintegral_rw₂, repeat { exact all_ae_eq_symm (to_simple_func_eq_to_fun _) } },
  { exact l1.lintegral_edist_to_fun_lt_top _ _ },
  { exact lintegral_edist_to_simple_func_lt_top _ _ }
end

lemma norm_to_simple_func (f : α →₁ₛ β) :
  ∥f∥ = ennreal.to_real (∫⁻ (a : α), nnnorm ((to_simple_func f) a)) :=
calc ∥f∥ = ennreal.to_real (∫⁻x, edist (f.to_simple_func x) ((0 : α →₁ₛ β).to_simple_func x)) :
begin
  rw [← dist_zero_right, dist_to_simple_func]
end
... = ennreal.to_real (∫⁻ (x : α), (coe ∘ nnnorm) (f.to_simple_func x)) :
begin
  rw lintegral_nnnorm_eq_lintegral_edist,
  have : (∫⁻ (x : α), edist ((to_simple_func f) x) ((to_simple_func (0:α→₁ₛβ)) x)) =
            ∫⁻ (x : α), edist ((to_simple_func f) x) 0,
  { apply lintegral_congr_ae, filter_upwards [zero_to_simple_func α β],
    assume a,
    simp only [mem_set_of_eq],
    assume h,
    rw h },
  rw [ennreal.to_real_eq_to_real],
  { exact this },
  { exact lintegral_edist_to_simple_func_lt_top _ _ },
  { rw ← this, exact lintegral_edist_to_simple_func_lt_top _ _ }
end

lemma norm_eq_bintegral (f : α →₁ₛ β) : ∥f∥ = (f.to_simple_func.map norm).bintegral :=
calc ∥f∥ = ennreal.to_real (∫⁻ (x : α), (coe ∘ nnnorm) (f.to_simple_func x)) :
  by { rw norm_to_simple_func }
... = (f.to_simple_func.map norm).bintegral :
begin
  rw ← f.to_simple_func.bintegral_eq_lintegral (coe ∘ nnnorm) f.integrable,
  { congr },
  { simp only [nnnorm_zero, function.comp_app, ennreal.coe_zero] },
  { assume b, exact coe_lt_top }
end

end to_simple_func

section coe_to_l1
/-! The embedding of integrable simple functions `α →₁ₛ β` into L1 is a uniform and dense embedding. -/

lemma exists_simple_func_near (f : α →₁ β) {ε : ℝ} (ε0 : 0 < ε) :
  ∃ s : α →₁ₛ β, dist f s < ε :=
begin
  rcases f with ⟨⟨f, hfm⟩, hfi⟩,
  simp only [integrable_mk, quot_mk_eq_mk] at hfi,
  rcases simple_func_sequence_tendsto' hfm hfi with ⟨F, ⟨h₁, h₂⟩⟩,
  rw ennreal.tendsto_at_top at h₂,
  rcases h₂ (ennreal.of_real (ε/2)) (of_real_pos.2 $ half_pos ε0) with ⟨N, hN⟩,
  have : (∫⁻ (x : α), nndist (F N x) (f x)) < ennreal.of_real ε :=
    calc (∫⁻ (x : α), nndist (F N x) (f x)) ≤ 0 + ennreal.of_real (ε/2) : (hN N (le_refl _)).2
    ... < ennreal.of_real ε :
      by { simp only [zero_add, of_real_lt_of_real_iff ε0], exact half_lt_self ε0 },
  { refine ⟨of_simple_func (F N) (h₁ N), _⟩, rw dist_comm,
    rw lt_of_real_iff_to_real_lt _ at this,
    { simpa [edist_mk_mk', of_simple_func, l1.of_fun, l1.dist_eq] },
    rw ← lt_top_iff_ne_top, exact lt_trans this (by simp [lt_top_iff_ne_top, of_real_ne_top]) },
  { exact zero_ne_top }
end

protected lemma uniform_continuous : uniform_continuous (coe : (α →₁ₛ β) → (α →₁ β)) :=
uniform_continuous_comap

protected lemma uniform_embedding : uniform_embedding (coe : (α →₁ₛ β) → (α →₁ β)) :=
uniform_embedding_comap subtype.val_injective

protected lemma uniform_inducing : uniform_inducing (coe : (α →₁ₛ β) → (α →₁ β)) :=
simple_func.uniform_embedding.to_uniform_inducing

protected lemma dense_embedding : dense_embedding (coe : (α →₁ₛ β) → (α →₁ β)) :=
simple_func.uniform_embedding.dense_embedding $
λ f, mem_closure_iff_nhds.2 $ λ t ht,
let ⟨ε,ε0, hε⟩ := metric.mem_nhds_iff.1 ht in
let ⟨s, h⟩ := exists_simple_func_near f ε0 in
⟨_, hε (metric.mem_ball'.2 h), s, rfl⟩

protected lemma dense_inducing : dense_inducing (coe : (α →₁ₛ β) → (α →₁ β)) :=
simple_func.dense_embedding.to_dense_inducing

protected lemma dense_range : dense_range (coe : (α →₁ₛ β) → (α →₁ β)) :=
simple_func.dense_inducing.dense

variables (𝕜 : Type*) [normed_field 𝕜] [normed_space 𝕜 β]

variables (α β)

/-- The uniform and dense embedding of L1 simple functions into L1 functions. -/
def coe_to_l1 : (α →₁ₛ β) →L[𝕜] (α →₁ β) :=
{ to_fun := (coe : (α →₁ₛ β) → (α →₁ β)),
  add := λf g, rfl,
  smul := λk f, rfl,
  cont := l1.simple_func.uniform_continuous.continuous, }

variables {α β 𝕜}

end coe_to_l1

section pos_part

/-- Positive part of a simple function in L1 space.  -/
def pos_part (f : α →₁ₛ ℝ) : α →₁ₛ ℝ := ⟨l1.pos_part (f : α →₁ ℝ),
begin
  rcases f with ⟨f, s, hsi, hsf⟩,
  use s.pos_part,
  split,
  { exact integrable.max_zero hsi },
  { simp only [subtype.coe_mk],
    rw [l1.coe_pos_part, ← hsf, ae_eq_fun.pos_part, ae_eq_fun.zero_def, comp₂_mk_mk, mk_eq_mk],
    filter_upwards [],
    simp only [mem_set_of_eq],
    assume a,
    refl }
end ⟩

/-- Negative part of a simple function in L1 space. -/
def neg_part (f : α →₁ₛ ℝ) : α →₁ₛ ℝ := pos_part (-f)

@[norm_cast] lemma coe_pos_part (f : α →₁ₛ ℝ) : (f.pos_part : α →₁ ℝ) = (f : α →₁ ℝ).pos_part := rfl

@[norm_cast] lemma coe_neg_part (f : α →₁ₛ ℝ) : (f.neg_part : α →₁ ℝ) = (f : α →₁ ℝ).neg_part := rfl

end pos_part

section simple_func_integral
/-! Define the Bochner integral on `α →₁ₛ β` and prove basic properties of this integral. -/

variables [normed_space ℝ β]

/-- The Bochner integral over simple functions in l1 space. -/
def integral (f : α →₁ₛ β) : β := (f.to_simple_func).bintegral

lemma integral_eq_bintegral (f : α →₁ₛ β) : integral f = (f.to_simple_func).bintegral := rfl

lemma integral_eq_lintegral {f : α →₁ₛ ℝ} (h_pos : ∀ₘ a, 0 ≤ f.to_simple_func a) :
  integral f = ennreal.to_real (∫⁻ a, ennreal.of_real (f.to_simple_func a)) :=
by { rw [integral, simple_func.bintegral_eq_lintegral' f.integrable h_pos], refl }

lemma integral_congr (f g : α →₁ₛ β) (h : ∀ₘ a, f.to_simple_func a = g.to_simple_func a) :
  integral f = integral g :=
by { simp only [integral], apply simple_func.bintegral_congr f.integrable g.integrable, exact h }

lemma integral_add (f g : α →₁ₛ β) : integral (f + g) = integral f + integral g :=
begin
  simp only [integral],
  rw ← simple_func.bintegral_add f.integrable g.integrable,
  apply simple_func.bintegral_congr (f + g).integrable,
    { exact f.integrable.add f.measurable g.measurable g.integrable },
    { apply add_to_simple_func },
end

lemma integral_smul (r : ℝ) (f : α →₁ₛ β) : integral (r • f) = r • integral f :=
begin
  simp only [integral],
  rw ← simple_func.bintegral_smul _ f.integrable,
  apply simple_func.bintegral_congr (r • f).integrable,
    { exact integrable.smul _ f.integrable },
    { apply smul_to_simple_func }
end

lemma norm_integral_le_norm (f : α →₁ₛ β) : ∥ integral f ∥ ≤ ∥f∥ :=
begin
  rw [integral, norm_eq_bintegral],
  exact f.to_simple_func.norm_bintegral_le_bintegral_norm f.integrable
end

/-- The Bochner integral over simple functions in l1 space as a continuous linear map. -/
def integral_clm : (α →₁ₛ β) →L[ℝ] β :=
linear_map.mk_continuous ⟨integral, integral_add, integral_smul⟩
  1 (λf, le_trans (norm_integral_le_norm _) $ by rw one_mul)

local notation `Integral` := @integral_clm α _ β _ _ _ _ _

open continuous_linear_map

lemma norm_Integral_le_one : ∥Integral∥ ≤ 1 :=
linear_map.mk_continuous_norm_le _ (zero_le_one) _

section pos_part

lemma pos_part_to_simple_func (f : α →₁ₛ ℝ) :
  ∀ₘ a, f.pos_part.to_simple_func a = f.to_simple_func.pos_part a :=
begin
  have eq : ∀ a, f.to_simple_func.pos_part a = max (f.to_simple_func a) 0 := λa, rfl,
  have ae_eq : ∀ₘ a, f.pos_part.to_simple_func a = max (f.to_simple_func a) 0,
  { filter_upwards [to_simple_func_eq_to_fun f.pos_part, pos_part_to_fun (f : α →₁ ℝ),
      to_simple_func_eq_to_fun f],
    simp only [mem_set_of_eq],
    assume a h₁ h₂ h₃,
    rw [h₁, coe_pos_part, h₂, ← h₃] },
  filter_upwards [ae_eq],
  simp only [mem_set_of_eq],
  assume a h,
  rw [h, eq]
end

lemma neg_part_to_simple_func (f : α →₁ₛ ℝ) :
  ∀ₘ a, f.neg_part.to_simple_func a = f.to_simple_func.neg_part a :=
begin
  rw [simple_func.neg_part, measure_theory.simple_func.neg_part],
  filter_upwards [pos_part_to_simple_func (-f), neg_to_simple_func f],
  simp only [mem_set_of_eq],
  assume a h₁ h₂,
  rw h₁,
  show max _ _ = max _ _,
  rw h₂,
  refl
end

lemma integral_eq_norm_pos_part_sub (f : α →₁ₛ ℝ) : f.integral = ∥f.pos_part∥ - ∥f.neg_part∥ :=
begin
  -- Convert things in `L¹` to their `simple_func` counterpart
  have ae_eq₁ : ∀ₘ a, f.to_simple_func.pos_part a = (f.pos_part).to_simple_func.map norm a,
  { filter_upwards [pos_part_to_simple_func f],
    simp only [mem_set_of_eq],
    assume a h,
    rw [simple_func.map_apply, h],
    conv_lhs { rw [← simple_func.pos_part_map_norm, simple_func.map_apply] } },
  -- Convert things in `L¹` to their `simple_func` counterpart
  have ae_eq₂ : ∀ₘ a, f.to_simple_func.neg_part a = (f.neg_part).to_simple_func.map norm a,
  { filter_upwards [neg_part_to_simple_func f],
    simp only [mem_set_of_eq],
    assume a h,
    rw [simple_func.map_apply, h],
    conv_lhs { rw [← simple_func.neg_part_map_norm, simple_func.map_apply] } },
  -- Convert things in `L¹` to their `simple_func` counterpart
  have ae_eq : ∀ₘ a, f.to_simple_func.pos_part a - f.to_simple_func.neg_part a =
    (f.pos_part).to_simple_func.map norm a - (f.neg_part).to_simple_func.map norm a,
  { filter_upwards [ae_eq₁, ae_eq₂],
    simp only [mem_set_of_eq],
    assume a h₁ h₂,
    rw [h₁, h₂] },
  rw [integral, norm_eq_bintegral, norm_eq_bintegral, ← simple_func.bintegral_sub],
  { show f.to_simple_func.bintegral =
      ((f.pos_part.to_simple_func).map norm - f.neg_part.to_simple_func.map norm).bintegral,
    apply simple_func.bintegral_congr f.integrable,
    { show integrable (f.pos_part.to_simple_func.map norm - f.neg_part.to_simple_func.map norm),
      refine integrable_of_ae_eq _ _,
      { exact (f.to_simple_func.pos_part - f.to_simple_func.neg_part) },
      { exact (integrable.max_zero f.integrable).sub f.to_simple_func.pos_part.measurable
        f.to_simple_func.neg_part.measurable (integrable.max_zero f.integrable.neg) },
      exact ae_eq },
    filter_upwards [ae_eq₁, ae_eq₂],
    simp only [mem_set_of_eq],
    assume a h₁ h₂, show _ = _ - _,
    rw [← h₁, ← h₂],
    have := f.to_simple_func.pos_part_sub_neg_part,
    conv_lhs {rw ← this},
    refl },
  { refine integrable_of_ae_eq (integrable.max_zero f.integrable) ae_eq₁ },
  { refine integrable_of_ae_eq (integrable.max_zero f.integrable.neg) ae_eq₂ }
end

end pos_part

end simple_func_integral

end simple_func

open simple_func

variables [normed_space ℝ β] [normed_space ℝ γ] [complete_space β]

section integration_in_l1

local notation `to_l1` := coe_to_l1 α β ℝ
local attribute [instance] simple_func.normed_group simple_func.normed_space

open continuous_linear_map

/-- The Bochner integral in l1 space as a continuous linear map. -/
def integral_clm : (α →₁ β) →L[ℝ] β :=
  integral_clm.extend to_l1 simple_func.dense_range simple_func.uniform_inducing

/-- The Bochner integral in l1 space -/
def integral (f : α →₁ β) : β := (integral_clm).to_fun f

lemma integral_eq (f : α →₁ β) : integral f = (integral_clm).to_fun f := rfl

@[norm_cast] lemma simple_func.integral_eq_integral (f : α →₁ₛ β) :
  integral (f : α →₁ β) = f.integral :=
uniformly_extend_of_ind simple_func.uniform_inducing simple_func.dense_range
  simple_func.integral_clm.uniform_continuous _

variables (α β)
@[simp] lemma integral_zero : integral (0 : α →₁ β) = 0 :=
map_zero integral_clm
variables {α β}

lemma integral_add (f g : α →₁ β) : integral (f + g) = integral f + integral g :=
map_add integral_clm f g

lemma integral_neg (f : α →₁ β) : integral (-f) = - integral f :=
map_neg integral_clm f

lemma integral_sub (f g : α →₁ β) : integral (f - g) = integral f - integral g :=
map_sub integral_clm f g

lemma integral_smul (r : ℝ) (f : α →₁ β) : integral (r • f) = r • integral f :=
map_smul r integral_clm f

local notation `Integral` := @integral_clm α _ β _ _ _ _ _ _
local notation `sIntegral` := @simple_func.integral_clm α _ β _ _ _ _ _

lemma norm_Integral_le_one : ∥Integral∥ ≤ 1 :=
calc ∥Integral∥ ≤ (1 : nnreal) * ∥sIntegral∥ :
  op_norm_extend_le _ _ _ $ λs, by {rw [nnreal.coe_one, one_mul], refl}
  ... = ∥sIntegral∥ : one_mul _
  ... ≤ 1 : norm_Integral_le_one

lemma norm_integral_le (f : α →₁ β) : ∥integral f∥ ≤ ∥f∥ :=
calc ∥integral f∥ = ∥Integral f∥ : rfl
  ... ≤ ∥Integral∥ * ∥f∥ : le_op_norm _ _
  ... ≤ 1 * ∥f∥ : mul_le_mul_of_nonneg_right norm_Integral_le_one $ norm_nonneg _
  ... = ∥f∥ : one_mul _

section pos_part

lemma integral_eq_norm_pos_part_sub (f : α →₁ ℝ) : integral f = ∥pos_part f∥ - ∥neg_part f∥ :=
begin
  -- Use `is_closed_property` and `is_closed_eq`
  refine @is_closed_property _ _ _ (coe : (α →₁ₛ ℝ) → (α →₁ ℝ))
    (λ f : α →₁ ℝ, integral f = ∥pos_part f∥ - ∥neg_part f∥)
    l1.simple_func.dense_range (is_closed_eq _ _) _ f,
  { exact cont _ },
  { refine continuous.sub (continuous_norm.comp l1.continuous_pos_part)
      (continuous_norm.comp l1.continuous_neg_part) },
  -- Show that the property holds for all simple functions in the `L¹` space.
  { assume s,
    norm_cast,
    rw [← simple_func.norm_eq, ← simple_func.norm_eq],
    exact simple_func.integral_eq_norm_pos_part_sub _}
end

end pos_part

end integration_in_l1

end l1

variables [normed_group β] [second_countable_topology β] [normed_space ℝ β] [complete_space β]
  [measurable_space β] [borel_space β]
          [normed_group γ] [second_countable_topology γ] [normed_space ℝ γ] [complete_space γ]
  [measurable_space γ] [borel_space γ]

/-- The Bochner integral -/
def integral (f : α → β) : β :=
if hf : measurable f ∧ integrable f
then (l1.of_fun f hf.1 hf.2).integral
else 0

notation `∫` binders `, ` r:(scoped f, integral f) := r

section properties

open continuous_linear_map measure_theory.simple_func

variables {f g : α → β}

lemma integral_eq (f : α → β) (h₁ : measurable f) (h₂ : integrable f) :
  (∫ a, f a) = (l1.of_fun f h₁ h₂).integral :=
dif_pos ⟨h₁, h₂⟩

lemma integral_undef (h : ¬ (measurable f ∧ integrable f)) : (∫ a, f a) = 0 :=
dif_neg h

lemma integral_non_integrable (h : ¬ integrable f) : (∫ a, f a) = 0 :=
integral_undef $ not_and_of_not_right _ h

lemma integral_non_measurable (h : ¬ measurable f) : (∫ a, f a) = 0 :=
integral_undef $ not_and_of_not_left _ h

variables (α β)
@[simp] lemma integral_zero : (∫ a : α, (0:β)) = 0 :=
by rw [integral_eq, l1.of_fun_zero, l1.integral_zero]
variables {α β}

lemma integral_add
  (hfm : measurable f) (hfi : integrable f) (hgm : measurable g) (hgi : integrable g) :
  (∫ a, f a + g a) = (∫ a, f a) + (∫ a, g a) :=
by rw [integral_eq, integral_eq f hfm hfi, integral_eq g hgm hgi, l1.of_fun_add, l1.integral_add]

lemma integral_neg (f : α → β) : (∫ a, -f a) = - (∫ a, f a) :=
begin
  by_cases hf : measurable f ∧ integrable f,
  { rw [integral_eq f hf.1 hf.2, integral_eq (λa, - f a) hf.1.neg hf.2.neg, l1.of_fun_neg,
    l1.integral_neg] },
  { have hf' : ¬(measurable (λa, -f a) ∧ integrable (λa, -f a)),
    { rwa [measurable_neg_iff, integrable_neg_iff] },
    rw [integral_undef hf, integral_undef hf', neg_zero] }
end

lemma integral_sub
  (hfm : measurable f) (hfi : integrable f) (hgm : measurable g) (hgi : integrable g) :
  (∫ a, f a - g a) = (∫ a, f a) - (∫ a, g a) :=
by { rw [sub_eq_add_neg, ← integral_neg], exact integral_add hfm hfi hgm.neg hgi.neg }

lemma integral_smul (r : ℝ) (f : α → β) : (∫ a, r • (f a)) = r • (∫ a, f a) :=
begin
  by_cases hf : measurable f ∧ integrable f,
  { rw [integral_eq f hf.1 hf.2, integral_eq (λa, r • (f a)), l1.of_fun_smul, l1.integral_smul] },
  { by_cases hr : r = 0,
    { simp only [hr, measure_theory.integral_zero, zero_smul] },
    have hf' : ¬(measurable (λa, r • f a) ∧ integrable (λa, r • f a)),
    { rwa [measurable_const_smul_iff hr, integrable_smul_iff hr f]; apply_instance },
    rw [integral_undef hf, integral_undef hf', smul_zero] }
end

lemma integral_mul_left (r : ℝ) (f : α → ℝ) : (∫ a, r * (f a)) = r * (∫ a, f a) :=
integral_smul r f

lemma integral_mul_right (r : ℝ) (f : α → ℝ) : (∫ a, (f a) * r) = (∫ a, f a) * r :=
by { simp only [mul_comm], exact integral_mul_left r f }

lemma integral_div (r : ℝ) (f : α → ℝ) : (∫ a, (f a) / r) = (∫ a, f a) / r :=
integral_mul_right r⁻¹ f

lemma integral_congr_ae (hfm : measurable f) (hgm : measurable g) (h : ∀ₘ a, f a = g a) :
   (∫ a, f a) = (∫ a, g a) :=
begin
  by_cases hfi : integrable f,
  { have hgi : integrable g := integrable_of_ae_eq hfi h,
    rw [integral_eq f hfm hfi, integral_eq g hgm hgi, (l1.of_fun_eq_of_fun f g hfm hfi hgm hgi).2 h] },
  { have hgi : ¬ integrable g, { rw integrable_congr_ae h at hfi, exact hfi },
    rw [integral_non_integrable hfi, integral_non_integrable hgi] },
end

lemma norm_integral_le_lintegral_norm (f : α → β) :
  ∥(∫ a, f a)∥ ≤ ennreal.to_real (∫⁻ a, ennreal.of_real ∥f a∥) :=
begin
  by_cases hf : measurable f ∧ integrable f,
  { rw [integral_eq f hf.1 hf.2, ← l1.norm_of_fun_eq_lintegral_norm f hf.1 hf.2],
    exact l1.norm_integral_le _ },
  { rw [integral_undef hf, _root_.norm_zero],
    exact to_real_nonneg }
end

/-- Lebesgue dominated convergence theorem provides sufficient conditions under which almost
  everywhere convergence of a sequence of functions implies the convergence of their integrals. -/
theorem tendsto_integral_of_dominated_convergence {F : ℕ → α → β} {f : α → β} (bound : α → ℝ)
  (F_measurable : ∀ n, measurable (F n))
  (f_measurable : measurable f)
  (bound_integrable : integrable bound)
  (h_bound : ∀ n, ∀ₘ a, ∥F n a∥ ≤ bound a)
  (h_lim : ∀ₘ a, tendsto (λ n, F n a) at_top (𝓝 (f a))) :
  tendsto (λn, ∫ a, F n a) at_top (𝓝 $ (∫ a, f a)) :=
begin
  /- To show `(∫ a, F n a) --> (∫ f)`, suffices to show `∥∫ a, F n a - ∫ f∥ --> 0` -/
  rw tendsto_iff_norm_tendsto_zero,
  /- But `0 ≤ ∥∫ a, F n a - ∫ f∥ = ∥∫ a, (F n a - f a) ∥ ≤ ∫ a, ∥F n a - f a∥, and thus we apply the
    sandwich theorem and prove that `∫ a, ∥F n a - f a∥ --> 0` -/
  have lintegral_norm_tendsto_zero :
    tendsto (λn, ennreal.to_real $ ∫⁻ a, ennreal.of_real ∥F n a - f a∥) at_top (𝓝 0) :=
  (tendsto_to_real (zero_ne_top)).comp
    (tendsto_lintegral_norm_of_dominated_convergence
      F_measurable f_measurable bound_integrable h_bound h_lim),
  -- Use the sandwich theorem
  refine squeeze_zero (λ n, norm_nonneg _) _ lintegral_norm_tendsto_zero,
  -- Show `∥∫ a, F n a - ∫ f∥ ≤ ∫ a, ∥F n a - f a∥` for all `n`
  { assume n,
    have h₁ : integrable (F n) := integrable_of_integrable_bound bound_integrable (h_bound _),
    have h₂ : integrable f := integrable_of_dominated_convergence bound_integrable h_bound h_lim,
    rw ← integral_sub (F_measurable _) h₁ f_measurable h₂,
    exact norm_integral_le_lintegral_norm _ }
end

/-- Lebesgue dominated convergence theorem for filters with a countable basis -/
lemma tendsto_integral_filter_of_dominated_convergence {ι} {l : filter ι}
  {F : ι → α → β} {f : α → β} (bound : α → ℝ)
  (hl_cb : l.is_countably_generated)
  (hF_meas : ∀ᶠ n in l, measurable (F n))
  (f_measurable : measurable f)
  (h_bound : ∀ᶠ n in l, ∀ₘ a, ∥F n a∥ ≤ bound a)
  (bound_integrable : integrable bound)
  (h_lim : ∀ₘ a, tendsto (λ n, F n a) l (𝓝 (f a))) :
  tendsto (λn, ∫ a, F n a) l (𝓝 $ (∫ a, f a)) :=
begin
  rw hl_cb.tendsto_iff_seq_tendsto,
  { intros x xl,
    have hxl, { rw tendsto_at_top' at xl, exact xl },
    have h := inter_mem_sets hF_meas h_bound,
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
      simp only [mem_set_of_eq],
      assume a h_lim,
      apply @tendsto.comp _ _ _ (λn, x (n + k)) (λn, F n a),
      { assumption },
      rw tendsto_add_at_top_iff_nat,
      assumption } },
end

/-- The Bochner integral of a real-valued function `f : α → ℝ` is the difference between the
  integral of the positive part of `f` and the integral of the negative part of `f`.  -/
lemma integral_eq_lintegral_max_sub_lintegral_min {f : α → ℝ}
  (hfm : measurable f) (hfi : integrable f) : (∫ a, f a) =
  ennreal.to_real (∫⁻ a, ennreal.of_real $ max (f a) 0) -
  ennreal.to_real (∫⁻ a, ennreal.of_real $ - min (f a) 0) :=
let f₁ : α →₁ ℝ := l1.of_fun f hfm hfi in
-- Go to the `L¹` space
have eq₁ : ennreal.to_real (∫⁻ a, ennreal.of_real $ max (f a) 0) = ∥l1.pos_part f₁∥ :=
begin
  rw l1.norm_eq_norm_to_fun,
  congr' 1,
  apply lintegral_congr_ae,
  filter_upwards [l1.pos_part_to_fun f₁, l1.to_fun_of_fun f hfm hfi],
  simp only [mem_set_of_eq],
  assume a h₁ h₂,
  rw [h₁, h₂, real.norm_eq_abs, abs_of_nonneg],
  exact le_max_right _ _
end,
-- Go to the `L¹` space
have eq₂ : ennreal.to_real (∫⁻ a, ennreal.of_real $ -min (f a) 0) = ∥l1.neg_part f₁∥ :=
begin
  rw l1.norm_eq_norm_to_fun,
  congr' 1,
  apply lintegral_congr_ae,
  filter_upwards [l1.neg_part_to_fun_eq_min f₁, l1.to_fun_of_fun f hfm hfi],
  simp only [mem_set_of_eq],
  assume a h₁ h₂,
  rw [h₁, h₂, real.norm_eq_abs, abs_of_nonneg],
  rw [min_eq_neg_max_neg_neg, _root_.neg_neg, neg_zero],
  exact le_max_right _ _
end,
begin
  rw [eq₁, eq₂, integral, dif_pos],
  exact l1.integral_eq_norm_pos_part_sub _,
  { exact ⟨hfm, hfi⟩ }
end

lemma integral_eq_lintegral_of_nonneg_ae {f : α → ℝ} (hf : ∀ₘ a, 0 ≤ f a) (hfm : measurable f) :
  (∫ a, f a) = ennreal.to_real (∫⁻ a, ennreal.of_real $ f a) :=
begin
  by_cases hfi : integrable f,
  { rw integral_eq_lintegral_max_sub_lintegral_min hfm hfi,
    have h_min : (∫⁻ a, ennreal.of_real (-min (f a) 0)) = 0,
    { rw lintegral_eq_zero_iff,
      { filter_upwards [hf],
        simp only [mem_set_of_eq],
        assume a h,
        simp only [min_eq_right h, neg_zero, ennreal.of_real_zero] },
      { refine measurable_of_real.comp
          ((measurable.neg measurable_id).comp $ measurable.min hfm measurable_const) } },
    have h_max : (∫⁻ a, ennreal.of_real (max (f a) 0)) = (∫⁻ a, ennreal.of_real $ f a),
    { apply lintegral_congr_ae,
      filter_upwards [hf],
      simp only [mem_set_of_eq],
      assume a h,
      rw max_eq_left h },
    rw [h_min, h_max, zero_to_real, _root_.sub_zero] },
  { rw integral_non_integrable hfi,
    rw [integrable_iff_norm, lt_top_iff_ne_top, ne.def, not_not] at hfi,
    have : (∫⁻ (a : α), ennreal.of_real (f a)) = (∫⁻ a, ennreal.of_real ∥f a∥),
    { apply lintegral_congr_ae,
      filter_upwards [hf],
      simp only [mem_set_of_eq],
      assume a h,
      rw [real.norm_eq_abs, abs_of_nonneg h] },
    rw [this, hfi], refl }
end

lemma integral_nonneg_of_ae {f : α → ℝ} (hf : ∀ₘ a, 0 ≤ f a) : 0 ≤ (∫ a, f a) :=
begin
  by_cases hfm : measurable f,
  { rw integral_eq_lintegral_of_nonneg_ae hf hfm, exact to_real_nonneg },
  { rw integral_non_measurable hfm }
end

lemma integral_nonpos_of_nonpos_ae {f : α → ℝ} (hf : ∀ₘ a, f a ≤ 0) : (∫ a, f a) ≤ 0 :=
begin
  have hf : ∀ₘ a, 0 ≤ (-f) a,
  { filter_upwards [hf], simp only [mem_set_of_eq], assume a h, rwa [pi.neg_apply, neg_nonneg] },
  have : 0 ≤ (∫ a, -f a) := integral_nonneg_of_ae hf,
  rwa [integral_neg, neg_nonneg] at this,
end

lemma integral_le_integral_ae {f g : α → ℝ} (hfm : measurable f) (hfi : integrable f)
  (hgm : measurable g) (hgi : integrable g) (h : ∀ₘ a, f a ≤ g a) : (∫ a, f a) ≤ (∫ a, g a) :=
le_of_sub_nonneg
begin
  rw ← integral_sub hgm hgi hfm hfi,
  apply integral_nonneg_of_ae,
  filter_upwards [h],
  simp only [mem_set_of_eq],
  assume a,
  exact sub_nonneg_of_le
end

lemma integral_le_integral {f g : α → ℝ} (hfm : measurable f) (hfi : integrable f)
  (hgm : measurable g) (hgi : integrable g) (h : ∀ a, f a ≤ g a) : (∫ a, f a) ≤ (∫ a, g a) :=
integral_le_integral_ae hfm hfi hgm hgi $ univ_mem_sets' h

lemma norm_integral_le_integral_norm (f : α → β) : ∥(∫ a, f a)∥ ≤ ∫ a, ∥f a∥ :=
have le_ae : ∀ₘ (a : α), 0 ≤ ∥f a∥ := by filter_upwards [] λa, norm_nonneg _,
classical.by_cases
( λh : measurable f,
  calc ∥(∫ a, f a)∥ ≤ ennreal.to_real (∫⁻ a, ennreal.of_real ∥f a∥) : norm_integral_le_lintegral_norm _
    ... = ∫ a, ∥f a∥ : (integral_eq_lintegral_of_nonneg_ae le_ae $ measurable.norm h).symm )
( λh : ¬measurable f,
  begin
    rw [integral_non_measurable h, _root_.norm_zero],
    exact integral_nonneg_of_ae le_ae
  end )

lemma integral_finset_sum {ι} (s : finset ι) {f : ι → α → β}
  (hfm : ∀ i, measurable (f i)) (hfi : ∀ i, integrable (f i)) :
  (∫ a, s.sum (λ i, f i a)) = s.sum (λ i, ∫ a, f i a) :=
begin
  refine finset.induction_on s _ _,
  { simp only [integral_zero, finset.sum_empty] },
  { assume i s his ih,
    simp only [his, finset.sum_insert, not_false_iff],
    rw [integral_add (hfm _) (hfi _) (s.measurable_sum hfm)
        (integrable_finset_sum s hfm hfi), ih] }
end

end properties

mk_simp_attribute integral_simps "Simp set for integral rules."

attribute [integral_simps] integral_neg integral_smul l1.integral_add l1.integral_sub
  l1.integral_smul l1.integral_neg

attribute [irreducible] integral l1.integral

end measure_theory
