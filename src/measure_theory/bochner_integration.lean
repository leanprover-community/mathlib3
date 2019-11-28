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

Step 1: Define the integral on simple functions of the type `simple_func α β` (notation : `α →ₛ β`)
  where `β` is a real normed space.

  (See `simple_func.bintegral` and section `bintegral` for details. Also see `simple_func.integral`
  for the integral on simple functions of the type `simple_func α ennreal`.)

Step 2: Use `simple_func α β` to cut out the simple functions from L1 functions, and define integral
  on these. The type of simple functions in L1 space is written as `α →₁ₛ β`.

Step 3: Show that the embedding of `α →₁ₛ β` into L1 is a dense and uniform one.

Step 4: Show that the integral defined on `α →₁ₛ β` is a continuous linear map.

Step 5: Define the Bochner integral on L1 functions by extending the integral on integrable simple
  functions `α →₁ₛ β` using `continuous_linear_map.extend`. Define the Bochner integral on functions
  as the Bochner integral of its equivalence class in L1 space.

## Main statements

`section bintegral` : basic properties of `simple_func.bintegral` proved.

`section instances` : `l1.simple_func` forms a `normed_space`.

`section coe_to_l1` : `coe` from `l1.simple_func` to `l1` is a uniform and dense embedding.

`section simple_func_integral` : basic properties of `l1.simple_func.integral` proved.

## Notations

`α →ₛ β` : simple functions (defined in `measure_theory/integration`)
`α →₁ β` : functions in L1 space, i.e., equivalence classes of integrable functions (defined in
           `measure_theory/l1_space`)
`α →₁ₛ β` : simple functions in L1 space, i.e., equivalence classes of integrable simple functions

Note : `ₛ` is typed using `\_s`. Sometimes it shows as a box if font is missing.

## Tags

Bochner integral, simple function, function space

-/

noncomputable theory
open_locale classical

set_option class.instance_max_depth 100

namespace measure_theory
open set lattice filter topological_space ennreal emetric

universes u v w
variables {α : Type u} [measure_space α] {β : Type v} {γ : Type w}

local infixr ` →ₛ `:25 := simple_func

namespace simple_func

section bintegral
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
  ... = s'.sum (λb, (ennreal.to_real (volume (f ⁻¹' {b}))) • (g (f a))) : by rw [finset.smul_sum']
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
calc bintegral (f + g) = sum (pair f g).range
       (λx, ennreal.to_real (volume ((pair f g) ⁻¹' {x})) • (x.fst + x.snd)) :
begin
  rw [add_eq_map₂, map_bintegral (pair f g)],
  { exact integrable_pair hf hg },
  { simp only [add_zero, prod.fst_zero, prod.snd_zero] }
end
... = sum (pair f g).range
        (λx, ennreal.to_real (volume ((pair f g) ⁻¹' {x})) • x.fst +
             ennreal.to_real (volume ((pair f g) ⁻¹' {x})) • x.snd) :
  finset.sum_congr rfl $ assume a ha, smul_add _ _ _
... = sum (simple_func.range (pair f g))
        (λ (x : β × β), ennreal.to_real (volume ((pair f g) ⁻¹' {x})) • x.fst) +
      sum (simple_func.range (pair f g))
        (λ (x : β × β), ennreal.to_real (volume ((pair f g) ⁻¹' {x})) • x.snd) :
  by rw finset.sum_add_distrib
... = ((pair f g).map prod.fst).bintegral + ((pair f g).map prod.snd).bintegral :
begin
  rw [map_bintegral (pair f g), map_bintegral (pair f g)],
  { exact integrable_pair hf hg }, { refl },
  { exact integrable_pair hf hg }, { refl }
end
... = bintegral f + bintegral g : rfl

lemma bintegral_smul (r : ℝ) {f : α →ₛ β} (hf : integrable f) :
  bintegral (r • f) = r • bintegral f :=
calc bintegral (r • f) = sum f.range (λx, ennreal.to_real (volume (f ⁻¹' {x})) • r • x) :
  by rw [smul_eq_map r f, map_bintegral f _ hf (smul_zero _)]
... = (f.range).sum (λ (x : β), ((ennreal.to_real (volume (f ⁻¹' {x}))) * r) • x) :
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
  calc ∥sum f.range (λx, ennreal.to_real (volume (f ⁻¹' {x})) • x)∥ ≤
       sum f.range (λx, ∥ennreal.to_real (volume (f ⁻¹' {x})) • x∥) :
    norm_sum_le _ _
    ... = sum f.range (λx, ennreal.to_real (volume (f ⁻¹' {x})) • ∥x∥) :
    begin
      refine finset.sum_congr rfl (λb hb, _),
      rw [norm_smul, smul_eq_mul, real.norm_eq_abs, abs_of_nonneg to_real_nonneg]
    end
end

end bintegral

end simple_func

namespace l1

open ae_eq_fun

variables [normed_group β] [second_countable_topology β]
          [normed_group γ] [second_countable_topology γ]

variables (α β)
/-- `l1.simple_func` is a subspace of L1 consisting of equivalence classes of an integrable simple
    function. -/
def simple_func : Type* :=
{ f : α →₁ β // ∃ (s : α →ₛ β),  integrable s ∧ ae_eq_fun.mk s s.measurable = f}

variables {α β}

infixr ` →₁ₛ `:25 := measure_theory.l1.simple_func

namespace simple_func

section instances

instance : has_coe (α →₁ₛ β) (α →₁ β) := ⟨subtype.val⟩

protected lemma eq {f g : α →₁ₛ β} : (f : α →₁ β) = (g : α →₁ β) → f = g := subtype.eq
protected lemma eq' {f g : α →₁ₛ β} : (f : α →ₘ β) = (g : α →ₘ β) → f = g := subtype.eq ∘ subtype.eq

@[elim_cast] protected lemma eq_iff {f g : α →₁ₛ β} : (f : α →₁ β) = (g : α →₁ β) ↔ f = g :=
iff.intro (subtype.eq) (congr_arg coe)

@[elim_cast] protected lemma eq_iff' {f g : α →₁ₛ β} : (f : α →ₘ β) = (g : α →ₘ β) ↔ f = g :=
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
{ zero_mem := by { use 0, split, { exact integrable_zero }, { refl } },
  add_mem :=
  begin
    rintros f g ⟨s, hsi, hs⟩ ⟨t, hti, ht⟩,
    use s + t, split,
    { exact integrable_add s.measurable t.measurable hsi hti },
    { rw [coe_add, ← hs, ← ht], refl }
  end,
  neg_mem :=
  begin
    rintros f ⟨s, hsi, hs⟩,
    use -s, split,
    { exact integrable_neg hsi },
    { rw [coe_neg, ← hs], refl }
  end }

/-- Not declared as an instance as `α →₁ₛ β` will only be useful in the construction of the bochner
  integral. -/
protected def add_comm_group : add_comm_group (α →₁ₛ β) := subtype.add_comm_group

local attribute [instance] simple_func.add_comm_group simple_func.metric_space
  simple_func.emetric_space

@[simp] lemma coe_zero : ((0 : α →₁ₛ β) : α →₁ β) = 0 := rfl
@[simp] lemma coe_add (f g : α →₁ₛ β) : ((f + g : α →₁ₛ β) : α →₁ β) = f + g := rfl
@[simp] lemma coe_neg (f : α →₁ₛ β) : ((-f : α →₁ₛ β) : α →₁ β) = -f := rfl
@[simp] lemma coe_sub (f g : α →₁ₛ β) : ((f - g : α →₁ₛ β) : α →₁ β) = f - g := rfl
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
  { exact integrable_smul _ hsi },
  { rw [coe_smul, subtype.coe_mk, ← hs], refl }
end ⟩⟩

local attribute [instance] simple_func.has_scalar

@[simp] lemma coe_smul (c : 𝕜) (f : α →₁ₛ β) : ((c • f : α →₁ₛ β) : α →₁ β) = c • (f : α →₁ β) := rfl

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

lemma of_simple_func_zero : of_simple_func (0 : α →ₛ β) integrable_zero = 0 := rfl

lemma of_simple_func_add (f g : α →ₛ β) (hf hg) :
  of_simple_func (f + g) (integrable_add f.measurable g.measurable hf hg) = of_simple_func f hf +
    of_simple_func g hg := rfl

lemma of_simple_func_neg (f : α →ₛ β) (hf) :
  of_simple_func (-f) (integrable_neg hf) = -of_simple_func f hf := rfl

lemma of_simple_func_sub (f g : α →ₛ β) (hf hg) :
  of_simple_func (f - g) (integrable_sub f.measurable g.measurable hf hg) = of_simple_func f hf -
    of_simple_func g hg := rfl

variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 β]

lemma of_simple_func_smul (f : α →ₛ β) (hf) (c : 𝕜) :
  of_simple_func (c • f) (integrable_smul _ hf) = c • of_simple_func f hf := rfl

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
ne_empty_iff_exists_mem.2 ⟨_, hε (metric.mem_ball'.2 h), s, rfl⟩

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

section simple_func_integral

variables [normed_space ℝ β]

/-- The Bochner integral over simple functions in l1 space. -/
def integral (f : α →₁ₛ β) : β := simple_func.bintegral (f.to_simple_func)

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
    { exact integrable_add f.measurable g.measurable f.integrable g.integrable },
    { apply add_to_simple_func },
end

lemma integral_smul (r : ℝ) (f : α →₁ₛ β) : integral (r • f) = r • integral f :=
begin
  simp only [integral],
  rw ← simple_func.bintegral_smul _ f.integrable,
  apply simple_func.bintegral_congr (r • f).integrable,
    { exact integrable_smul _ f.integrable },
    { apply smul_to_simple_func }
end

lemma norm_integral_le_norm (f : α →₁ₛ β) : ∥ integral f ∥ ≤ ∥f∥ :=
begin
  rw [integral, norm_eq_bintegral],
  exact f.to_simple_func.norm_bintegral_le_bintegral_norm f.integrable
end

/-- The Bochner integral over simple functions in l1 space as a continuous linear map. -/
def integral_clm : (α →₁ₛ β) →L[ℝ] β :=
linear_map.with_bound ⟨integral, integral_add, integral_smul⟩
  ⟨1, (λf, le_trans (norm_integral_le_norm _) $ by rw one_mul)⟩

local notation `Integral` := @integral_clm α _ β _ _ _

open continuous_linear_map

lemma norm_Integral_le_one : ∥Integral∥ ≤ 1 :=
begin
  apply op_norm_le_bound,
  { exact zero_le_one },
  assume f,
  rw [one_mul],
  exact norm_integral_le_norm _
end

end simple_func_integral

end simple_func

open simple_func

variables [normed_space ℝ β] [normed_space ℝ γ] [complete_space β]

local notation `to_l1` := coe_to_l1 α β ℝ
local attribute [instance] simple_func.normed_group simple_func.normed_space

open continuous_linear_map

/-- The Bochner integral in l1 space as a continuous linear map. -/
def integral_clm : (α →₁ β) →L[ℝ] β :=
  integral_clm.extend to_l1 simple_func.dense_range simple_func.uniform_inducing

/-- The Bochner integral in l1 space -/
def integral (f : α →₁ β) : β := (integral_clm).to_fun f

lemma integral_eq (f : α →₁ β) : integral f = (integral_clm).to_fun f := rfl

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

end l1

variables [normed_group β] [second_countable_topology β] [normed_space ℝ β] [complete_space β]
          [normed_group γ] [second_countable_topology γ] [normed_space ℝ γ] [complete_space γ]

/-- The Bochner integral -/
def integral (f : α → β) : β :=
if hf : measurable f ∧ integrable f
then (l1.of_fun f hf.1 hf.2).integral
else 0

section properties

open continuous_linear_map measure_theory.simple_func

variables {f g : α → β}

lemma integral_eq (f : α → β) : integral f =
  if hf : measurable f ∧ integrable f then (l1.of_fun f hf.1 hf.2).integral else 0 := rfl

lemma integral_zero_of_non_measurable (h : ¬ measurable f) : integral f = 0 :=
by { rw [integral, dif_neg], rw not_and_distrib, exact or.inl h }

lemma integral_zero_of_non_integrable (h : ¬ integrable f) : integral f = 0 :=
by { rw [integral, dif_neg], rw not_and_distrib, exact or.inr h }

variables (α β)
@[simp] lemma integral_zero : integral (0 : α → β) = 0 :=
begin
  simp only [integral], rw dif_pos,
  { apply l1.integral_zero },
  { exact ⟨(measurable_const : measurable (λb:α, (0:β))), integrable_zero⟩ }
end
variables {α β}

lemma integral_add (hfm : measurable f) (hfi : integrable f) (hgm : measurable g)
  (hgi : integrable g) : integral (f + g) = integral f + integral g :=
begin
  simp only [integral], repeat { rw dif_pos },
  { rw ← l1.integral_add, refl },
  { exact ⟨hgm, hgi⟩ },
  { exact ⟨hfm, hfi⟩ },
  { exact ⟨measurable_add hfm hgm, integrable_add hfm hgm hfi hgi⟩ }
end

lemma integral_neg (f : α → β) : integral (-f) = - integral f :=
begin
  simp only [integral],
  by_cases hfm : measurable f, by_cases hfi : integrable f,
  { repeat { rw dif_pos },
    { rw ← l1.integral_neg, refl },
    { exact ⟨hfm, hfi⟩ },
    { exact ⟨measurable_neg hfm, integrable_neg hfi⟩ } },
  { repeat { rw dif_neg },
    { rw neg_zero },
    { rw not_and_distrib, exact or.inr hfi },
    { rw not_and_distrib, rw integrable_neg_iff, exact or.inr hfi } },
  { repeat { rw dif_neg },
    { rw neg_zero },
    { rw not_and_distrib, exact or.inl hfm },
    { rw not_and_distrib, rw measurable_neg_iff, exact or.inl hfm } }
end

lemma integral_sub (hfm : measurable f) (hfi : integrable f) (hgm : measurable g)
  (hgi : integrable g) : integral (f - g) = integral f - integral g :=
begin
  simp only [integral], repeat {rw dif_pos},
  { rw ← l1.integral_sub, refl },
  { exact ⟨hgm, hgi⟩ },
  { exact ⟨hfm, hfi⟩ },
  { exact ⟨measurable_sub hfm hgm, integrable_sub hfm hgm hfi hgi⟩ }
end

lemma integral_smul (r : ℝ) (f : α → β) : integral (λx, r • (f x)) = r • integral f :=
begin
  by_cases r0 : r = 0,
  { have : (λx, r • (f x)) = 0, { funext, rw [r0, zero_smul, pi.zero_apply] },
    rw [this, r0, zero_smul], apply integral_zero },
  simp only [integral],
  by_cases hfm : measurable f, by_cases hfi : integrable f,
  { rw dif_pos, rw dif_pos,
    { rw ← l1.integral_smul, refl  },
    { exact ⟨hfm, hfi⟩ },
    { exact ⟨measurable_smul _ hfm, integrable_smul _ hfi⟩ } },
  { repeat { rw dif_neg },
    { rw smul_zero },
    { rw not_and_distrib, exact or.inr hfi },
    { rw not_and_distrib,
      have : (λx, r • (f x)) = r • f, { funext, simp only [pi.smul_apply] },
      rw [this, integrable_smul_iff r0], exact or.inr hfi } },
  { repeat { rw dif_neg },
    { rw smul_zero },
    { rw not_and_distrib, exact or.inl hfm },
    { rw not_and_distrib, rw [measurable_smul_iff r0], exact or.inl hfm, apply_instance } },
end

lemma integral_congr (h : ∀ a, f a = g a) : integral f = integral g :=
begin
  sorry
end

lemma integral_congr_ae (h : ∀ₘ a, f a = g a) : integral f = integral g :=
begin
  sorry
end

/-- T : β →L[𝕜] β?-/
lemma integral_bounded_linear (T : β →L[ℝ] β) : integral (λa, T (f a)) =  T (integral f) :=
begin
  sorry
end

lemma integral_bounded_linear' (T T' : β →L[ℝ] β)
  (h : ¬ (∀b, T b = 0) → (∀b, T' (T b) = b)) : integral (λx, T (f x)) = T (integral f) :=
begin
  sorry
end

#check lintegral_const_mul

end properties

run_cmd mk_simp_attr `integral_simps

attribute [integral_simps] integral_neg integral_smul l1.integral_add l1.integral_sub
  l1.integral_smul l1.integral_neg

attribute [irreducible] integral l1.integral

end measure_theory
