/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
import analysis.normed.group.hom
import measure_theory.function.lp_seminorm
import topology.continuous_function.compact

/-!
# ℒp space and Lp space

This file provides the space `Lp E p μ` as the subtype of elements of `α →ₘ[μ] E` (see ae_eq_fun)
such that `snorm f p μ` is finite. For `1 ≤ p`, `snorm` defines a norm and `Lp` is a complete metric space.

## Main definitions

* `Lp E p μ` : elements of `α →ₘ[μ] E` (see ae_eq_fun) such that `snorm f p μ` is finite. Defined
  as an `add_subgroup` of `α →ₘ[μ] E`.

Lipschitz functions vanishing at zero act by composition on `Lp`. We define this action, and prove
that it is continuous. In particular,
* `continuous_linear_map.comp_Lp` defines the action on `Lp` of a continuous linear map.
* `Lp.pos_part` is the positive part of an `Lp` function.
* `Lp.neg_part` is the negative part of an `Lp` function.

When `α` is a topological space equipped with a finite Borel measure, there is a bounded linear map
from the normed space of bounded continuous functions (`α →ᵇ E`) to `Lp E p μ`.  We construct this
as `bounded_continuous_function.to_Lp`.

## Notations

* `α →₁[μ] E` : the type `Lp E 1 μ`.
* `α →₂[μ] E` : the type `Lp E 2 μ`.

## Implementation

Since `Lp` is defined as an `add_subgroup`, dot notation does not work. Use `Lp.measurable f` to
say that the coercion of `f` to a genuine function is measurable, instead of the non-working
`f.measurable`.

To prove that two `Lp` elements are equal, it suffices to show that their coercions to functions
coincide almost everywhere (this is registered as an `ext` rule). This can often be done using
`filter_upwards`. For instance, a proof from first principles that `f + (g + h) = (f + g) + h`
could read (in the `Lp` namespace)
```
example (f g h : Lp E p μ) : (f + g) + h = f + (g + h) :=
begin
  ext1,
  filter_upwards [coe_fn_add (f + g) h, coe_fn_add f g, coe_fn_add f (g + h), coe_fn_add g h]
    with _ ha1 ha2 ha3 ha4,
  simp only [ha1, ha2, ha3, ha4, add_assoc],
end
```
The lemma `coe_fn_add` states that the coercion of `f + g` coincides almost everywhere with the sum
of the coercions of `f` and `g`. All such lemmas use `coe_fn` in their name, to distinguish the
function coercion from the coercion to almost everywhere defined functions.
-/

noncomputable theory
open topological_space measure_theory filter
open_locale nnreal ennreal big_operators topology measure_theory

variables {α E F G : Type*} {m m0 : measurable_space α} {p : ℝ≥0∞} {q : ℝ} {μ ν : measure α}
  [normed_add_comm_group E] [normed_add_comm_group F] [normed_add_comm_group G]

namespace measure_theory

/-!
### Lp space

The space of equivalence classes of measurable functions for which `snorm f p μ < ∞`.
-/

@[simp] lemma snorm_ae_eq_fun {α E : Type*} [measurable_space α] {μ : measure α}
  [normed_add_comm_group E] {p : ℝ≥0∞} {f : α → E} (hf : ae_strongly_measurable f μ) :
  snorm (ae_eq_fun.mk f hf) p μ = snorm f p μ :=
snorm_congr_ae (ae_eq_fun.coe_fn_mk _ _)

lemma mem_ℒp.snorm_mk_lt_top {α E : Type*} [measurable_space α] {μ : measure α}
  [normed_add_comm_group E] {p : ℝ≥0∞} {f : α → E} (hfp : mem_ℒp f p μ) :
  snorm (ae_eq_fun.mk f hfp.1) p μ < ∞ :=
by simp [hfp.2]

/-- Lp space -/
def Lp {α} (E : Type*) {m : measurable_space α} [normed_add_comm_group E]
  (p : ℝ≥0∞) (μ : measure α . volume_tac) : add_subgroup (α →ₘ[μ] E) :=
{ carrier := {f | snorm f p μ < ∞},
  zero_mem' := by simp [snorm_congr_ae ae_eq_fun.coe_fn_zero, snorm_zero],
  add_mem' := λ f g hf hg, by simp [snorm_congr_ae (ae_eq_fun.coe_fn_add _ _),
    snorm_add_lt_top ⟨f.ae_strongly_measurable, hf⟩ ⟨g.ae_strongly_measurable, hg⟩],
  neg_mem' := λ f hf,
    by rwa [set.mem_set_of_eq, snorm_congr_ae (ae_eq_fun.coe_fn_neg _), snorm_neg] }

localized "notation (name := measure_theory.L1)
  α ` →₁[`:25 μ `] ` E := measure_theory.Lp E 1 μ" in measure_theory
localized "notation (name := measure_theory.L2)
  α ` →₂[`:25 μ `] ` E := measure_theory.Lp E 2 μ" in measure_theory

namespace mem_ℒp

/-- make an element of Lp from a function verifying `mem_ℒp` -/
def to_Lp (f : α → E) (h_mem_ℒp : mem_ℒp f p μ) : Lp E p μ :=
⟨ae_eq_fun.mk f h_mem_ℒp.1, h_mem_ℒp.snorm_mk_lt_top⟩

lemma coe_fn_to_Lp {f : α → E} (hf : mem_ℒp f p μ) : hf.to_Lp f =ᵐ[μ] f :=
ae_eq_fun.coe_fn_mk _ _

lemma to_Lp_congr {f g : α → E} (hf : mem_ℒp f p μ) (hg : mem_ℒp g p μ) (hfg : f =ᵐ[μ] g) :
  hf.to_Lp f = hg.to_Lp g :=
by simp [to_Lp, hfg]

@[simp] lemma to_Lp_eq_to_Lp_iff {f g : α → E} (hf : mem_ℒp f p μ) (hg : mem_ℒp g p μ) :
  hf.to_Lp f = hg.to_Lp g ↔ f =ᵐ[μ] g :=
by simp [to_Lp]

@[simp] lemma to_Lp_zero (h : mem_ℒp (0 : α → E) p μ) : h.to_Lp 0 = 0 := rfl

lemma to_Lp_add {f g : α → E} (hf : mem_ℒp f p μ) (hg : mem_ℒp g p μ) :
  (hf.add hg).to_Lp (f + g) = hf.to_Lp f + hg.to_Lp g := rfl

lemma to_Lp_neg {f : α → E} (hf : mem_ℒp f p μ) : hf.neg.to_Lp (-f) = - hf.to_Lp f := rfl

lemma to_Lp_sub {f g : α → E} (hf : mem_ℒp f p μ) (hg : mem_ℒp g p μ) :
  (hf.sub hg).to_Lp (f - g) = hf.to_Lp f - hg.to_Lp g := rfl

end mem_ℒp

namespace Lp

instance : has_coe_to_fun (Lp E p μ) (λ _, α → E) := ⟨λ f, ((f : α →ₘ[μ] E) : α → E)⟩

@[ext] lemma ext {f g : Lp E p μ} (h : f =ᵐ[μ] g) : f = g :=
begin
  cases f,
  cases g,
  simp only [subtype.mk_eq_mk],
  exact ae_eq_fun.ext h
end

lemma ext_iff {f g : Lp E p μ} : f = g ↔ f =ᵐ[μ] g :=
⟨λ h, by rw h, λ h, ext h⟩

lemma mem_Lp_iff_snorm_lt_top {f : α →ₘ[μ] E} : f ∈ Lp E p μ ↔ snorm f p μ < ∞ := iff.refl _

lemma mem_Lp_iff_mem_ℒp {f : α →ₘ[μ] E} : f ∈ Lp E p μ ↔ mem_ℒp f p μ :=
by simp [mem_Lp_iff_snorm_lt_top, mem_ℒp, f.strongly_measurable.ae_strongly_measurable]

protected lemma antitone [is_finite_measure μ] {p q : ℝ≥0∞} (hpq : p ≤ q) : Lp E q μ ≤ Lp E p μ :=
λ f hf, (mem_ℒp.mem_ℒp_of_exponent_le ⟨f.ae_strongly_measurable, hf⟩ hpq).2

@[simp] lemma coe_fn_mk {f : α →ₘ[μ] E} (hf : snorm f p μ < ∞) :
  ((⟨f, hf⟩ : Lp E p μ) : α → E) = f := rfl

@[simp] lemma coe_mk {f : α →ₘ[μ] E} (hf : snorm f p μ < ∞) :
  ((⟨f, hf⟩ : Lp E p μ) : α →ₘ[μ] E) = f := rfl

@[simp] lemma to_Lp_coe_fn (f : Lp E p μ) (hf : mem_ℒp f p μ) : hf.to_Lp f = f :=
by { cases f, simp [mem_ℒp.to_Lp] }

lemma snorm_lt_top (f : Lp E p μ) : snorm f p μ < ∞ := f.prop

lemma snorm_ne_top (f : Lp E p μ) : snorm f p μ ≠ ∞ := (snorm_lt_top f).ne

@[measurability]
protected lemma strongly_measurable (f : Lp E p μ) : strongly_measurable f :=
f.val.strongly_measurable

@[measurability]
protected lemma ae_strongly_measurable (f : Lp E p μ) : ae_strongly_measurable f μ :=
f.val.ae_strongly_measurable

protected lemma mem_ℒp (f : Lp E p μ) : mem_ℒp f p μ := ⟨Lp.ae_strongly_measurable f, f.prop⟩

variables (E p μ)
lemma coe_fn_zero : ⇑(0 : Lp E p μ) =ᵐ[μ] 0 := ae_eq_fun.coe_fn_zero
variables {E p μ}

lemma coe_fn_neg (f : Lp E p μ) : ⇑(-f) =ᵐ[μ] -f := ae_eq_fun.coe_fn_neg _

lemma coe_fn_add (f g : Lp E p μ) : ⇑(f + g) =ᵐ[μ] f + g := ae_eq_fun.coe_fn_add _ _

lemma coe_fn_sub (f g : Lp E p μ) : ⇑(f - g) =ᵐ[μ] f - g := ae_eq_fun.coe_fn_sub _ _

lemma mem_Lp_const (α) {m : measurable_space α} (μ : measure α) (c : E) [is_finite_measure μ] :
  @ae_eq_fun.const α _ _ μ _ c ∈ Lp E p μ :=
(mem_ℒp_const c).snorm_mk_lt_top

instance : has_norm (Lp E p μ) := { norm := λ f, ennreal.to_real (snorm f p μ) }

-- note: we need this to be defeq to the instance from `seminormed_add_group.to_has_nnnorm`, so
-- can't use `ennreal.to_nnreal (snorm f p μ)`
instance : has_nnnorm (Lp E p μ) := { nnnorm := λ f, ⟨‖f‖, ennreal.to_real_nonneg⟩ }

instance : has_dist (Lp E p μ) := { dist := λ f g, ‖f - g‖}

instance : has_edist (Lp E p μ) := { edist := λ f g, snorm (f - g) p μ }

lemma norm_def (f : Lp E p μ) : ‖f‖ = ennreal.to_real (snorm f p μ) := rfl

lemma nnnorm_def (f : Lp E p μ) : ‖f‖₊ = ennreal.to_nnreal (snorm f p μ) := subtype.eta _ _

@[simp, norm_cast] protected lemma coe_nnnorm (f : Lp E p μ) : (‖f‖₊ : ℝ) = ‖f‖ := rfl

@[simp] lemma norm_to_Lp (f : α → E) (hf : mem_ℒp f p μ) :
  ‖hf.to_Lp f‖ = ennreal.to_real (snorm f p μ) :=
by rw [norm_def, snorm_congr_ae (mem_ℒp.coe_fn_to_Lp hf)]

@[simp] lemma nnnorm_to_Lp (f : α → E) (hf : mem_ℒp f p μ) :
  ‖hf.to_Lp f‖₊ = ennreal.to_nnreal (snorm f p μ) :=
nnreal.eq $ norm_to_Lp f hf

lemma dist_def (f g : Lp E p μ) : dist f g = (snorm (f - g) p μ).to_real :=
begin
  simp_rw [dist, norm_def],
  congr' 1,
  apply snorm_congr_ae (coe_fn_sub _ _),
end

lemma edist_def (f g : Lp E p μ) : edist f g = snorm (f - g) p μ :=
rfl

@[simp] lemma edist_to_Lp_to_Lp (f g : α → E) (hf : mem_ℒp f p μ) (hg : mem_ℒp g p μ) :
  edist (hf.to_Lp f) (hg.to_Lp g) = snorm (f - g) p μ :=
by { rw edist_def, exact snorm_congr_ae (hf.coe_fn_to_Lp.sub hg.coe_fn_to_Lp) }

@[simp] lemma edist_to_Lp_zero (f : α → E) (hf : mem_ℒp f p μ) :
  edist (hf.to_Lp f) 0 = snorm f p μ :=
by { convert edist_to_Lp_to_Lp f 0 hf zero_mem_ℒp, simp }

@[simp] lemma nnnorm_zero : ‖(0 : Lp E p μ)‖₊ = 0 :=
begin
  rw [nnnorm_def],
  change (snorm ⇑(0 : α →ₘ[μ] E) p μ).to_nnreal = 0,
  simp [snorm_congr_ae ae_eq_fun.coe_fn_zero, snorm_zero]
end

@[simp] lemma norm_zero : ‖(0 : Lp E p μ)‖ = 0 :=
congr_arg coe nnnorm_zero

lemma nnnorm_eq_zero_iff {f : Lp E p μ} (hp : 0 < p) : ‖f‖₊ = 0 ↔ f = 0 :=
begin
  refine ⟨λ hf, _, λ hf, by simp [hf]⟩,
  rw [nnnorm_def, ennreal.to_nnreal_eq_zero_iff] at hf,
  cases hf,
  { rw snorm_eq_zero_iff (Lp.ae_strongly_measurable f) hp.ne.symm at hf,
    exact subtype.eq (ae_eq_fun.ext (hf.trans ae_eq_fun.coe_fn_zero.symm)), },
  { exact absurd hf (snorm_ne_top f), },
end

lemma norm_eq_zero_iff {f : Lp E p μ} (hp : 0 < p) : ‖f‖ = 0 ↔ f = 0 :=
iff.symm $ (nnnorm_eq_zero_iff hp).symm.trans $ (nnreal.coe_eq_zero _).symm

lemma eq_zero_iff_ae_eq_zero {f : Lp E p μ} : f = 0 ↔ f =ᵐ[μ] 0 :=
begin
  split,
  { assume h,
    rw h,
    exact ae_eq_fun.coe_fn_const _ _ },
  { assume h,
    ext1,
    filter_upwards [h, ae_eq_fun.coe_fn_const α (0 : E)] with _ ha h'a,
    rw ha,
    exact h'a.symm, },
end

@[simp] lemma nnnorm_neg (f : Lp E p μ) : ‖-f‖₊ = ‖f‖₊ :=
by rw [nnnorm_def, nnnorm_def, snorm_congr_ae (coe_fn_neg _), snorm_neg]

@[simp] lemma norm_neg (f : Lp E p μ) : ‖-f‖ = ‖f‖ :=
(congr_arg (coe : ℝ≥0 → ℝ) (nnnorm_neg f) : _)

lemma nnnorm_le_mul_nnnorm_of_ae_le_mul {c : ℝ≥0} {f : Lp E p μ} {g : Lp F p μ}
  (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ c * ‖g x‖₊ ) : ‖f‖₊ ≤ c * ‖g‖₊  :=
begin
  simp only [nnnorm_def],
  have := snorm_le_nnreal_smul_snorm_of_ae_le_mul h p,
  rwa [← ennreal.to_nnreal_le_to_nnreal, ennreal.smul_def, smul_eq_mul, ennreal.to_nnreal_mul,
    ennreal.to_nnreal_coe] at this,
  { exact (Lp.mem_ℒp _).snorm_ne_top },
  { exact ennreal.mul_ne_top ennreal.coe_ne_top (Lp.mem_ℒp _).snorm_ne_top },
end

lemma norm_le_mul_norm_of_ae_le_mul {c : ℝ} {f : Lp E p μ} {g : Lp F p μ}
  (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖) : ‖f‖ ≤ c * ‖g‖ :=
begin
  cases le_or_lt 0 c with hc hc,
  { lift c to ℝ≥0 using hc,
    exact nnreal.coe_le_coe.mpr (nnnorm_le_mul_nnnorm_of_ae_le_mul h) },
  { simp only [norm_def],
    have := snorm_eq_zero_and_zero_of_ae_le_mul_neg h hc p,
    simp [this] }
end

lemma norm_le_norm_of_ae_le {f : Lp E p μ} {g : Lp F p μ} (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) :
  ‖f‖ ≤ ‖g‖ :=
begin
  rw [norm_def, norm_def, ennreal.to_real_le_to_real (snorm_ne_top _) (snorm_ne_top _)],
  exact snorm_mono_ae h
end

lemma mem_Lp_of_nnnorm_ae_le_mul {c : ℝ≥0} {f : α →ₘ[μ] E} {g : Lp F p μ}
  (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ c * ‖g x‖₊) :
  f ∈ Lp E p μ :=
mem_Lp_iff_mem_ℒp.2 $ mem_ℒp.of_nnnorm_le_mul (Lp.mem_ℒp g) f.ae_strongly_measurable h

lemma mem_Lp_of_ae_le_mul {c : ℝ} {f : α →ₘ[μ] E} {g : Lp F p μ} (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖) :
  f ∈ Lp E p μ :=
mem_Lp_iff_mem_ℒp.2 $ mem_ℒp.of_le_mul (Lp.mem_ℒp g) f.ae_strongly_measurable h

lemma mem_Lp_of_nnnorm_ae_le {f : α →ₘ[μ] E} {g : Lp F p μ} (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ ‖g x‖₊) :
  f ∈ Lp E p μ :=
mem_Lp_iff_mem_ℒp.2 $ mem_ℒp.of_le (Lp.mem_ℒp g) f.ae_strongly_measurable h

lemma mem_Lp_of_ae_le {f : α →ₘ[μ] E} {g : Lp F p μ} (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) :
  f ∈ Lp E p μ :=
mem_Lp_of_nnnorm_ae_le h

lemma mem_Lp_of_ae_nnnorm_bound [is_finite_measure μ] {f : α →ₘ[μ] E} (C : ℝ≥0)
  (hfC : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ C) :
  f ∈ Lp E p μ :=
mem_Lp_iff_mem_ℒp.2 $ mem_ℒp.of_bound f.ae_strongly_measurable _ hfC

lemma mem_Lp_of_ae_bound [is_finite_measure μ] {f : α →ₘ[μ] E} (C : ℝ) (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
  f ∈ Lp E p μ :=
mem_Lp_iff_mem_ℒp.2 $ mem_ℒp.of_bound f.ae_strongly_measurable _ hfC

lemma nnnorm_le_of_ae_bound [is_finite_measure μ] {f : Lp E p μ} {C : ℝ≥0}
  (hfC : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ C) :
  ‖f‖₊ ≤ (measure_univ_nnreal μ) ^ (p.to_real)⁻¹ * C :=
begin
  by_cases hμ : μ = 0,
  { by_cases hp : p.to_real⁻¹ = 0,
    { simp [hp, hμ, nnnorm_def] },
    { simp [hμ, nnnorm_def, real.zero_rpow hp] } },
  rw [←ennreal.coe_le_coe, nnnorm_def, ennreal.coe_to_nnreal (snorm_ne_top _)],
  refine (snorm_le_of_ae_nnnorm_bound hfC).trans_eq _,
  rw [← coe_measure_univ_nnreal μ, ennreal.coe_rpow_of_ne_zero (measure_univ_nnreal_pos hμ).ne',
    ennreal.coe_mul, mul_comm, ennreal.smul_def, smul_eq_mul],
end

lemma norm_le_of_ae_bound [is_finite_measure μ] {f : Lp E p μ} {C : ℝ} (hC : 0 ≤ C)
  (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
  ‖f‖ ≤ (measure_univ_nnreal μ) ^ (p.to_real)⁻¹ * C :=
begin
  lift C to ℝ≥0 using hC,
  have := nnnorm_le_of_ae_bound hfC,
  rwa [←nnreal.coe_le_coe, nnreal.coe_mul, nnreal.coe_rpow] at this,
end

instance [hp : fact (1 ≤ p)] : normed_add_comm_group (Lp E p μ) :=
{ edist := edist,
  edist_dist := λ f g, by
    rw [edist_def, dist_def, ←snorm_congr_ae (coe_fn_sub _ _),
      ennreal.of_real_to_real (snorm_ne_top (f - g))],
  ..add_group_norm.to_normed_add_comm_group
    { to_fun := (norm : Lp E p μ → ℝ),
      map_zero' := norm_zero,
      neg' := by simp,
      add_le' := λ f g, begin
        simp only [norm_def],
        rw ← ennreal.to_real_add (snorm_ne_top f) (snorm_ne_top g),
        suffices h_snorm : snorm ⇑(f + g) p μ ≤ snorm ⇑f p μ + snorm ⇑g p μ,
        { rwa ennreal.to_real_le_to_real (snorm_ne_top (f + g)),
          exact ennreal.add_ne_top.mpr ⟨snorm_ne_top f, snorm_ne_top g⟩, },
        rw [snorm_congr_ae (coe_fn_add _ _)],
        exact snorm_add_le (Lp.ae_strongly_measurable f) (Lp.ae_strongly_measurable g) hp.1,
      end,
      eq_zero_of_map_eq_zero' := λ f, (norm_eq_zero_iff $ zero_lt_one.trans_le hp.1).1 } }

-- check no diamond is created
example [fact (1 ≤ p)] :
  pseudo_emetric_space.to_has_edist = (Lp.has_edist : has_edist (Lp E p μ)) :=
rfl

example [fact (1 ≤ p)] :
  seminormed_add_group.to_has_nnnorm = (Lp.has_nnnorm : has_nnnorm (Lp E p μ)) :=
rfl

section has_bounded_smul

variables {𝕜 𝕜' : Type*}
variables [normed_ring 𝕜] [normed_ring 𝕜'] [module 𝕜 E] [module 𝕜' E]
variables [has_bounded_smul 𝕜 E] [has_bounded_smul 𝕜' E]

lemma mem_Lp_const_smul (c : 𝕜) (f : Lp E p μ) : c • ↑f ∈ Lp E p μ :=
begin
  rw [mem_Lp_iff_snorm_lt_top, snorm_congr_ae (ae_eq_fun.coe_fn_smul _ _)],
  refine (snorm_const_smul_le _ _).trans_lt _,
  rw [ennreal.smul_def, smul_eq_mul, ennreal.mul_lt_top_iff],
  exact or.inl ⟨ennreal.coe_lt_top, f.prop⟩,
end

variables (E p μ 𝕜)

/-- The `𝕜`-submodule of elements of `α →ₘ[μ] E` whose `Lp` norm is finite.  This is `Lp E p μ`,
with extra structure. -/
def Lp_submodule : submodule 𝕜 (α →ₘ[μ] E) :=
{ smul_mem' := λ c f hf, by simpa using mem_Lp_const_smul c ⟨f, hf⟩,
  .. Lp E p μ }

variables {E p μ 𝕜}

lemma coe_Lp_submodule : (Lp_submodule E p μ 𝕜).to_add_subgroup = Lp E p μ := rfl

instance : module 𝕜 (Lp E p μ) :=
{ .. (Lp_submodule E p μ 𝕜).module }

lemma coe_fn_smul (c : 𝕜) (f : Lp E p μ) : ⇑(c • f) =ᵐ[μ] c • f := ae_eq_fun.coe_fn_smul _ _

instance [module 𝕜ᵐᵒᵖ E] [has_bounded_smul 𝕜ᵐᵒᵖ E] [is_central_scalar 𝕜 E] :
  is_central_scalar 𝕜 (Lp E p μ) :=
{ op_smul_eq_smul := λ k f, subtype.ext $ op_smul_eq_smul k (f : α →ₘ[μ] E) }

instance [smul_comm_class 𝕜 𝕜' E] : smul_comm_class 𝕜 𝕜' (Lp E p μ) :=
{ smul_comm := λ k k' f, subtype.ext $ smul_comm k k' (f : α →ₘ[μ] E) }

instance [has_smul 𝕜 𝕜'] [is_scalar_tower 𝕜 𝕜' E] : is_scalar_tower 𝕜 𝕜' (Lp E p μ) :=
{ smul_assoc := λ k k' f, subtype.ext $ smul_assoc k k' (f : α →ₘ[μ] E) }

instance [fact (1 ≤ p)] : has_bounded_smul 𝕜 (Lp E p μ) :=
-- TODO: add `has_bounded_smul.of_nnnorm_smul_le
has_bounded_smul.of_norm_smul_le $ λ r f, begin
  suffices : (‖r • f‖₊ : ℝ≥0∞) ≤ ‖r‖₊ * ‖f‖₊,
  { exact_mod_cast this },
  rw [nnnorm_def, nnnorm_def, ennreal.coe_to_nnreal (Lp.snorm_ne_top _),
    snorm_congr_ae (coe_fn_smul _ _), ennreal.coe_to_nnreal (Lp.snorm_ne_top _)],
  exact snorm_const_smul_le r f,
end

end has_bounded_smul

section normed_space
variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 E]

instance [fact (1 ≤ p)] : normed_space 𝕜 (Lp E p μ) :=
{ norm_smul_le := λ _ _, norm_smul_le _ _ }

end normed_space

end Lp

namespace mem_ℒp
variables {𝕜 : Type*} [normed_ring 𝕜] [module 𝕜 E] [has_bounded_smul 𝕜 E]

lemma to_Lp_const_smul {f : α → E} (c : 𝕜) (hf : mem_ℒp f p μ) :
  (hf.const_smul c).to_Lp (c • f) = c • hf.to_Lp f := rfl

end mem_ℒp

/-! ### Indicator of a set as an element of Lᵖ

For a set `s` with `(hs : measurable_set s)` and `(hμs : μ s < ∞)`, we build
`indicator_const_Lp p hs hμs c`, the element of `Lp` corresponding to `s.indicator (λ x, c)`.
-/

section indicator

variables {s : set α} {hs : measurable_set s} {c : E} {f : α → E} {hf : ae_strongly_measurable f μ}

lemma snorm_ess_sup_indicator_le (s : set α) (f : α → G) :
  snorm_ess_sup (s.indicator f) μ ≤ snorm_ess_sup f μ :=
begin
  refine ess_sup_mono_ae (eventually_of_forall (λ x, _)),
  rw [ennreal.coe_le_coe, nnnorm_indicator_eq_indicator_nnnorm],
  exact set.indicator_le_self s _ x,
end

lemma snorm_ess_sup_indicator_const_le (s : set α) (c : G) :
  snorm_ess_sup (s.indicator (λ x : α , c)) μ ≤ ‖c‖₊ :=
begin
  by_cases hμ0 : μ = 0,
  { rw [hμ0, snorm_ess_sup_measure_zero],
    exact zero_le _ },
  { exact (snorm_ess_sup_indicator_le s (λ x, c)).trans (snorm_ess_sup_const c hμ0).le, },
end

lemma snorm_ess_sup_indicator_const_eq (s : set α) (c : G) (hμs : μ s ≠ 0) :
  snorm_ess_sup (s.indicator (λ x : α , c)) μ = ‖c‖₊ :=
begin
  refine le_antisymm (snorm_ess_sup_indicator_const_le s c) _,
  by_contra' h,
  have h' := ae_iff.mp (ae_lt_of_ess_sup_lt h),
  push_neg at h',
  refine hμs (measure_mono_null (λ x hx_mem, _) h'),
  rw [set.mem_set_of_eq, set.indicator_of_mem hx_mem],
  exact le_rfl,
end

variables (hs)

lemma snorm_indicator_le {E : Type*} [normed_add_comm_group E] (f : α → E) :
  snorm (s.indicator f) p μ ≤ snorm f p μ :=
begin
  refine snorm_mono_ae (eventually_of_forall (λ x, _)),
  suffices : ‖s.indicator f x‖₊ ≤ ‖f x‖₊,
  { exact nnreal.coe_mono this },
  rw nnnorm_indicator_eq_indicator_nnnorm,
  exact s.indicator_le_self _ x,
end

variables {hs}

lemma snorm_indicator_const {c : G} (hs : measurable_set s) (hp : p ≠ 0) (hp_top : p ≠ ∞) :
  snorm (s.indicator (λ x, c)) p μ = ‖c‖₊ * (μ s) ^ (1 / p.to_real) :=
begin
  have hp_pos : 0 < p.to_real, from ennreal.to_real_pos hp hp_top,
  rw snorm_eq_lintegral_rpow_nnnorm hp hp_top,
  simp_rw [nnnorm_indicator_eq_indicator_nnnorm, ennreal.coe_indicator],
  have h_indicator_pow : (λ a : α, s.indicator (λ (x : α), (‖c‖₊ : ℝ≥0∞)) a ^ p.to_real)
    = s.indicator (λ (x : α), ↑‖c‖₊ ^ p.to_real),
  { rw set.comp_indicator_const (‖c‖₊ : ℝ≥0∞) (λ x, x ^ p.to_real) _,
    simp [hp_pos], },
  rw [h_indicator_pow, lintegral_indicator _ hs, set_lintegral_const, ennreal.mul_rpow_of_nonneg],
  { rw [← ennreal.rpow_mul, mul_one_div_cancel hp_pos.ne.symm, ennreal.rpow_one], },
  { simp [hp_pos.le], },
end

lemma snorm_indicator_const' {c : G} (hs : measurable_set s) (hμs : μ s ≠ 0) (hp : p ≠ 0) :
  snorm (s.indicator (λ _, c)) p μ = ‖c‖₊ * (μ s) ^ (1 / p.to_real) :=
begin
  by_cases hp_top : p = ∞,
  { simp [hp_top, snorm_ess_sup_indicator_const_eq s c hμs], },
  { exact snorm_indicator_const hs hp hp_top, },
end

lemma snorm_indicator_const_le (c : G) (p : ℝ≥0∞) :
  snorm (s.indicator (λ x, c)) p μ ≤ ‖c‖₊ * (μ s) ^ (1 / p.to_real) :=
begin
  rcases eq_or_ne p 0 with rfl|hp,
  { simp only [snorm_exponent_zero, zero_le'] },
  rcases eq_or_ne p ∞ with rfl|h'p,
  { simp only [snorm_exponent_top, ennreal.top_to_real, div_zero, ennreal.rpow_zero, mul_one],
    exact snorm_ess_sup_indicator_const_le _ _ },
  let t := to_measurable μ s,
  calc snorm (s.indicator (λ x, c)) p μ
      ≤ snorm (t.indicator (λ x, c)) p μ :
    snorm_mono (norm_indicator_le_of_subset (subset_to_measurable _ _) _)
  ... = ‖c‖₊ * (μ t) ^ (1 / p.to_real) :
    snorm_indicator_const (measurable_set_to_measurable _ _) hp h'p
  ... = ‖c‖₊ * (μ s) ^ (1 / p.to_real) : by rw measure_to_measurable
end

lemma mem_ℒp.indicator (hs : measurable_set s) (hf : mem_ℒp f p μ) :
  mem_ℒp (s.indicator f) p μ :=
⟨hf.ae_strongly_measurable.indicator hs, lt_of_le_of_lt (snorm_indicator_le f) hf.snorm_lt_top⟩

lemma snorm_ess_sup_indicator_eq_snorm_ess_sup_restrict {f : α → F} (hs : measurable_set s) :
  snorm_ess_sup (s.indicator f) μ = snorm_ess_sup f (μ.restrict s) :=
begin
  simp_rw [snorm_ess_sup, nnnorm_indicator_eq_indicator_nnnorm, ennreal.coe_indicator],
  by_cases hs_null : μ s = 0,
  { rw measure.restrict_zero_set hs_null,
    simp only [ess_sup_measure_zero, ennreal.ess_sup_eq_zero_iff, ennreal.bot_eq_zero],
    have hs_empty : s =ᵐ[μ] (∅ : set α), by { rw ae_eq_set, simpa using hs_null, },
    refine (indicator_ae_eq_of_ae_eq_set hs_empty).trans _,
    rw set.indicator_empty,
    refl, },
  rw ess_sup_indicator_eq_ess_sup_restrict (eventually_of_forall (λ x, _)) hs hs_null,
  rw pi.zero_apply,
  exact zero_le _,
end

lemma snorm_indicator_eq_snorm_restrict {f : α → F} (hs : measurable_set s) :
  snorm (s.indicator f) p μ = snorm f p (μ.restrict s) :=
begin
  by_cases hp_zero : p = 0,
  { simp only [hp_zero, snorm_exponent_zero], },
  by_cases hp_top : p = ∞,
  { simp_rw [hp_top, snorm_exponent_top],
    exact snorm_ess_sup_indicator_eq_snorm_ess_sup_restrict hs, },
  simp_rw snorm_eq_lintegral_rpow_nnnorm hp_zero hp_top,
  suffices : ∫⁻ x, ‖s.indicator f x‖₊ ^ p.to_real ∂μ = ∫⁻ x in s, ‖f x‖₊ ^ p.to_real ∂μ,
    by rw this,
  rw ← lintegral_indicator _ hs,
  congr,
  simp_rw [nnnorm_indicator_eq_indicator_nnnorm, ennreal.coe_indicator],
  have h_zero : (λ x, x ^ p.to_real) (0 : ℝ≥0∞) = 0,
    by simp [ennreal.to_real_pos hp_zero hp_top],
  exact (set.indicator_comp_of_zero h_zero).symm,
end

lemma mem_ℒp_indicator_iff_restrict (hs : measurable_set s) :
  mem_ℒp (s.indicator f) p μ ↔ mem_ℒp f p (μ.restrict s) :=
by simp [mem_ℒp, ae_strongly_measurable_indicator_iff hs, snorm_indicator_eq_snorm_restrict hs]

lemma mem_ℒp_indicator_const (p : ℝ≥0∞) (hs : measurable_set s) (c : E) (hμsc : c = 0 ∨ μ s ≠ ∞) :
  mem_ℒp (s.indicator (λ _, c)) p μ :=
begin
  rw mem_ℒp_indicator_iff_restrict hs,
  by_cases hp_zero : p = 0,
  { rw hp_zero, exact mem_ℒp_zero_iff_ae_strongly_measurable.mpr ae_strongly_measurable_const, },
  by_cases hp_top : p = ∞,
  { rw hp_top,
    exact mem_ℒp_top_of_bound ae_strongly_measurable_const (‖c‖)
      (eventually_of_forall (λ x, le_rfl)), },
  rw [mem_ℒp_const_iff hp_zero hp_top, measure.restrict_apply_univ],
  cases hμsc,
  { exact or.inl hμsc, },
  { exact or.inr hμsc.lt_top, },
end

/-- The `ℒ^p` norm of the indicator of a set is uniformly small if the set itself has small measure,
for any `p < ∞`. Given here as an existential `∀ ε > 0, ∃ η > 0, ...` to avoid later
management of `ℝ≥0∞`-arithmetic. -/
lemma exists_snorm_indicator_le (hp : p ≠ ∞) (c : E) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
  ∃ (η : ℝ≥0), 0 < η ∧ ∀ (s : set α), μ s ≤ η → snorm (s.indicator (λ x, c)) p μ ≤ ε :=
begin
  rcases eq_or_ne p 0 with rfl|h'p,
  { exact ⟨1, zero_lt_one, λ s hs, by simp⟩ },
  have hp₀ : 0 < p := bot_lt_iff_ne_bot.2 h'p,
  have hp₀' : 0 ≤ 1 / p.to_real := div_nonneg zero_le_one ennreal.to_real_nonneg,
  have hp₀'' : 0 < p.to_real,
  { simpa [← ennreal.to_real_lt_to_real ennreal.zero_ne_top hp] using hp₀ },
  obtain ⟨η, hη_pos, hη_le⟩ : ∃ (η : ℝ≥0), 0 < η ∧ (‖c‖₊ * η ^ (1 / p.to_real) : ℝ≥0∞) ≤ ε,
  { have : filter.tendsto (λ x : ℝ≥0, ((‖c‖₊ * x ^ (1 / p.to_real) : ℝ≥0) : ℝ≥0∞))
      (𝓝 0) (𝓝 (0 : ℝ≥0)),
    { rw ennreal.tendsto_coe,
      convert ((nnreal.continuous_at_rpow_const (or.inr hp₀')).tendsto).const_mul _,
      simp [hp₀''.ne'] },
    have hε' : 0 < ε := hε.bot_lt,
    obtain ⟨δ, hδ, hδε'⟩ :=
      nnreal.nhds_zero_basis.eventually_iff.mp (eventually_le_of_tendsto_lt hε' this),
    obtain ⟨η, hη, hηδ⟩ := exists_between hδ,
    refine ⟨η, hη, _⟩,
    rw [ennreal.coe_rpow_of_nonneg _ hp₀', ← ennreal.coe_mul],
    exact hδε' hηδ },
  refine ⟨η, hη_pos, λ s hs, _⟩,
  refine (snorm_indicator_const_le _ _).trans (le_trans _ hη_le),
  exact mul_le_mul_left' (ennreal.rpow_le_rpow hs hp₀') _,
end

end indicator

section indicator_const_Lp

open set function

variables {s : set α} {hs : measurable_set s} {hμs : μ s ≠ ∞} {c : E}

/-- Indicator of a set as an element of `Lp`. -/
def indicator_const_Lp (p : ℝ≥0∞) (hs : measurable_set s) (hμs : μ s ≠ ∞) (c : E) : Lp E p μ :=
mem_ℒp.to_Lp (s.indicator (λ _, c)) (mem_ℒp_indicator_const p hs c (or.inr hμs))

lemma indicator_const_Lp_coe_fn : ⇑(indicator_const_Lp p hs hμs c) =ᵐ[μ] s.indicator (λ _, c) :=
mem_ℒp.coe_fn_to_Lp (mem_ℒp_indicator_const p hs c (or.inr hμs))

lemma indicator_const_Lp_coe_fn_mem :
  ∀ᵐ (x : α) ∂μ, x ∈ s → indicator_const_Lp p hs hμs c x = c :=
indicator_const_Lp_coe_fn.mono (λ x hx hxs, hx.trans (set.indicator_of_mem hxs _))

lemma indicator_const_Lp_coe_fn_nmem :
  ∀ᵐ (x : α) ∂μ, x ∉ s → indicator_const_Lp p hs hμs c x = 0 :=
indicator_const_Lp_coe_fn.mono (λ x hx hxs, hx.trans (set.indicator_of_not_mem hxs _))

lemma norm_indicator_const_Lp (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
  ‖indicator_const_Lp p hs hμs c‖ = ‖c‖ * (μ s).to_real ^ (1 / p.to_real) :=
by rw [Lp.norm_def, snorm_congr_ae indicator_const_Lp_coe_fn,
    snorm_indicator_const hs hp_ne_zero hp_ne_top, ennreal.to_real_mul, ennreal.to_real_rpow,
    ennreal.coe_to_real, coe_nnnorm]

lemma norm_indicator_const_Lp_top (hμs_ne_zero : μ s ≠ 0) : ‖indicator_const_Lp ∞ hs hμs c‖ = ‖c‖ :=
by rw [Lp.norm_def, snorm_congr_ae indicator_const_Lp_coe_fn,
    snorm_indicator_const' hs hμs_ne_zero ennreal.top_ne_zero, ennreal.top_to_real, div_zero,
    ennreal.rpow_zero, mul_one, ennreal.coe_to_real, coe_nnnorm]

lemma norm_indicator_const_Lp' (hp_pos : p ≠ 0) (hμs_pos : μ s ≠ 0) :
  ‖indicator_const_Lp p hs hμs c‖ = ‖c‖ * (μ s).to_real ^ (1 / p.to_real) :=
begin
  by_cases hp_top : p = ∞,
  { rw [hp_top, ennreal.top_to_real, div_zero, real.rpow_zero, mul_one],
    exact norm_indicator_const_Lp_top hμs_pos, },
  { exact norm_indicator_const_Lp hp_pos hp_top, },
end

@[simp] lemma indicator_const_empty :
  indicator_const_Lp p measurable_set.empty (by simp : μ ∅ ≠ ∞) c = 0 :=
begin
  rw Lp.eq_zero_iff_ae_eq_zero,
  convert indicator_const_Lp_coe_fn,
  simp [set.indicator_empty'],
end

lemma mem_ℒp_add_of_disjoint {f g : α → E}
  (h : disjoint (support f) (support g)) (hf : strongly_measurable f) (hg : strongly_measurable g) :
  mem_ℒp (f + g) p μ ↔ mem_ℒp f p μ ∧ mem_ℒp g p μ :=
begin
  borelize E,
  refine ⟨λ hfg, ⟨_, _⟩, λ h, h.1.add h.2⟩,
  { rw ← indicator_add_eq_left h, exact hfg.indicator (measurable_set_support hf.measurable) },
  { rw ← indicator_add_eq_right h, exact hfg.indicator (measurable_set_support hg.measurable) }
end

/-- The indicator of a disjoint union of two sets is the sum of the indicators of the sets. -/
lemma indicator_const_Lp_disjoint_union {s t : set α} (hs : measurable_set s)
  (ht : measurable_set t) (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞) (hst : s ∩ t = ∅) (c : E) :
  (indicator_const_Lp p (hs.union ht) ((measure_union_le s t).trans_lt
      (lt_top_iff_ne_top.mpr (ennreal.add_ne_top.mpr ⟨hμs, hμt⟩))).ne c)
    = indicator_const_Lp p hs hμs c + indicator_const_Lp p ht hμt c :=
begin
  ext1,
  refine indicator_const_Lp_coe_fn.trans (eventually_eq.trans _ (Lp.coe_fn_add _ _).symm),
  refine eventually_eq.trans _
    (eventually_eq.add indicator_const_Lp_coe_fn.symm indicator_const_Lp_coe_fn.symm),
  rw set.indicator_union_of_disjoint (set.disjoint_iff_inter_eq_empty.mpr hst) _,
end

end indicator_const_Lp

lemma mem_ℒp.norm_rpow_div {f : α → E}
  (hf : mem_ℒp f p μ) (q : ℝ≥0∞) :
  mem_ℒp (λ (x : α), ‖f x‖ ^ q.to_real) (p/q) μ :=
begin
  refine ⟨(hf.1.norm.ae_measurable.pow_const q.to_real).ae_strongly_measurable, _⟩,
  by_cases q_top : q = ∞, { simp [q_top] },
  by_cases q_zero : q = 0,
  { simp [q_zero],
    by_cases p_zero : p = 0, { simp [p_zero] },
    rw ennreal.div_zero p_zero,
    exact (mem_ℒp_top_const (1 : ℝ)).2 },
  rw snorm_norm_rpow _ (ennreal.to_real_pos q_zero q_top),
  apply ennreal.rpow_lt_top_of_nonneg ennreal.to_real_nonneg,
  rw [ennreal.of_real_to_real q_top, div_eq_mul_inv, mul_assoc,
    ennreal.inv_mul_cancel q_zero q_top, mul_one],
  exact hf.2.ne
end

lemma mem_ℒp_norm_rpow_iff {q : ℝ≥0∞} {f : α → E} (hf : ae_strongly_measurable f μ)
  (q_zero : q ≠ 0) (q_top : q ≠ ∞) :
  mem_ℒp (λ (x : α), ‖f x‖ ^ q.to_real) (p/q) μ ↔ mem_ℒp f p μ :=
begin
  refine ⟨λ h, _, λ h, h.norm_rpow_div q⟩,
  apply (mem_ℒp_norm_iff hf).1,
  convert h.norm_rpow_div (q⁻¹),
  { ext x,
    rw [real.norm_eq_abs, real.abs_rpow_of_nonneg (norm_nonneg _), ← real.rpow_mul (abs_nonneg _),
      ennreal.to_real_inv, mul_inv_cancel, abs_of_nonneg (norm_nonneg _), real.rpow_one],
    simp [ennreal.to_real_eq_zero_iff, not_or_distrib, q_zero, q_top] },
  { rw [div_eq_mul_inv, inv_inv, div_eq_mul_inv, mul_assoc, ennreal.inv_mul_cancel q_zero q_top,
    mul_one] }
end

lemma mem_ℒp.norm_rpow {f : α → E}
  (hf : mem_ℒp f p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
  mem_ℒp (λ (x : α), ‖f x‖ ^ p.to_real) 1 μ :=
begin
  convert hf.norm_rpow_div p,
  rw [div_eq_mul_inv, ennreal.mul_inv_cancel hp_ne_zero hp_ne_top],
end

end measure_theory

open measure_theory

/-!
### Composition on `L^p`

We show that Lipschitz functions vanishing at zero act by composition on `L^p`, and specialize
this to the composition with continuous linear maps, and to the definition of the positive
part of an `L^p` function.
-/

section composition

variables {g : E → F} {c : ℝ≥0}

lemma lipschitz_with.comp_mem_ℒp {α E F} {K} [measurable_space α] {μ : measure α}
  [normed_add_comm_group E] [normed_add_comm_group F] {f : α → E} {g : E → F}
  (hg : lipschitz_with K g) (g0 : g 0 = 0) (hL : mem_ℒp f p μ) : mem_ℒp (g ∘ f) p μ  :=
begin
  have : ∀ x, ‖g (f x)‖ ≤ K * ‖f x‖,
  { intro a,
    -- TODO: add `lipschitz_with.nnnorm_sub_le` and `lipschitz_with.nnnorm_le`
    simpa [g0] using hg.norm_sub_le (f a) 0, },
  exact hL.of_le_mul (hg.continuous.comp_ae_strongly_measurable hL.1) (eventually_of_forall this),
end

lemma measure_theory.mem_ℒp.of_comp_antilipschitz_with {α E F} {K'}
  [measurable_space α] {μ : measure α} [normed_add_comm_group E] [normed_add_comm_group F]
  {f : α → E} {g : E → F} (hL : mem_ℒp (g ∘ f) p μ)
  (hg : uniform_continuous g) (hg' : antilipschitz_with K' g) (g0 : g 0 = 0) : mem_ℒp f p μ :=
begin
  have A : ∀ x, ‖f x‖ ≤ K' * ‖g (f x)‖,
  { intro x,
    -- TODO: add `antilipschitz_with.le_mul_nnnorm_sub` and `antilipschitz_with.le_mul_norm`
    rw [← dist_zero_right, ← dist_zero_right, ← g0],
    apply hg'.le_mul_dist },
  have B : ae_strongly_measurable f μ :=
    ((hg'.uniform_embedding hg).embedding.ae_strongly_measurable_comp_iff.1 hL.1),
  exact hL.of_le_mul B (filter.eventually_of_forall A),
end

namespace lipschitz_with

lemma mem_ℒp_comp_iff_of_antilipschitz {α E F} {K K'} [measurable_space α] {μ : measure α}
  [normed_add_comm_group E] [normed_add_comm_group F]
  {f : α → E} {g : E → F} (hg : lipschitz_with K g) (hg' : antilipschitz_with K' g) (g0 : g 0 = 0) :
  mem_ℒp (g ∘ f) p μ ↔ mem_ℒp f p μ :=
⟨λ h, h.of_comp_antilipschitz_with hg.uniform_continuous hg' g0, λ h, hg.comp_mem_ℒp g0 h⟩

/-- When `g` is a Lipschitz function sending `0` to `0` and `f` is in `Lp`, then `g ∘ f` is well
defined as an element of `Lp`. -/
def comp_Lp (hg : lipschitz_with c g) (g0 : g 0 = 0) (f : Lp E p μ) : Lp F p μ :=
⟨ae_eq_fun.comp g hg.continuous (f : α →ₘ[μ] E),
begin
  suffices : ∀ᵐ x ∂μ, ‖ae_eq_fun.comp g hg.continuous (f : α →ₘ[μ] E) x‖ ≤ c * ‖f x‖,
  { exact Lp.mem_Lp_of_ae_le_mul this },
  filter_upwards [ae_eq_fun.coe_fn_comp g hg.continuous (f : α →ₘ[μ] E)] with a ha,
  simp only [ha],
  rw [← dist_zero_right, ← dist_zero_right, ← g0],
  exact hg.dist_le_mul (f a) 0,
end⟩

lemma coe_fn_comp_Lp (hg : lipschitz_with c g) (g0 : g 0 = 0) (f : Lp E p μ) :
  hg.comp_Lp g0 f =ᵐ[μ] g ∘ f :=
ae_eq_fun.coe_fn_comp _ _ _

@[simp] lemma comp_Lp_zero (hg : lipschitz_with c g) (g0 : g 0 = 0) :
  hg.comp_Lp g0 (0 : Lp E p μ) = 0 :=
begin
  rw Lp.eq_zero_iff_ae_eq_zero,
  apply (coe_fn_comp_Lp _ _ _).trans,
  filter_upwards [Lp.coe_fn_zero E p μ] with _ ha,
  simp [ha, g0],
end

lemma norm_comp_Lp_sub_le (hg : lipschitz_with c g) (g0 : g 0 = 0) (f f' : Lp E p μ) :
  ‖hg.comp_Lp g0 f - hg.comp_Lp g0 f'‖ ≤ c * ‖f - f'‖ :=
begin
  apply Lp.norm_le_mul_norm_of_ae_le_mul,
  filter_upwards [hg.coe_fn_comp_Lp g0 f, hg.coe_fn_comp_Lp g0 f',
    Lp.coe_fn_sub (hg.comp_Lp g0 f) (hg.comp_Lp g0 f'), Lp.coe_fn_sub f f'] with a ha1 ha2 ha3 ha4,
  simp [ha1, ha2, ha3, ha4, ← dist_eq_norm],
  exact hg.dist_le_mul (f a) (f' a)
end

lemma norm_comp_Lp_le (hg : lipschitz_with c g) (g0 : g 0 = 0) (f : Lp E p μ) :
  ‖hg.comp_Lp g0 f‖ ≤ c * ‖f‖ :=
by simpa using hg.norm_comp_Lp_sub_le g0 f 0

lemma lipschitz_with_comp_Lp [fact (1 ≤ p)] (hg : lipschitz_with c g) (g0 : g 0 = 0) :
  lipschitz_with c (hg.comp_Lp g0 : Lp E p μ → Lp F p μ) :=
lipschitz_with.of_dist_le_mul $ λ f g, by simp [dist_eq_norm, norm_comp_Lp_sub_le]

lemma continuous_comp_Lp [fact (1 ≤ p)] (hg : lipschitz_with c g) (g0 : g 0 = 0) :
  continuous (hg.comp_Lp g0 : Lp E p μ → Lp F p μ) :=
(lipschitz_with_comp_Lp hg g0).continuous

end lipschitz_with

namespace continuous_linear_map
variables {𝕜 : Type*} [nontrivially_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]

/-- Composing `f : Lp ` with `L : E →L[𝕜] F`. -/
def comp_Lp (L : E →L[𝕜] F) (f : Lp E p μ) : Lp F p μ :=
L.lipschitz.comp_Lp (map_zero L) f

lemma coe_fn_comp_Lp (L : E →L[𝕜] F) (f : Lp E p μ) :
  ∀ᵐ a ∂μ, (L.comp_Lp f) a = L (f a) :=
lipschitz_with.coe_fn_comp_Lp _ _ _

lemma coe_fn_comp_Lp' (L : E →L[𝕜] F) (f : Lp E p μ) :
  L.comp_Lp f =ᵐ[μ] λ a, L (f a) :=
L.coe_fn_comp_Lp f

lemma comp_mem_ℒp (L : E →L[𝕜] F) (f : Lp E p μ) : mem_ℒp (L ∘ f) p μ :=
(Lp.mem_ℒp (L.comp_Lp f)).ae_eq (L.coe_fn_comp_Lp' f)

lemma comp_mem_ℒp' (L : E →L[𝕜] F) {f : α → E} (hf : mem_ℒp f p μ) : mem_ℒp (L ∘ f) p μ :=
(L.comp_mem_ℒp (hf.to_Lp f)).ae_eq (eventually_eq.fun_comp (hf.coe_fn_to_Lp) _)

section is_R_or_C

variables {K : Type*} [is_R_or_C K]

lemma _root_.measure_theory.mem_ℒp.of_real
  {f : α → ℝ} (hf : mem_ℒp f p μ) : mem_ℒp (λ x, (f x : K)) p μ :=
(@is_R_or_C.of_real_clm K _).comp_mem_ℒp' hf

lemma _root_.measure_theory.mem_ℒp_re_im_iff {f : α → K} :
  mem_ℒp (λ x, is_R_or_C.re (f x)) p μ ∧ mem_ℒp (λ x, is_R_or_C.im (f x)) p μ ↔
  mem_ℒp f p μ :=
begin
  refine ⟨_, λ hf, ⟨hf.re, hf.im⟩⟩,
  rintro ⟨hre, him⟩,
  convert hre.of_real.add (him.of_real.const_mul is_R_or_C.I),
  { ext1 x,
    rw [pi.add_apply, mul_comm, is_R_or_C.re_add_im] },
  all_goals { apply_instance }
end

end is_R_or_C

lemma add_comp_Lp (L L' : E →L[𝕜] F) (f : Lp E p μ) :
  (L + L').comp_Lp f = L.comp_Lp f + L'.comp_Lp f :=
begin
  ext1,
  refine (coe_fn_comp_Lp' (L + L') f).trans _,
  refine eventually_eq.trans _ (Lp.coe_fn_add _ _).symm,
  refine eventually_eq.trans _
    (eventually_eq.add (L.coe_fn_comp_Lp' f).symm (L'.coe_fn_comp_Lp' f).symm),
  refine eventually_of_forall (λ x, _),
  refl,
end

lemma smul_comp_Lp {𝕜'} [normed_ring 𝕜'] [module 𝕜' F] [has_bounded_smul 𝕜' F]
  [smul_comm_class 𝕜 𝕜' F]
  (c : 𝕜') (L : E →L[𝕜] F) (f : Lp E p μ) :
  (c • L).comp_Lp f = c • L.comp_Lp f :=
begin
  ext1,
  refine (coe_fn_comp_Lp' (c • L) f).trans _,
  refine eventually_eq.trans _ (Lp.coe_fn_smul _ _).symm,
  refine (L.coe_fn_comp_Lp' f).mono (λ x hx, _),
  rw [pi.smul_apply, hx],
  refl,
end

lemma norm_comp_Lp_le (L : E →L[𝕜] F) (f : Lp E p μ)  : ‖L.comp_Lp f‖ ≤ ‖L‖ * ‖f‖ :=
lipschitz_with.norm_comp_Lp_le _ _ _

variables (μ p)

/-- Composing `f : Lp E p μ` with `L : E →L[𝕜] F`, seen as a `𝕜`-linear map on `Lp E p μ`. -/
def comp_Lpₗ (L : E →L[𝕜] F) : (Lp E p μ) →ₗ[𝕜] (Lp F p μ) :=
{ to_fun := λ f, L.comp_Lp f,
  map_add' := begin
    intros f g,
    ext1,
    filter_upwards [Lp.coe_fn_add f g, coe_fn_comp_Lp L (f + g), coe_fn_comp_Lp L f,
      coe_fn_comp_Lp L g, Lp.coe_fn_add (L.comp_Lp f) (L.comp_Lp g)],
    assume a ha1 ha2 ha3 ha4 ha5,
    simp only [ha1, ha2, ha3, ha4, ha5, map_add, pi.add_apply],
  end,
  map_smul' := begin
    intros c f,
    dsimp,
    ext1,
    filter_upwards [Lp.coe_fn_smul c f, coe_fn_comp_Lp L (c • f), Lp.coe_fn_smul c (L.comp_Lp f),
      coe_fn_comp_Lp L f] with _ ha1 ha2 ha3 ha4,
    simp only [ha1, ha2, ha3, ha4, smul_hom_class.map_smul, pi.smul_apply],
  end }

/-- Composing `f : Lp E p μ` with `L : E →L[𝕜] F`, seen as a continuous `𝕜`-linear map on
`Lp E p μ`. See also the similar
* `linear_map.comp_left` for functions,
* `continuous_linear_map.comp_left_continuous` for continuous functions,
* `continuous_linear_map.comp_left_continuous_bounded` for bounded continuous functions,
* `continuous_linear_map.comp_left_continuous_compact` for continuous functions on compact spaces.
-/
def comp_LpL [fact (1 ≤ p)] (L : E →L[𝕜] F) : (Lp E p μ) →L[𝕜] (Lp F p μ) :=
linear_map.mk_continuous (L.comp_Lpₗ p μ) ‖L‖ L.norm_comp_Lp_le

variables {μ p}

lemma coe_fn_comp_LpL [fact (1 ≤ p)] (L : E →L[𝕜] F) (f : Lp E p μ) :
  L.comp_LpL p μ f =ᵐ[μ] λ a, L (f a) :=
L.coe_fn_comp_Lp f

lemma add_comp_LpL [fact (1 ≤ p)] (L L' : E →L[𝕜] F) :
  (L + L').comp_LpL p μ = L.comp_LpL p μ + L'.comp_LpL p μ :=
by { ext1 f, exact add_comp_Lp L L' f }

lemma smul_comp_LpL [fact (1 ≤ p)] {𝕜'} [normed_ring 𝕜'] [module 𝕜' F]
  [has_bounded_smul 𝕜' F] [smul_comm_class 𝕜 𝕜' F] (c : 𝕜') (L : E →L[𝕜] F) :
  (c • L).comp_LpL p μ = c • L.comp_LpL p μ :=
by { ext1 f, exact smul_comp_Lp c L f }

lemma norm_compLpL_le [fact (1 ≤ p)] (L : E →L[𝕜] F) :
  ‖L.comp_LpL p μ‖ ≤ ‖L‖ :=
linear_map.mk_continuous_norm_le _ (norm_nonneg _) _

end continuous_linear_map

namespace measure_theory

lemma indicator_const_Lp_eq_to_span_singleton_comp_Lp {s : set α} [normed_space ℝ F]
  (hs : measurable_set s) (hμs : μ s ≠ ∞) (x : F) :
  indicator_const_Lp 2 hs hμs x =
    (continuous_linear_map.to_span_singleton ℝ x).comp_Lp (indicator_const_Lp 2 hs hμs (1 : ℝ)) :=
begin
  ext1,
  refine indicator_const_Lp_coe_fn.trans _,
  have h_comp_Lp := (continuous_linear_map.to_span_singleton ℝ x).coe_fn_comp_Lp
    (indicator_const_Lp 2 hs hμs (1 : ℝ)),
  rw ← eventually_eq at h_comp_Lp,
  refine eventually_eq.trans _ h_comp_Lp.symm,
  refine (@indicator_const_Lp_coe_fn _ _ _ 2 μ _ s hs hμs (1 : ℝ)).mono (λ y hy, _),
  dsimp only,
  rw hy,
  simp_rw [continuous_linear_map.to_span_singleton_apply],
  by_cases hy_mem : y ∈ s; simp [hy_mem, continuous_linear_map.lsmul_apply],
end

namespace Lp
section pos_part

lemma lipschitz_with_pos_part : lipschitz_with 1 (λ (x : ℝ), max x 0) :=
lipschitz_with.of_dist_le_mul $ λ x y, by simp [real.dist_eq, abs_max_sub_max_le_abs]

lemma _root_.measure_theory.mem_ℒp.pos_part {f : α → ℝ} (hf : mem_ℒp f p μ) :
  mem_ℒp (λ x, max (f x) 0) p μ :=
lipschitz_with_pos_part.comp_mem_ℒp  (max_eq_right le_rfl) hf

lemma _root_.measure_theory.mem_ℒp.neg_part {f : α → ℝ} (hf : mem_ℒp f p μ) :
  mem_ℒp (λ x, max (-f x) 0) p μ :=
lipschitz_with_pos_part.comp_mem_ℒp (max_eq_right le_rfl) hf.neg

/-- Positive part of a function in `L^p`. -/
def pos_part (f : Lp ℝ p μ) : Lp ℝ p μ :=
lipschitz_with_pos_part.comp_Lp (max_eq_right le_rfl) f

/-- Negative part of a function in `L^p`. -/
def neg_part (f : Lp ℝ p μ) : Lp ℝ p μ := pos_part (-f)

@[norm_cast]
lemma coe_pos_part (f : Lp ℝ p μ) : (pos_part f : α →ₘ[μ] ℝ) = (f : α →ₘ[μ] ℝ).pos_part := rfl

lemma coe_fn_pos_part (f : Lp ℝ p μ) : ⇑(pos_part f) =ᵐ[μ] λ a, max (f a) 0 :=
ae_eq_fun.coe_fn_pos_part _

lemma coe_fn_neg_part_eq_max (f : Lp ℝ p μ) : ∀ᵐ a ∂μ, neg_part f a = max (- f a) 0 :=
begin
  rw neg_part,
  filter_upwards [coe_fn_pos_part (-f), coe_fn_neg f] with _ h₁ h₂,
  rw [h₁, h₂, pi.neg_apply],
end

lemma coe_fn_neg_part (f : Lp ℝ p μ) : ∀ᵐ a ∂μ, neg_part f a = - min (f a) 0 :=
(coe_fn_neg_part_eq_max f).mono $ assume a h,
by rw [h, ← max_neg_neg, neg_zero]

lemma continuous_pos_part [fact (1 ≤ p)] : continuous (λf : Lp ℝ p μ, pos_part f) :=
lipschitz_with.continuous_comp_Lp _ _

lemma continuous_neg_part [fact (1 ≤ p)] : continuous (λf : Lp ℝ p μ, neg_part f) :=
have eq : (λf : Lp ℝ p μ, neg_part f) = (λf : Lp ℝ p μ, pos_part (-f)) := rfl,
by { rw eq, exact continuous_pos_part.comp continuous_neg }

end pos_part
end Lp
end measure_theory

end composition



/-!
## `L^p` is a complete space

We show that `L^p` is a complete space for `1 ≤ p`.
-/

section complete_space

namespace measure_theory
namespace Lp

lemma snorm'_lim_eq_lintegral_liminf {ι} [nonempty ι] [linear_order ι] {f : ι → α → G} {p : ℝ}
  (hp_nonneg : 0 ≤ p) {f_lim : α → G}
  (h_lim : ∀ᵐ (x : α) ∂μ, tendsto (λ n, f n x) at_top (𝓝 (f_lim x))) :
  snorm' f_lim p μ = (∫⁻ a, at_top.liminf (λ m, (‖f m a‖₊ : ℝ≥0∞)^p) ∂μ) ^ (1/p) :=
begin
  suffices h_no_pow : (∫⁻ a, ‖f_lim a‖₊ ^ p ∂μ)
    = (∫⁻ a, at_top.liminf (λ m, (‖f m a‖₊ : ℝ≥0∞)^p) ∂μ),
  { rw [snorm', h_no_pow], },
  refine lintegral_congr_ae (h_lim.mono (λ a ha, _)),
  rw tendsto.liminf_eq,
  simp_rw [ennreal.coe_rpow_of_nonneg _ hp_nonneg, ennreal.tendsto_coe],
  refine ((nnreal.continuous_rpow_const hp_nonneg).tendsto (‖f_lim a‖₊)).comp _,
  exact (continuous_nnnorm.tendsto (f_lim a)).comp ha,
end

lemma snorm'_lim_le_liminf_snorm' {E} [normed_add_comm_group E] {f : ℕ → α → E} {p : ℝ}
  (hp_pos : 0 < p) (hf : ∀ n, ae_strongly_measurable (f n) μ) {f_lim : α → E}
  (h_lim : ∀ᵐ (x : α) ∂μ, tendsto (λ n, f n x) at_top (𝓝 (f_lim x)))  :
  snorm' f_lim p μ ≤ at_top.liminf (λ n, snorm' (f n) p μ) :=
begin
  rw snorm'_lim_eq_lintegral_liminf hp_pos.le h_lim,
  rw [←ennreal.le_rpow_one_div_iff (by simp [hp_pos] : 0 < 1 / p), one_div_one_div],
  refine (lintegral_liminf_le' (λ m, ((hf m).ennnorm.pow_const _))).trans_eq _,
  have h_pow_liminf : at_top.liminf (λ n, snorm' (f n) p μ) ^ p
    = at_top.liminf (λ n, (snorm' (f n) p μ) ^ p),
  { have h_rpow_mono := ennreal.strict_mono_rpow_of_pos hp_pos,
    have h_rpow_surj := (ennreal.rpow_left_bijective hp_pos.ne.symm).2,
    refine (h_rpow_mono.order_iso_of_surjective _ h_rpow_surj).liminf_apply _ _ _ _,
    all_goals { is_bounded_default }, },
  rw h_pow_liminf,
  simp_rw [snorm', ← ennreal.rpow_mul, one_div, inv_mul_cancel hp_pos.ne.symm, ennreal.rpow_one],
end

lemma snorm_exponent_top_lim_eq_ess_sup_liminf {ι} [nonempty ι] [linear_order ι] {f : ι → α → G}
  {f_lim : α → G}
  (h_lim : ∀ᵐ (x : α) ∂μ, tendsto (λ n, f n x) at_top (𝓝 (f_lim x))) :
  snorm f_lim ∞ μ = ess_sup (λ x, at_top.liminf (λ m, (‖f m x‖₊ : ℝ≥0∞))) μ :=
begin
  rw [snorm_exponent_top, snorm_ess_sup],
  refine ess_sup_congr_ae (h_lim.mono (λ x hx, _)),
  rw tendsto.liminf_eq,
  rw ennreal.tendsto_coe,
  exact (continuous_nnnorm.tendsto (f_lim x)).comp hx,
end

lemma snorm_exponent_top_lim_le_liminf_snorm_exponent_top {ι} [nonempty ι] [countable ι]
  [linear_order ι] {f : ι → α → F} {f_lim : α → F}
  (h_lim : ∀ᵐ (x : α) ∂μ, tendsto (λ n, f n x) at_top (𝓝 (f_lim x))) :
  snorm f_lim ∞ μ ≤ at_top.liminf (λ n, snorm (f n) ∞ μ) :=
begin
  rw snorm_exponent_top_lim_eq_ess_sup_liminf h_lim,
  simp_rw [snorm_exponent_top, snorm_ess_sup],
  exact ennreal.ess_sup_liminf_le (λ n, (λ x, (‖f n x‖₊ : ℝ≥0∞))),
end

lemma snorm_lim_le_liminf_snorm {E} [normed_add_comm_group E]
  {f : ℕ → α → E} (hf : ∀ n, ae_strongly_measurable (f n) μ) (f_lim : α → E)
  (h_lim : ∀ᵐ (x : α) ∂μ, tendsto (λ n, f n x) at_top (𝓝 (f_lim x))) :
  snorm f_lim p μ ≤ at_top.liminf (λ n, snorm (f n) p μ) :=
begin
  by_cases hp0 : p = 0,
  { simp [hp0], },
  rw ← ne.def at hp0,
  by_cases hp_top : p = ∞,
  { simp_rw [hp_top],
    exact snorm_exponent_top_lim_le_liminf_snorm_exponent_top h_lim, },
  simp_rw snorm_eq_snorm' hp0 hp_top,
  have hp_pos : 0 < p.to_real, from ennreal.to_real_pos hp0 hp_top,
  exact snorm'_lim_le_liminf_snorm' hp_pos hf h_lim,
end

/-! ### `Lp` is complete iff Cauchy sequences of `ℒp` have limits in `ℒp` -/

lemma tendsto_Lp_iff_tendsto_ℒp' {ι} {fi : filter ι} [fact (1 ≤ p)]
  (f : ι → Lp E p μ) (f_lim : Lp E p μ) :
  fi.tendsto f (𝓝 f_lim) ↔ fi.tendsto (λ n, snorm (f n - f_lim) p μ) (𝓝 0) :=
begin
  rw tendsto_iff_dist_tendsto_zero,
  simp_rw dist_def,
  rw [← ennreal.zero_to_real, ennreal.tendsto_to_real_iff (λ n, _) ennreal.zero_ne_top],
  rw snorm_congr_ae (Lp.coe_fn_sub _ _).symm,
  exact Lp.snorm_ne_top _,
end

lemma tendsto_Lp_iff_tendsto_ℒp {ι} {fi : filter ι} [fact (1 ≤ p)]
  (f : ι → Lp E p μ) (f_lim : α → E) (f_lim_ℒp : mem_ℒp f_lim p μ) :
  fi.tendsto f (𝓝 (f_lim_ℒp.to_Lp f_lim)) ↔ fi.tendsto (λ n, snorm (f n - f_lim) p μ) (𝓝 0) :=
begin
  rw tendsto_Lp_iff_tendsto_ℒp',
  suffices h_eq : (λ n, snorm (f n - mem_ℒp.to_Lp f_lim f_lim_ℒp) p μ)
      = (λ n, snorm (f n - f_lim) p μ),
    by rw h_eq,
  exact funext (λ n, snorm_congr_ae (eventually_eq.rfl.sub (mem_ℒp.coe_fn_to_Lp f_lim_ℒp))),
end

lemma tendsto_Lp_iff_tendsto_ℒp'' {ι} {fi : filter ι} [fact (1 ≤ p)]
  (f : ι → α → E) (f_ℒp : ∀ n, mem_ℒp (f n) p μ) (f_lim : α → E) (f_lim_ℒp : mem_ℒp f_lim p μ) :
  fi.tendsto (λ n, (f_ℒp n).to_Lp (f n)) (𝓝 (f_lim_ℒp.to_Lp f_lim))
    ↔ fi.tendsto (λ n, snorm (f n - f_lim) p μ) (𝓝 0) :=
begin
  convert Lp.tendsto_Lp_iff_tendsto_ℒp' _ _,
  ext1 n,
  apply snorm_congr_ae,
  filter_upwards [((f_ℒp n).sub f_lim_ℒp).coe_fn_to_Lp,
    Lp.coe_fn_sub ((f_ℒp n).to_Lp (f n)) (f_lim_ℒp.to_Lp f_lim)] with _ hx₁ hx₂,
  rw ← hx₂,
  exact hx₁.symm,
end

lemma tendsto_Lp_of_tendsto_ℒp {ι} {fi : filter ι} [hp : fact (1 ≤ p)]
  {f : ι → Lp E p μ} (f_lim : α → E) (f_lim_ℒp : mem_ℒp f_lim p μ)
  (h_tendsto : fi.tendsto (λ n, snorm (f n - f_lim) p μ) (𝓝 0)) :
  fi.tendsto f (𝓝 (f_lim_ℒp.to_Lp f_lim)) :=
(tendsto_Lp_iff_tendsto_ℒp f f_lim f_lim_ℒp).mpr h_tendsto

lemma cauchy_seq_Lp_iff_cauchy_seq_ℒp {ι} [nonempty ι] [semilattice_sup ι] [hp : fact (1 ≤ p)]
  (f : ι → Lp E p μ) :
  cauchy_seq f ↔ tendsto (λ (n : ι × ι), snorm (f n.fst - f n.snd) p μ) at_top (𝓝 0) :=
begin
  simp_rw [cauchy_seq_iff_tendsto_dist_at_top_0, dist_def],
  rw [← ennreal.zero_to_real, ennreal.tendsto_to_real_iff (λ n, _) ennreal.zero_ne_top],
  rw snorm_congr_ae (Lp.coe_fn_sub _ _).symm,
  exact snorm_ne_top _,
end

lemma complete_space_Lp_of_cauchy_complete_ℒp [hp : fact (1 ≤ p)]
  (H : ∀ (f : ℕ → α → E) (hf : ∀ n, mem_ℒp (f n) p μ) (B : ℕ → ℝ≥0∞) (hB : ∑' i, B i < ∞)
      (h_cau : ∀ (N n m : ℕ), N ≤ n → N ≤ m → snorm (f n - f m) p μ < B N),
    ∃ (f_lim : α → E) (hf_lim_meas : mem_ℒp f_lim p μ),
      at_top.tendsto (λ n, snorm (f n - f_lim) p μ) (𝓝 0)) :
  complete_space (Lp E p μ) :=
begin
  let B := λ n : ℕ, ((1:ℝ) / 2) ^ n,
  have hB_pos : ∀ n, 0 < B n, from λ n, pow_pos (div_pos zero_lt_one zero_lt_two) n,
  refine metric.complete_of_convergent_controlled_sequences B hB_pos (λ f hf, _),
  rsuffices ⟨f_lim, hf_lim_meas, h_tendsto⟩ : ∃ (f_lim : α → E) (hf_lim_meas : mem_ℒp f_lim p μ),
    at_top.tendsto (λ n, snorm (f n - f_lim) p μ) (𝓝 0),
  { exact ⟨hf_lim_meas.to_Lp f_lim, tendsto_Lp_of_tendsto_ℒp f_lim hf_lim_meas h_tendsto⟩, },
  have hB : summable B, from summable_geometric_two,
  cases hB with M hB,
  let B1 := λ n, ennreal.of_real (B n),
  have hB1_has : has_sum B1 (ennreal.of_real M),
  { have h_tsum_B1 : ∑' i, B1 i = (ennreal.of_real M),
    { change (∑' (n : ℕ), ennreal.of_real (B n)) = ennreal.of_real M,
      rw ←hB.tsum_eq,
      exact (ennreal.of_real_tsum_of_nonneg (λ n, le_of_lt (hB_pos n)) hB.summable).symm, },
    have h_sum := (@ennreal.summable _ B1).has_sum,
    rwa h_tsum_B1 at h_sum, },
  have hB1 : ∑' i, B1 i < ∞, by {rw hB1_has.tsum_eq, exact ennreal.of_real_lt_top, },
  let f1 : ℕ → α → E := λ n, f n,
  refine H f1 (λ n, Lp.mem_ℒp (f n)) B1 hB1 (λ N n m hn hm, _),
  specialize hf N n m hn hm,
  rw dist_def at hf,
  simp_rw [f1, B1],
  rwa ennreal.lt_of_real_iff_to_real_lt,
  rw snorm_congr_ae (Lp.coe_fn_sub _ _).symm,
  exact Lp.snorm_ne_top _,
end

/-! ### Prove that controlled Cauchy sequences of `ℒp` have limits in `ℒp` -/

private lemma snorm'_sum_norm_sub_le_tsum_of_cauchy_snorm' {f : ℕ → α → E}
  (hf : ∀ n, ae_strongly_measurable (f n) μ) {p : ℝ} (hp1 : 1 ≤ p)
  {B : ℕ → ℝ≥0∞} (h_cau : ∀ (N n m : ℕ), N ≤ n → N ≤ m → snorm' (f n - f m) p μ < B N) (n : ℕ) :
  snorm' (λ x, ∑ i in finset.range (n + 1), ‖f (i + 1) x - f i x‖) p μ ≤ ∑' i, B i :=
begin
  let f_norm_diff := λ i x, ‖f (i + 1) x - f i x‖,
  have hgf_norm_diff : ∀ n, (λ x, ∑ i in finset.range (n + 1), ‖f (i + 1) x - f i x‖)
      = ∑ i in finset.range (n + 1), f_norm_diff i,
    from λ n, funext (λ x, by simp [f_norm_diff]),
  rw hgf_norm_diff,
  refine (snorm'_sum_le (λ i _, ((hf (i+1)).sub (hf i)).norm) hp1).trans _,
  simp_rw [←pi.sub_apply, snorm'_norm],
  refine (finset.sum_le_sum _).trans (sum_le_tsum _ (λ m _, zero_le _) ennreal.summable),
  exact λ m _, (h_cau m (m + 1) m (nat.le_succ m) (le_refl m)).le,
end

private lemma lintegral_rpow_sum_coe_nnnorm_sub_le_rpow_tsum {f : ℕ → α → E}
  (hf : ∀ n, ae_strongly_measurable (f n) μ) {p : ℝ} (hp1 : 1 ≤ p) {B : ℕ → ℝ≥0∞} (n : ℕ)
  (hn : snorm' (λ x, ∑ i in finset.range (n + 1), ‖f (i + 1) x - f i x‖) p μ ≤ ∑' i, B i) :
  ∫⁻ a, (∑ i in finset.range (n + 1), ‖f (i + 1) a - f i a‖₊ : ℝ≥0∞)^p ∂μ
    ≤ (∑' i, B i) ^ p :=
begin
  have hp_pos : 0 < p := zero_lt_one.trans_le hp1,
  rw [←one_div_one_div p, @ennreal.le_rpow_one_div_iff _ _ (1/p) (by simp [hp_pos]),
    one_div_one_div p],
  simp_rw snorm' at hn,
  have h_nnnorm_nonneg :
    (λ a, (‖∑ i in finset.range (n + 1), ‖f (i + 1) a - f i a‖‖₊ : ℝ≥0∞) ^ p)
    = λ a, (∑ i in finset.range (n + 1), (‖f (i + 1) a - f i a‖₊ : ℝ≥0∞)) ^ p,
  { ext1 a,
    congr,
    simp_rw ←of_real_norm_eq_coe_nnnorm,
    rw ←ennreal.of_real_sum_of_nonneg,
    { rw real.norm_of_nonneg _,
      exact finset.sum_nonneg (λ x hx, norm_nonneg _), },
    { exact λ x hx, norm_nonneg _, }, },
  change (∫⁻ a, (λ x, ↑‖∑ i in finset.range (n + 1), ‖f (i+1) x - f i x‖‖₊^p) a ∂μ)^(1/p)
    ≤ ∑' i, B i at hn,
  rwa h_nnnorm_nonneg at hn,
end

private lemma lintegral_rpow_tsum_coe_nnnorm_sub_le_tsum {f : ℕ → α → E}
  (hf : ∀ n, ae_strongly_measurable (f n) μ) {p : ℝ} (hp1 : 1 ≤ p) {B : ℕ → ℝ≥0∞}
  (h : ∀ n, ∫⁻ a, (∑ i in finset.range (n + 1), ‖f (i + 1) a - f i a‖₊ : ℝ≥0∞)^p ∂μ
    ≤ (∑' i, B i) ^ p) :
  (∫⁻ a, (∑' i, ‖f (i + 1) a - f i a‖₊ : ℝ≥0∞)^p ∂μ) ^ (1/p) ≤ ∑' i, B i :=
begin
  have hp_pos : 0 < p := zero_lt_one.trans_le hp1,
  suffices h_pow : ∫⁻ a, (∑' i, ‖f (i + 1) a - f i a‖₊ : ℝ≥0∞)^p ∂μ ≤ (∑' i, B i) ^ p,
    by rwa [←ennreal.le_rpow_one_div_iff (by simp [hp_pos] : 0 < 1 / p), one_div_one_div],
  have h_tsum_1 : ∀ g : ℕ → ℝ≥0∞,
      ∑' i, g i = at_top.liminf (λ n, ∑ i in finset.range (n + 1), g i),
    by { intro g, rw [ennreal.tsum_eq_liminf_sum_nat, ← liminf_nat_add _ 1], },
  simp_rw h_tsum_1 _,
  rw ← h_tsum_1,
  have h_liminf_pow : ∫⁻ a, at_top.liminf (λ n, ∑ i in finset.range (n + 1),
      (‖f (i + 1) a - f i a‖₊))^p ∂μ
    = ∫⁻ a, at_top.liminf (λ n, (∑ i in finset.range (n + 1), (‖f (i + 1) a - f i a‖₊))^p) ∂μ,
  { refine lintegral_congr (λ x, _),
    have h_rpow_mono := ennreal.strict_mono_rpow_of_pos (zero_lt_one.trans_le hp1),
    have h_rpow_surj := (ennreal.rpow_left_bijective hp_pos.ne.symm).2,
    refine (h_rpow_mono.order_iso_of_surjective _ h_rpow_surj).liminf_apply _ _ _ _,
    all_goals { is_bounded_default }, },
  rw h_liminf_pow,
  refine (lintegral_liminf_le' _).trans _,
  { exact λ n, (finset.ae_measurable_sum (finset.range (n+1))
      (λ i _, ((hf (i+1)).sub (hf i)).ennnorm)).pow_const _, },
  { exact liminf_le_of_frequently_le' (frequently_of_forall h), },
end

private lemma tsum_nnnorm_sub_ae_lt_top
  {f : ℕ → α → E} (hf : ∀ n, ae_strongly_measurable (f n) μ) {p : ℝ} (hp1 : 1 ≤ p) {B : ℕ → ℝ≥0∞}
  (hB : ∑' i, B i ≠ ∞)
  (h : (∫⁻ a, (∑' i, ‖f (i + 1) a - f i a‖₊ : ℝ≥0∞)^p ∂μ) ^ (1/p) ≤ ∑' i, B i) :
  ∀ᵐ x ∂μ, (∑' i, ‖f (i + 1) x - f i x‖₊ : ℝ≥0∞) < ∞ :=
begin
  have hp_pos : 0 < p := zero_lt_one.trans_le hp1,
  have h_integral : ∫⁻ a, (∑' i, ‖f (i + 1) a - f i a‖₊ : ℝ≥0∞)^p ∂μ < ∞,
  { have h_tsum_lt_top : (∑' i, B i) ^ p < ∞,
      from ennreal.rpow_lt_top_of_nonneg hp_pos.le hB,
    refine lt_of_le_of_lt _ h_tsum_lt_top,
    rwa [←ennreal.le_rpow_one_div_iff (by simp [hp_pos] : 0 < 1 / p), one_div_one_div] at h, },
  have rpow_ae_lt_top : ∀ᵐ x ∂μ, (∑' i, ‖f (i + 1) x - f i x‖₊ : ℝ≥0∞)^p < ∞,
  { refine ae_lt_top' (ae_measurable.pow_const _ _) h_integral.ne,
    exact ae_measurable.ennreal_tsum (λ n, ((hf (n+1)).sub (hf n)).ennnorm), },
  refine rpow_ae_lt_top.mono (λ x hx, _),
  rwa [←ennreal.lt_rpow_one_div_iff hp_pos,
    ennreal.top_rpow_of_pos (by simp [hp_pos] : 0 < 1 / p)] at hx,
end

lemma ae_tendsto_of_cauchy_snorm' [complete_space E] {f : ℕ → α → E} {p : ℝ}
  (hf : ∀ n, ae_strongly_measurable (f n) μ) (hp1 : 1 ≤ p) {B : ℕ → ℝ≥0∞} (hB : ∑' i, B i ≠ ∞)
  (h_cau : ∀ (N n m : ℕ), N ≤ n → N ≤ m → snorm' (f n - f m) p μ < B N) :
  ∀ᵐ x ∂μ, ∃ l : E, at_top.tendsto (λ n, f n x) (𝓝 l) :=
begin
  have h_summable : ∀ᵐ x ∂μ, summable (λ (i : ℕ), f (i + 1) x - f i x),
  { have h1 : ∀ n, snorm' (λ x, ∑ i in finset.range (n + 1), ‖f (i + 1) x - f i x‖) p μ
        ≤ ∑' i, B i,
      from snorm'_sum_norm_sub_le_tsum_of_cauchy_snorm' hf hp1 h_cau,
    have h2 : ∀ n, ∫⁻ a, (∑ i in finset.range (n + 1), ‖f (i + 1) a - f i a‖₊ : ℝ≥0∞)^p ∂μ
        ≤ (∑' i, B i) ^ p,
      from λ n, lintegral_rpow_sum_coe_nnnorm_sub_le_rpow_tsum hf hp1 n (h1 n),
    have h3 : (∫⁻ a, (∑' i, ‖f (i + 1) a - f i a‖₊ : ℝ≥0∞)^p ∂μ) ^ (1/p) ≤ ∑' i, B i,
      from lintegral_rpow_tsum_coe_nnnorm_sub_le_tsum hf hp1 h2,
    have h4 : ∀ᵐ x ∂μ, (∑' i, ‖f (i + 1) x - f i x‖₊ : ℝ≥0∞) < ∞,
      from tsum_nnnorm_sub_ae_lt_top hf hp1 hB h3,
    exact h4.mono (λ x hx, summable_of_summable_nnnorm
      (ennreal.tsum_coe_ne_top_iff_summable.mp (lt_top_iff_ne_top.mp hx))), },
  have h : ∀ᵐ x ∂μ, ∃ l : E,
    at_top.tendsto (λ n, ∑ i in finset.range n, (f (i + 1) x - f i x)) (𝓝 l),
  { refine h_summable.mono (λ x hx, _),
    let hx_sum := hx.has_sum.tendsto_sum_nat,
    exact ⟨∑' i, (f (i + 1) x - f i x), hx_sum⟩, },
  refine h.mono (λ x hx, _),
  cases hx with l hx,
  have h_rw_sum : (λ n, ∑ i in finset.range n, (f (i + 1) x - f i x)) = λ n, f n x - f 0 x,
  { ext1 n,
    change ∑ (i : ℕ) in finset.range n, ((λ m, f m x) (i + 1) - (λ m, f m x) i) = f n x - f 0 x,
    rw finset.sum_range_sub, },
  rw h_rw_sum at hx,
  have hf_rw : (λ n, f n x) = λ n, f n x - f 0 x + f 0 x, by { ext1 n, abel, },
  rw hf_rw,
  exact ⟨l + f 0 x, tendsto.add_const _ hx⟩,
end

lemma ae_tendsto_of_cauchy_snorm [complete_space E] {f : ℕ → α → E}
  (hf : ∀ n, ae_strongly_measurable (f n) μ) (hp : 1 ≤ p) {B : ℕ → ℝ≥0∞} (hB : ∑' i, B i ≠ ∞)
  (h_cau : ∀ (N n m : ℕ), N ≤ n → N ≤ m → snorm (f n - f m) p μ < B N) :
  ∀ᵐ x ∂μ, ∃ l : E, at_top.tendsto (λ n, f n x) (𝓝 l) :=
begin
  by_cases hp_top : p = ∞,
  { simp_rw [hp_top] at *,
    have h_cau_ae : ∀ᵐ x ∂μ, ∀ N n m, N ≤ n → N ≤ m → (‖(f n - f m) x‖₊ : ℝ≥0∞) < B N,
    { simp_rw ae_all_iff,
      exact λ N n m hnN hmN, ae_lt_of_ess_sup_lt (h_cau N n m hnN hmN), },
    simp_rw [snorm_exponent_top, snorm_ess_sup] at h_cau,
    refine h_cau_ae.mono (λ x hx, cauchy_seq_tendsto_of_complete _),
    refine cauchy_seq_of_le_tendsto_0 (λ n, (B n).to_real) _ _,
    { intros n m N hnN hmN,
      specialize hx N n m hnN hmN,
      rw [dist_eq_norm, ←ennreal.to_real_of_real (norm_nonneg _),
        ennreal.to_real_le_to_real ennreal.of_real_ne_top
        (ennreal.ne_top_of_tsum_ne_top hB N)],
      rw ←of_real_norm_eq_coe_nnnorm at hx,
      exact hx.le, },
    { rw ← ennreal.zero_to_real,
      exact tendsto.comp (ennreal.tendsto_to_real ennreal.zero_ne_top)
        (ennreal.tendsto_at_top_zero_of_tsum_ne_top hB), }, },
  have hp1 : 1 ≤ p.to_real,
  { rw [← ennreal.of_real_le_iff_le_to_real hp_top, ennreal.of_real_one],
    exact hp, },
  have h_cau' : ∀ (N n m : ℕ), N ≤ n → N ≤ m → snorm' (f n - f m) (p.to_real) μ < B N,
  { intros N n m hn hm,
    specialize h_cau N n m hn hm,
    rwa snorm_eq_snorm' (zero_lt_one.trans_le hp).ne.symm hp_top at h_cau, },
  exact ae_tendsto_of_cauchy_snorm' hf hp1 hB h_cau',
end

lemma cauchy_tendsto_of_tendsto {f : ℕ → α → E} (hf : ∀ n, ae_strongly_measurable (f n) μ)
  (f_lim : α → E) {B : ℕ → ℝ≥0∞}
  (hB : ∑' i, B i ≠ ∞) (h_cau : ∀ (N n m : ℕ), N ≤ n → N ≤ m → snorm (f n - f m) p μ < B N)
  (h_lim : ∀ᵐ (x : α) ∂μ, tendsto (λ n, f n x) at_top (𝓝 (f_lim x))) :
  at_top.tendsto (λ n, snorm (f n - f_lim) p μ) (𝓝 0) :=
begin
  rw ennreal.tendsto_at_top_zero,
  intros ε hε,
  have h_B : ∃ (N : ℕ), B N ≤ ε,
  { suffices h_tendsto_zero : ∃ (N : ℕ), ∀ n : ℕ, N ≤ n → B n ≤ ε,
      from ⟨h_tendsto_zero.some, h_tendsto_zero.some_spec _ le_rfl⟩,
    exact (ennreal.tendsto_at_top_zero.mp (ennreal.tendsto_at_top_zero_of_tsum_ne_top hB))
      ε hε, },
  cases h_B with N h_B,
  refine ⟨N, λ n hn, _⟩,
  have h_sub : snorm (f n - f_lim) p μ ≤ at_top.liminf (λ m, snorm (f n - f m) p μ),
  { refine snorm_lim_le_liminf_snorm (λ m, (hf n).sub (hf m)) (f n - f_lim) _,
    refine h_lim.mono (λ x hx, _),
    simp_rw sub_eq_add_neg,
    exact tendsto.add tendsto_const_nhds (tendsto.neg hx), },
  refine h_sub.trans _,
  refine liminf_le_of_frequently_le' (frequently_at_top.mpr _),
  refine λ N1, ⟨max N N1, le_max_right _ _, _⟩,
  exact (h_cau N n (max N N1) hn (le_max_left _ _)).le.trans h_B,
end

lemma mem_ℒp_of_cauchy_tendsto (hp : 1 ≤ p) {f : ℕ → α → E} (hf : ∀ n, mem_ℒp (f n) p μ)
  (f_lim : α → E) (h_lim_meas : ae_strongly_measurable f_lim μ)
  (h_tendsto : at_top.tendsto (λ n, snorm (f n - f_lim) p μ) (𝓝 0)) :
  mem_ℒp f_lim p μ :=
begin
  refine ⟨h_lim_meas, _⟩,
  rw ennreal.tendsto_at_top_zero at h_tendsto,
  cases (h_tendsto 1 zero_lt_one) with N h_tendsto_1,
  specialize h_tendsto_1 N (le_refl N),
  have h_add : f_lim = f_lim - f N + f N, by abel,
  rw h_add,
  refine lt_of_le_of_lt (snorm_add_le (h_lim_meas.sub (hf N).1) (hf N).1 hp) _,
  rw ennreal.add_lt_top,
  split,
  { refine lt_of_le_of_lt _ ennreal.one_lt_top,
    have h_neg : f_lim - f N = -(f N - f_lim), by simp,
    rwa [h_neg, snorm_neg], },
  { exact (hf N).2, },
end

lemma cauchy_complete_ℒp [complete_space E] (hp : 1 ≤ p)
  {f : ℕ → α → E} (hf : ∀ n, mem_ℒp (f n) p μ) {B : ℕ → ℝ≥0∞} (hB : ∑' i, B i ≠ ∞)
  (h_cau : ∀ (N n m : ℕ), N ≤ n → N ≤ m → snorm (f n - f m) p μ < B N) :
  ∃ (f_lim : α → E) (hf_lim_meas : mem_ℒp f_lim p μ),
    at_top.tendsto (λ n, snorm (f n - f_lim) p μ) (𝓝 0) :=
begin
  obtain ⟨f_lim, h_f_lim_meas, h_lim⟩ : ∃ (f_lim : α → E) (hf_lim_meas : strongly_measurable f_lim),
      ∀ᵐ x ∂μ, tendsto (λ n, f n x) at_top (nhds (f_lim x)),
    from exists_strongly_measurable_limit_of_tendsto_ae (λ n, (hf n).1)
      (ae_tendsto_of_cauchy_snorm (λ n, (hf n).1) hp hB h_cau),
  have h_tendsto' : at_top.tendsto (λ n, snorm (f n - f_lim) p μ) (𝓝 0),
    from cauchy_tendsto_of_tendsto (λ m, (hf m).1) f_lim hB h_cau h_lim,
  have h_ℒp_lim : mem_ℒp f_lim p μ,
    from mem_ℒp_of_cauchy_tendsto hp hf f_lim h_f_lim_meas.ae_strongly_measurable h_tendsto',
  exact ⟨f_lim, h_ℒp_lim, h_tendsto'⟩,
end

/-! ### `Lp` is complete for `1 ≤ p` -/

instance [complete_space E] [hp : fact (1 ≤ p)] : complete_space (Lp E p μ) :=
complete_space_Lp_of_cauchy_complete_ℒp $
  λ f hf B hB h_cau, cauchy_complete_ℒp hp.elim hf hB.ne h_cau

end Lp
end measure_theory

end complete_space

/-! ### Continuous functions in `Lp` -/

open_locale bounded_continuous_function
open bounded_continuous_function

section

variables [topological_space α] [borel_space α] [second_countable_topology_either α E]
variables (E p μ)

/-- An additive subgroup of `Lp E p μ`, consisting of the equivalence classes which contain a
bounded continuous representative. -/
def measure_theory.Lp.bounded_continuous_function : add_subgroup (Lp E p μ) :=
add_subgroup.add_subgroup_of
  ((continuous_map.to_ae_eq_fun_add_hom μ).comp (to_continuous_map_add_hom α E)).range
  (Lp E p μ)

variables {E p μ}

/-- By definition, the elements of `Lp.bounded_continuous_function E p μ` are the elements of
`Lp E p μ` which contain a bounded continuous representative. -/
lemma measure_theory.Lp.mem_bounded_continuous_function_iff {f : (Lp E p μ)} :
  f ∈ measure_theory.Lp.bounded_continuous_function E p μ
    ↔ ∃ f₀ : (α →ᵇ E), f₀.to_continuous_map.to_ae_eq_fun μ = (f : α →ₘ[μ] E) :=
add_subgroup.mem_add_subgroup_of

namespace bounded_continuous_function

variables [is_finite_measure μ]

/-- A bounded continuous function on a finite-measure space is in `Lp`. -/
lemma mem_Lp (f : α →ᵇ E) :
  f.to_continuous_map.to_ae_eq_fun μ ∈ Lp E p μ :=
begin
  refine Lp.mem_Lp_of_ae_bound (‖f‖) _,
  filter_upwards [f.to_continuous_map.coe_fn_to_ae_eq_fun μ] with x _,
  convert f.norm_coe_le_norm x
end

/-- The `Lp`-norm of a bounded continuous function is at most a constant (depending on the measure
of the whole space) times its sup-norm. -/
lemma Lp_nnnorm_le (f : α →ᵇ E) :
  ‖(⟨f.to_continuous_map.to_ae_eq_fun μ, mem_Lp f⟩ : Lp E p μ)‖₊
  ≤ (measure_univ_nnreal μ) ^ (p.to_real)⁻¹ * ‖f‖₊ :=
begin
  apply Lp.nnnorm_le_of_ae_bound,
  refine (f.to_continuous_map.coe_fn_to_ae_eq_fun μ).mono _,
  intros x hx,
  rw [←nnreal.coe_le_coe, coe_nnnorm, coe_nnnorm],
  convert f.norm_coe_le_norm x,
end

/-- The `Lp`-norm of a bounded continuous function is at most a constant (depending on the measure
of the whole space) times its sup-norm. -/
lemma Lp_norm_le (f : α →ᵇ E) :
  ‖(⟨f.to_continuous_map.to_ae_eq_fun μ, mem_Lp f⟩ : Lp E p μ)‖
  ≤ (measure_univ_nnreal μ) ^ (p.to_real)⁻¹ * ‖f‖ :=
Lp_nnnorm_le f

variables (p μ)

/-- The normed group homomorphism of considering a bounded continuous function on a finite-measure
space as an element of `Lp`. -/
def to_Lp_hom [fact (1 ≤ p)] : normed_add_group_hom (α →ᵇ E) (Lp E p μ) :=
{ bound' := ⟨_, Lp_norm_le⟩,
  .. add_monoid_hom.cod_restrict
      ((continuous_map.to_ae_eq_fun_add_hom μ).comp (to_continuous_map_add_hom α E))
      (Lp E p μ)
      mem_Lp }

lemma range_to_Lp_hom [fact (1 ≤ p)] :
  ((to_Lp_hom p μ).range : add_subgroup (Lp E p μ))
    = measure_theory.Lp.bounded_continuous_function E p μ :=
begin
  symmetry,
  convert add_monoid_hom.add_subgroup_of_range_eq_of_le
    ((continuous_map.to_ae_eq_fun_add_hom μ).comp (to_continuous_map_add_hom α E))
    (by { rintros - ⟨f, rfl⟩, exact mem_Lp f } : _ ≤ Lp E p μ),
end

variables (𝕜 : Type*) [fact (1 ≤ p)]

/-- The bounded linear map of considering a bounded continuous function on a finite-measure space
as an element of `Lp`. -/
def to_Lp [normed_field 𝕜] [normed_space 𝕜 E] :
  (α →ᵇ E) →L[𝕜] (Lp E p μ) :=
linear_map.mk_continuous
  (linear_map.cod_restrict
    (Lp.Lp_submodule E p μ 𝕜)
    ((continuous_map.to_ae_eq_fun_linear_map μ).comp (to_continuous_map_linear_map α E 𝕜))
    mem_Lp)
  _
  Lp_norm_le

lemma coe_fn_to_Lp [normed_field 𝕜] [normed_space 𝕜 E] (f : α →ᵇ E) :
  to_Lp p μ 𝕜 f =ᵐ[μ] f := ae_eq_fun.coe_fn_mk f _

variables {𝕜}

lemma range_to_Lp [normed_field 𝕜] [normed_space 𝕜 E] :
  ((linear_map.range (to_Lp p μ 𝕜 : (α →ᵇ E) →L[𝕜] Lp E p μ)).to_add_subgroup)
    = measure_theory.Lp.bounded_continuous_function E p μ :=
range_to_Lp_hom p μ

variables {p}

lemma to_Lp_norm_le [nontrivially_normed_field 𝕜] [normed_space 𝕜 E]:
  ‖(to_Lp p μ 𝕜 : (α →ᵇ E) →L[𝕜] (Lp E p μ))‖ ≤ (measure_univ_nnreal μ) ^ (p.to_real)⁻¹ :=
linear_map.mk_continuous_norm_le _ ((measure_univ_nnreal μ) ^ (p.to_real)⁻¹).coe_nonneg _

lemma to_Lp_inj {f g : α →ᵇ E} [μ.is_open_pos_measure] [normed_field 𝕜] [normed_space 𝕜 E] :
  to_Lp p μ 𝕜 f = to_Lp p μ 𝕜 g ↔ f = g :=
begin
  refine ⟨λ h, _, by tauto⟩,
  rw [←fun_like.coe_fn_eq, ←(map_continuous f).ae_eq_iff_eq μ (map_continuous g)],
  refine (coe_fn_to_Lp p μ 𝕜 f).symm.trans (eventually_eq.trans _ $ coe_fn_to_Lp p μ 𝕜 g),
  rw h,
end

lemma to_Lp_injective [μ.is_open_pos_measure] [normed_field 𝕜] [normed_space 𝕜 E] :
  function.injective ⇑(to_Lp p μ 𝕜 : (α →ᵇ E) →L[𝕜] (Lp E p μ)) := λ f g hfg, (to_Lp_inj μ).mp hfg

end bounded_continuous_function

namespace continuous_map

variables [compact_space α] [is_finite_measure μ]
variables (𝕜 : Type*) (p μ) [fact (1 ≤ p)]

/-- The bounded linear map of considering a continuous function on a compact finite-measure
space `α` as an element of `Lp`.  By definition, the norm on `C(α, E)` is the sup-norm, transferred
from the space `α →ᵇ E` of bounded continuous functions, so this construction is just a matter of
transferring the structure from `bounded_continuous_function.to_Lp` along the isometry. -/
def to_Lp [normed_field 𝕜] [normed_space 𝕜 E] :
  C(α, E) →L[𝕜] (Lp E p μ) :=
(bounded_continuous_function.to_Lp p μ 𝕜).comp
  (linear_isometry_bounded_of_compact α E 𝕜).to_linear_isometry.to_continuous_linear_map

variables {𝕜}

lemma range_to_Lp [normed_field 𝕜] [normed_space 𝕜 E] :
  (linear_map.range (to_Lp p μ 𝕜 : C(α, E) →L[𝕜] Lp E p μ)).to_add_subgroup
    = measure_theory.Lp.bounded_continuous_function E p μ :=
begin
  refine set_like.ext' _,
  have := (linear_isometry_bounded_of_compact α E 𝕜).surjective,
  convert function.surjective.range_comp this (bounded_continuous_function.to_Lp p μ 𝕜),
  rw ←bounded_continuous_function.range_to_Lp p μ,
  refl,
end

variables {p}

lemma coe_fn_to_Lp [normed_field 𝕜] [normed_space 𝕜 E] (f : C(α,  E)) :
  to_Lp p μ 𝕜 f =ᵐ[μ] f :=
ae_eq_fun.coe_fn_mk f _

lemma to_Lp_def [normed_field 𝕜] [normed_space 𝕜 E] (f : C(α, E)) :
  to_Lp p μ 𝕜 f
  = bounded_continuous_function.to_Lp p μ 𝕜 (linear_isometry_bounded_of_compact α E 𝕜 f) :=
rfl

@[simp] lemma to_Lp_comp_to_continuous_map [normed_field 𝕜] [normed_space 𝕜 E] (f : α →ᵇ E) :
  to_Lp p μ 𝕜 f.to_continuous_map
  = bounded_continuous_function.to_Lp p μ 𝕜 f :=
rfl

@[simp] lemma coe_to_Lp [normed_field 𝕜] [normed_space 𝕜 E] (f : C(α, E)) :
  (to_Lp p μ 𝕜 f : α →ₘ[μ] E) = f.to_ae_eq_fun μ :=
rfl

lemma to_Lp_injective [μ.is_open_pos_measure] [normed_field 𝕜] [normed_space 𝕜 E] :
  function.injective ⇑(to_Lp p μ 𝕜 : C(α, E) →L[𝕜] (Lp E p μ)) :=
(bounded_continuous_function.to_Lp_injective _).comp
  (linear_isometry_bounded_of_compact α E 𝕜).injective

lemma to_Lp_inj {f g : C(α, E)} [μ.is_open_pos_measure] [normed_field 𝕜] [normed_space 𝕜 E] :
  to_Lp p μ 𝕜 f = to_Lp p μ 𝕜 g ↔ f = g :=
(to_Lp_injective μ).eq_iff

variables {μ}

/-- If a sum of continuous functions `g n` is convergent, and the same sum converges in `Lᵖ` to `h`,
then in fact `g n` converges uniformly to `h`.  -/
lemma has_sum_of_has_sum_Lp {β : Type*} [μ.is_open_pos_measure] [normed_field 𝕜] [normed_space 𝕜 E]
  {g : β → C(α, E)} {f : C(α, E)} (hg : summable g)
  (hg2 : has_sum (to_Lp p μ 𝕜 ∘ g) (to_Lp p μ 𝕜 f)) : has_sum g f :=
begin
  convert summable.has_sum hg,
  exact to_Lp_injective μ (hg2.unique ((to_Lp p μ 𝕜).has_sum $ summable.has_sum hg)),
end

variables (μ) [nontrivially_normed_field 𝕜] [normed_space 𝕜 E]

lemma to_Lp_norm_eq_to_Lp_norm_coe :
  ‖(to_Lp p μ 𝕜 : C(α, E) →L[𝕜] (Lp E p μ))‖
  = ‖(bounded_continuous_function.to_Lp p μ 𝕜 : (α →ᵇ E) →L[𝕜] (Lp E p μ))‖ :=
continuous_linear_map.op_norm_comp_linear_isometry_equiv _ _

/-- Bound for the operator norm of `continuous_map.to_Lp`. -/
lemma to_Lp_norm_le :
  ‖(to_Lp p μ 𝕜 : C(α, E) →L[𝕜] (Lp E p μ))‖ ≤ (measure_univ_nnreal μ) ^ (p.to_real)⁻¹ :=
by { rw to_Lp_norm_eq_to_Lp_norm_coe, exact bounded_continuous_function.to_Lp_norm_le μ }

end continuous_map

end

namespace measure_theory

namespace Lp

lemma pow_mul_meas_ge_le_norm (f : Lp E p μ)
  (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) (ε : ℝ≥0∞) :
  (ε * μ {x | ε ≤ ‖f x‖₊ ^ p.to_real}) ^ (1 / p.to_real) ≤ (ennreal.of_real ‖f‖) :=
(ennreal.of_real_to_real (snorm_ne_top f)).symm ▸
  pow_mul_meas_ge_le_snorm μ hp_ne_zero hp_ne_top (Lp.ae_strongly_measurable f) ε

lemma mul_meas_ge_le_pow_norm (f : Lp E p μ)
  (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) (ε : ℝ≥0∞) :
  ε * μ {x | ε ≤ ‖f x‖₊ ^ p.to_real} ≤ (ennreal.of_real ‖f‖) ^ p.to_real :=
(ennreal.of_real_to_real (snorm_ne_top f)).symm ▸
  mul_meas_ge_le_pow_snorm μ hp_ne_zero hp_ne_top (Lp.ae_strongly_measurable f) ε

/-- A version of Markov's inequality with elements of Lp. -/
lemma mul_meas_ge_le_pow_norm' (f : Lp E p μ)
  (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) (ε : ℝ≥0∞) :
  ε ^ p.to_real * μ {x | ε ≤ ‖f x‖₊} ≤ (ennreal.of_real ‖f‖) ^ p.to_real :=
(ennreal.of_real_to_real (snorm_ne_top f)).symm ▸
  mul_meas_ge_le_pow_snorm' μ hp_ne_zero hp_ne_top (Lp.ae_strongly_measurable f) ε

lemma meas_ge_le_mul_pow_norm (f : Lp E p μ)
  (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
  μ {x | ε ≤ ‖f x‖₊} ≤ ε⁻¹ ^ p.to_real * (ennreal.of_real ‖f‖) ^ p.to_real :=
(ennreal.of_real_to_real (snorm_ne_top f)).symm ▸
  meas_ge_le_mul_pow_snorm μ hp_ne_zero hp_ne_top (Lp.ae_strongly_measurable f) hε

end Lp

end measure_theory
