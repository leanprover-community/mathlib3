/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/

import measure_theory.simple_func_dense
import analysis.normed_space.bounded_linear_maps

/-!
# Bochner integral

To be added soon.

## Main definitions

`simple_func.bintegral` :
    bochner integral of simple functions.

`l1.simple_func` :
    subspace of L1 consisting of equivalence classes of an integrable simple function.

`l1.simple_func.integral` :
    bochner integral of `l1.simple_func`; basically the same thing as `simple_func.bintegral`.

`l1.simple_func.integral_clm` :
    `l1.simple_func.integral` as a continuous linear map.

## Main statements

`section bintegral` : basic properties of `simple_func.bintegral` proved.

`section instances` : `l1.simple_func` forms a `normed_space`.

`section coe_to_l1` : `coe` from `l1.simple_func` to `l1` is a uniform and dense embedding.

`section simple_func_integral` : basic properties of `l1.simple_func.integral`.
-/

noncomputable theory
open_locale classical

set_option class.instance_max_depth 100

namespace measure_theory
open set lattice filter topological_space ennreal emetric

universes u v w
variables {α : Type u} [measure_space α]{β : Type v} {γ : Type w}

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
    finite support. -/
lemma integrable_iff_fin_vol_supp (f : α →ₛ β) : integrable f ↔ f.fin_vol_supp :=
iff.intro fin_vol_supp_of_integrable integrable_of_fin_vol_supp

lemma integrable_pair {f : α →ₛ β} {g : α →ₛ γ} (hf : integrable f) (hg : integrable g) :
  integrable (pair f g) :=
by { rw integrable_iff_fin_vol_supp at *, apply fin_vol_supp_pair; assumption }

variables [normed_space ℝ γ]

/-- Bochner integral of simple functions whose codomain is a real `normed_space`.
    The name `simple_func.integral` has been taken in the file `integration.lean`, which calculates
    the integral of a simple function with type `α → ennreal`.
    The name `bintegral` stands for bochner integral. -/
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

/-- `simple_func.bintegral` and `simple_func.integral` agrees when the integrand has type
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

/-- `simple_func.bintegral` and `simple_func.integral` agrees when the integrand has type
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

/-- `simple_func.bintegral` and `lintegral : (α → ennreal) → ennreal` agrees when the integrand has
    type `α →ₛ ennreal`. But since `ennreal` is not a `normed_space`, we need some form of coercion. -/
lemma bintegral_eq_lintegral' {f : α →ₛ ℝ} (hf : integrable f) (h_pos : ∀ₘ a, 0 ≤ f a) :
  f.bintegral = ennreal.to_real (∫⁻ a, (f.map ennreal.of_real a)) :=
by rw [bintegral_eq_integral' hf h_pos, ← lintegral_eq_integral]

lemma bintegral_add {f g : α →ₛ β} (hf : integrable f) (hg : integrable g) :
  bintegral (f + g) = bintegral f + bintegral g :=
calc bintegral (f + g) = _ :
begin
  rw [add_eq_map₂, map_bintegral (pair f g)],
  { exact integrable_pair hf hg },
  { simp only [add_zero, prod.fst_zero, prod.snd_zero] }
end
... = sum (simple_func.range (pair f g))
    (λ (x : β × β), ennreal.to_real (volume ((pair f g) ⁻¹' {x})) • x.fst +
                    ennreal.to_real (volume ((pair f g) ⁻¹' {x})) • x.snd) :
  finset.sum_congr rfl $ assume a ha, smul_add _ _ _
... = _ : by { rw [finset.sum_add_distrib] }
... = ((pair f g).map prod.fst).bintegral + ((pair f g).map prod.snd).bintegral :
begin
  rw [map_bintegral (pair f g), map_bintegral (pair f g)],
  { exact integrable_pair hf hg }, { refl },
  { exact integrable_pair hf hg }, { refl }
end
... = bintegral f + bintegral g : rfl

lemma bintegral_smul (r : ℝ) {f : α →ₛ β} (hf : integrable f) :
  bintegral (r • f) = r • bintegral f :=
calc bintegral (r • f) = _ : by rw [smul_eq_map r f, map_bintegral f _ hf (smul_zero _)]
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
  calc _ ≤ _ : norm_triangle_sum _ _
    ... = _ :
    begin
      refine finset.sum_congr rfl (λb hb, _),
      rw [norm_smul, smul_eq_mul, real.norm_eq_abs, abs_of_nonneg to_real_nonneg]
    end
end

end bintegral

end simple_func

namespace l1

variables [normed_group β] [second_countable_topology β]
          [normed_group γ] [second_countable_topology γ]

variables (α β)
/-- `l1.simple_func` is a subspace of L1 consisting of equivalence classes of an integrable simple
    function. -/
def simple_func : Type* :=
{ f : α →₁ β // ∃ (s : simple_func α β) (hs : integrable s), mk s s.measurable hs = f}
variables {α β}

local infixr ` →ₛ `:25 := measure_theory.l1.simple_func

namespace simple_func
open ae_eq_fun

/-- Construct the equivalence class `[f]` of a integrable simple function `f`. -/
def mk (f : measure_theory.simple_func α β) (hf : integrable f) : (α →ₛ β) :=
⟨l1.mk f f.measurable hf, ⟨f, ⟨hf, rfl⟩⟩⟩

@[simp] lemma mk_eq_mk (f g : measure_theory.simple_func α β) (hf hg) :
  mk f hf = mk g hg ↔ (∀ₘ a, f a = g a) :=
by { simp only [mk, subtype.mk_eq_mk, l1.mk_eq_mk] }

/-- Find a representative of a `l1.simple_func`. -/
def to_simple_func (f : α →ₛ β) : measure_theory.simple_func α β := classical.some f.2

/-- `f.to_simple_func` is measurable. -/
protected lemma measurable (f : α →ₛ β) : measurable f.to_simple_func := f.to_simple_func.measurable

/-- `f.to_simple_func` is integrable. -/
protected lemma integrable (f : α →ₛ β) : integrable f.to_simple_func :=
let ⟨h, _⟩ := classical.some_spec f.2 in h

lemma to_simple_func_to_fun (f : α →ₛ β) : ∀ₘ a, (f.to_simple_func) a = f.1.to_fun a :=
begin
  rw ← l1.mk_eq_mk (f.to_simple_func) f.1.to_fun f.measurable f.integrable
    f.1.measurable f.1.integrable,
  rw ← self_eq_mk f.1,
  rcases classical.some_spec f.2 with ⟨_, h⟩,
  exact h
end

lemma mk_eq_mk' (f g : α →ₛ β) (hf hg) :
  mk f.to_simple_func hf = mk g.to_simple_func hg ↔ (∀ₘ a, f.to_simple_func a = g.to_simple_func a) :=
by { rw mk_eq_mk }

lemma ext_iff {f g : α →ₛ β} : f = g ↔ (∀ₘ a, f.to_simple_func a = g.to_simple_func a) :=
begin
  rcases f with ⟨f, hf⟩, rcases g with ⟨g, hg⟩,
  rcases classical.some_spec hf with ⟨hfi, hf⟩,
  rcases classical.some_spec hg with ⟨hfi, hg⟩,
  rw [subtype.mk_eq_mk, l1.ext_iff],
  repeat { assumption }
end

lemma mk_to_simple_func (f : α →ₛ β) : mk f.to_simple_func f.integrable = f :=
begin
  rcases f with ⟨f, hf⟩,
  rcases classical.some_spec hf with ⟨_, hf⟩,
  simp only [mk, subtype.mk_eq_mk],
  exact hf
end

lemma to_simple_func_mk (f : measure_theory.simple_func α β) (hf) :
  ∀ₘ a, to_simple_func (mk f hf) a = f a :=
let f' := to_simple_func (mk f hf) in
have h : mk f' (mk f hf).integrable = mk f hf := mk_to_simple_func _,
by { rw mk_eq_mk at h, exact h }

section instances

instance : has_zero (α →ₛ β) := ⟨⟨0, ⟨0, ⟨integrable_zero, mk_zero α β⟩⟩⟩⟩

variables (α β)

lemma zero_def : (0 : α →ₛ β) = ⟨0, ⟨0, ⟨integrable_zero, mk_zero α β⟩⟩⟩ := rfl

lemma mk_zero : mk (0 : measure_theory.simple_func α β) integrable_zero = 0 := rfl

lemma zero_to_simple_func : ∀ₘ a, (0 : α →ₛ β).to_simple_func a = 0 :=
begin
  filter_upwards [to_simple_func_to_fun (0 : α →ₛ β), l1.zero_to_fun α β],
  assume a,
  simp only [mem_set_of_eq],
  assume h,
  rw h,
  assume h,
  exact h
end

variables {α β}

instance : has_add (α →ₛ β) := ⟨λ f g,
  let f' := f.to_simple_func in
  let g' := g.to_simple_func in
  have hfm : measurable f' := f'.measurable,
  have hgm : measurable g' := g'.measurable,
  have hfi : integrable f' := f.integrable,
  have hgi : integrable g' := g.integrable,
  ⟨f.1 + g.1, ⟨f' + g', ⟨integrable_add hfm hgm hfi hgi,
    begin
      rcases f with ⟨f, hf⟩, rcases g with ⟨g, hg⟩,
      rcases classical.some_spec hf with ⟨_, hf⟩,
      rcases classical.some_spec hg with ⟨_, hg⟩,
      have : l1.mk f' hfm hfi + l1.mk g' hgm hgi = f + g, { rw [←hf, ←hg], refl },
      rw ← mk_add at this, exact this
    end⟩⟩⟩⟩

lemma add_def (f g : α →ₛ β) : f + g =
  let f' := f.to_simple_func in
  let g' := g.to_simple_func in
  have hfm : measurable f' := f'.measurable,
  have hgm : measurable g' := g'.measurable,
  have hfi : integrable f' := f.integrable,
  have hgi : integrable g' := g.integrable,
  ⟨f.1 + g.1, ⟨f' + g', ⟨integrable_add hfm hgm hfi hgi,
    begin
      rcases f with ⟨f, hf⟩, rcases g with ⟨g, hg⟩,
      rcases classical.some_spec hf with ⟨_, hf⟩,
      rcases classical.some_spec hg with ⟨_, hg⟩,
      have : l1.mk f' hfm hfi + l1.mk g' hgm hgi = f + g, { rw [←hf, ←hg], refl },
      rw ← mk_add at this,
      exact this
    end⟩⟩⟩ := rfl

lemma mk_add (f g : measure_theory.simple_func α β) (hf hg) :
  mk (f + g) (integrable_add f.measurable g.measurable hf hg) = mk f hf + mk g hg := rfl

lemma add_to_simple_func (f g : α →ₛ β) :
  ∀ₘ a, (f + g).to_simple_func a = f.to_simple_func a + g.to_simple_func a :=
begin
  filter_upwards [to_simple_func_to_fun (f + g), to_simple_func_to_fun f, to_simple_func_to_fun g,
                  l1.add_to_fun f.1 g.1],
  assume a, simp only [mem_set_of_eq],
  repeat { assume h, rw h },
  assume h,
  rw ← h,
  refl
end

instance : has_neg (α →ₛ β) := ⟨λf,
  let f' := f.to_simple_func in
  have hfm : measurable f' := f'.measurable,
  have hfi : integrable f' := f.integrable,
  ⟨-f.1, ⟨-f', ⟨integrable_neg hfi,
    begin
      rcases f with ⟨f, hf⟩,
      rcases classical.some_spec hf with ⟨_, hf⟩,
      have : -l1.mk f' hfm hfi = -f, rw ← hf, refl,
      rw neg_mk at this, exact this
    end⟩⟩⟩⟩

lemma neg_def (f : α →ₛ β) : (-f) =
  let f' := f.to_simple_func in
  have hfm : measurable f' := f'.measurable,
  have hfi : integrable f' := f.integrable,
  ⟨-f.1, ⟨-f', ⟨integrable_neg hfi,
    begin
      rcases f with ⟨f, hf⟩,
      rcases classical.some_spec hf with ⟨_, hf⟩,
      have : -l1.mk f' hfm hfi = -f, rw ← hf, refl,
      rw neg_mk at this, exact this
    end⟩⟩⟩ := rfl

lemma neg_to_simple_func (f : α →ₛ β) : ∀ₘ a, (-f).to_simple_func a = - f.to_simple_func a :=
begin
  filter_upwards [to_simple_func_to_fun (-f), to_simple_func_to_fun f, l1.neg_to_fun f.1],
  assume a, simp only [mem_set_of_eq],
  repeat { assume h, rw h },
  assume h, rw ← h,
  refl
end

instance : add_monoid (α →ₛ β) :=
{ add := (+), zero := 0,
  add_assoc :=
    by { rintros ⟨f, hf⟩ ⟨g, hg⟩ ⟨h, hh⟩, simp only [add_def, subtype.mk_eq_mk, add_assoc] },
  zero_add :=
    by { rintros ⟨f, hf⟩, simp only [zero_def, neg_def, add_def, subtype.mk_eq_mk, zero_add] },
  add_zero :=
    by { rintros ⟨f, hf⟩, simp only [zero_def, neg_def, add_def, subtype.mk_eq_mk, add_zero] } }

instance : add_group (α →ₛ β) :=
{ neg := has_neg.neg,
  add_left_neg :=
    by {rintros ⟨f, hf⟩, simp only [zero_def, neg_def, add_def, subtype.mk_eq_mk, add_left_neg] },
  .. simple_func.add_monoid }

lemma sub_to_simple_func (f g : α →ₛ β) :
  ∀ₘ a, (f - g).to_simple_func a = f.to_simple_func a - g.to_simple_func a :=
begin
  filter_upwards [to_simple_func_to_fun (f - g), to_simple_func_to_fun f, to_simple_func_to_fun g,
                  l1.sub_to_fun f.1 g.1],
  assume a, simp only [mem_set_of_eq],
  repeat { assume h, rw h },
  assume h, rw ← h,
  refl
end

instance : add_comm_group (α →ₛ β) :=
{ add_comm :=
    by { rintros ⟨f, hf⟩ ⟨g, hg⟩, simp only [add_def, subtype.mk_eq_mk, add_comm] },
  .. simple_func.add_group }

variables {K : Type*} [normed_field K] [second_countable_topology K] [normed_space K β]

instance : has_scalar K (α →ₛ β) := ⟨λk f,
  let f' := f.to_simple_func in
  have hfm : measurable f' := f'.measurable,
  have hfi : integrable f' := f.integrable,
  ⟨k • f.1, ⟨k • f', ⟨integrable_smul hfi,
    begin
      rcases f with ⟨f, hf⟩,
      rcases classical.some_spec hf with ⟨_, hf⟩,
      have : k • l1.mk f' hfm hfi = k • f, rw ← hf, refl,
      rw smul_mk at this, exact this
    end⟩⟩⟩⟩

lemma smul_def (k : K) (f : α →ₛ β) : (k • f) =
  let f' := f.to_simple_func in
  have hfm : measurable f' := f'.measurable,
  have hfi : integrable f' := f.integrable,
  ⟨k • f.1, ⟨k • f', ⟨integrable_smul hfi,
    begin
      rcases f with ⟨f, hf⟩,
      rcases classical.some_spec hf with ⟨_, hf⟩,
      have : k • l1.mk f' hfm hfi = k • f, rw ← hf, refl,
      rw smul_mk at this, exact this
    end⟩⟩⟩ := rfl

lemma smul_to_simple_func (k : K) (f : α →ₛ β) :
  ∀ₘ a, (k • f).to_simple_func a = k • f.to_simple_func a :=
begin
  filter_upwards [to_simple_func_to_fun (k • f), to_simple_func_to_fun f, l1.smul_to_fun k f.1],
  assume a, simp only [mem_set_of_eq],
  repeat { assume h, rw h },
  assume h, rw ← h,
  refl
end

instance : module K (α →ₛ β) :=
{ one_smul :=
    by { rintros ⟨f, hf⟩, simp only [smul_def, subtype.mk_eq_mk], exact one_smul _ _ },
  mul_smul :=
    by { rintros x y ⟨f, hf⟩, simp only [smul_def, subtype.mk_eq_mk], exact mul_smul _ _ _ },
  smul_add :=
    by { rintros k ⟨f, _⟩ ⟨g, _⟩, simp only [smul_def, add_def, subtype.mk_eq_mk],
         exact smul_add _ _ _ },
  smul_zero := by { intro k, simp only [zero_def, smul_def, subtype.mk_eq_mk], exact smul_zero _ },
  add_smul :=
    by { rintros x y ⟨f, _⟩, simp only [smul_def, add_def, subtype.mk_eq_mk], exact add_smul _ _ _ },
  zero_smul :=
    by { rintros ⟨f, _⟩, simp only [smul_def, zero_def, subtype.mk_eq_mk], exact zero_smul _ _ } }

instance : vector_space K (α →ₛ β) := { .. simple_func.module }

instance : has_coe (α →ₛ β) (α →₁ β) := ⟨subtype.val⟩

instance : metric_space (α →ₛ β) :=
metric_space.induced (coe : (α →ₛ β) → (α →₁ β)) subtype.val_injective l1.metric_space

lemma dist_def (f g : α →ₛ β) : dist f g = dist f.1 g.1 := rfl

lemma lintegral_edist_to_simple_func_lt_top (f g : α →ₛ β) :
  (∫⁻ (x : α), edist ((to_simple_func f) x) ((to_simple_func g) x)) < ⊤ :=
begin
  rw lintegral_rw₂ (to_simple_func_to_fun f) (to_simple_func_to_fun g),
  exact lintegral_edist_to_fun_lt_top _ _
end

lemma dist_to_simple_func (f g : α →ₛ β) : dist f g =
  ennreal.to_real (∫⁻ x, edist (f.to_simple_func x) (g.to_simple_func x)) :=
begin
  rw [dist_def, l1.dist_to_fun, ennreal.to_real_eq_to_real],
  { rw lintegral_rw₂, repeat { exact all_ae_eq_symm (to_simple_func_to_fun _) } },
  { exact l1.lintegral_edist_to_fun_lt_top _ _ },
  { exact lintegral_edist_to_simple_func_lt_top _ _ }
end

/-- The norm of a simple function is the norm of its underlying l1 function. -/
instance : has_norm (α →ₛ β) := ⟨λf, ∥f.1∥⟩

lemma norm_def (f : α →ₛ β) : ∥f∥ = ∥f.1∥ := rfl

instance : normed_group (α →ₛ β) :=
{ dist_eq :=
    begin
      rintros ⟨f, hf⟩ ⟨g, hg⟩,
      simp only [dist_def, norm_def, sub_eq_add_neg, neg_def, add_def, normed_group.dist_eq]
    end }

lemma norm_to_simple_func (f : α →ₛ β) :
  ∥f∥ = ennreal.to_real (∫⁻ (a : α), nnnorm ((to_simple_func f) a)) :=
calc ∥f∥ = _ :
    begin
      rw [← dist_zero_right, dist_to_simple_func],
    end
  ... = ennreal.to_real (∫⁻ (x : α), (coe ∘ nnnorm) ((to_simple_func f) x)) :
    begin
      rw lintegral_nnnorm_eq_lintegral_edist,
      have : (∫⁻ (x : α), edist ((to_simple_func f) x) ((to_simple_func (0:α→ₛβ)) x)) =
               ∫⁻ (x : α), edist ((to_simple_func f) x) 0,
      { apply lintegral_congr_ae, filter_upwards [zero_to_simple_func α β],
        assume a, simp only [mem_set_of_eq],
        assume h, rw h },
      rw [ennreal.to_real_eq_to_real],
      { exact this },
      { exact lintegral_edist_to_simple_func_lt_top _ _ },
      { rw ← this, exact lintegral_edist_to_simple_func_lt_top _ _ }
    end

lemma norm_eq_bintegral (f : α →ₛ β) : ∥f∥ = (f.to_simple_func.map norm).bintegral :=
calc ∥f∥ = ennreal.to_real (∫⁻ (x : α), (coe ∘ nnnorm) (f.to_simple_func x)) :
    by { rw norm_to_simple_func }
  ... = (f.to_simple_func.map norm).bintegral :
    begin
      rw ← f.to_simple_func.bintegral_eq_lintegral (coe ∘ nnnorm) f.integrable,
      { congr },
      { simp only [nnnorm_zero, function.comp_app, ennreal.coe_zero] },
      { assume b, exact coe_lt_top }
    end

instance : normed_space K (α →ₛ β) :=
{ norm_smul := by { rintros k ⟨f, _⟩, simp only [norm_def, smul_def], exact norm_smul _ _ } }

end instances

section coe_to_l1

lemma exists_simple_func_near (f : α →₁ β) {ε : ℝ} (ε0 : 0 < ε) :
  ∃ s : α →ₛ β, dist f s < ε :=
begin
  rcases f with ⟨⟨f, hfm⟩, hfi⟩,
  simp only [integrable_mk, quot_mk_eq_mk] at hfi,
  rcases simple_func_sequence_tendsto' hfm hfi with ⟨F, ⟨h₁, h₂⟩⟩,
  rw ennreal.tendsto_at_top at h₂,
  rcases h₂ (ennreal.of_real (ε/2)) (of_real_pos.2 $ half_pos ε0) with ⟨N, hN⟩,
  have : (∫⁻ (x : α), nndist (F N x) (f x)) < ennreal.of_real ε :=
  calc
    (∫⁻ (x : α), nndist (F N x) (f x)) ≤ 0 + ennreal.of_real (ε/2) : (hN N (le_refl _)).2
    ... < ennreal.of_real ε :
      by { simp only [zero_add, of_real_lt_of_real_iff ε0], exact half_lt_self ε0 },
  { refine ⟨mk (F N) (h₁ N), _⟩, rw dist_comm,
    rw lt_of_real_iff_to_real_lt _ at this,
    { simpa [edist_mk_mk', mk, l1.mk, l1.dist_def] },
    rw ← lt_top_iff_ne_top, exact lt_trans this (by simp [lt_top_iff_ne_top, of_real_ne_top]) },
  { exact zero_ne_top }
end

protected lemma uniform_continuous : uniform_continuous (coe : (α →ₛ β) → (α →₁ β)) :=
uniform_continuous_comap

protected lemma uniform_embedding : uniform_embedding (coe : (α →ₛ β) → (α →₁ β)) :=
uniform_embedding_comap subtype.val_injective

protected lemma uniform_inducing : uniform_inducing (coe : (α →ₛ β) → (α →₁ β)) :=
l1.simple_func.uniform_embedding.to_uniform_inducing

protected lemma dense_embedding : dense_embedding (coe : (α →ₛ β) → (α →₁ β)) :=
l1.simple_func.uniform_embedding.dense_embedding $
λ f, mem_closure_iff_nhds.2 $ λ t ht,
let ⟨ε,ε0, hε⟩ := metric.mem_nhds_iff.1 ht in
let ⟨s, h⟩ := exists_simple_func_near f ε0 in
ne_empty_iff_exists_mem.2 ⟨_, hε (metric.mem_ball'.2 h), s, rfl⟩

protected lemma dense_inducing : dense_inducing (coe : (α →ₛ β) → (α →₁ β)) :=
l1.simple_func.dense_embedding.to_dense_inducing

protected lemma closure_range : closure (range (coe : (α →ₛ β) → (α →₁ β))) = univ :=
l1.simple_func.dense_embedding.to_dense_inducing.closure_range

variables (K : Type*) [normed_field K] [second_countable_topology K] [normed_space K β]

variables (α β)

def coe_to_l1 : (α →ₛ β) →L[K] (α →₁ β) :=
{ to_fun := (coe : (α →ₛ β) → (α →₁ β)),
  add := λf g, rfl,
  smul := λk f, rfl,
  cont := l1.simple_func.uniform_continuous.continuous, }

variables {α β K}

end coe_to_l1

section simple_func_integral

variables [normed_space ℝ β]

/-- Bochner integration over simple functions in l1 space. -/
def integral (f : α →ₛ β) : β := simple_func.bintegral (f.to_simple_func)

lemma integral_eq_lintegral {f : α →ₛ ℝ} (h_pos : ∀ₘ a, 0 ≤ f.to_simple_func a) :
  integral f = ennreal.to_real (∫⁻ a, ennreal.of_real (f.to_simple_func a)) :=
by { rw [integral, simple_func.bintegral_eq_lintegral' f.integrable h_pos], refl }

lemma integral_congr (f g : α →ₛ β) (h : ∀ₘ a, f.to_simple_func a = g.to_simple_func a) :
  integral f = integral g :=
begin
  rw [← mk_eq_mk' f g f.integrable g.integrable] at h,
  simp only [mk_to_simple_func] at h,
  rw h
end

lemma integral_add (f g : α →ₛ β) : integral (f + g) = integral f + integral g :=
begin
  simp only [integral],
  rw ← simple_func.bintegral_add f.integrable g.integrable,
  apply simple_func.bintegral_congr (f + g).integrable,
    { exact integrable_add f.measurable g.measurable f.integrable g.integrable },
    { apply add_to_simple_func },
end

lemma integral_smul (r : ℝ) (f : α →ₛ β) : integral (r • f) = r • integral f :=
begin
  simp only [integral],
  rw ← simple_func.bintegral_smul _ f.integrable,
  apply simple_func.bintegral_congr (r • f).integrable,
    { exact integrable_smul f.integrable },
    { apply smul_to_simple_func }
end

instance : is_add_group_hom (integral : (α →ₛ β) → β) := { map_add := integral_add }

lemma tendsto_integral : tendsto (integral : (α →ₛ β) → β) (nhds 0) (nhds 0) :=
begin
  have := @metric.tendsto_nhds_nhds (α →ₛ β) β _ _ integral 0 0,
  rw this,
  assume ε ε0,
  use ε, use ε0,
  assume f,
  rw [dist_zero_right, norm_eq_bintegral, dist_zero_right, integral],
  assume hf,
  exact lt_of_le_of_lt (f.to_simple_func.norm_bintegral_le_bintegral_norm f.integrable) hf
end

lemma uniform_continuous_integral : uniform_continuous (integral : (α →ₛ β) → β) :=
uniform_continuous_of_tendsto_zero tendsto_integral

/-- Bochner integration over simple functions in l1 space as a continuous linear map. -/
def integral_clm : (α →ₛ β) →L[ℝ] β :=
{ to_fun := integral,
  add := integral_add,
  smul := integral_smul,
  cont := uniform_continuous_integral.continuous }

local notation `Integral` := @integral_clm α _ β _ _ _

lemma norm_integral_le_norm (f : α →ₛ β) : ∥ integral f ∥ ≤ ∥f∥ :=
begin
  rw [integral, norm_eq_bintegral],
  exact f.to_simple_func.norm_bintegral_le_bintegral_norm f.integrable
end

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

end l1

end measure_theory
