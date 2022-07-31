/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/

import topology.basic
import topology.algebra.module.continuous_linear_pmap

/-!
# Continuous Linear Pmap

## Main definitions

* `continuous_linear_pmap.extend_to_closure`: construct an extention of `f : E →L.[𝕜] F` to the
  closure of `f.domain`.

## Main statements

* `continuous_linear_pmap.exists_unique_extend_to_closure`: there is a unique extension to the
  topological closure of the domain

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open_locale topological_space

variables {E F 𝕜: Type*}

variables [is_R_or_C 𝕜] [normed_group E] [normed_space 𝕜 E] [normed_group F] [normed_space 𝕜 F]

def linear_pmap.mk_continuous {f : linear_pmap 𝕜 E F} (C : ℝ) (h : ∀ (x : f.domain), ∥f x∥ ≤ C * ∥x∥) :
  E →L.[𝕜] F :=
⟨f, (f.to_fun.mk_continuous C h).2⟩

lemma mem_topological_closure_iff_mem_closure {x : E} {S : submodule 𝕜 E} :
  x ∈ S.topological_closure ↔ x ∈ closure (S : set E) :=
by rw [←set_like.mem_coe, submodule.topological_closure_coe]
.
lemma mem_topological_closure_iff_seq_limit {x : E} {S : submodule 𝕜 E} : x ∈ S.topological_closure ↔
  ∃ a : ℕ → E, (∀ n : ℕ, a n ∈ S) ∧ filter.tendsto a filter.at_top (𝓝 x) :=
begin
  simp_rw [mem_topological_closure_iff_mem_closure, ←set_like.mem_coe],
  exact mem_closure_iff_seq_limit,
end

lemma topological_closure_seq_limit {S : submodule 𝕜 E} (x : S.topological_closure) :
  ∃ a : ℕ → E, (∀ n : ℕ, a n ∈ S) ∧ filter.tendsto a filter.at_top (𝓝 x) :=
begin
  cases x with x hx,
  exact mem_topological_closure_iff_seq_limit.mp hx,
end

/-- blubb -/
lemma cauchy_seq_iff {α α' : Type*} [pseudo_metric_space α] {s : ℕ → α} [pseudo_metric_space α'] {s' : ℕ → α'}
  (hs : ∀ n m, dist (s n) (s m) = dist (s' n) (s' m)) : cauchy_seq s ↔ cauchy_seq s' :=
by simp_rw [cauchy_seq_iff_le_tendsto_0, hs]

lemma cauchy_seq_submodule {S : submodule 𝕜 E} {a : ℕ → E} {a' : ℕ → S} (ha_dom : ∀ n : ℕ, a n = a' n) :
  cauchy_seq a ↔ cauchy_seq a' :=
begin
  refine cauchy_seq_iff _,
  intros a m,
  simp_rw [ha_dom, dist_eq_norm, submodule.coe_norm, add_subgroup_class.coe_sub],
end

namespace continuous_linear_pmap
/-- The image of a cauchy sequence is again a cauchy sequence. -/
lemma cauchy_seq_image {a : ℕ → E} {a' : ℕ → f.domain} (ha_dom : ∀ n : ℕ, a n = a' n) (ha : cauchy_seq a) :
  cauchy_seq (f ∘ a') :=
f.to_cont_fun.uniform_continuous.comp_cauchy_seq ((cauchy_seq_submodule ha_dom).mp ha)

lemma exists_unique_image (f : E →L.[𝕜] F) (x : f.domain.topological_closure) :
  ∃! y : F, ∀ (a : ℕ → E) (a' : ℕ → f.domain) (ha_dom : ∀ n : ℕ, a n = a' n)
  (ha : filter.tendsto a filter.at_top (𝓝 x)),
  filter.tendsto (f ∘ a') filter.at_top (𝓝 y) :=
begin
  cases x with x hx,
  simp only [submodule.coe_mk],
  rw mem_topological_closure_iff_seq_limit at hx,
  rcases hx with ⟨a, ha, hx⟩,
  let a' : ℕ → f.domain := λ n, ⟨a n, ha n⟩,
  have ha_dom : ∀ n : ℕ, a n = a' n := λ (n : ℕ), eq.refl (a n),
  refine exists_unique_of_exists_of_unique _ _,
  { -- Existence:
    -- Show that f ∘ a' is Cauchy
    have ha' : cauchy_seq (f ∘ a') := cauchy_seq_image f ha_dom hx.cauchy_seq,
    cases cauchy_seq_tendsto_of_complete ha' with y hy,
    -- Use limit of a'
    use y,
    intros b b' hb hb',
    rw ←add_zero y,
    have hab := filter.tendsto.sub hb' hx,
    rw sub_self at hab,
    have : filter.tendsto (λ n, f (b' n) - f (a' n)) filter.at_top (𝓝 0) :=
    begin
      simp_rw ←continuous_linear_pmap.map_sub,
      refine continuous_linear_pmap.tendsto_zero _ hab,
      simp [hb],
    end,
    convert filter.tendsto.add hy this,
    simp },
  -- Uniqueness
  intros y1 y2 hy1 hy2,
  specialize hy1 a a' (λ _, by rw submodule.coe_mk) hx,
  specialize hy2 a a' (λ _, by rw submodule.coe_mk) hx,
  exact tendsto_nhds_unique hy1 hy2,
end

noncomputable
def image_closure (f : E →L.[𝕜] F) (x : f.domain.topological_closure) : F :=
(exists_of_exists_unique (f.exists_unique_image x)).some

lemma image_closure_spec (f : E →L.[𝕜] F) {x : f.domain.topological_closure}
  {a : ℕ → E} {a' : ℕ → f.domain} (ha_dom : ∀ n : ℕ, a n = a' n) (ha : filter.tendsto a filter.at_top (𝓝 x)) :
  filter.tendsto (f ∘ a') filter.at_top (𝓝 (f.image_closure x)) :=
(exists_of_exists_unique (f.exists_unique_image x)).some_spec a a' ha_dom ha

@[simp] lemma image_closure_apply_domain (f : E →L.[𝕜] F)
  {x : f.domain.topological_closure} {x' : f.domain} (hx : (x : E) = x') : f.image_closure x = f x' :=
begin
  refine (f.exists_unique_image x).unique (λ _ _, f.image_closure_spec) _,
  intros ax ax' hax_dom,
  exact f.tendsto hax_dom hx,
end

lemma image_closure_add (f : E →L.[𝕜] F) (x y : f.domain.topological_closure) :
  f.image_closure (x + y) = f.image_closure x + f.image_closure y :=
begin
  refine (f.exists_unique_image (x + y)).unique (λ _ _, f.image_closure_spec) _,
  intros axy axy' haxy_dom haxy_lim,
  rcases topological_closure_seq_limit x with ⟨ax, hax_dom, hax_lim⟩,
  let ax' : ℕ → f.domain := λ n, ⟨ax n, hax_dom n⟩,
  have hax' : ∀ n, ax n = ax' n := λ _, rfl,
  have hfax_lim := f.image_closure_spec hax' hax_lim,
  let ay : ℕ → E := λ n, axy n - ax n,
  let ay' : ℕ → f.domain := λ n, ⟨axy n - ax n,
    f.domain.sub_mem (by simp_rw [haxy_dom n, submodule.coe_mem]) (hax_dom n)⟩,
  have hay' : ∀ n, ay n = ay' n := λ _, rfl,
  have hfay_lim : filter.tendsto (f ∘ ay') filter.at_top (𝓝 (f.image_closure y)) :=
  begin
    refine f.image_closure_spec hay' _,
    convert haxy_lim.sub hax_lim,
    simp,
  end,
  convert hfax_lim.add hfay_lim,
  ext n,
  simp_rw [function.comp_app, ←f.map_add (ax' n) (ay' n)],
  congr,
  simp [haxy_dom n],
end

lemma image_closure_smul (f : E →L.[𝕜] F) (r : 𝕜) (x : f.domain.topological_closure) :
  f.image_closure (r • x) = r • f.image_closure x :=
begin
  refine (f.exists_unique_image (r • x)).unique (λ _ _, f.image_closure_spec) _,
  intros arx arx' harx_dom harx_lim,
  by_cases hr : r = 0,
  { simp only [hr, zero_smul] at ⊢ harx_lim,
    exact continuous_linear_pmap.tendsto_zero harx_dom harx_lim },
  let ax : ℕ → E := λ n, r⁻¹ • arx n,
  let ax' : ℕ → f.domain := λ n, ⟨r⁻¹ • arx n, f.domain.smul_mem _ (by simp_rw [harx_dom n, submodule.coe_mem])⟩,
  have hay' : ∀ n, ax n = ax' n := λ _, rfl,
  have hfax_lim : filter.tendsto (f ∘ ax') filter.at_top (𝓝 (f.image_closure x)) :=
  begin
    refine f.image_closure_spec hay' _,
    convert harx_lim.const_smul r⁻¹,
    simp [hr],
  end,
  convert hfax_lim.const_smul r,
  ext n,
  simp_rw [function.comp_app, ←f.map_smul],
  congr,
  ext,
  simp [←harx_dom n, hr],
end

noncomputable
def extend_to_closure_aux (f : E →L.[𝕜] F) : linear_pmap 𝕜 E F :=
{ domain := f.domain.topological_closure,
  to_fun := { to_fun := f.image_closure,
    map_add' := f.image_closure_add,
    map_smul' := f.image_closure_smul} }

lemma extend_to_closure_aux_domain (f : E →L.[𝕜] F) :
  f.extend_to_closure_aux.domain = f.domain.topological_closure := rfl

lemma extend_to_closure_aux_bound (f : E →L.[𝕜] F)
  (x : f.extend_to_closure_aux.domain) : ∥f.extend_to_closure_aux x∥ ≤ ∥f.to_cont_fun∥ * ∥x∥ :=
begin
  rcases topological_closure_seq_limit x with ⟨ax, hax_dom, hax_lim⟩,
  let ax' : ℕ → f.domain := λ n, ⟨ax n, hax_dom n⟩,
  have hax' : ∀ n, ax n = ax' n := λ _, rfl,
  have hfax_lim := f.image_closure_spec hax' hax_lim,
  have hax_lim_norm := hax_lim.norm,
  rw ←submodule.coe_norm at hax_lim_norm,
  refine le_of_tendsto_of_tendsto' hfax_lim.norm (hax_lim_norm.const_mul (∥f.to_cont_fun∥)) _,
  intro n,
  simp only [function.comp_app],
  rw [hax' n, ←submodule.coe_norm],
  exact f.to_cont_fun.le_op_norm _,
end

noncomputable
def extend_to_closure (f : E →L.[𝕜] F) : E →L.[𝕜] F :=
linear_pmap.mk_continuous ∥f.to_cont_fun∥ f.extend_to_closure_aux_bound

lemma extend_to_closure_domain (f : E →L.[𝕜] F) :
  f.extend_to_closure.domain = f.domain.topological_closure := rfl

lemma extend_to_closure_extension (f : E →L.[𝕜] F) :
  f ≤ (extend_to_closure f) :=
begin
  rw le_iff,
  refine ⟨f.domain.submodule_topological_closure, _⟩,
  intros _ _ hxy,
  exact (f.image_closure_apply_domain hxy.symm).symm,
end

lemma extend_to_closure_norm (f : E →L.[𝕜] F) :
  ∥f.extend_to_closure.to_cont_fun∥ = ∥f.to_cont_fun∥ :=
begin
  refine has_le.le.antisymm _ _,
  { -- Show that ∥f.extend_to_closure∥ ≤ ∥f∥ by using `f.extend_to_closure_aux_bound`
    exact @continuous_linear_map.op_norm_le_bound _ _ (f.extend_to_closure.domain) _ _ _ _ _ _ _ _
      f.extend_to_closure.to_cont_fun _ (norm_nonneg _) f.extend_to_closure_aux_bound },
  -- Show that ∥f∥ ≤ ∥f.extend_to_closure∥
  refine f.to_cont_fun.op_norm_le_bound (norm_nonneg _) _,
  intros x,
  let y : f.extend_to_closure.domain := ⟨x.1, f.extend_to_closure_extension.1 x.2⟩,
  have hx : (y : E) = x := rfl,
  rw [f.to_cont_fun_apply, ←f.image_closure_apply_domain hx],
  rw [submodule.coe_norm, ←hx, ←submodule.coe_norm],
  refine @continuous_linear_map.le_op_norm _ _ (f.extend_to_closure.domain) _ _ _ _ _ _ _ _ _
    f.extend_to_closure.to_cont_fun y,
end

lemma exists_unique_extend_to_closure (f : E →L.[𝕜] F) : ∃! f' : E →L.[𝕜] F,
  f'.domain = f.domain.topological_closure ∧
  f.to_linear_pmap ≤ f'.to_linear_pmap :=
begin
  refine exists_unique_of_exists_of_unique _ _,
  { use f.extend_to_closure,
    exact ⟨f.extend_to_closure_domain, f.extend_to_closure_extension⟩ },
  -- Uniqueness
  intros f1 f2 hf1 hf2,
  refine continuous_linear_pmap.ext (by rw [hf1.1, hf2.1]) _,
  intros x1 x2 hx,
  let z : E := x1,
  have hz : z ∈ f.domain.topological_closure :=
  by simp only [←hf1.1, submodule.coe_mem],
  rcases topological_closure_seq_limit ⟨z, hz⟩ with ⟨az, haz_dom, haz_lim⟩,
  simp only [submodule.coe_mk] at haz_lim,
  let aw : ℕ → f.domain := λ n, ⟨az n, haz_dom n⟩,
  let ax1 : ℕ → f1.domain := λ n, ⟨az n, hf1.2.1 (haz_dom n)⟩,
  let ax2 : ℕ → f2.domain := λ n, ⟨az n, hf2.2.1 (haz_dom n)⟩,
  have hfax1 : f ∘ aw = f1 ∘ ax1 := funext (λ _, hf1.right.right rfl),
  have hfax2 : f ∘ aw = f2 ∘ ax2 := funext (λ _, hf2.right.right rfl),
  have hfaz1 : filter.tendsto (f ∘ aw) filter.at_top (𝓝 (f1 x1)) :=
  begin
    rw hfax1,
    exact f1.tendsto (λ _, rfl) rfl haz_lim,
  end,
  have hfaz2 : filter.tendsto (f ∘ aw) filter.at_top (𝓝 (f2 x2)) :=
  begin
    rw hfax2,
    refine f2.tendsto (λ _, rfl) rfl _,
    simp_rw [submodule.coe_mk, ←hx],
    exact haz_lim,
  end,
  exact tendsto_nhds_unique hfaz1 hfaz2,
end

end continuous_linear_pmap
