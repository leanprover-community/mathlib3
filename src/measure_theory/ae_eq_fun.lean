/-
Copyright (c) 2019 Johannes Hölzl, Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Zhouhang Zhou
-/
import measure_theory.integration
import order.filter.germ

/-!

# Almost everywhere equal functions

Two measurable functions are treated as identical if they are almost everywhere equal. We form the
set of equivalence classes under the relation of being almost everywhere equal, which is sometimes
known as the `L⁰` space.

See `l1_space.lean` for `L¹` space.

## Notation

* `α →ₘ[μ] β` is the type of `L⁰` space, where `α` and `β` are measurable spaces and `μ`
  is a measure on `α`. `f : α →ₘ β` is a "function" in `L⁰`. In comments, `[f]` is also used
  to denote an `L⁰` function.

  `ₘ` can be typed as `\_m`. Sometimes it is shown as a box if font is missing.


## Main statements

* The linear structure of `L⁰` :
    Addition and scalar multiplication are defined on `L⁰` in the natural way, i.e.,
    `[f] + [g] := [f + g]`, `c • [f] := [c • f]`. So defined, `α →ₘ β` inherits the linear structure
    of `β`. For example, if `β` is a module, then `α →ₘ β` is a module over the same ring.

    See `mk_add_mk`,  `neg_mk`,     `mk_sub_mk`,  `smul_mk`,
        `add_to_fun`, `neg_to_fun`, `sub_to_fun`, `smul_to_fun`

* The order structure of `L⁰` :
    `≤` can be defined in a similar way: `[f] ≤ [g]` if `f a ≤ g a` for almost all `a` in domain.
    And `α →ₘ β` inherits the preorder and partial order of `β`.

    TODO: Define `sup` and `inf` on `L⁰` so that it forms a lattice. It seems that `β` must be a
    linear order, since otherwise `f ⊔ g` may not be a measurable function.

* Emetric on `L⁰` :
    If `β` is an `emetric_space`, then `L⁰` can be made into an `emetric_space`, where
    `edist [f] [g]` is defined to be `∫⁻ a, edist (f a) (g a)`.

    The integral used here is `lintegral : (α → ennreal) → ennreal`, which is defined in the file
    `integration.lean`.

    See `edist_mk_mk` and `edist_to_fun`.

## Implementation notes

* `f.to_fun`     : To find a representative of `f : α →ₘ β`, use `f.to_fun`.
                 For each operation `op` in `L⁰`, there is a lemma called `op_to_fun`,
                 characterizing, say, `(f op g).to_fun`.
* `ae_eq_fun.mk` : To constructs an `L⁰` function `α →ₘ β` from a measurable function `f : α → β`,
                 use `ae_eq_fun.mk`
* `comp`         : Use `comp g f` to get `[g ∘ f]` from `g : β → γ` and `[f] : α →ₘ γ`
* `comp₂`        : Use `comp₂ g f₁ f₂ to get `[λa, g (f₁ a) (f₂ a)]`.
                 For example, `[f + g]` is `comp₂ (+)`


## Tags

function space, almost everywhere equal, `L⁰`, ae_eq_fun

-/

noncomputable theory
open_locale classical

open set filter topological_space ennreal emetric measure_theory function
variables {α β γ δ : Type*} [measurable_space α] {μ ν : measure α}


namespace function

lemma preimage_inv_fun_of_mem [n : nonempty α] {f : α → β} (hf : injective f) {s : set α}
  (h : classical.choice n ∈ s) : inv_fun f ⁻¹' s = f '' s ∪ (f '' univ)ᶜ :=
begin
  apply subset.antisymm,
  { assume x hx,
    by_cases H : ∃ a, f a = x,
    { simp only [inv_fun, inv_fun_on, H, true_and, dif_pos, mem_univ, mem_preimage] at hx,
      left,
      simp only [mem_image],
      exact ⟨_, hx, classical.some_spec H⟩ },
    { push_neg at H,
      simp [H] } },
  { assume x hx,
    cases hx,
    { rcases hx with ⟨y, ys, fy⟩,
      simp only [←fy, left_inverse_inv_fun hf y, ys, mem_preimage] },
    { have : ¬ (∃ a, f a = x), by simpa using hx,
      simp only [inv_fun, inv_fun_on, this, h, true_and, mem_univ, mem_preimage, dif_neg,
        not_false_iff] } }
end

lemma preimage_inv_fun_of_not_mem [n : nonempty α] {f : α → β} (hf : injective f)
  {s : set α} (h : classical.choice n ∉ s) : inv_fun f ⁻¹' s = f '' s :=
begin
  apply subset.antisymm,
  { assume x hx,
    by_cases H : ∃ a, f a = x,
    { simp only [inv_fun, inv_fun_on, H, true_and, dif_pos, mem_univ, mem_preimage] at hx,
      simp only [mem_image],
      exact ⟨_, hx, classical.some_spec H⟩ },
    { simp [inv_fun, inv_fun_on, H] at hx,
      exact false.elim (h hx) } },
  { assume x hx,
    rcases hx with ⟨y, ys, fy⟩,
    simp only [←fy, left_inverse_inv_fun hf y, ys, mem_preimage] },
end


end function

section ae_measurable

variables [measurable_space β] {f g : α → β}

/-- A function is almost everywhere measurable if there exists a measurable function which
coincides with it almost everywhere. -/
def ae_measurable (f : α → β) (μ : measure α . volume_tac) : Prop :=
∃ g : α → β, measurable g ∧ f =ᵐ[μ] g

/-- Given an almost everywhere measurable function `f`, associate to it a measurable function
which coincides with it almost everywhere. -/
def ae_measurable.mk (f : α → β) (h : ae_measurable f μ) : α → β := classical.some h

lemma ae_measurable.measurable_mk (h : ae_measurable f μ) : measurable (h.mk f) :=
(classical.some_spec h).1

lemma ae_measurable.ae_eq_mk (h : ae_measurable f μ) : f =ᵐ[μ] (h.mk f) :=
(classical.some_spec h).2

lemma measurable.ae_measurable (h : measurable f) :
  ae_measurable f μ :=
⟨f, h, ae_eq_refl f⟩

lemma ae_measurable.congr (hf : ae_measurable f μ) (h : f =ᵐ[μ] g) : ae_measurable g μ :=
⟨hf.mk f, hf.measurable_mk, h.symm.trans hf.ae_eq_mk⟩

lemma ae_measurable_congr (h : f =ᵐ[μ] g) :
  ae_measurable f μ ↔ ae_measurable g μ :=
⟨λ hf, ae_measurable.congr hf h, λ hg, ae_measurable.congr hg h.symm⟩

lemma ae_measurable.mono_measure (h : ae_measurable f μ) (h' : ν ≤ μ) : ae_measurable f ν :=
begin
  exact ⟨h.mk f, h.measurable_mk, eventually.filter_mono (ae_mono h') h.ae_eq_mk⟩
end

lemma ae_measurable.add_measure {f : α → β} (hμ : ae_measurable f μ) (hν : ae_measurable f ν) :
  ae_measurable f (μ + ν) :=
begin
  let s := {x | f x ≠ hμ.mk f x},
  have : μ s = 0 := hμ.ae_eq_mk,
  obtain ⟨t, st, t_meas, μt⟩ : ∃ t, s ⊆ t ∧ is_measurable t ∧ μ t = 0 :=
    exists_is_measurable_superset_of_measure_eq_zero this,
  let g : α → β := t.piecewise (hν.mk f) (hμ.mk f),
  refine ⟨g, measurable.piecewise t_meas hν.measurable_mk hμ.measurable_mk, _⟩,
  change μ {x | f x ≠ g x} + ν {x | f x ≠ g x} = 0,
  suffices : μ {x | f x ≠ g x} = 0 ∧ ν {x | f x ≠ g x} = 0, by simp [this.1, this.2],
  have ht : {x | f x ≠ g x} ⊆ t,
  { assume x hx,
    by_contra h,
    simp only [g, h, mem_set_of_eq, ne.def, not_false_iff, piecewise_eq_of_not_mem] at hx,
    exact h (st hx) },
  split,
  { have : μ {x | f x ≠ g x} ≤ μ t := measure_mono ht,
    rw μt at this,
    exact le_antisymm this bot_le },
  { have : {x | f x ≠ g x} ⊆ {x | f x ≠ hν.mk f x},
    { assume x hx,
      simpa [ht hx, g] using hx },
    apply le_antisymm _ bot_le,
    calc ν {x | f x ≠ g x} ≤ ν {x | f x ≠ hν.mk f x} : measure_mono this
    ... = 0 : hν.ae_eq_mk }
end

@[simp] lemma ae_measurable_add_measure_iff :
  ae_measurable f (μ + ν) ↔ ae_measurable f μ ∧ ae_measurable f ν :=
⟨λ h, ⟨h.mono_measure (measure.le_add_right (le_refl _)),
         h.mono_measure (measure.le_add_left (le_refl _))⟩,
  λ h, h.1.add_measure h.2⟩

lemma ae_measurable.smul_measure (h : ae_measurable f μ) (c : ennreal) :
  ae_measurable f (c • μ) :=
begin
  exact ⟨h.mk f, h.measurable_mk, ae_smul_measure h.ae_eq_mk c⟩
end

lemma ae_eq_comp {f : α → β} {g g' : β → δ} (hf : measurable f)
  (h : g =ᵐ[measure.map f μ] g') : g ∘ f =ᵐ[μ] g' ∘ f :=
begin
  rcases exists_is_measurable_superset_of_measure_eq_zero h with ⟨t, ht, tmeas, tzero⟩,
  refine le_antisymm _ bot_le,
  calc μ {x | g (f x) ≠ g' (f x)} ≤ μ (f⁻¹' t) : measure_mono (λ x hx, ht hx)
  ... = 0 : by rwa ← measure.map_apply hf tmeas
end

lemma ae_measurable.comp_measurable [measurable_space δ] {f : α → δ} {g : δ → β}
  (hg : ae_measurable g (measure.map f μ)) (hf : measurable f) : ae_measurable (g ∘ f) μ :=
⟨(hg.mk g) ∘ f, hg.measurable_mk.comp hf, ae_eq_comp hf hg.ae_eq_mk⟩

lemma measurable.comp_ae_measurable [measurable_space δ] {f : α → δ} {g : δ → β}
  (hg : measurable g) (hf : ae_measurable f μ) : ae_measurable (g ∘ f) μ :=
⟨g ∘ hf.mk f, hg.comp hf.measurable_mk, eventually_eq.fun_comp hf.ae_eq_mk _⟩

lemma lintegral_map' {f : β → ennreal} {g : α → β}
  (hf : ae_measurable f (measure.map g μ)) (hg : measurable g) :
  ∫⁻ a, f a ∂(measure.map g μ) = ∫⁻ a, f (g a) ∂μ :=
calc ∫⁻ a, f a ∂(measure.map g μ) = ∫⁻ a, hf.mk f a ∂(measure.map g μ) :
  lintegral_congr_ae hf.ae_eq_mk
... = ∫⁻ a, hf.mk f (g a) ∂μ : lintegral_map hf.measurable_mk hg
... = ∫⁻ a, f (g a) ∂μ : lintegral_congr_ae (ae_eq_comp hg hf.ae_eq_mk.symm)

lemma lintegral_add' {f g : α → ennreal} (hf : ae_measurable f μ) (hg : ae_measurable g μ) :
  (∫⁻ a, f a + g a ∂μ) = (∫⁻ a, f a ∂μ) + (∫⁻ a, g a ∂μ) :=
calc (∫⁻ a, f a + g a ∂μ) = (∫⁻ a, hf.mk f a + hg.mk g a ∂μ) :
  lintegral_congr_ae (eventually_eq.add hf.ae_eq_mk hg.ae_eq_mk)
... = (∫⁻ a, hf.mk f a ∂μ) + (∫⁻ a, hg.mk g a ∂μ) : lintegral_add hf.measurable_mk hg.measurable_mk
... = (∫⁻ a, f a ∂μ) + (∫⁻ a, g a ∂μ) : begin
  congr' 1,
  { exact lintegral_congr_ae hf.ae_eq_mk.symm },
  { exact lintegral_congr_ae hg.ae_eq_mk.symm },
end

@[simp] lemma lintegral_eq_zero_iff' {f : α → ennreal} (hf : ae_measurable f μ) :
  ∫⁻ a, f a ∂μ = 0 ↔ (f =ᵐ[μ] 0) :=
begin
  have : ∫⁻ a, f a ∂μ = ∫⁻ a, hf.mk f a ∂μ := lintegral_congr_ae hf.ae_eq_mk,
  rw [this, lintegral_eq_zero_iff hf.measurable_mk],
  exact ⟨λ H, hf.ae_eq_mk.trans H, λ H, hf.ae_eq_mk.symm.trans H⟩
end

lemma ae_measurable.norm [normed_group β] [opens_measurable_space β] (hf : ae_measurable f μ) :
  ae_measurable (λ a, norm (f a)) μ :=
⟨λ a, norm (hf.mk f a), hf.measurable_mk.norm, hf.ae_eq_mk.fun_comp _⟩

lemma ae_measurable.ennnorm [normed_group β] [opens_measurable_space β] (hf : ae_measurable f μ) :
  ae_measurable (λ a, (nnnorm (f a) : ennreal)) μ :=
⟨(λ a, (nnnorm (hf.mk f a) : ennreal)), hf.measurable_mk.ennnorm,
  hf.ae_eq_mk.fun_comp (λ a : β, (nnnorm a : ennreal))⟩

lemma ae_measurable.edist [emetric_space β] [second_countable_topology β] [opens_measurable_space β]
  (hf : ae_measurable f μ) (hg : ae_measurable g μ) : ae_measurable (λ a, edist (f a) (g a)) μ :=
⟨λ a, edist (hf.mk f a) (hg.mk g a), hf.measurable_mk.edist hg.measurable_mk,
  eventually_eq.comp₂ hf.ae_eq_mk _ hg.ae_eq_mk⟩

lemma ae_measurable.prod_mk [measurable_space γ] {f : α → β} {g : α → γ}
  (hf : ae_measurable f μ) (hg : ae_measurable g μ) : ae_measurable (λ x, (f x, g x)) μ :=
⟨λ a, (hf.mk f a, hg.mk g a), hf.measurable_mk.prod_mk hg.measurable_mk,
  eventually_eq.prod_mk hf.ae_eq_mk hg.ae_eq_mk,⟩

lemma ae_measurable.max [linear_order β] [topological_space β] [order_closed_topology β]
  [second_countable_topology β] [opens_measurable_space β]
  (hf : ae_measurable f μ) (hg : ae_measurable g μ) :
  ae_measurable (λ a, max (f a) (g a)) μ :=
⟨λ a, max (hf.mk f a) (hg.mk g a), hf.measurable_mk.max hg.measurable_mk,
  eventually_eq.comp₂ hf.ae_eq_mk _ hg.ae_eq_mk⟩

lemma ae_measurable.min [linear_order β] [topological_space β] [order_closed_topology β]
  [second_countable_topology β] [opens_measurable_space β]
  (hf : ae_measurable f μ) (hg : ae_measurable g μ) :
  ae_measurable (λ a, min (f a) (g a)) μ :=
⟨λ a, min (hf.mk f a) (hg.mk g a), hf.measurable_mk.min hg.measurable_mk,
  eventually_eq.comp₂ hf.ae_eq_mk _ hg.ae_eq_mk⟩

lemma ae_measurable.smul [semiring β] [topological_space β] [second_countable_topology β]
  [opens_measurable_space β] [add_comm_monoid γ] [topological_space γ] [second_countable_topology γ]
  [semimodule β γ] [topological_semimodule β γ] [measurable_space γ] [borel_space γ]
  {g : α → γ} (hf : ae_measurable f μ) (hg : ae_measurable g μ) :
  ae_measurable (λ c, f c • g c) μ :=
⟨λ a, hf.mk f a • hg.mk g a, hf.measurable_mk.smul hg.measurable_mk,
  eventually_eq.comp₂ hf.ae_eq_mk _ hg.ae_eq_mk⟩

@[to_additive]
lemma ae_measurable.mul [topological_space β] [borel_space β] [has_mul β] [has_continuous_mul β]
  [second_countable_topology β]
  (hf : ae_measurable f μ) (hg : ae_measurable g μ) : ae_measurable (λ a, f a * g a) μ :=
⟨λ a, hf.mk f a * hg.mk g a, hf.measurable_mk.mul hg.measurable_mk,
  eventually_eq.comp₂ hf.ae_eq_mk _ hg.ae_eq_mk⟩

@[to_additive]
lemma ae_measurable.inv [topological_space β] [group β] [topological_group β] [borel_space β]
  (hf : ae_measurable f μ) : ae_measurable (λ a, (f a)⁻¹) μ :=
⟨λ a, (hf.mk f a)⁻¹, hf.measurable_mk.inv, eventually_eq.fun_comp hf.ae_eq_mk _⟩

lemma ae_measurable.sub [add_group β] [topological_space β] [topological_add_group β]
  [second_countable_topology β] [borel_space β]
  (hf : ae_measurable f μ) (hg : ae_measurable g μ) : ae_measurable (λ x, f x - g x) μ :=
by simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma ae_measurable.const_smul {R M : Type*} [topological_space R] [semiring R]
  [add_comm_monoid M] [semimodule R M] [topological_space M] [topological_semimodule R M]
  [measurable_space M] [borel_space M]
  {f : α → M} (hf : ae_measurable f μ) (c : R) :
  ae_measurable (λ x, c • f x) μ :=
⟨λ a, c • hf.mk f a, hf.measurable_mk.const_smul _, eventually_eq.fun_comp hf.ae_eq_mk _⟩

lemma ae_measurable_const_smul_iff {R M : Type*} [topological_space R] [division_ring R]
  [add_comm_monoid M] [semimodule R M] [topological_space M] [topological_semimodule R M]
  [measurable_space M] [borel_space M]
  {f : α → M} {c : R} (hc : c ≠ 0) :
  ae_measurable (λ x, c • f x) μ ↔ ae_measurable f μ :=
⟨λ h, by simpa only [smul_smul, inv_mul_cancel hc, one_smul] using h.const_smul c⁻¹,
  λ h, h.const_smul c⟩

lemma closed_embedding.measurable_inv_fun [topological_space β] [borel_space β] [n : nonempty β]
  [measurable_space γ] [topological_space γ] [borel_space γ] {g : β → γ} (hg : closed_embedding g) :
  measurable (function.inv_fun g) :=
begin
  refine measurable_of_is_closed (λ s hs, _),
  let o := classical.choice n,
  by_cases h : o ∈ s,
  { have : function.inv_fun g ⁻¹' s = g '' s ∪ (g '' univ)ᶜ :=
      function.preimage_inv_fun_of_mem hg.to_embedding.inj h,
    rw this,
    apply is_measurable.union,
    { exact ((closed_embedding.closed_iff_image_closed hg).mp hs).is_measurable },
    { exact ((closed_embedding.closed_iff_image_closed hg).mp is_closed_univ).is_measurable.compl } },
  { have : function.inv_fun g ⁻¹' s = g '' s :=
      function.preimage_inv_fun_of_not_mem hg.to_embedding.inj h,
    rw this,
    exact ((closed_embedding.closed_iff_image_closed hg).mp hs).is_measurable }
end

lemma measurable_of_not_nonempty  (h : ¬ nonempty α) (f : α → β) : measurable f :=
begin
  assume s hs,
  convert is_measurable.empty,
  exact eq_empty_of_not_nonempty h _,
end

lemma ae_measurable_comp_iff_of_closed_embedding
  [topological_space β] [borel_space β] [topological_space γ]
  [measurable_space γ] [borel_space γ] (g : β → γ) (hg : closed_embedding g) :
  ae_measurable (g ∘ f) μ ↔ ae_measurable f μ :=
begin
  by_cases h : nonempty β,
  { resetI,
    refine ⟨λ hf, _, λ hf, hg.continuous.measurable.comp_ae_measurable hf⟩,
    convert hg.measurable_inv_fun.comp_ae_measurable hf,
    ext x,
    exact (function.left_inverse_inv_fun hg.to_embedding.inj (f x)).symm },
  { have H : ¬ nonempty α, by { contrapose! h, exact nonempty.map f h },
    simp [(measurable_of_not_nonempty H (g ∘ f)).ae_measurable,
          (measurable_of_not_nonempty H f).ae_measurable] }
end

lemma ae_measurable_smul_const
  {𝕜 : Type*} [nondiscrete_normed_field 𝕜] [complete_space 𝕜] [measurable_space 𝕜] [borel_space 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] [measurable_space E] [borel_space E]
  {f : α → 𝕜} {c : E} (hc : c ≠ 0) :
  ae_measurable (λ x, f x • c) μ ↔ ae_measurable f μ :=
ae_measurable_comp_iff_of_closed_embedding (λ y : 𝕜, y • c) (closed_embedding_smul_left hc)

@[simp] lemma ae_measurable_const {b : β} : ae_measurable (λ a : α, b) μ :=
measurable_const.ae_measurable

end ae_measurable

/-

/-- Given an almost everywhere measurable function `f`, associate its class of almost everywhere
defined functions. -/
def ae_measurable.mk_ae (f : α → β) (h : ae_measurable f μ) : α →ₘ[μ] β :=
ae_eq_fun.mk (h.mk f) h.measurable_mk

@[simp] lemma ae_measurable.mk_ae_eq_mk_ae_iff (hf : ae_measurable f μ) (hg : ae_measurable g μ) :
  hf.mk_ae f = hg.mk_ae g ↔ f =ᵐ[μ] g :=
begin
  simp only [ae_measurable.mk_ae, ae_eq_fun.mk_eq_mk],
  exact ⟨λ H, (hf.ae_eq_mk.trans H).trans hg.ae_eq_mk.symm,
    λ H, (hf.ae_eq_mk.symm.trans H).trans hg.ae_eq_mk⟩
end

lemma ae_measurable.mk_ae_eq_mk (hf : measurable f) :
  (hf.ae_measurable.mk_ae f : α →ₘ[μ] β) = ae_eq_fun.mk f hf :=
begin
  rw [ae_measurable.mk_ae, ae_eq_fun.mk_eq_mk],
  exact hf.ae_measurable.ae_eq_mk.symm
end

@[simp] lemma coe_fn_mk_ae (f : α →ₘ[μ] β) :
  ae_measurable.mk_ae f f.measurable.ae_measurable = f :=
begin
  conv_rhs { rw ← ae_eq_fun.mk_coe_fn f },
  rw [ae_measurable.mk_ae, ae_eq_fun.mk_eq_mk],
  exact (ae_measurable.ae_eq_mk _).symm
end

lemma edist_mk_ae_mk_ae'
  [metric_space β] [second_countable_topology β] [opens_measurable_space β]
  (hf : ae_measurable f μ) (hg : ae_measurable g μ) :
  edist (hf.mk_ae f) (hg.mk_ae g) = ∫⁻ x, nndist (f x) (g x) ∂μ :=
calc
edist (hf.mk_ae f) (hg.mk_ae g) = ∫⁻ x, nndist (hf.mk f x) (hg.mk g x) ∂μ :
  ae_eq_fun.edist_mk_mk' hf.measurable_mk hg.measurable_mk
... = ∫⁻ x, nndist (f x) (g x) ∂μ :
begin
  apply lintegral_congr_ae,
  apply eventually_eq.comp₂ hf.ae_eq_mk.symm (λ x y, (nndist x y : ennreal)) hg.ae_eq_mk.symm,
end
-/

namespace measure_theory

section measurable_space
variables [measurable_space β]

variable (β)

/-- The equivalence relation of being almost everywhere equal -/
def measure.ae_eq_setoid (μ : measure α) : setoid { f : α → β // ae_measurable f μ } :=
⟨λf g, (f : α → β) =ᵐ[μ] g, λ f, ae_eq_refl f, λ f g, ae_eq_symm, λ f g h, ae_eq_trans⟩

variable (α)

/-- The space of equivalence classes of measurable functions, where two measurable functions are
    equivalent if they agree almost everywhere, i.e., they differ on a set of measure `0`.  -/
def ae_eq_fun (μ : measure α) : Type* := quotient (μ.ae_eq_setoid β)

variables {α β}

notation α ` →ₘ[`:25 μ `] ` β := ae_eq_fun α β μ

end measurable_space

namespace ae_eq_fun
variables [measurable_space β] [measurable_space γ] [measurable_space δ]

/-- Construct the equivalence class `[f]` of a measurable function `f`, based on the equivalence
    relation of being almost everywhere equal. -/
def mk (f : α → β) (hf : ae_measurable f μ) : α →ₘ[μ] β := quotient.mk' ⟨f, hf⟩

/-- A representative of an `ae_eq_fun` [f] -/
instance : has_coe_to_fun (α →ₘ[μ] β) :=
⟨_, λf, ae_measurable.mk _ (quotient.out' f : {f : α → β // ae_measurable f μ}).2⟩

protected lemma measurable (f : α →ₘ[μ] β) : measurable f :=
ae_measurable.measurable_mk _

protected lemma ae_measurable (f : α →ₘ[μ] β) : ae_measurable f μ :=
f.measurable.ae_measurable

@[simp] lemma quot_mk_eq_mk (f : α → β) (hf) :
  (quot.mk (@setoid.r _ $ μ.ae_eq_setoid β) ⟨f, hf⟩ : α →ₘ[μ] β) = mk f hf :=
rfl

@[simp] lemma mk_eq_mk {f g : α → β} {hf hg} :
  (mk f hf : α →ₘ[μ] β) = mk g hg ↔ f =ᵐ[μ] g :=
quotient.eq'

@[simp] lemma mk_coe_fn (f : α →ₘ[μ] β) : mk f f.ae_measurable = f :=
begin
  conv_rhs { rw ← quotient.out_eq' f },
  set g : {f : α → β // ae_measurable f μ} := quotient.out' f with hg,
  have : g = ⟨g.1, g.2⟩ := subtype.eq rfl,
  rw [this, ← mk, mk_eq_mk],
  exact (ae_measurable.ae_eq_mk _).symm,
end

@[ext] lemma ext {f g : α →ₘ[μ] β} (h : f =ᵐ[μ] g) : f = g :=
by rwa [← f.mk_coe_fn, ← g.mk_coe_fn, mk_eq_mk]

lemma coe_fn_mk (f : α → β) (hf) : (mk f hf : α →ₘ[μ] β) =ᵐ[μ] f :=
begin
   apply (ae_measurable.ae_eq_mk _).symm.trans,
   exact @quotient.mk_out' _ (μ.ae_eq_setoid β) (⟨f, hf⟩ : {f // ae_measurable f μ})
end

@[elab_as_eliminator]
lemma induction_on (f : α →ₘ[μ] β) {p : (α →ₘ[μ] β) → Prop} (H : ∀ f hf, p (mk f hf)) : p f :=
quotient.induction_on' f $ subtype.forall.2 H

@[elab_as_eliminator]
lemma induction_on₂ {α' β' : Type*} [measurable_space α'] [measurable_space β'] {μ' : measure α'}
  (f : α →ₘ[μ] β) (f' : α' →ₘ[μ'] β') {p : (α →ₘ[μ] β) → (α' →ₘ[μ'] β') → Prop}
  (H : ∀ f hf f' hf', p (mk f hf) (mk f' hf')) :
  p f f' :=
induction_on f $ λ f hf, induction_on f' $ H f hf

@[elab_as_eliminator]
lemma induction_on₃ {α' β' : Type*} [measurable_space α'] [measurable_space β'] {μ' : measure α'}
  {α'' β'' : Type*} [measurable_space α''] [measurable_space β''] {μ'' : measure α''}
  (f : α →ₘ[μ] β) (f' : α' →ₘ[μ'] β') (f'' : α'' →ₘ[μ''] β'')
  {p : (α →ₘ[μ] β) → (α' →ₘ[μ'] β') → (α'' →ₘ[μ''] β'') → Prop}
  (H : ∀ f hf f' hf' f'' hf'', p (mk f hf) (mk f' hf') (mk f'' hf'')) :
  p f f' f'' :=
induction_on f $ λ f hf, induction_on₂ f' f'' $ H f hf

/-- Given a measurable function `g : β → γ`, and an almost everywhere equal function `[f] : α →ₘ β`,
    return the equivalence class of `g ∘ f`, i.e., the almost everywhere equal function
    `[g ∘ f] : α →ₘ γ`. -/
def comp (g : β → γ) (hg : measurable g) (f : α →ₘ[μ] β) : α →ₘ[μ] γ :=
quotient.lift_on' f (λ f, mk (g ∘ (f : α → β)) (hg.comp_ae_measurable f.2)) $
  λ f f' H, mk_eq_mk.2 $ H.fun_comp g

@[simp] lemma comp_mk (g : β → γ) (hg : measurable g)
  (f : α → β) (hf) :
  comp g hg (mk f hf : α →ₘ[μ] β) = mk (g ∘ f) (hg.comp_ae_measurable hf) :=
rfl

lemma comp_eq_mk (g : β → γ) (hg : measurable g) (f : α →ₘ[μ] β) :
  comp g hg f = mk (g ∘ f) (hg.comp_ae_measurable f.ae_measurable) :=
by rw [← comp_mk g hg f f.ae_measurable, mk_coe_fn]

lemma coe_fn_comp (g : β → γ) (hg : measurable g) (f : α →ₘ[μ] β) :
  comp g hg f =ᵐ[μ] g ∘ f :=
by { rw [comp_eq_mk], apply coe_fn_mk }

/-- The class of `x ↦ (f x, g x)`. -/
def pair (f : α →ₘ[μ] β) (g : α →ₘ[μ] γ) : α →ₘ[μ] β × γ :=
quotient.lift_on₂' f g (λ f g, mk (λ x, (f.1 x, g.1 x)) (f.2.prod_mk g.2)) $
  λ f g f' g' Hf Hg, mk_eq_mk.2 $ Hf.prod_mk Hg

@[simp] lemma pair_mk_mk (f : α → β) (hf) (g : α → γ) (hg) :
  (mk f hf : α →ₘ[μ] β).pair (mk g hg) = mk (λ x, (f x, g x)) (hf.prod_mk hg) :=
rfl

lemma pair_eq_mk (f : α →ₘ[μ] β) (g : α →ₘ[μ] γ) :
  f.pair g = mk (λ x, (f x, g x)) (f.ae_measurable.prod_mk g.ae_measurable) :=
by simp only [← pair_mk_mk, mk_coe_fn]

lemma coe_fn_pair (f : α →ₘ[μ] β) (g : α →ₘ[μ] γ) :
  f.pair g =ᵐ[μ] (λ x, (f x, g x)) :=
by { rw pair_eq_mk, apply coe_fn_mk }

/-- Given a measurable function `g : β → γ → δ`, and almost everywhere equal functions
    `[f₁] : α →ₘ β` and `[f₂] : α →ₘ γ`, return the equivalence class of the function
    `λa, g (f₁ a) (f₂ a)`, i.e., the almost everywhere equal function
    `[λa, g (f₁ a) (f₂ a)] : α →ₘ γ` -/
def comp₂ {γ δ : Type*} [measurable_space γ] [measurable_space δ] (g : β → γ → δ)
  (hg : measurable (uncurry g)) (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) : α →ₘ[μ] δ :=
comp _ hg (f₁.pair f₂)

@[simp] lemma comp₂_mk_mk {γ δ : Type*} [measurable_space γ] [measurable_space δ]
  (g : β → γ → δ) (hg : measurable (uncurry g)) (f₁ : α → β) (f₂ : α → γ) (hf₁ hf₂) :
  comp₂ g hg (mk f₁ hf₁ : α →ₘ[μ] β) (mk f₂ hf₂) =
    mk (λa, g (f₁ a) (f₂ a)) (hg.comp_ae_measurable (hf₁.prod_mk hf₂)) :=
rfl

lemma comp₂_eq_pair {γ δ : Type*} [measurable_space γ] [measurable_space δ]
  (g : β → γ → δ) (hg : measurable (uncurry g)) (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) :
  comp₂ g hg f₁ f₂ = comp _ hg (f₁.pair f₂) :=
rfl

lemma comp₂_eq_mk {γ δ : Type*} [measurable_space γ] [measurable_space δ]
  (g : β → γ → δ) (hg : measurable (uncurry g)) (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) :
  comp₂ g hg f₁ f₂ = mk (λ a, g (f₁ a) (f₂ a))
    (hg.comp_ae_measurable (f₁.ae_measurable.prod_mk f₂.ae_measurable)) :=
by rw [comp₂_eq_pair, pair_eq_mk, comp_mk]; refl

lemma coe_fn_comp₂ {γ δ : Type*} [measurable_space γ] [measurable_space δ]
  (g : β → γ → δ) (hg : measurable (uncurry g)) (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) :
  comp₂ g hg f₁ f₂ =ᵐ[μ] λ a, g (f₁ a) (f₂ a) :=
by { rw comp₂_eq_mk, apply coe_fn_mk }

/-- Interpret `f : α →ₘ[μ] β` as a germ at `μ.ae` forgetting that `f` is measurable. -/
def to_germ (f : α →ₘ[μ] β) : germ μ.ae β :=
quotient.lift_on' f (λ f, ((f : α → β) : germ μ.ae β)) $ λ f g H, germ.coe_eq.2 H

@[simp] lemma mk_to_germ (f : α → β) (hf) : (mk f hf : α →ₘ[μ] β).to_germ = f := rfl

lemma to_germ_eq (f : α →ₘ[μ] β) : f.to_germ = (f : α → β) :=
by rw [← mk_to_germ, mk_coe_fn]

lemma to_germ_injective : injective (to_germ : (α →ₘ[μ] β) → germ μ.ae β) :=
λ f g H, ext $ germ.coe_eq.1 $ by rwa [← to_germ_eq, ← to_germ_eq]

lemma comp_to_germ (g : β → γ) (hg : measurable g) (f : α →ₘ[μ] β) :
  (comp g hg f).to_germ = f.to_germ.map g :=
induction_on f $ λ f hf, by simp

lemma comp₂_to_germ (g : β → γ → δ) (hg : measurable (uncurry g))
  (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) :
  (comp₂ g hg f₁ f₂).to_germ = f₁.to_germ.map₂ g f₂.to_germ :=
induction_on₂ f₁ f₂ $ λ f₁ hf₁ f₂ hf₂, by simp

/-- Given a predicate `p` and an equivalence class `[f]`, return true if `p` holds of `f a`
    for almost all `a` -/
def lift_pred (p : β → Prop) (f : α →ₘ[μ] β) : Prop := f.to_germ.lift_pred p

/-- Given a relation `r` and equivalence class `[f]` and `[g]`, return true if `r` holds of
    `(f a, g a)` for almost all `a` -/
def lift_rel (r : β → γ → Prop) (f : α →ₘ[μ] β) (g : α →ₘ[μ] γ) : Prop :=
f.to_germ.lift_rel r g.to_germ

lemma lift_rel_mk_mk {r : β → γ → Prop} {f : α → β} {g : α → γ} {hf hg} :
  lift_rel r (mk f hf : α →ₘ[μ] β) (mk g hg) ↔ ∀ᵐ a ∂μ, r (f a) (g a) :=
iff.rfl

lemma lift_rel_iff_coe_fn {r : β → γ → Prop} {f : α →ₘ[μ] β} {g : α →ₘ[μ] γ} :
  lift_rel r f g ↔ ∀ᵐ a ∂μ, r (f a) (g a) :=
by rw [← lift_rel_mk_mk, mk_coe_fn, mk_coe_fn]

section order

instance [preorder β] : preorder (α →ₘ[μ] β) := preorder.lift to_germ

@[simp] lemma mk_le_mk [preorder β] {f g : α → β} (hf hg) :
  (mk f hf : α →ₘ[μ] β) ≤ mk g hg ↔ f ≤ᵐ[μ] g :=
iff.rfl

@[simp, norm_cast] lemma coe_fn_le [preorder β] {f g : α →ₘ[μ] β} :
  (f : α → β) ≤ᵐ[μ] g ↔ f ≤ g :=
lift_rel_iff_coe_fn.symm

instance [partial_order β] : partial_order (α →ₘ[μ] β) :=
partial_order.lift to_germ to_germ_injective

/- TODO: Prove `L⁰` space is a lattice if β is linear order.
         What if β is only a lattice? -/

-- instance [linear_order β] : semilattice_sup (α →ₘ β) :=
-- { sup := comp₂ (⊔) (_),
--    .. ae_eq_fun.partial_order }

end order

variable (α)
/-- The equivalence class of a constant function: `[λa:α, b]`, based on the equivalence relation of
    being almost everywhere equal -/
def const (b : β) : α →ₘ[μ] β := mk (λa:α, b) ae_measurable_const

lemma coe_fn_const (b : β) : (const α b : α →ₘ[μ] β) =ᵐ[μ] function.const α b :=
coe_fn_mk _ _

variable {α}

instance [inhabited β] : inhabited (α →ₘ[μ] β) := ⟨const α (default β)⟩

@[to_additive] instance [has_one β] : has_one (α →ₘ[μ] β) := ⟨const α 1⟩
@[to_additive] lemma one_def [has_one β] :
  (1 : α →ₘ[μ] β) = mk (λa:α, 1) ae_measurable_const := rfl
@[to_additive] lemma coe_fn_one [has_one β] : ⇑(1 : α →ₘ[μ] β) =ᵐ[μ] 1 := coe_fn_const _ _
@[simp, to_additive] lemma one_to_germ [has_one β] : (1 : α →ₘ[μ] β).to_germ = 1 := rfl

section monoid
variables
  [topological_space γ] [second_countable_topology γ] [borel_space γ]
  [monoid γ] [has_continuous_mul γ]

@[to_additive]
instance : has_mul (α →ₘ[μ] γ) := ⟨comp₂ (*) measurable_mul⟩

@[simp, to_additive] lemma mk_mul_mk (f g : α → γ) (hf hg) :
  (mk f hf : α →ₘ[μ] γ) * (mk g hg) = mk (f * g) (hf.mul hg) :=
rfl

@[to_additive] lemma coe_fn_mul (f g : α →ₘ[μ] γ) : ⇑(f * g) =ᵐ[μ] f * g := coe_fn_comp₂ _ _ _ _

@[simp, to_additive] lemma mul_to_germ (f g : α →ₘ[μ] γ) :
  (f * g).to_germ = f.to_germ * g.to_germ :=
comp₂_to_germ _ _ _ _

@[to_additive]
instance : monoid (α →ₘ[μ] γ) :=
to_germ_injective.monoid to_germ one_to_germ mul_to_germ

end monoid

@[to_additive]
instance comm_monoid [topological_space γ] [second_countable_topology γ] [borel_space γ]
  [comm_monoid γ] [has_continuous_mul γ] : comm_monoid (α →ₘ[μ] γ) :=
to_germ_injective.comm_monoid to_germ one_to_germ mul_to_germ

section group

variables [topological_space γ] [borel_space γ] [group γ] [topological_group γ]

@[to_additive] instance : has_inv (α →ₘ[μ] γ) := ⟨comp has_inv.inv measurable_inv⟩

@[simp, to_additive] lemma inv_mk (f : α → γ) (hf) : (mk f hf : α →ₘ[μ] γ)⁻¹ = mk f⁻¹ hf.inv := rfl

@[to_additive] lemma coe_fn_inv (f : α →ₘ[μ] γ) : ⇑(f⁻¹) =ᵐ[μ] f⁻¹ := coe_fn_comp _ _ _

@[to_additive] lemma inv_to_germ (f : α →ₘ[μ] γ) : (f⁻¹).to_germ = f.to_germ⁻¹ := comp_to_germ _ _ _

variables [second_countable_topology γ]
@[to_additive]
instance : group (α →ₘ[μ] γ) := to_germ_injective.group _ one_to_germ mul_to_germ inv_to_germ

end group

section add_group

variables [topological_space γ] [borel_space γ] [add_group γ] [topological_add_group γ]
  [second_countable_topology γ]

@[simp] lemma mk_sub (f g : α → γ) (hf hg) :
  mk (f - g) (ae_measurable.sub hf hg) = (mk f hf : α →ₘ[μ] γ) - (mk g hg) :=
by simp [sub_eq_add_neg]

lemma coe_fn_sub (f g : α →ₘ[μ] γ) : ⇑(f - g) =ᵐ[μ] f - g :=
by { simp only [sub_eq_add_neg],
     exact ((coe_fn_add f (-g)).trans $ (coe_fn_neg g).mono $ λ x hx, congr_arg ((+) (f x)) hx) }

end add_group

@[to_additive]
instance [topological_space γ] [borel_space γ] [comm_group γ] [topological_group γ]
  [second_countable_topology γ] : comm_group (α →ₘ[μ] γ) :=
{ .. ae_eq_fun.group, .. ae_eq_fun.comm_monoid }

section semimodule

variables {𝕜 : Type*} [semiring 𝕜] [topological_space 𝕜]
variables [topological_space γ] [borel_space γ] [add_comm_monoid γ] [semimodule 𝕜 γ]
  [topological_semimodule 𝕜 γ]

instance : has_scalar 𝕜 (α →ₘ[μ] γ) :=
⟨λ c f, comp ((•) c) (measurable_id.const_smul c) f⟩

@[simp] lemma smul_mk (c : 𝕜) (f : α → γ) (hf) :
  c • (mk f hf : α →ₘ[μ] γ) = mk (c • f) (hf.const_smul _) :=
rfl

lemma coe_fn_smul (c : 𝕜) (f : α →ₘ[μ] γ) : ⇑(c • f) =ᵐ[μ] c • f := coe_fn_comp _ _ _

lemma smul_to_germ (c : 𝕜) (f : α →ₘ[μ] γ) : (c • f).to_germ = c • f.to_germ :=
comp_to_germ _ _ _

variables [second_countable_topology γ] [has_continuous_add γ]

instance : semimodule 𝕜 (α →ₘ[μ] γ) :=
to_germ_injective.semimodule 𝕜 ⟨@to_germ α γ _ μ _, zero_to_germ, add_to_germ⟩ smul_to_germ

end semimodule

/- TODO : Prove that `L⁰` is a complete space if the codomain is complete. -/

open ennreal

/-- For `f : α → ennreal`, define `∫ [f]` to be `∫ f` -/
def lintegral (f : α →ₘ[μ] ennreal) : ennreal :=
quotient.lift_on' f (λf, ∫⁻ a, (f : α → ennreal) a ∂μ) (assume f g, lintegral_congr_ae)

@[simp] lemma lintegral_mk (f : α → ennreal) (hf) :
  (mk f hf : α →ₘ[μ] ennreal).lintegral = ∫⁻ a, f a ∂μ := rfl

lemma lintegral_coe_fn (f : α →ₘ[μ] ennreal) : ∫⁻ a, f a ∂μ = f.lintegral :=
by rw [← lintegral_mk, mk_coe_fn]

@[simp] lemma lintegral_zero : lintegral (0 : α →ₘ[μ] ennreal) = 0 := lintegral_zero

@[simp] lemma lintegral_eq_zero_iff {f : α →ₘ[μ] ennreal} : lintegral f = 0 ↔ f = 0 :=
induction_on f $ λ f hf, (lintegral_eq_zero_iff' hf).trans mk_eq_mk.symm

lemma lintegral_add (f g : α →ₘ[μ] ennreal) : lintegral (f + g) = lintegral f + lintegral g :=
induction_on₂ f g $ λ f hf g hg, by simp [lintegral_add' hf hg]

lemma lintegral_mono {f g : α →ₘ[μ] ennreal} : f ≤ g → lintegral f ≤ lintegral g :=
induction_on₂ f g $ λ f hf g hg hfg, lintegral_mono_ae hfg

section
variables [emetric_space γ] [second_countable_topology γ] [opens_measurable_space γ]

/-- `comp_edist [f] [g] a` will return `edist (f a) (g a) -/
protected def edist (f g : α →ₘ[μ] γ) : α →ₘ[μ] ennreal := comp₂ edist measurable_edist f g

protected lemma edist_comm (f g : α →ₘ[μ] γ) : f.edist g = g.edist f :=
induction_on₂ f g $ λ f hf g hg, mk_eq_mk.2 $ eventually_of_forall $ λ x, edist_comm (f x) (g x)

lemma coe_fn_edist (f g : α →ₘ[μ] γ) : ⇑(f.edist g) =ᵐ[μ] λ a, edist (f a) (g a) :=
coe_fn_comp₂ _ _ _ _

protected lemma edist_self (f : α →ₘ[μ] γ) : f.edist f = 0 :=
induction_on f $ λ f hf, mk_eq_mk.2 $ eventually_of_forall $ λ x, edist_self (f x)

/-- Almost everywhere equal functions form an `emetric_space`, with the emetric defined as
  `edist f g = ∫⁻ a, edist (f a) (g a)`. -/
instance : emetric_space (α →ₘ[μ] γ) :=
{ edist               := λf g, lintegral (f.edist g),
  edist_self          := assume f, lintegral_eq_zero_iff.2 f.edist_self,
  edist_comm          := λ f g, congr_arg lintegral $ f.edist_comm g,
  edist_triangle      := λ f g h, induction_on₃ f g h $ λ f hf g hg h hh,
    calc ∫⁻ a, edist (f a) (h a) ∂μ ≤ ∫⁻ a, edist (f a) (g a) + edist (g a) (h a) ∂μ :
      measure_theory.lintegral_mono (λ a, edist_triangle (f a) (g a) (h a))
    ... = ∫⁻ a, edist (f a) (g a) ∂μ + ∫⁻ a, edist (g a) (h a) ∂μ :
      lintegral_add' (hf.edist hg) (hg.edist hh),
  eq_of_edist_eq_zero := λ f g, induction_on₂ f g $ λ f hf g hg H, mk_eq_mk.2 $
    ((lintegral_eq_zero_iff' (hf.edist hg)).1 H).mono $ λ x, eq_of_edist_eq_zero }

lemma edist_mk_mk {f g : α → γ} (hf hg) :
  edist (mk f hf : α →ₘ[μ] γ) (mk g hg) = ∫⁻ x, edist (f x) (g x) ∂μ :=
rfl

lemma edist_eq_coe (f g : α →ₘ[μ] γ) : edist f g = ∫⁻ x, edist (f x) (g x) ∂μ :=
by rw [← edist_mk_mk, mk_coe_fn, mk_coe_fn]

lemma edist_zero_eq_coe [has_zero γ] (f : α →ₘ[μ] γ) : edist f 0 = ∫⁻ x, edist (f x) 0 ∂μ :=
by rw [← edist_mk_mk, mk_coe_fn, zero_def]

end

section metric
variables [metric_space γ] [second_countable_topology γ] [opens_measurable_space γ]

lemma edist_mk_mk' {f g : α → γ} (hf hg) :
  edist (mk f hf : α →ₘ[μ] γ) (mk g hg) = ∫⁻ x, nndist (f x) (g x) ∂μ :=
by simp only [edist_mk_mk, edist_nndist]

lemma edist_eq_coe' (f g : α →ₘ[μ] γ) : edist f g = ∫⁻ x, nndist (f x) (g x) ∂μ :=
by simp only [edist_eq_coe, edist_nndist]

end metric

lemma edist_add_right [normed_group γ] [second_countable_topology γ] [borel_space γ]
  (f g h : α →ₘ[μ] γ) :
  edist (f + h) (g + h) = edist f g :=
induction_on₃ f g h $ λ f hf g hg h hh, by simp [edist_mk_mk, edist_dist, dist_add_right]

section normed_space

variables {𝕜 : Type*} [normed_field 𝕜]
variables [normed_group γ] [second_countable_topology γ] [normed_space 𝕜 γ] [borel_space γ]

lemma edist_smul (c : 𝕜) (f : α →ₘ[μ] γ) : edist (c • f) 0 = (ennreal.of_real ∥c∥) * edist f 0 :=
induction_on f $ λ f hf, by simp [edist_mk_mk, zero_def, smul_mk, edist_dist, norm_smul,
  ennreal.of_real_mul, lintegral_const_mul']

end normed_space

section pos_part

variables [topological_space γ] [linear_order γ] [order_closed_topology γ]
  [second_countable_topology γ] [has_zero γ] [opens_measurable_space γ]

/-- Positive part of an `ae_eq_fun`. -/
def pos_part (f : α →ₘ[μ] γ) : α →ₘ[μ] γ :=
comp (λ x, max x 0) (measurable_id.max measurable_const) f

@[simp] lemma pos_part_mk (f : α → γ) (hf) :
  pos_part (mk f hf : α →ₘ[μ] γ) = mk (λ x, max (f x) 0) (hf.max ae_measurable_const) :=
rfl

lemma coe_fn_pos_part (f : α →ₘ[μ] γ) : ⇑(pos_part f) =ᵐ[μ] (λ a, max (f a) 0) :=
coe_fn_comp _ _ _

end pos_part

end ae_eq_fun

end measure_theory
