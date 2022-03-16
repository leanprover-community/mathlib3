/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import measure_theory.constructions.borel_space
import measure_theory.function.l1_space
import measure_theory.function.strongly_measurable
import topology.instances.discrete

/-!
# Filtration and stopping time

This file defines some standard definition from the theory of stochastic processes including
filtrations and stopping times. These definitions are used to model the amount of information
at a specific time and is the first step in formalizing stochastic processes.

## Main definitions

* `measure_theory.filtration`: a filtration on a measurable space
* `measure_theory.adapted`: a sequence of functions `u` is said to be adapted to a
  filtration `f` if at each point in time `i`, `u i` is `f i`-measurable
* `measure_theory.prog_measurable`: a sequence of functions `u` is said to be progressively
  measurable with respect to a filtration `f` if at each point in time `i`, `u` restricted to
  `set.Iic i × α` is measurable with respect to the product `measurable_space` structure where the
  σ-algebra used for `α` is `f i`.
* `measure_theory.filtration.natural`: the natural filtration with respect to a sequence of
  measurable functions is the smallest filtration to which it is adapted to
* `measure_theory.is_stopping_time`: a stopping time with respect to some filtration `f` is a
  function `τ` such that for all `i`, the preimage of `{j | j ≤ i}` along `τ` is
  `f i`-measurable
* `measure_theory.is_stopping_time.measurable_space`: the σ-algebra associated with a stopping time

## Main results

* `adapted.prog_measurable_of_continuous`: a continuous adapted process is progressively measurable.
* `prog_measurable.stopped_process`: the stopped process of a progressively measurable process is
  progressively measurable.
* `mem_ℒp_stopped_process`: if a process belongs to `ℒp` at every time in `ℕ`, then its stopped
  process belongs to `ℒp` as well.

## Tags

filtration, stopping time, stochastic process

-/

open topological_space filter
open_locale classical measure_theory nnreal ennreal topological_space big_operators

namespace measure_theory

/-! ### Filtrations -/

/-- A `filtration` on measurable space `α` with σ-algebra `m` is a monotone
sequence of sub-σ-algebras of `m`. -/
structure filtration {α : Type*} (ι : Type*) [preorder ι] (m : measurable_space α) :=
(seq   : ι → measurable_space α)
(mono' : monotone seq)
(le'   : ∀ i : ι, seq i ≤ m)

variables {α β ι : Type*} {m : measurable_space α}

instance [preorder ι] : has_coe_to_fun (filtration ι m) (λ _, ι → measurable_space α) :=
⟨λ f, f.seq⟩

namespace filtration
variables [preorder ι]

protected lemma mono {i j : ι} (f : filtration ι m) (hij : i ≤ j) : f i ≤ f j := f.mono' hij

protected lemma le (f : filtration ι m) (i : ι) : f i ≤ m := f.le' i

@[ext] protected lemma ext {f g : filtration ι m} (h : (f : ι → measurable_space α) = g) : f = g :=
by { cases f, cases g, simp only, exact h, }

variable (ι)
/-- The constant filtration which is equal to `m` for all `i : ι`. -/
def const (m' : measurable_space α) (hm' : m' ≤ m) : filtration ι m :=
⟨λ _, m', monotone_const, λ _, hm'⟩
variable {ι}

@[simp]
lemma const_apply {m' : measurable_space α} {hm' : m' ≤ m} (i : ι) : const ι m' hm' i = m' := rfl

instance : inhabited (filtration ι m) := ⟨const ι m le_rfl⟩

instance : has_le (filtration ι m) := ⟨λ f g, ∀ i, f i ≤ g i⟩

instance : has_bot (filtration ι m) := ⟨const ι ⊥ bot_le⟩

instance : has_top (filtration ι m) := ⟨const ι m le_rfl⟩

instance : has_sup (filtration ι m) := ⟨λ f g,
{ seq   := λ i, f i ⊔ g i,
  mono' := λ i j hij, sup_le ((f.mono hij).trans le_sup_left) ((g.mono hij).trans le_sup_right),
  le'   := λ i, sup_le (f.le i) (g.le i) }⟩

@[norm_cast] lemma coe_fn_sup {f g : filtration ι m} : ⇑(f ⊔ g) = f ⊔ g := rfl

instance : has_inf (filtration ι m) := ⟨λ f g,
{ seq   := λ i, f i ⊓ g i,
  mono' := λ i j hij, le_inf (inf_le_left.trans (f.mono hij)) (inf_le_right.trans (g.mono hij)),
  le'   := λ i, inf_le_left.trans (f.le i) }⟩

@[norm_cast] lemma coe_fn_inf {f g : filtration ι m} : ⇑(f ⊓ g) = f ⊓ g := rfl

instance : has_Sup (filtration ι m) := ⟨λ s,
{ seq   := λ i, Sup ((λ f : filtration ι m, f i) '' s),
  mono' := λ i j hij,
  begin
    refine Sup_le (λ m' hm', _),
    rw [set.mem_image] at hm',
    obtain ⟨f, hf_mem, hfm'⟩ := hm',
    rw ← hfm',
    refine (f.mono hij).trans _,
    have hfj_mem : f j ∈ ((λ g : filtration ι m, g j) '' s), from ⟨f, hf_mem, rfl⟩,
    exact le_Sup hfj_mem,
  end,
  le'   := λ i,
  begin
    refine Sup_le (λ m' hm', _),
    rw [set.mem_image] at hm',
    obtain ⟨f, hf_mem, hfm'⟩ := hm',
    rw ← hfm',
    exact f.le i,
  end, }⟩

lemma Sup_def (s : set (filtration ι m)) (i : ι) :
  Sup s i = Sup ((λ f : filtration ι m, f i) '' s) :=
rfl

noncomputable
instance : has_Inf (filtration ι m) := ⟨λ s,
{ seq   := λ i, if set.nonempty s then Inf ((λ f : filtration ι m, f i) '' s) else m,
  mono' := λ i j hij,
  begin
    by_cases h_nonempty : set.nonempty s,
    swap, { simp only [h_nonempty, set.nonempty_image_iff, if_false, le_refl], },
    simp only [h_nonempty, if_true, le_Inf_iff, set.mem_image, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂],
    refine λ f hf_mem, le_trans _ (f.mono hij),
    have hfi_mem : f i ∈ ((λ g : filtration ι m, g i) '' s), from ⟨f, hf_mem, rfl⟩,
    exact Inf_le hfi_mem,
  end,
  le'   := λ i,
  begin
    by_cases h_nonempty : set.nonempty s,
    swap, { simp only [h_nonempty, if_false, le_refl], },
    simp only [h_nonempty, if_true],
    obtain ⟨f, hf_mem⟩ := h_nonempty,
    exact le_trans (Inf_le ⟨f, hf_mem, rfl⟩) (f.le i),
  end, }⟩

lemma Inf_def (s : set (filtration ι m)) (i : ι) :
  Inf s i = if set.nonempty s then Inf ((λ f : filtration ι m, f i) '' s) else m :=
rfl

noncomputable
instance : complete_lattice (filtration ι m) :=
{ le           := (≤),
  le_refl      := λ f i, le_rfl,
  le_trans     := λ f g h h_fg h_gh i, (h_fg i).trans (h_gh i),
  le_antisymm  := λ f g h_fg h_gf, filtration.ext $ funext $ λ i, (h_fg i).antisymm (h_gf i),
  sup          := (⊔),
  le_sup_left  := λ f g i, le_sup_left,
  le_sup_right := λ f g i, le_sup_right,
  sup_le       := λ f g h h_fh h_gh i, sup_le (h_fh i) (h_gh _),
  inf          := (⊓),
  inf_le_left  := λ f g i, inf_le_left,
  inf_le_right := λ f g i, inf_le_right,
  le_inf       := λ f g h h_fg h_fh i, le_inf (h_fg i) (h_fh i),
  Sup          := Sup,
  le_Sup       := λ s f hf_mem i, le_Sup ⟨f, hf_mem, rfl⟩,
  Sup_le       := λ s f h_forall i, Sup_le $ λ m' hm',
  begin
    obtain ⟨g, hg_mem, hfm'⟩ := hm',
    rw ← hfm',
    exact h_forall g hg_mem i,
  end,
  Inf          := Inf,
  Inf_le       := λ s f hf_mem i,
  begin
    have hs : s.nonempty := ⟨f, hf_mem⟩,
    simp only [Inf_def, hs, if_true],
    exact Inf_le ⟨f, hf_mem, rfl⟩,
  end,
  le_Inf       := λ s f h_forall i,
  begin
    by_cases hs : s.nonempty,
    swap, { simp only [Inf_def, hs, if_false], exact f.le i, },
    simp only [Inf_def, hs, if_true, le_Inf_iff, set.mem_image, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂],
    exact λ g hg_mem, h_forall g hg_mem i,
  end,
  top          := ⊤,
  bot          := ⊥,
  le_top       := λ f i, f.le' i,
  bot_le       := λ f i, bot_le, }

end filtration

lemma measurable_set_of_filtration [preorder ι] {f : filtration ι m} {s : set α} {i : ι}
  (hs : measurable_set[f i] s) : measurable_set[m] s :=
f.le i s hs

/-- A measure is σ-finite with respect to filtration if it is σ-finite with respect
to all the sub-σ-algebra of the filtration. -/
class sigma_finite_filtration [preorder ι] (μ : measure α) (f : filtration ι m) : Prop :=
(sigma_finite : ∀ i : ι, sigma_finite (μ.trim (f.le i)))

instance sigma_finite_of_sigma_finite_filtration [preorder ι] (μ : measure α) (f : filtration ι m)
  [hf : sigma_finite_filtration μ f] (i : ι) :
  sigma_finite (μ.trim (f.le i)) :=
by apply hf.sigma_finite -- can't exact here


section adapted_process

variables [measurable_space β] [preorder ι]
  {u v : ι → α → β} {f : filtration ι m}

/-- A sequence of functions `u` is adapted to a filtration `f` if for all `i`,
`u i` is `f i`-measurable. -/
def adapted (f : filtration ι m) (u : ι → α → β) : Prop :=
∀ i : ι, measurable[f i] (u i)

namespace adapted

lemma add [has_add β] [has_measurable_add₂ β] (hu : adapted f u) (hv : adapted f v) :
  adapted f (u + v) :=
λ i, (hu i).add (hv i)

lemma neg [has_neg β] [has_measurable_neg β] (hu : adapted f u) : adapted f (-u) :=
λ i, (hu i).neg

lemma smul [has_scalar ℝ β] [has_measurable_smul ℝ β] (c : ℝ) (hu : adapted f u) :
  adapted f (c • u) :=
λ i, (hu i).const_smul c

end adapted

variable (β)
lemma adapted_zero [has_zero β] (f : filtration ι m) : adapted f (0 : ι → α → β) :=
λ i, @measurable_zero β α _ (f i) _
variable {β}

/-- Progressively measurable process. A sequence of functions `u` is said to be progressively
measurable with respect to a filtration `f` if at each point in time `i`, `u` restricted to
`set.Iic i × α` is measurable with respect to the product `measurable_space` structure where the
σ-algebra used for `α` is `f i`.
The usual definition uses the interval `[0,i]`, which we replace by `set.Iic i`. We recover the
usual definition for index types `ℝ≥0` or `ℕ`. -/
def prog_measurable [measurable_space ι] (f : filtration ι m) (u : ι → α → β) : Prop :=
∀ i, measurable[subtype.measurable_space.prod (f i)] (λ p : set.Iic i × α, u p.1 p.2)

lemma prog_measurable_const [measurable_space ι] (f : filtration ι m) (b : β) :
  prog_measurable f ((λ _ _, b) : ι → α → β) :=
λ i, @measurable_const _ _ _ (subtype.measurable_space.prod (f i)) _

namespace prog_measurable

variables [measurable_space ι]

protected lemma adapted (h : prog_measurable f u) : adapted f u :=
begin
  intro i,
  have : u i = (λ p : set.Iic i × α, u p.1 p.2) ∘ (λ x, (⟨i, set.mem_Iic.mpr le_rfl⟩, x)) := rfl,
  rw this,
  exact (h i).comp ((@measurable_const _ _ _ (f i) _).prod_mk (@measurable_id _ (f i))),
end

protected lemma comp {t : ι → α → ι} (h : prog_measurable f u) (ht : prog_measurable f t)
  (ht_le : ∀ i x, t i x ≤ i) :
  prog_measurable f (λ i x, u (t i x) x) :=
begin
  intro i,
  have : (λ p : ↥(set.Iic i) × α, u (t (p.fst : ι) p.snd) p.snd)
    = (λ p : ↥(set.Iic i) × α, u (p.fst : ι) p.snd) ∘ (λ p : ↥(set.Iic i) × α,
      (⟨t (p.fst : ι) p.snd, set.mem_Iic.mpr ((ht_le _ _).trans p.fst.prop)⟩, p.snd)) := rfl,
  rw this,
  exact (h i).comp ((ht i).subtype_mk.prod_mk (@measurable_snd _ _ _ (f i))),
end

section arithmetic

@[to_additive] protected lemma mul [has_mul β] [has_measurable_mul₂ β]
  (hu : prog_measurable f u) (hv : prog_measurable f v) :
  prog_measurable f (λ i x, u i x * v i x) :=
λ i, (hu i).mul (hv i)

@[to_additive] protected lemma finset_prod' {γ} [comm_monoid β] [has_measurable_mul₂ β]
  {U : γ → ι → α → β} {s : finset γ} (h : ∀ c ∈ s, prog_measurable f (U c)) :
  prog_measurable f (∏ c in s, U c) :=
finset.prod_induction U (prog_measurable f) (λ _ _, prog_measurable.mul)
  (prog_measurable_const _ 1) h

@[to_additive] protected lemma finset_prod {γ} [comm_monoid β] [has_measurable_mul₂ β]
  {U : γ → ι → α → β} {s : finset γ} (h : ∀ c ∈ s, prog_measurable f (U c)) :
  prog_measurable f (λ i a, ∏ c in s, U c i a) :=
by { convert prog_measurable.finset_prod' h, ext i a, simp only [finset.prod_apply], }

@[to_additive] protected lemma inv [has_inv β] [has_measurable_inv β] (hu : prog_measurable f u) :
  prog_measurable f (λ i x, (u i x)⁻¹) :=
λ i, (hu i).inv

@[to_additive] protected lemma div [has_div β] [has_measurable_div₂ β]
  (hu : prog_measurable f u) (hv : prog_measurable f v) :
  prog_measurable f (λ i x, u i x / v i x) :=
λ i, (hu i).div (hv i)

end arithmetic

end prog_measurable

lemma prog_measurable_of_tendsto' {γ} [measurable_space ι] [metric_space β] [borel_space β]
  (fltr : filter γ) [fltr.ne_bot] [fltr.is_countably_generated] {U : γ → ι → α → β}
  (h : ∀ l, prog_measurable f (U l)) (h_tendsto : tendsto U fltr (𝓝 u)) :
  prog_measurable f u :=
begin
  refine λ i, @measurable_of_tendsto_metric' (set.Iic i × α) β (measurable_space.prod _ (f i))
    _ _ _ γ _ _ fltr _ _ (λ l, h l i) _,
  rw tendsto_pi_nhds at h_tendsto ⊢,
  intro x,
  specialize h_tendsto x.fst,
  rw tendsto_nhds at h_tendsto ⊢,
  exact λ s hs h_mem, h_tendsto {g | g x.snd ∈ s} (hs.preimage (continuous_apply x.snd)) h_mem,
end

lemma prog_measurable_of_tendsto [measurable_space ι] [metric_space β] [borel_space β]
  {U : ℕ → ι → α → β}
  (h : ∀ l, prog_measurable f (U l)) (h_tendsto : tendsto U at_top (𝓝 u)) :
  prog_measurable f u :=
prog_measurable_of_tendsto' at_top h h_tendsto

/-- A continuous and adapted process is progressively measurable. -/
theorem adapted.prog_measurable_of_continuous [emetric_space ι] [measurable_space ι]
  [second_countable_topology ι] [opens_measurable_space ι] [metric_space β] [borel_space β]
  (h : adapted f u) (hu_cont : ∀ x, continuous (λ i, u i x)) :
  prog_measurable f u :=
λ i, @measurable_uncurry_of_continuous_of_measurable _ _ (set.Iic i) _ _ _ _ _ _ _ _ _
  (λ x, (hu_cont x).comp continuous_induced_dom) (λ j, (h j).mono (f.mono j.prop) le_rfl)

end adapted_process

namespace filtration
variables {mβ : measurable_space β} [preorder ι]

include mβ

/-- Given a sequence of functions, the natural filtration is the smallest sequence
of σ-algebras such that that sequence of functions is measurable with respect to
the filtration. -/
def natural (u : ι → α → β) (hum : ∀ i, measurable (u i)) : filtration ι m :=
{ seq   := λ i, ⨆ j ≤ i, measurable_space.comap (u j) infer_instance,
  mono' := λ i j hij, bsupr_le_bsupr' $ λ k hk, le_trans hk hij,
  le'   := λ i, bsupr_le (λ j hj s hs, let ⟨t, ht, ht'⟩ := hs in ht' ▸ hum j ht) }

lemma adapted_natural {u : ι → α → β} (hum : ∀ i, measurable[m] (u i)) :
  adapted (natural u hum) u :=
λ i, measurable.le (le_bsupr_of_le i (le_refl i) le_rfl) (λ s hs, ⟨s, hs, rfl⟩)

end filtration

/-! ### Stopping times -/

/-- A stopping time with respect to some filtration `f` is a function
`τ` such that for all `i`, the preimage of `{j | j ≤ i}` along `τ` is measurable
with respect to `f i`.

Intuitively, the stopping time `τ` describes some stopping rule such that at time
`i`, we may determine it with the information we have at time `i`. -/
def is_stopping_time [preorder ι] (f : filtration ι m) (τ : α → ι) :=
∀ i : ι, measurable_set[f i] $ {x | τ x ≤ i}

lemma is_stopping_time_const [preorder ι] {f : filtration ι m} (i : ι) :
  is_stopping_time f (λ x, i) :=
λ j, by simp only [measurable_set.const]

section measurable_set

section preorder
variables [preorder ι] {f : filtration ι m} {τ : α → ι}

lemma is_stopping_time.measurable_set_le (hτ : is_stopping_time f τ) (i : ι) :
  measurable_set[f i] {x | τ x ≤ i} :=
hτ i

lemma is_stopping_time.measurable_set_lt_of_pred [pred_order ι]
  (hτ : is_stopping_time f τ) (i : ι) :
  measurable_set[f i] {x | τ x < i} :=
begin
  by_cases hi_min : is_min i,
  { suffices : {x : α | τ x < i} = ∅, by { rw this, exact @measurable_set.empty _ (f i), },
    ext1 x,
    simp only [set.mem_set_of_eq, set.mem_empty_eq, iff_false],
    rw is_min_iff_forall_not_lt at hi_min,
    exact hi_min (τ x), },
  have : {x : α | τ x < i} = τ ⁻¹' (set.Iio i),
  { ext1 x, simp only [set.mem_set_of_eq, set.mem_preimage, set.mem_Iio], },
  rw [this, pred_order.Iio_eq_Iic_pred' hi_min],
  have : τ ⁻¹' set.Iic (pred_order.pred i) = {x : α | τ x ≤ pred_order.pred i},
  { ext1 x, simp only [set.mem_preimage, set.mem_Iic, set.mem_set_of_eq], },
  rw this,
  exact f.mono (pred_order.pred_le i) _ (hτ.measurable_set_le (pred_order.pred i)),
end

end preorder

section linear_order
variables [linear_order ι] {f : filtration ι m} {τ : α → ι}

lemma is_stopping_time.measurable_set_gt (hτ : is_stopping_time f τ) (i : ι) :
  measurable_set[f i] {x | i < τ x} :=
begin
  have : {x | i < τ x} = {x | τ x ≤ i}ᶜ,
  { ext1 x, simp only [set.mem_set_of_eq, set.mem_compl_eq, not_le], },
  rw this,
  exact (hτ.measurable_set_le i).compl,
end

variables [topological_space ι] [order_topology ι] [first_countable_topology ι]

/-- Auxiliary lemma for `is_stopping_time.measurable_set_lt`. -/
lemma is_stopping_time.measurable_set_lt_of_is_lub
  (hτ : is_stopping_time f τ) (i : ι) (h_lub : is_lub (set.Iio i) i) :
  measurable_set[f i] {x | τ x < i} :=
begin
  by_cases hi_min : is_min i,
  { suffices : {x : α | τ x < i} = ∅, by { rw this, exact @measurable_set.empty _ (f i), },
    ext1 x,
    simp only [set.mem_set_of_eq, set.mem_empty_eq, iff_false],
    exact is_min_iff_forall_not_lt.mp hi_min (τ x), },
  obtain ⟨seq, -, -, h_tendsto, h_bound⟩ : ∃ seq : ℕ → ι,
      monotone seq ∧ (∀ j, seq j ≤ i) ∧ tendsto seq at_top (𝓝 i) ∧ (∀ j, seq j < i),
    from h_lub.exists_seq_monotone_tendsto (not_is_min_iff.mp hi_min),
  have h_Ioi_eq_Union : set.Iio i = ⋃ j, { k | k ≤ seq j},
  { ext1 k,
    simp only [set.mem_Iio, set.mem_Union, set.mem_set_of_eq],
    refine ⟨λ hk_lt_i, _, λ h_exists_k_le_seq, _⟩,
    { rw tendsto_at_top' at h_tendsto,
      have h_nhds : set.Ici k ∈ 𝓝 i,
        from mem_nhds_iff.mpr ⟨set.Ioi k, set.Ioi_subset_Ici le_rfl, is_open_Ioi, hk_lt_i⟩,
      obtain ⟨a, ha⟩ : ∃ (a : ℕ), ∀ (b : ℕ), b ≥ a → k ≤ seq b := h_tendsto (set.Ici k) h_nhds,
      exact ⟨a, ha a le_rfl⟩, },
    { obtain ⟨j, hk_seq_j⟩ := h_exists_k_le_seq,
      exact hk_seq_j.trans_lt (h_bound j), }, },
  have h_lt_eq_preimage : {x : α | τ x < i} = τ ⁻¹' (set.Iio i),
  { ext1 x, simp only [set.mem_set_of_eq, set.mem_preimage, set.mem_Iio], },
  rw [h_lt_eq_preimage, h_Ioi_eq_Union],
  simp only [set.preimage_Union, set.preimage_set_of_eq],
  exact measurable_set.Union
    (λ n, f.mono (h_bound n).le _ (hτ.measurable_set_le (seq n))),
end

lemma is_stopping_time.measurable_set_lt (hτ : is_stopping_time f τ) (i : ι) :
  measurable_set[f i] {x | τ x < i} :=
begin
  obtain ⟨i', hi'_lub⟩ : ∃ i', is_lub (set.Iio i) i', from exists_lub_Iio i,
  cases lub_Iio_eq_self_or_Iio_eq_Iic i hi'_lub with hi'_eq_i h_Iio_eq_Iic,
  { rw ← hi'_eq_i at hi'_lub ⊢,
    exact hτ.measurable_set_lt_of_is_lub i' hi'_lub, },
  { have h_lt_eq_preimage : {x : α | τ x < i} = τ ⁻¹' (set.Iio i) := rfl,
    rw [h_lt_eq_preimage, h_Iio_eq_Iic],
    exact f.mono (lub_Iio_le i hi'_lub) _ (hτ.measurable_set_le i'), },
end

lemma is_stopping_time.measurable_set_ge (hτ : is_stopping_time f τ) (i : ι) :
  measurable_set[f i] {x | i ≤ τ x} :=
begin
  have : {x | i ≤ τ x} = {x | τ x < i}ᶜ,
  { ext1 x, simp only [set.mem_set_of_eq, set.mem_compl_eq, not_lt], },
  rw this,
  exact (hτ.measurable_set_lt i).compl,
end

lemma is_stopping_time.measurable_set_eq (hτ : is_stopping_time f τ) (i : ι) :
  measurable_set[f i] {x | τ x = i} :=
begin
  have : {x | τ x = i} = {x | τ x ≤ i} ∩ {x | τ x ≥ i},
  { ext1 x, simp only [set.mem_set_of_eq, ge_iff_le, set.mem_inter_eq, le_antisymm_iff], },
  rw this,
  exact (hτ.measurable_set_le i).inter (hτ.measurable_set_ge i),
end

lemma is_stopping_time.measurable_set_eq_le (hτ : is_stopping_time f τ) {i j : ι} (hle : i ≤ j) :
  measurable_set[f j] {x | τ x = i} :=
f.mono hle _ $ hτ.measurable_set_eq i

lemma is_stopping_time.measurable_set_lt_le (hτ : is_stopping_time f τ) {i j : ι} (hle : i ≤ j) :
  measurable_set[f j] {x | τ x < i} :=
f.mono hle _ $ hτ.measurable_set_lt i

end linear_order

section encodable

lemma is_stopping_time_of_measurable_set_eq [preorder ι] [encodable ι]
  {f : filtration ι m} {τ : α → ι} (hτ : ∀ i, measurable_set[f i] {x | τ x = i}) :
  is_stopping_time f τ :=
begin
  intro i,
  rw show {x | τ x ≤ i} = ⋃ k ≤ i, {x | τ x = k}, by { ext, simp },
  refine measurable_set.bUnion (set.countable_encodable _) (λ k hk, _),
  exact f.mono hk _ (hτ k),
end

end encodable

end measurable_set

namespace is_stopping_time

protected lemma max [linear_order ι] {f : filtration ι m} {τ π : α → ι}
  (hτ : is_stopping_time f τ) (hπ : is_stopping_time f π) :
  is_stopping_time f (λ x, max (τ x) (π x)) :=
begin
  intro i,
  simp_rw [max_le_iff, set.set_of_and],
  exact (hτ i).inter (hπ i),
end

protected lemma min [linear_order ι] {f : filtration ι m} {τ π : α → ι}
  (hτ : is_stopping_time f τ) (hπ : is_stopping_time f π) :
  is_stopping_time f (λ x, min (τ x) (π x)) :=
begin
  intro i,
  simp_rw [min_le_iff, set.set_of_or],
  exact (hτ i).union (hπ i),
end

lemma add_const [add_group ι] [preorder ι] [covariant_class ι ι (function.swap (+)) (≤)]
  [covariant_class ι ι (+) (≤)]
  {f : filtration ι m} {τ : α → ι} (hτ : is_stopping_time f τ) {i : ι} (hi : 0 ≤ i) :
  is_stopping_time f (λ x, τ x + i) :=
begin
  intro j,
  simp_rw [← le_sub_iff_add_le],
  exact f.mono (sub_le_self j hi) _ (hτ (j - i)),
end

section preorder

variables [preorder ι] {f : filtration ι m}

/-- The associated σ-algebra with a stopping time. -/
protected def measurable_space
  {τ : α → ι} (hτ : is_stopping_time f τ) : measurable_space α :=
{ measurable_set' := λ s, ∀ i : ι, measurable_set[f i] (s ∩ {x | τ x ≤ i}),
  measurable_set_empty :=
    λ i, (set.empty_inter {x | τ x ≤ i}).symm ▸ @measurable_set.empty _ (f i),
  measurable_set_compl := λ s hs i,
    begin
      rw (_ : sᶜ ∩ {x | τ x ≤ i} = (sᶜ ∪ {x | τ x ≤ i}ᶜ) ∩ {x | τ x ≤ i}),
      { refine measurable_set.inter _ _,
        { rw ← set.compl_inter,
          exact (hs i).compl },
        { exact hτ i} },
      { rw set.union_inter_distrib_right,
        simp only [set.compl_inter_self, set.union_empty] }
    end,
  measurable_set_Union := λ s hs i,
    begin
      rw forall_swap at hs,
      rw set.Union_inter,
      exact measurable_set.Union (hs i),
    end }

@[protected]
lemma measurable_set {τ : α → ι} (hτ : is_stopping_time f τ) (s : set α) :
  measurable_set[hτ.measurable_space] s ↔
  ∀ i : ι, measurable_set[f i] (s ∩ {x | τ x ≤ i}) :=
iff.rfl

lemma measurable_space_mono
  {τ π : α → ι} (hτ : is_stopping_time f τ) (hπ : is_stopping_time f π) (hle : τ ≤ π) :
  hτ.measurable_space ≤ hπ.measurable_space :=
begin
  intros s hs i,
  rw (_ : s ∩ {x | π x ≤ i} = s ∩ {x | τ x ≤ i} ∩ {x | π x ≤ i}),
  { exact (hs i).inter (hπ i) },
  { ext,
    simp only [set.mem_inter_eq, iff_self_and, and.congr_left_iff, set.mem_set_of_eq],
    intros hle' _,
    exact le_trans (hle _) hle' },
end

lemma measurable_space_le [encodable ι] {τ : α → ι} (hτ : is_stopping_time f τ) :
  hτ.measurable_space ≤ m :=
begin
  intros s hs,
  change ∀ i, measurable_set[f i] (s ∩ {x | τ x ≤ i}) at hs,
  rw (_ : s = ⋃ i, s ∩ {x | τ x ≤ i}),
  { exact measurable_set.Union (λ i, f.le i _ (hs i)) },
  { ext x, split; rw set.mem_Union,
    { exact λ hx, ⟨τ x, hx, le_rfl⟩ },
    { rintro ⟨_, hx, _⟩,
      exact hx } }
end

section nat

lemma measurable_set_eq_const {f : filtration ℕ m}
  {τ : α → ℕ} (hτ : is_stopping_time f τ) (i : ℕ) :
  measurable_set[hτ.measurable_space] {x | τ x = i} :=
begin
  rw hτ.measurable_set,
  intro j,
  by_cases i ≤ j,
  { rw (_ : {x | τ x = i} ∩ {x | τ x ≤ j} = {x | τ x = i}),
    { exact hτ.measurable_set_eq_le h },
    { ext,
      simp only [set.mem_inter_eq, and_iff_left_iff_imp, set.mem_set_of_eq],
      rintro rfl,
      assumption } },
  { rw (_ : {x | τ x = i} ∩ {x | τ x ≤ j} = ∅),
    { exact @measurable_set.empty _ (f j) },
    { ext,
      simp only [set.mem_empty_eq, set.mem_inter_eq, not_and, not_le, set.mem_set_of_eq, iff_false],
      rintro rfl,
      rwa not_le at h } }
end

end nat

end preorder

section linear_order

variable [linear_order ι]

lemma measurable [topological_space ι] [measurable_space ι]
  [borel_space ι] [order_topology ι] [second_countable_topology ι]
  {f : filtration ι m} {τ : α → ι} (hτ : is_stopping_time f τ) :
  measurable[hτ.measurable_space] τ :=
begin
  refine @measurable_of_Iic ι α _ _ _ hτ.measurable_space _ _ _ _ _,
  simp_rw [hτ.measurable_set, set.preimage, set.mem_Iic],
  intros i j,
  rw (_ : {x | τ x ≤ i} ∩ {x | τ x ≤ j} = {x | τ x ≤ min i j}),
  { exact f.mono (min_le_right i j) _ (hτ (min i j)) },
  { ext,
    simp only [set.mem_inter_eq, iff_self, le_min_iff, set.mem_set_of_eq] }
end

end linear_order

end is_stopping_time

section linear_order

/-! ## Stopped value and stopped process -/

/-- Given a map `u : ι → α → E`, its stopped value with respect to the stopping
time `τ` is the map `x ↦ u (τ x) x`. -/
def stopped_value (u : ι → α → β) (τ : α → ι) : α → β :=
λ x, u (τ x) x

variable [linear_order ι]

/-- Given a map `u : ι → α → E`, the stopped process with respect to `τ` is `u i x` if
`i ≤ τ x`, and `u (τ x) x` otherwise.

Intuitively, the stopped process stops evolving once the stopping time has occured. -/
def stopped_process (u : ι → α → β) (τ : α → ι) : ι → α → β :=
λ i x, u (min i (τ x)) x

lemma stopped_process_eq_of_le {u : ι → α → β} {τ : α → ι}
  {i : ι} {x : α} (h : i ≤ τ x) : stopped_process u τ i x = u i x :=
by simp [stopped_process, min_eq_left h]

lemma stopped_process_eq_of_ge {u : ι → α → β} {τ : α → ι}
  {i : ι} {x : α} (h : τ x ≤ i) : stopped_process u τ i x = u (τ x) x :=
by simp [stopped_process, min_eq_right h]

section prog_measurable

variables [measurable_space ι] [topological_space ι] [order_topology ι]
  [second_countable_topology ι] [borel_space ι]
  [measurable_space β]
  {u : ι → α → β} {τ : α → ι} {f : filtration ι m}

lemma prog_measurable_min_stopping_time (hτ : is_stopping_time f τ) :
  prog_measurable f (λ i x, min i (τ x)) :=
begin
  intro i,
  let m_prod : measurable_space (set.Iic i × α) := measurable_space.prod _ (f i),
  let m_set : ∀ t : set (set.Iic i × α), measurable_space t :=
    λ _, @subtype.measurable_space (set.Iic i × α) _ m_prod,
  let s := {p : set.Iic i × α | τ p.2 ≤ i},
  have hs : measurable_set[m_prod] s, from @measurable_snd (set.Iic i) α _ (f i) _ (hτ i),
  have h_meas_fst : ∀ t : set (set.Iic i × α),
      measurable[m_set t] (λ x : t, ((x : set.Iic i × α).fst : ι)),
    from λ t, (@measurable_subtype_coe (set.Iic i × α) m_prod _).fst.subtype_coe,
  refine measurable_of_restrict_of_restrict_compl hs _ _,
  { refine @measurable.min _ _ _ _ _ (m_set s) _ _ _ _ _ (h_meas_fst s) _,
    refine @measurable_of_Iic ι s _ _ _ (m_set s) _ _ _ _ (λ j, _),
    have h_set_eq : (λ x : s, τ (x : set.Iic i × α).snd) ⁻¹' set.Iic j
      = (λ x : s, (x : set.Iic i × α).snd) ⁻¹' {x | τ x ≤ min i j},
    { ext1 x,
      simp only [set.mem_preimage, set.mem_Iic, iff_and_self, le_min_iff, set.mem_set_of_eq],
      exact λ _, x.prop, },
    rw h_set_eq,
    suffices h_meas : @measurable _ _ (m_set s) (f i) (λ x : s, (x : set.Iic i × α).snd),
      from h_meas (f.mono (min_le_left _ _) _ (hτ.measurable_set_le (min i j))),
    exact (@measurable_snd _ _ _ (f i)).comp (@measurable_subtype_coe _ m_prod _), },
  { suffices h_min_eq_left : (λ x : sᶜ, min ↑((x : set.Iic i × α).fst) (τ (x : set.Iic i × α).snd))
      = λ x : sᶜ, ↑((x : set.Iic i × α).fst),
    { rw [set.restrict, h_min_eq_left],
      exact h_meas_fst _, },
    ext1 x,
    rw min_eq_left,
    have hx_fst_le : ↑(x : set.Iic i × α).fst ≤ i, from (x : set.Iic i × α).fst.prop,
    refine hx_fst_le.trans (le_of_lt _),
    convert x.prop,
    simp only [not_le, set.mem_compl_eq, set.mem_set_of_eq], },
end

lemma prog_measurable.stopped_process (h : prog_measurable f u) (hτ : is_stopping_time f τ) :
  prog_measurable f (stopped_process u τ) :=
h.comp (prog_measurable_min_stopping_time hτ) (λ i x, min_le_left _ _)

lemma prog_measurable.adapted_stopped_process
  (h : prog_measurable f u) (hτ : is_stopping_time f τ) :
  adapted f (stopped_process u τ) :=
(h.stopped_process hτ).adapted

lemma prog_measurable.measurable_stopped_process
  (hu : prog_measurable f u) (hτ : is_stopping_time f τ) (i : ι) :
  measurable (stopped_process u τ i) :=
(hu.adapted_stopped_process hτ i).le (f.le _)

end prog_measurable

end linear_order

section nat
/-! ### Filtrations indexed by `ℕ` -/

open filtration

variables {f : filtration ℕ m} {u : ℕ → α → β} {τ π : α → ℕ}

lemma stopped_value_sub_eq_sum [add_comm_group β] (hle : τ ≤ π) :
  stopped_value u π - stopped_value u τ =
  λ x, (∑ i in finset.Ico (τ x) (π x), (u (i + 1) - u i)) x :=
begin
  ext x,
  rw [finset.sum_Ico_eq_sub _ (hle x), finset.sum_range_sub, finset.sum_range_sub],
  simp [stopped_value],
end

lemma stopped_value_sub_eq_sum' [add_comm_group β] (hle : τ ≤ π) {N : ℕ} (hbdd : ∀ x, π x ≤ N) :
  stopped_value u π - stopped_value u τ =
  λ x, (∑ i in finset.range (N + 1),
    set.indicator {x | τ x ≤ i ∧ i < π x} (u (i + 1) - u i)) x :=
begin
  rw stopped_value_sub_eq_sum hle,
  ext x,
  simp only [finset.sum_apply, finset.sum_indicator_eq_sum_filter],
  refine finset.sum_congr _ (λ _ _, rfl),
  ext i,
  simp only [finset.mem_filter, set.mem_set_of_eq, finset.mem_range, finset.mem_Ico],
  exact ⟨λ h, ⟨lt_trans h.2 (nat.lt_succ_iff.2 $ hbdd _), h⟩, λ h, h.2⟩
end

section add_comm_monoid

variables [add_comm_monoid β]

/-- For filtrations indexed by `ℕ`, `adapted` and `prog_measurable` are equivalent. This lemma
provides `adapted f u → prog_measurable f u`. See `prog_measurable.adapted` for the reverse
direction, which is true more generally. -/
lemma adapted.prog_measurable_of_nat [measurable_space β] [has_measurable_add₂ β]
  (h : adapted f u) : prog_measurable f u :=
begin
  intro i,
  have : (λ p : ↥(set.Iic i) × α, u ↑(p.fst) p.snd)
    = λ p : ↥(set.Iic i) × α, ∑ j in finset.range (i + 1), if ↑p.fst = j then u j p.snd else 0,
  { ext1 p,
    rw finset.sum_ite_eq,
    have hp_mem : (p.fst : ℕ) ∈ finset.range (i + 1) := finset.mem_range_succ_iff.mpr p.fst.prop,
    simp only [hp_mem, if_true], },
  rw this,
  refine finset.measurable_sum _ (λ j hj, measurable.ite _ _ _),
  { suffices h_meas : measurable[measurable_space.prod _ (f i)]
        (λ a : ↥(set.Iic i) × α, (a.fst : ℕ)),
      from h_meas (measurable_set_singleton j),
    exact (@measurable_fst _ α _ (f i)).subtype_coe, },
  { have h_le : j ≤ i, from finset.mem_range_succ_iff.mp hj,
    exact (measurable.le (f.mono h_le) (h j)).comp (@measurable_snd _ α _ (f i)), },
  { exact @measurable_const _ (set.Iic i × α) _ (measurable_space.prod _ (f i)) _, },
end

/-- For filtrations indexed by `ℕ`, the stopped process obtained from an adapted process is
adapted. -/
lemma adapted.stopped_process_of_nat [measurable_space β] [has_measurable_add₂ β]
  (hu : adapted f u) (hτ : is_stopping_time f τ) :
  adapted f (stopped_process u τ) :=
(hu.prog_measurable_of_nat.stopped_process hτ).adapted

lemma adapted.measurable_stopped_process_of_nat [measurable_space β] [has_measurable_add₂ β]
  (hτ : is_stopping_time f τ) (hu : adapted f u) (n : ℕ) :
  measurable (stopped_process u τ n) :=
hu.prog_measurable_of_nat.measurable_stopped_process hτ n

lemma stopped_value_eq {N : ℕ} (hbdd : ∀ x, τ x ≤ N) :
  stopped_value u τ =
  λ x, (∑ i in finset.range (N + 1), set.indicator {x | τ x = i} (u i)) x :=
begin
  ext y,
  rw [stopped_value, finset.sum_apply, finset.sum_eq_single (τ y)],
  { rw set.indicator_of_mem,
    exact rfl },
  { exact λ i hi hneq, set.indicator_of_not_mem hneq.symm _ },
  { intro hy,
    rw set.indicator_of_not_mem,
    exact λ _, hy (finset.mem_range.2 $ lt_of_le_of_lt (hbdd _) (nat.lt_succ_self _)) }
end

lemma stopped_process_eq (n : ℕ) :
  stopped_process u τ n =
  set.indicator {a | n ≤ τ a} (u n) +
    ∑ i in finset.range n, set.indicator {a | τ a = i} (u i) :=
begin
  ext x,
  rw [pi.add_apply, finset.sum_apply],
  cases le_or_lt n (τ x),
  { rw [stopped_process_eq_of_le h, set.indicator_of_mem, finset.sum_eq_zero, add_zero],
    { intros m hm,
      rw finset.mem_range at hm,
      exact set.indicator_of_not_mem ((lt_of_lt_of_le hm h).ne.symm) _ },
    { exact h } },
  { rw [stopped_process_eq_of_ge (le_of_lt h), finset.sum_eq_single_of_mem (τ x)],
    { rw [set.indicator_of_not_mem, zero_add, set.indicator_of_mem],
      { exact rfl }, -- refl does not work
      { exact not_le.2 h } },
    { rwa [finset.mem_range] },
    { intros b hb hneq,
      rw set.indicator_of_not_mem,
      exact hneq.symm } },
end

end add_comm_monoid

section normed_group

variables [measurable_space β] [normed_group β] [has_measurable_add₂ β] [borel_space β] {p : ℝ≥0∞}
  {μ : measure α}

lemma mem_ℒp_stopped_process (hτ : is_stopping_time f τ) (hu : ∀ n, mem_ℒp (u n) p μ) (n : ℕ) :
  mem_ℒp (stopped_process u τ n) p μ :=
begin
  rw stopped_process_eq,
  refine mem_ℒp.add _ _,
  { exact mem_ℒp.indicator (f.le n {a : α | n ≤ τ a} (hτ.measurable_set_ge n)) (hu n) },
  { suffices : mem_ℒp (λ x, ∑ (i : ℕ) in finset.range n, {a : α | τ a = i}.indicator (u i) x) p μ,
    { convert this, ext1 x, simp only [finset.sum_apply] },
    refine mem_ℒp_finset_sum _ (λ i hi, mem_ℒp.indicator _ (hu i)),
    exact f.le i {a : α | τ a = i} (hτ.measurable_set_eq i) },
end

lemma integrable_stopped_process (hτ : is_stopping_time f τ)
  (hu : ∀ n, integrable (u n) μ) (n : ℕ) :
  integrable (stopped_process u τ n) μ :=
by { simp_rw ← mem_ℒp_one_iff_integrable at hu ⊢, exact mem_ℒp_stopped_process hτ hu n, }

lemma mem_ℒp_stopped_value (hτ : is_stopping_time f τ)
  (hu : ∀ n, mem_ℒp (u n) p μ) {N : ℕ} (hbdd : ∀ x, τ x ≤ N) :
  mem_ℒp (stopped_value u τ) p μ :=
begin
  rw stopped_value_eq hbdd,
  suffices : mem_ℒp (λ x, ∑ (i : ℕ) in finset.range (N + 1),
    {a : α | τ a = i}.indicator (u i) x) p μ,
  { convert this, ext1 x, simp only [finset.sum_apply] },
  refine mem_ℒp_finset_sum _ (λ i hi, mem_ℒp.indicator _ (hu i)),
  exact f.le i {a : α | τ a = i} (hτ.measurable_set_eq i)
end

lemma integrable_stopped_value (hτ : is_stopping_time f τ)
  (hu : ∀ n, integrable (u n) μ) {N : ℕ} (hbdd : ∀ x, τ x ≤ N) :
  integrable (stopped_value u τ) μ :=
by { simp_rw ← mem_ℒp_one_iff_integrable at hu ⊢, exact mem_ℒp_stopped_value hτ hu hbdd, }

end normed_group

end nat

end measure_theory
