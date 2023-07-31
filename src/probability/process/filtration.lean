/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Rémy Degenne
-/
import measure_theory.function.conditional_expectation.real

/-!
# Filtrations

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines filtrations of a measurable space and σ-finite filtrations.

## Main definitions

* `measure_theory.filtration`: a filtration on a measurable space. That is, a monotone sequence of
  sub-σ-algebras.
* `measure_theory.sigma_finite_filtration`: a filtration `f` is σ-finite with respect to a measure
  `μ` if for all `i`, `μ.trim (f.le i)` is σ-finite.
* `measure_theory.filtration.natural`: the smallest filtration that makes a process adapted. That
  notion `adapted` is not defined yet in this file. See `measure_theory.adapted`.

## Main results

* `measure_theory.filtration.complete_lattice`: filtrations are a complete lattice.

## Tags

filtration, stochastic process

-/

open filter order topological_space
open_locale classical measure_theory nnreal ennreal topology big_operators

namespace measure_theory


/-- A `filtration` on a measurable space `Ω` with σ-algebra `m` is a monotone
sequence of sub-σ-algebras of `m`. -/
structure filtration {Ω : Type*} (ι : Type*) [preorder ι] (m : measurable_space Ω) :=
(seq   : ι → measurable_space Ω)
(mono' : monotone seq)
(le'   : ∀ i : ι, seq i ≤ m)

variables {Ω β ι : Type*} {m : measurable_space Ω}

instance [preorder ι] : has_coe_to_fun (filtration ι m) (λ _, ι → measurable_space Ω) :=
⟨λ f, f.seq⟩

namespace filtration
variables [preorder ι]

protected lemma mono {i j : ι} (f : filtration ι m) (hij : i ≤ j) : f i ≤ f j := f.mono' hij

protected lemma le (f : filtration ι m) (i : ι) : f i ≤ m := f.le' i

@[ext] protected lemma ext {f g : filtration ι m} (h : (f : ι → measurable_space Ω) = g) : f = g :=
by { cases f, cases g, simp only, exact h, }

variable (ι)
/-- The constant filtration which is equal to `m` for all `i : ι`. -/
def const (m' : measurable_space Ω) (hm' : m' ≤ m) : filtration ι m :=
⟨λ _, m', monotone_const, λ _, hm'⟩
variable {ι}

@[simp]
lemma const_apply {m' : measurable_space Ω} {hm' : m' ≤ m} (i : ι) : const ι m' hm' i = m' := rfl

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

lemma measurable_set_of_filtration [preorder ι] {f : filtration ι m} {s : set Ω} {i : ι}
  (hs : measurable_set[f i] s) : measurable_set[m] s :=
f.le i s hs

/-- A measure is σ-finite with respect to filtration if it is σ-finite with respect
to all the sub-σ-algebra of the filtration. -/
class sigma_finite_filtration [preorder ι] (μ : measure Ω) (f : filtration ι m) : Prop :=
(sigma_finite : ∀ i : ι, sigma_finite (μ.trim (f.le i)))

instance sigma_finite_of_sigma_finite_filtration [preorder ι] (μ : measure Ω) (f : filtration ι m)
  [hf : sigma_finite_filtration μ f] (i : ι) :
  sigma_finite (μ.trim (f.le i)) :=
by apply hf.sigma_finite -- can't exact here

@[priority 100]
instance is_finite_measure.sigma_finite_filtration [preorder ι] (μ : measure Ω) (f : filtration ι m)
  [is_finite_measure μ] :
  sigma_finite_filtration μ f :=
⟨λ n, by apply_instance⟩

/-- Given a integrable function `g`, the conditional expectations of `g` with respect to a
filtration is uniformly integrable. -/
lemma integrable.uniform_integrable_condexp_filtration
  [preorder ι] {μ : measure Ω} [is_finite_measure μ] {f : filtration ι m}
  {g : Ω → ℝ} (hg : integrable g μ) :
  uniform_integrable (λ i, μ[g | f i]) 1 μ :=
hg.uniform_integrable_condexp f.le

section of_set

variables [preorder ι]

/-- Given a sequence of measurable sets `(sₙ)`, `filtration_of_set` is the smallest filtration
such that `sₙ` is measurable with respect to the `n`-the sub-σ-algebra in `filtration_of_set`. -/
def filtration_of_set {s : ι → set Ω} (hsm : ∀ i, measurable_set (s i)) : filtration ι m :=
{ seq := λ i, measurable_space.generate_from {t | ∃ j ≤ i, s j = t},
  mono' := λ n m hnm, measurable_space.generate_from_mono
    (λ t ⟨k, hk₁, hk₂⟩, ⟨k, hk₁.trans hnm, hk₂⟩),
  le' := λ n, measurable_space.generate_from_le (λ t ⟨k, hk₁, hk₂⟩, hk₂ ▸ hsm k) }

lemma measurable_set_filtration_of_set {s : ι → set Ω}
  (hsm : ∀ i, measurable_set[m] (s i)) (i : ι) {j : ι} (hj : j ≤ i) :
  measurable_set[filtration_of_set hsm i] (s j) :=
measurable_space.measurable_set_generate_from ⟨j, hj, rfl⟩

lemma measurable_set_filtration_of_set' {s : ι → set Ω}
  (hsm : ∀ n, measurable_set[m] (s n)) (i : ι) :
  measurable_set[filtration_of_set hsm i] (s i) :=
measurable_set_filtration_of_set hsm i le_rfl

end of_set

namespace filtration
variables [topological_space β] [metrizable_space β] [mβ : measurable_space β] [borel_space β]
  [preorder ι]

include mβ

/-- Given a sequence of functions, the natural filtration is the smallest sequence
of σ-algebras such that that sequence of functions is measurable with respect to
the filtration. -/
def natural (u : ι → Ω → β) (hum : ∀ i, strongly_measurable (u i)) : filtration ι m :=
{ seq   := λ i, ⨆ j ≤ i, measurable_space.comap (u j) mβ,
  mono' := λ i j hij, bsupr_mono $ λ k, ge_trans hij,
  le'   := λ i,
  begin
    refine supr₂_le _,
    rintros j hj s ⟨t, ht, rfl⟩,
    exact (hum j).measurable ht,
  end }

section

open measurable_space

lemma filtration_of_set_eq_natural [mul_zero_one_class β] [nontrivial β]
  {s : ι → set Ω} (hsm : ∀ i, measurable_set[m] (s i)) :
  filtration_of_set hsm = natural (λ i, (s i).indicator (λ ω, 1 : Ω → β))
    (λ i, strongly_measurable_one.indicator (hsm i)) :=
begin
  simp only [natural, filtration_of_set, measurable_space_supr_eq],
  ext1 i,
  refine le_antisymm (generate_from_le _) (generate_from_le _),
  { rintro _ ⟨j, hij, rfl⟩,
    refine measurable_set_generate_from ⟨j, measurable_set_generate_from ⟨hij, _⟩⟩,
    rw comap_eq_generate_from,
    refine measurable_set_generate_from ⟨{1}, measurable_set_singleton 1, _⟩,
    ext x,
    simp [set.indicator_const_preimage_eq_union] },
  { rintro t ⟨n, ht⟩,
    suffices : measurable_space.generate_from
      {t | ∃ (H : n ≤ i), measurable_set[(measurable_space.comap
        ((s n).indicator (λ ω, 1 : Ω → β)) mβ)] t}
      ≤ generate_from {t | ∃ (j : ι) (H : j ≤ i), s j = t},
    { exact this _ ht },
    refine generate_from_le _,
    rintro t ⟨hn, u, hu, hu'⟩,
    obtain heq | heq | heq | heq := set.indicator_const_preimage (s n) u (1 : β),
    swap 4, rw set.mem_singleton_iff at heq,
    all_goals { rw heq at hu', rw ← hu' },
    exacts [measurable_set_empty _, measurable_set.univ, measurable_set_generate_from ⟨n, hn, rfl⟩,
      measurable_set.compl (measurable_set_generate_from ⟨n, hn, rfl⟩)] }
end

end

section limit

omit mβ

variables {E : Type*} [has_zero E] [topological_space E]
  {ℱ : filtration ι m} {f : ι → Ω → E} {μ : measure Ω}

/-- Given a process `f` and a filtration `ℱ`, if `f` converges to some `g` almost everywhere and
`g` is `⨆ n, ℱ n`-measurable, then `limit_process f ℱ μ` chooses said `g`, else it returns 0.

This definition is used to phrase the a.e. martingale convergence theorem
`submartingale.ae_tendsto_limit_process` where an L¹-bounded submartingale `f` adapted to `ℱ`
converges to `limit_process f ℱ μ` `μ`-almost everywhere. -/
noncomputable
def limit_process (f : ι → Ω → E) (ℱ : filtration ι m) (μ : measure Ω . volume_tac) :=
if h : ∃ g : Ω → E, strongly_measurable[⨆ n, ℱ n] g ∧
  ∀ᵐ ω ∂μ, tendsto (λ n, f n ω) at_top (𝓝 (g ω)) then classical.some h else 0

lemma strongly_measurable_limit_process :
  strongly_measurable[⨆ n, ℱ n] (limit_process f ℱ μ) :=
begin
  rw limit_process,
  split_ifs with h h,
  exacts [(classical.some_spec h).1, strongly_measurable_zero]
end

lemma strongly_measurable_limit_process' :
  strongly_measurable[m] (limit_process f ℱ μ) :=
strongly_measurable_limit_process.mono (Sup_le (λ m ⟨n, hn⟩, hn ▸ ℱ.le _))

lemma mem_ℒp_limit_process_of_snorm_bdd {R : ℝ≥0} {p : ℝ≥0∞}
  {F : Type*} [normed_add_comm_group F] {ℱ : filtration ℕ m} {f : ℕ → Ω → F}
  (hfm : ∀ n, ae_strongly_measurable (f n) μ) (hbdd : ∀ n, snorm (f n) p μ ≤ R) :
  mem_ℒp (limit_process f ℱ μ) p μ :=
begin
  rw limit_process,
  split_ifs with h,
  { refine ⟨strongly_measurable.ae_strongly_measurable
      ((classical.some_spec h).1.mono (Sup_le (λ m ⟨n, hn⟩, hn ▸ ℱ.le _))),
      lt_of_le_of_lt (Lp.snorm_lim_le_liminf_snorm hfm _ (classical.some_spec h).2)
        (lt_of_le_of_lt _ (ennreal.coe_lt_top : ↑R < ∞))⟩,
    simp_rw [liminf_eq, eventually_at_top],
    exact Sup_le (λ b ⟨a, ha⟩, (ha a le_rfl).trans (hbdd _)) },
  { exact zero_mem_ℒp }
end

end limit

end filtration

end measure_theory
