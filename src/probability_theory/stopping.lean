/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import measure_theory.constructions.borel_space
import measure_theory.function.l1_space
import data.nat.succ_pred

/-!
# Filtration and stopping time

This file defines some standard definition from the theory of stochastic processes including
filtrations and stopping times. These definitions are used to model the amount of information
at a specific time and is the first step in formalizing stochastic processes.

## Main definitions

* `measure_theory.filtration`: a filtration on a measurable space
* `measure_theory.adapted`: a sequence of functions `u` is said to be adapted to a
  filtration `f` if at each point in time `i`, `u i` is `f i`-measurable
* `measure_theory.filtration.natural`: the natural filtration with respect to a sequence of
  measurable functions is the smallest filtration to which it is adapted to
* `measure_theory.stopping_time`: a stopping time with respect to some filtration `f` is a
  function `τ` such that for all `i`, the preimage of `{j | j ≤ i}` along `τ` is
  `f i`-measurable
* `measure_theory.stopping_time.measurable_space`: the σ-algebra associated with a stopping time

## Tags

filtration, stopping time, stochastic process

-/

noncomputable theory
open_locale classical measure_theory nnreal ennreal topological_space big_operators

namespace measure_theory

/-- A `filtration` on measurable space `α` with σ-algebra `m` is a monotone
sequence of of sub-σ-algebras of `m`. -/
structure filtration {α : Type*} (ι : Type*) [preorder ι] (m : measurable_space α) :=
(seq : ι → measurable_space α)
(mono : monotone seq)
(le : ∀ i : ι, seq i ≤ m)

variables {α β ι : Type*} {m : measurable_space α}

open topological_space

section preorder

variables [preorder ι]

instance : has_coe_to_fun (filtration ι m) (λ _, ι → measurable_space α) :=
⟨λ f, f.seq⟩

/-- The constant filtration which is equal to `m` for all `i : ι`. -/
def const_filtration (m : measurable_space α) : filtration ι m :=
⟨λ _, m, monotone_const, λ _, le_rfl⟩

instance : inhabited (filtration ι m) :=
⟨const_filtration m⟩

lemma measurable_set_of_filtration {f : filtration ι m} {s : set α} {i : ι}
  (hs : measurable_set[f i] s) : measurable_set[m] s :=
f.le i s hs

/-- A measure is σ-finite with respect to filtration if it is σ-finite with respect
to all the sub-σ-algebra of the filtration. -/
class sigma_finite_filtration (μ : measure α) (f : filtration ι m) : Prop :=
(sigma_finite : ∀ i : ι, sigma_finite (μ.trim (f.le i)))

instance sigma_finite_of_sigma_finite_filtration (μ : measure α) (f : filtration ι m)
  [hf : sigma_finite_filtration μ f] (i : ι) :
  sigma_finite (μ.trim (f.le i)) :=
by apply hf.sigma_finite -- can't exact here

variables [measurable_space β]

section adapted_process

variables {u v : ι → α → β} {f : filtration ι m}

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
λ i, @measurable_zero β α (f i) _ _

variable {β}

/-- Progressively measurable process. The usual definition uses the interval `[0,i]`, which we
replace by `set.Iic i`. We recover the usual definition for `ι = ℝ≥0` or `ι = ℕ`. -/
def prog_measurable [measurable_space ι] (f : filtration ι m) (u : ι → α → β) : Prop :=
∀ i, measurable[@prod.measurable_space (set.Iic i) α _ (f i)] (λ p : set.Iic i × α, u p.1 p.2)

/-- A process u is said to be continuous if every path is continuous. -/
def continuous_process {ι β} [topological_space ι] [topological_space β] (u : ι → α → β) : Prop :=
∀ x, continuous (λ i, u i x)

lemma _root_.measurable.comp' {α β γ} {mα : measurable_space α} {mβ : measurable_space β}
  {mγ : measurable_space γ} {g : β → γ} {f : α → β} (hg : measurable g) (hf : measurable f) :
  measurable (g ∘ f) :=
λ t ht, hf (hg ht)

lemma _root_.measurable.prod_mk' {α β γ} {mα : measurable_space α} {mβ : measurable_space β}
  {mγ : measurable_space γ} {f : α → β} {g : α → γ} (hf : measurable f) (hg : measurable g) :
  measurable (λ a : α, (f a, g a)) :=
measurable.prod hf hg

lemma _root_.measurable.min' {α δ} {mα : measurable_space α} {mδ : measurable_space δ}
  [linear_order α] [topological_space α] [opens_measurable_space α] [second_countable_topology α]
  [order_closed_topology α]
  {f g : δ → α} (hf : measurable f) (hg : measurable g) :
  measurable (λ a, min (f a) (g a)) :=
by simpa only [min_def] using hf.piecewise (measurable_set_le hf hg) hg

namespace prog_measurable

variables [measurable_space ι]

protected lemma adapted (h : prog_measurable f u) : adapted f u :=
begin
  intro i,
  have : u i = (λ p : set.Iic i × α, u p.1 p.2) ∘ (λ x, (⟨i, set.mem_Iic.mpr le_rfl⟩, x)) := rfl,
  rw this,
  refine @measurable.comp _ (set.Iic i × α) β (f i) (@prod.measurable_space (set.Iic i) α _ (f i))
    _ _ _ (h i) _,
  exact @measurable.prod_mk _ _ _ _ (f i) (f i) _ _
    (@measurable_const _ _ _ (f i) _) (@measurable_id _ (f i)),
end

protected lemma comp {t : ι → α → ι} (h : prog_measurable f u) (ht : prog_measurable f t)
  (ht_le : ∀ i x, t i x ≤ i) :
  prog_measurable f (λ i x, u (t i x) x) :=
begin
  intro i,
  dsimp only,
  have : (λ p : ↥(set.Iic i) × α, u (t (p.fst : ι) p.snd) p.snd)
    = (λ p : ↥(set.Iic i) × α, u (p.fst : ι) p.snd) ∘ (λ p : ↥(set.Iic i) × α,
      (⟨t (p.fst : ι) p.snd, set.mem_Iic.mpr ((ht_le _ _).trans p.fst.prop)⟩, p.snd)) := rfl,
  rw this,
  refine (h i).comp' _,
  refine measurable.prod_mk' (ht i).subtype_mk (@measurable_snd _ _ (f i) _),
end

end prog_measurable

end adapted_process

namespace filtration

/-- Given a sequence of functions, the natural filtration is the smallest sequence
of σ-algebras such that that sequence of functions is measurable with respect to
the filtration. -/
def natural (u : ι → α → β) (hum : ∀ i, measurable (u i)) : filtration ι m :=
{ seq := λ i, ⨆ j ≤ i, measurable_space.comap (u j) infer_instance,
  mono := λ i j hij, bsupr_le_bsupr' $ λ k hk, le_trans hk hij,
  le := λ i, bsupr_le (λ j hj s hs, let ⟨t, ht, ht'⟩ := hs in ht' ▸ hum j ht) }

lemma adapted_natural {u : ι → α → β} (hum : ∀ i, measurable[m] (u i)) :
  adapted (natural u hum) u :=
λ i, measurable.le (le_bsupr_of_le i (le_refl i) (le_refl _)) (λ s hs, ⟨s, hs, rfl⟩)

end filtration

/-- A stopping time with respect to some filtration `f` is a function
`τ` such that for all `i`, the preimage of `{j | j ≤ i}` along `τ` is measurable
with respect to `f i`.

Intuitively, the stopping time `τ` describes some stopping rule such that at time
`i`, we may determine it with the information we have at time `i`. -/
def is_stopping_time (f : filtration ι m) (τ : α → ι) :=
∀ i : ι, measurable_set[f i] $ {x | τ x ≤ i}

lemma is_stopping_time.measurable_set_le {f : filtration ι m} {τ : α → ι}
  (hτ : is_stopping_time f τ) (i : ι) :
  measurable_set[f i] {x | τ x ≤ i} :=
hτ i

variables {f : filtration ℕ m} {τ : α → ℕ}

lemma is_stopping_time.measurable_set_eq (hτ : is_stopping_time f τ) (i : ℕ) :
  measurable_set[f i] {x | τ x = i} :=
begin
  cases i,
  { convert (hτ 0),
    simp only [set.set_of_eq_eq_singleton, le_zero_iff] },
  { rw (_ : {x | τ x = i + 1} = {x | τ x ≤ i + 1} \ {x | τ x ≤ i}),
    { exact (hτ (i + 1)).diff (f.mono (nat.le_succ _) _ (hτ i)) },
    { ext, simp only [set.mem_diff, not_le, set.mem_set_of_eq],
      split,
      { intro h, simp [h] },
      { rintro ⟨h₁, h₂⟩,
        linarith } } }
end

lemma is_stopping_time.measurable_set_ge (hτ : is_stopping_time f τ) (i : ℕ) :
  measurable_set[f i] {x | i ≤ τ x} :=
begin
  have : {a : α | i ≤ τ a} = (set.univ \ {a | τ a ≤ i}) ∪ {a | τ a = i},
  { ext1 a,
    simp only [true_and, set.mem_univ, set.mem_diff, not_le, set.mem_union_eq,
      set.mem_set_of_eq],
    rw le_iff_lt_or_eq,
    by_cases h : τ a = i,
    { simp [h], },
    { simp only [h, ne.symm h, or_false, or_iff_left_iff_imp], }, },
  rw this,
  exact (measurable_set.univ.diff (hτ i)).union (hτ.measurable_set_eq i),
end

lemma is_stopping_time.measurable_set_eq_le
  {f : filtration ℕ m} {τ : α → ℕ} (hτ : is_stopping_time f τ) {i j : ℕ} (hle : i ≤ j) :
  measurable_set[f j] {x | τ x = i} :=
f.mono hle _ $ hτ.measurable_set_eq i

lemma is_stopping_time_of_measurable_set_eq
  {f : filtration ℕ m} {τ : α → ℕ} (hτ : ∀ i, measurable_set[f i] {x | τ x = i}) :
  is_stopping_time f τ :=
begin
  intro i,
  rw show {x | τ x ≤ i} = ⋃ k ≤ i, {x | τ x = k}, by { ext, simp },
  refine measurable_set.bUnion (set.countable_encodable _) (λ k hk, _),
  exact f.mono hk _ (hτ k),
end

lemma is_stopping_time_const {f : filtration ι m} (i : ι) :
  is_stopping_time f (λ x, i) :=
λ j, by simp

end preorder

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

lemma add_const
  [add_group ι] [preorder ι] [covariant_class ι ι (function.swap (+)) (≤)]
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
    { exact λ hx, ⟨τ x, hx, le_refl _⟩ },
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

lemma prog_measurable_min_stopping_time [measurable_space ι] [topological_space ι]
  [opens_measurable_space ι] [order_topology ι] [second_countable_topology ι] [borel_space ι]
  {τ : α → ι} {f : filtration ι m} (hτ : is_stopping_time f τ) :
  prog_measurable f (λ i x, min i (τ x)) :=
begin
  intro i,
  dsimp only,
  let s := {p : set.Iic i × α | τ p.2 ≤ i},
  have hs : measurable_set[@prod.measurable_space _ _ _ (f i)] s,
    from @measurable_snd (set.Iic i) α (f i) _ _ (hτ i),
  have h_meas_fst : ∀ t : set (set.Iic i × α),
    measurable[(@subtype.measurable_space (set.Iic i × α) _ (@prod.measurable_space _ _ _ (f i)))]
      (λ (x : ↥t), ((x : set.Iic i × α).fst : ι)),
  { refine λ t, measurable.subtype_coe _,
    refine @measurable.fst _ (set.Iic i) α _ (f i)
      (@subtype.measurable_space _ _ (@prod.measurable_space _ _ _ (f i))) _ _,
    exact @measurable_subtype_coe (set.Iic i × α) (@prod.measurable_space _ _ _ (f i)) _, },
  refine measurable_of_restrict_of_restrict_compl hs _ _,
  { rw set.restrict,
    refine measurable.min' (h_meas_fst s) _,
    refine @measurable_of_Iic ι (↥s) _ _ _ (@subtype.measurable_space _ _
      (@prod.measurable_space _ _ _ (f i))) _ _ _ _ (λ j, _),
    have h_set_eq : (λ x : ↥s, τ (x : set.Iic i × α).snd) ⁻¹' set.Iic j
      = (λ x : ↥s, (x : set.Iic i × α).snd) ⁻¹' {x | τ x ≤ min i j},
    { ext1 x,
      simp only [set.mem_preimage, set.mem_Iic, iff_and_self, le_min_iff, set.mem_set_of_eq],
      exact λ _, x.prop, },
    rw h_set_eq,
    have h_meas : @measurable _ _
      (@subtype.measurable_space _ _ (@prod.measurable_space _ _ _ (f i))) (f i)
      (λ x : ↥s, (x : set.Iic i × α).snd),
    { have : (λ x : ↥s, (x : set.Iic i × α).snd) = prod.snd ∘ (λ x : ↥s, (x : set.Iic i × α)),
        from rfl,
      rw this,
      have h_coe_meas : @measurable _ _
          (@subtype.measurable_space _ _ (@prod.measurable_space _ _ _ (f i)))
          (@prod.measurable_space _ _ _ (f i)) (λ x : ↥s, (x : set.Iic i × α)),
        from @measurable_subtype_coe _ (@prod.measurable_space _ _ _ (f i)) _,
      exact (@measurable_snd _ _ (f i) _).comp' h_coe_meas, },
    exact h_meas (f.mono (min_le_left _ _) _ (hτ.measurable_set_le (min i j))), },
  { rw set.restrict,
    have h_min_eq_left : (λ x : ↥sᶜ, min ↑((x : set.Iic i × α).fst) (τ (x : set.Iic i × α).snd))
      = (λ x : ↥sᶜ, ↑((x : set.Iic i × α).fst)),
    { ext1 x,
      rw min_eq_left,
      have hx_fst_le : ↑(x : set.Iic i × α).fst ≤ i, from (x : set.Iic i × α).fst.prop,
      refine hx_fst_le.trans (le_of_lt _),
      convert x.prop,
      simp only [not_le, set.mem_compl_eq, set.mem_set_of_eq], },
    rw h_min_eq_left,
    exact h_meas_fst _, },
end

lemma prog_measurable_stopped_process [measurable_space ι] [topological_space ι]
  [opens_measurable_space ι] [order_topology ι] [second_countable_topology ι] [borel_space ι]
  [measurable_space β]
  {u : ι → α → β} {τ : α → ι} {f : filtration ι m}
  (h : prog_measurable f u) (hτ : is_stopping_time f τ) :
  prog_measurable f (stopped_process u τ) :=
h.comp (prog_measurable_min_stopping_time hτ) (λ i x, min_le_left _ _)

lemma adapted_stopped_process [measurable_space ι] [topological_space ι]
  [opens_measurable_space ι] [order_topology ι] [second_countable_topology ι] [borel_space ι]
  [measurable_space β]
  {u : ι → α → β} {τ : α → ι} {f : filtration ι m}
  (h : prog_measurable f u) (hτ : is_stopping_time f τ) :
  adapted f (stopped_process u τ) :=
(prog_measurable_stopped_process h hτ).adapted

-- We will need cadlag to generalize the following to continuous processes
section nat

open filtration

variables {f : filtration ℕ m} {u : ℕ → α → β} {τ : α → ℕ}

section add_comm_monoid

variables [add_comm_monoid β]

lemma adapted.prog_measurable [measurable_space β] [has_measurable_add₂ β]
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
  { suffices h_meas : measurable[@prod.measurable_space _ _ _ (f i)]
        (λ a : ↥(set.Iic i) × α, (a.fst : ℕ)),
      from h_meas (measurable_set_singleton j),
    exact (@measurable_fst _ α (f i) _).subtype_coe, },
  { have h_le : j ≤ i, from finset.mem_range_succ_iff.mp hj,
    exact (measurable.le (f.mono h_le) (h j)).comp (@measurable_snd _ α (f i) _), },
  { exact @measurable_const _ (set.Iic i × α) _ (@prod.measurable_space _ _ _ (f i)) _, },
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

instance {α} [topological_space α] [encodable α] : separable_space α :=
{ exists_countable_dense := ⟨set.univ, set.countable_encodable set.univ, dense_univ⟩ }

lemma filter.is_countably_generated_pure {α} (a : α) : filter.is_countably_generated (pure a) :=
by { rw ← filter.principal_singleton, exact filter.is_countably_generated_principal _, }

instance discrete_topology.first_countable_topology {α} [topological_space α]
  [discrete_topology α] :
  first_countable_topology α :=
{ nhds_generated_countable :=
    by { rw nhds_discrete, exact λ a, filter.is_countably_generated_pure _, } }

instance discrete_topology.second_countable_topology_of_encodable {α} [topological_space α]
  [hd : discrete_topology α] [encodable α] :
  second_countable_topology α :=
begin
  haveI : ∀ (i : α), second_countable_topology ↥({i} : set α),
    from λ i, { is_open_generated_countable :=
      ⟨{set.univ}, set.countable_singleton _, by simp only [eq_iff_true_of_subsingleton]⟩, },
  have h_open : ∀ (i : α), is_open ({i} : set α), from λ i, is_open_discrete _,
  exact second_countable_topology_of_countable_cover h_open (set.Union_of_singleton α),
end

lemma is_open_generate_from_of_mem {α} [topological_space α] {S : set (set α)} {s : set α}
  (hs : s ∈ S) :
  (generate_from S).is_open s :=
generate_open.basic s hs

lemma lt_succ_of_exists_lt {α} [preorder α] [succ_order α] {a : α} (ha : ∃ b, a < b) :
  a < succ_order.succ a :=
(succ_order.le_succ a).lt_of_not_le (λ h, not_exists.2 (succ_order.maximal_of_succ_le h) ha)

lemma lt_succ_iff_of_exists_lt {α} [preorder α] [succ_order α] {a b : α} (ha : ∃ b, a < b) :
  b < succ_order.succ a ↔ b ≤ a :=
⟨succ_order.le_of_lt_succ, λ h_le, h_le.trans_lt (lt_succ_of_exists_lt ha)⟩

lemma pred_lt_of_exists_lt {α} [preorder α] [pred_order α] {a : α} (ha : ∃ b, b < a) :
  pred_order.pred a < a :=
(pred_order.pred_le a).lt_of_not_le (λ h, not_exists.2 (pred_order.minimal_of_le_pred h) ha)

lemma pred_lt_iff_of_exists_lt {α} [preorder α] [pred_order α] {a b : α} (ha : ∃ b, b < a) :
  pred_order.pred a < b ↔ a ≤ b :=
⟨pred_order.le_of_pred_lt, λ h_le, (pred_lt_of_exists_lt ha).trans_le h_le⟩

lemma Iic_eq_Iio_succ {α} [preorder α] [succ_order α] [no_top_order α] (a : α) :
  set.Iic a = set.Iio (succ_order.succ a) :=
by { ext1 x, rw [set.mem_Iic, set.mem_Iio], exact succ_order.lt_succ_iff.symm, }

lemma Iic_eq_Iio_succ' {α} [preorder α] [succ_order α] {a : α} (ha : ∃ b, a < b) :
  set.Iic a = set.Iio (succ_order.succ a) :=
by { ext1 x, rw [set.mem_Iic, set.mem_Iio], exact (lt_succ_iff_of_exists_lt ha).symm, }

lemma Ici_succ_eq_Ioi {α} [preorder α] [succ_order α] [no_top_order α] (a : α) :
  set.Ici (succ_order.succ a) = set.Ioi a :=
by { ext1 x, rw [set.mem_Ici, set.mem_Ioi], exact succ_order.succ_le_iff, }

lemma Ici_eq_Ioi_pred {α} [preorder α] [pred_order α] [no_bot_order α] (a : α) :
  set.Ici a = set.Ioi (pred_order.pred a) :=
by { ext1 x, rw [set.mem_Ici, set.mem_Ioi], exact pred_order.pred_lt_iff.symm, }

lemma Ici_eq_Ioi_pred' {α} [preorder α] [pred_order α] {a : α} (ha : ∃ b, b < a) :
  set.Ici a = set.Ioi (pred_order.pred a) :=
by { ext1 x, rw [set.mem_Ici, set.mem_Ioi], exact (pred_lt_iff_of_exists_lt ha).symm, }

instance todo {α} [topological_space α] [h : discrete_topology α] [partial_order α] [succ_order α]
  [pred_order α] [no_top_order α] [no_bot_order α] :
  order_topology α :=
begin
  constructor,
  rw h.eq_bot,
  refine (eq_bot_of_singletons_open (λ a, _)).symm,
  have h_singleton_eq_inter : {a} = set.Iio (succ_order.succ a) ∩ set.Ioi (pred_order.pred a),
  { suffices h_singleton_eq_inter' : {a} = set.Iic a ∩ set.Ici a,
      by rw [h_singleton_eq_inter', Ici_eq_Ioi_pred, Iic_eq_Iio_succ],
    rw [set.inter_comm, set.Ici_inter_Iic, set.Icc_self a], },
  rw h_singleton_eq_inter,
  refine @is_open.inter _ _ _ (generate_from {s : set α | ∃ a, s = set.Ioi a ∨ s = set.Iio a}) _ _,
  { exact is_open_generate_from_of_mem ⟨succ_order.succ a, or.inr rfl⟩, },
  { exact is_open_generate_from_of_mem ⟨pred_order.pred a, or.inl rfl⟩, },
end

instance {α} [topological_space α] [h : discrete_topology α] [linear_order α] [succ_order α]
  [pred_order α] :
  order_topology α :=
begin
  constructor,
  rw h.eq_bot,
  refine (eq_bot_of_singletons_open (λ a, _)).symm,
  have h_singleton_eq_inter : {a} = set.Iic a ∩ set.Ici a,
    by rw [set.inter_comm, set.Ici_inter_Iic, set.Icc_self a],
  have h_Iic_eq_univ_of_top : (∀ b, b ≤ a) → set.Iic a = set.univ,
  { intros ha_top, ext1 x, simp [ha_top x], },
  have h_Ici_eq_univ_of_bot : (∀ b, a ≤ b) → set.Ici a = set.univ,
  { intros ha_bot, ext1 x, simp [ha_bot x], },
  by_cases ha_top : ∃ b, a < b,
  { rw Iic_eq_Iio_succ' ha_top at h_singleton_eq_inter,
    by_cases ha_bot : ∃ b, b < a,
    { rw Ici_eq_Ioi_pred' ha_bot at h_singleton_eq_inter,
      rw h_singleton_eq_inter,
      refine @is_open.inter _ _ _
        (generate_from {s : set α | ∃ a, s = set.Ioi a ∨ s = set.Iio a}) _ _,
      { exact is_open_generate_from_of_mem ⟨succ_order.succ a, or.inr rfl⟩, },
      { exact is_open_generate_from_of_mem ⟨pred_order.pred a, or.inl rfl⟩, }, },
    { push_neg at ha_bot,
      rw [h_Ici_eq_univ_of_bot ha_bot, set.inter_univ] at h_singleton_eq_inter,
      rw h_singleton_eq_inter,
      exact is_open_generate_from_of_mem ⟨succ_order.succ a, or.inr rfl⟩, }, },
  { push_neg at ha_top,
    rw [h_Iic_eq_univ_of_top ha_top, set.inter_comm, set.inter_univ] at h_singleton_eq_inter,
    by_cases ha_bot : ∃ b, b < a,
    { rw Ici_eq_Ioi_pred' ha_bot at h_singleton_eq_inter,
      rw h_singleton_eq_inter,
      exact is_open_generate_from_of_mem ⟨pred_order.pred a, or.inl rfl⟩, },
    { push_neg at ha_bot,
      rw h_Ici_eq_univ_of_bot ha_bot at h_singleton_eq_inter,
      rw h_singleton_eq_inter,
      exact @is_open_univ _ (generate_from {s : set α | ∃ a, s = set.Ioi a ∨ s = set.Iio a}), }, },
end

lemma adapted.stopped_process [measurable_space β] [has_measurable_add₂ β]
  (hu : adapted f u) (hτ : is_stopping_time f τ) :
  adapted f (stopped_process u τ) :=
(prog_measurable_stopped_process hu.prog_measurable hτ).adapted

end add_comm_monoid

section normed_group

variables [measurable_space β] [normed_group β] [has_measurable_add₂ β]

lemma measurable_stopped_process (hτ : is_stopping_time f τ) (hu : adapted f u) (n : ℕ) :
  measurable (stopped_process u τ n) :=
(hu.stopped_process hτ n).le (f.le _)

lemma mem_ℒp_stopped_process {p : ℝ≥0∞} [borel_space β] {μ : measure α} (hτ : is_stopping_time f τ)
  (hu : ∀ n, mem_ℒp (u n) p μ) (n : ℕ) :
  mem_ℒp (stopped_process u τ n) p μ :=
begin
  rw stopped_process_eq,
  refine mem_ℒp.add _ _,
  { exact mem_ℒp.indicator (f.le n {a : α | n ≤ τ a} (hτ.measurable_set_ge n)) (hu n), },
  { suffices : mem_ℒp (λ x, ∑ (i : ℕ) in finset.range n, {a : α | τ a = i}.indicator (u i) x) p μ,
      by { convert this, ext1 x, simp only [finset.sum_apply], },
    refine mem_ℒp_finset_sum _ (λ i hi, mem_ℒp.indicator _ (hu i)),
    exact f.le i {a : α | τ a = i} (hτ.measurable_set_eq i) },
end

lemma integrable_stopped_process [borel_space β] {μ : measure α} (hτ : is_stopping_time f τ)
  (hu : ∀ n, integrable (u n) μ) (n : ℕ) :
  integrable (stopped_process u τ n) μ :=
begin
  simp_rw ← mem_ℒp_one_iff_integrable at hu ⊢,
  exact mem_ℒp_stopped_process hτ hu n,
end

end normed_group

end nat

end linear_order

end measure_theory
