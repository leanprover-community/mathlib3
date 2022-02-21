/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import measure_theory.constructions.borel_space
import measure_theory.function.l1_space

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
* `measure_theory.is_stopping_time`: a stopping time with respect to some filtration `f` is a
  function `τ` such that for all `i`, the preimage of `{j | j ≤ i}` along `τ` is
  `f i`-measurable
* `measure_theory.is_stopping_time.measurable_space`: the σ-algebra associated with a stopping time

## Tags

filtration, stopping time, stochastic process

-/

open topological_space
open_locale classical measure_theory nnreal ennreal topological_space big_operators

namespace measure_theory

/-- A `filtration` on measurable space `α` with σ-algebra `m` is a monotone
sequence of of sub-σ-algebras of `m`. -/
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

/-- The constant filtration which is equal to `m` for all `i : ι`. -/
def const (m' : measurable_space α) (hm' : m' ≤ m) : filtration ι m :=
⟨λ _, m', monotone_const, λ _, hm'⟩

instance : inhabited (filtration ι m) := ⟨const m le_rfl⟩

instance : has_le (filtration ι m) := ⟨λ f g, ∀ i, f i ≤ g i⟩

instance : has_bot (filtration ι m) := ⟨const ⊥ bot_le⟩

instance : has_top (filtration ι m) := ⟨const m le_rfl⟩

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

section preorder
variables [preorder ι]

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

variable [measurable_space β]

/-- A sequence of functions `u` is adapted to a filtration `f` if for all `i`,
`u i` is `f i`-measurable. -/
def adapted (f : filtration ι m) (u : ι → α → β) : Prop :=
∀ i : ι, measurable[f i] (u i)

namespace adapted

lemma add [has_add β] [has_measurable_add₂ β] {u v : ι → α → β} {f : filtration ι m}
  (hu : adapted f u) (hv : adapted f v) : adapted f (u + v) :=
λ i, @measurable.add _ _ _ _ (f i) _ _ _ (hu i) (hv i)

lemma neg [has_neg β] [has_measurable_neg β] {u : ι → α → β} {f : filtration ι m}
  (hu : adapted f u) : adapted f (-u) :=
λ i, @measurable.neg _ α _ _ _ (f i) _ (hu i)

lemma smul [has_scalar ℝ β] [has_measurable_smul ℝ β] {u : ι → α → β} {f : filtration ι m}
  (c : ℝ) (hu : adapted f u) : adapted f (c • u) :=
λ i, @measurable.const_smul ℝ β α _ _ _ (f i) _ _ (hu i) c

end adapted

variable (β)

lemma adapted_zero [has_zero β] (f : filtration ι m) : adapted f (0 : ι → α → β) :=
λ i, @measurable_zero β α (f i) _ _

variable {β}

namespace filtration

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

/-- A stopping time with respect to some filtration `f` is a function
`τ` such that for all `i`, the preimage of `{j | j ≤ i}` along `τ` is measurable
with respect to `f i`.

Intuitively, the stopping time `τ` describes some stopping rule such that at time
`i`, we may determine it with the information we have at time `i`. -/
def is_stopping_time (f : filtration ι m) (τ : α → ι) :=
∀ i : ι, measurable_set[f i] $ {x | τ x ≤ i}

variables {f : filtration ℕ m} {τ : α → ℕ}

lemma is_stopping_time.measurable_set_le (hτ : is_stopping_time f τ) (i : ℕ) :
  measurable_set[f i] {x | τ x ≤ i} :=
hτ i

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

lemma is_stopping_time.measurable_set_lt (hτ : is_stopping_time f τ) (i : ℕ) :
  measurable_set[f i] {x | τ x < i} :=
begin
  convert (hτ i).diff (hτ.measurable_set_eq i),
  ext,
  change τ x < i ↔ τ x ≤ i ∧ τ x ≠ i,
  rw lt_iff_le_and_ne,
end

lemma is_stopping_time.measurable_set_lt_le
  (hτ : is_stopping_time f τ) {i j : ℕ} (hle : i ≤ j) :
  measurable_set[f j] {x | τ x < i} :=
f.mono hle _ $ hτ.measurable_set_lt i

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

lemma max [linear_order ι] {f : filtration ι m} {τ π : α → ι}
  (hτ : is_stopping_time f τ) (hπ : is_stopping_time f π) :
  is_stopping_time f (λ x, max (τ x) (π x)) :=
begin
  intro i,
  simp_rw [max_le_iff, set.set_of_and],
  exact (hτ i).inter (hπ i),
end

lemma min [linear_order ι] {f : filtration ι m} {τ π : α → ι}
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
  rw (_ : {x | τ x ≤ i} ∩ {x | τ x ≤ j} = {x | τ x ≤ linear_order.min i j}),
  { exact f.mono (min_le_right i j) _ (hτ (linear_order.min i j)) },
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
λ i x, u (linear_order.min i (τ x)) x

lemma stopped_process_eq_of_le {u : ι → α → β} {τ : α → ι}
  {i : ι} {x : α} (h : i ≤ τ x) : stopped_process u τ i x = u i x :=
by simp [stopped_process, min_eq_left h]

lemma stopped_process_eq_of_ge {u : ι → α → β} {τ : α → ι}
  {i : ι} {x : α} (h : τ x ≤ i) : stopped_process u τ i x = u (τ x) x :=
by simp [stopped_process, min_eq_right h]

-- We will need cadlag to generalize the following to continuous processes
section nat

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

lemma adapted.stopped_process [measurable_space β] [has_measurable_add₂ β]
  (hu : adapted f u) (hτ : is_stopping_time f τ) :
  adapted f (stopped_process u τ) :=
begin
  intro i,
  rw stopped_process_eq,
  refine @measurable.add _ _ _ _ (f i) _ _ _ _ _,
  { refine (hu i).indicator _,
    convert measurable_set.union (hτ i).compl (hτ.measurable_set_eq i),
    ext x,
    change i ≤ τ x ↔ ¬ τ x ≤ i ∨ τ x = i,
    rw [not_le, le_iff_lt_or_eq, eq_comm] },
  { refine @finset.measurable_sum' _ _ _ _ _ _ (f i) _ _ _,
    refine λ j hij, measurable.indicator _ _,
    { rw finset.mem_range at hij,
      exact measurable.le (f.mono hij.le) (hu j) },
    { rw finset.mem_range at hij,
      refine f.mono hij.le _ _,
      convert hτ.measurable_set_eq j, } }
end

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
  { exact mem_ℒp.indicator (f.le n {a : α | n ≤ τ a} (hτ.measurable_set_ge n)) (hu n) },
  { suffices : mem_ℒp (λ x, ∑ (i : ℕ) in finset.range n, {a : α | τ a = i}.indicator (u i) x) p μ,
    { convert this, ext1 x, simp only [finset.sum_apply] },
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

lemma mem_ℒp_stopped_value {p : ℝ≥0∞} [borel_space β] {μ : measure α} (hτ : is_stopping_time f τ)
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

lemma integrable_stopped_value [borel_space β] {μ : measure α} (hτ : is_stopping_time f τ)
  (hu : ∀ n, integrable (u n) μ) {N : ℕ} (hbdd : ∀ x, τ x ≤ N) :
  integrable (stopped_value u τ) μ :=
begin
  simp_rw ← mem_ℒp_one_iff_integrable at hu ⊢,
  exact mem_ℒp_stopped_value hτ hu hbdd,
end

end normed_group

end nat

end linear_order

end measure_theory
