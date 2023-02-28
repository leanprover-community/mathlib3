/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
import algebra.big_operators.intervals
import algebra.big_operators.order
import algebra.indicator_function
import order.liminf_limsup
import order.filter.archimedean
import topology.order.basic

/-!
# Lemmas about liminf and limsup in an order topology.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

open filter
open_locale topology classical

universes u v
variables {α : Type u} {β : Type v}

section liminf_limsup

section order_closed_topology
variables [semilattice_sup α] [topological_space α] [order_topology α]

lemma is_bounded_le_nhds (a : α) : (𝓝 a).is_bounded (≤) :=
(is_top_or_exists_gt a).elim (λ h, ⟨a, eventually_of_forall h⟩) (λ ⟨b, hb⟩, ⟨b, ge_mem_nhds hb⟩)

lemma filter.tendsto.is_bounded_under_le {f : filter β} {u : β → α} {a : α}
  (h : tendsto u f (𝓝 a)) : f.is_bounded_under (≤) u :=
(is_bounded_le_nhds a).mono h

lemma filter.tendsto.bdd_above_range_of_cofinite {u : β → α} {a : α}
  (h : tendsto u cofinite (𝓝 a)) : bdd_above (set.range u) :=
h.is_bounded_under_le.bdd_above_range_of_cofinite

lemma filter.tendsto.bdd_above_range {u : ℕ → α} {a : α}
  (h : tendsto u at_top (𝓝 a)) : bdd_above (set.range u) :=
h.is_bounded_under_le.bdd_above_range

lemma is_cobounded_ge_nhds (a : α) : (𝓝 a).is_cobounded (≥) :=
(is_bounded_le_nhds a).is_cobounded_flip

lemma filter.tendsto.is_cobounded_under_ge {f : filter β} {u : β → α} {a : α}
  [ne_bot f] (h : tendsto u f (𝓝 a)) : f.is_cobounded_under (≥) u :=
h.is_bounded_under_le.is_cobounded_flip

lemma is_bounded_le_at_bot (α : Type*) [hα : nonempty α] [preorder α] :
  (at_bot : filter α).is_bounded (≤) :=
is_bounded_iff.2 ⟨set.Iic hα.some, mem_at_bot _, hα.some, λ x hx, hx⟩

lemma filter.tendsto.is_bounded_under_le_at_bot {α : Type*} [nonempty α] [preorder α]
  {f : filter β} {u : β → α} (h : tendsto u f at_bot) :
  f.is_bounded_under (≤) u :=
(is_bounded_le_at_bot α).mono h

lemma bdd_above_range_of_tendsto_at_top_at_bot {α : Type*} [nonempty α] [semilattice_sup α]
  {u : ℕ → α} (hx : tendsto u at_top at_bot) : bdd_above (set.range u) :=
(filter.tendsto.is_bounded_under_le_at_bot hx).bdd_above_range

end order_closed_topology

section order_closed_topology
variables [semilattice_inf α] [topological_space α] [order_topology α]

lemma is_bounded_ge_nhds (a : α) : (𝓝 a).is_bounded (≥) := @is_bounded_le_nhds αᵒᵈ _ _ _ a

lemma filter.tendsto.is_bounded_under_ge {f : filter β} {u : β → α} {a : α}
  (h : tendsto u f (𝓝 a)) : f.is_bounded_under (≥) u :=
(is_bounded_ge_nhds a).mono h

lemma filter.tendsto.bdd_below_range_of_cofinite {u : β → α} {a : α}
  (h : tendsto u cofinite (𝓝 a)) : bdd_below (set.range u) :=
h.is_bounded_under_ge.bdd_below_range_of_cofinite

lemma filter.tendsto.bdd_below_range {u : ℕ → α} {a : α}
  (h : tendsto u at_top (𝓝 a)) : bdd_below (set.range u) :=
h.is_bounded_under_ge.bdd_below_range

lemma is_cobounded_le_nhds (a : α) : (𝓝 a).is_cobounded (≤) :=
(is_bounded_ge_nhds a).is_cobounded_flip

lemma filter.tendsto.is_cobounded_under_le {f : filter β} {u : β → α} {a : α}
  [ne_bot f] (h : tendsto u f (𝓝 a)) : f.is_cobounded_under (≤) u :=
h.is_bounded_under_ge.is_cobounded_flip

lemma is_bounded_ge_at_top (α : Type*) [hα : nonempty α] [preorder α] :
  (at_top : filter α).is_bounded (≥) :=
is_bounded_le_at_bot αᵒᵈ

lemma filter.tendsto.is_bounded_under_ge_at_top {α : Type*} [nonempty α] [preorder α]
  {f : filter β} {u : β → α} (h : tendsto u f at_top) :
  f.is_bounded_under (≥) u :=
(is_bounded_ge_at_top α).mono h

lemma bdd_below_range_of_tendsto_at_top_at_top {α : Type*} [nonempty α] [semilattice_inf α]
  {u : ℕ → α} (hx : tendsto u at_top at_top) : bdd_below (set.range u) :=
(filter.tendsto.is_bounded_under_ge_at_top hx).bdd_below_range

end order_closed_topology

section conditionally_complete_linear_order
variables [conditionally_complete_linear_order α]

theorem lt_mem_sets_of_Limsup_lt {f : filter α} {b} (h : f.is_bounded (≤)) (l : f.Limsup < b) :
  ∀ᶠ a in f, a < b :=
let ⟨c, (h : ∀ᶠ a in f, a ≤ c), hcb⟩ := exists_lt_of_cInf_lt h l in
mem_of_superset h $ assume a hac, lt_of_le_of_lt hac hcb

theorem gt_mem_sets_of_Liminf_gt : ∀ {f : filter α} {b}, f.is_bounded (≥) → b < f.Liminf →
  ∀ᶠ a in f, b < a :=
@lt_mem_sets_of_Limsup_lt αᵒᵈ _

variables [topological_space α] [order_topology α]

/-- If the liminf and the limsup of a filter coincide, then this filter converges to
their common value, at least if the filter is eventually bounded above and below. -/
theorem le_nhds_of_Limsup_eq_Liminf {f : filter α} {a : α}
  (hl : f.is_bounded (≤)) (hg : f.is_bounded (≥)) (hs : f.Limsup = a) (hi : f.Liminf = a) :
  f ≤ 𝓝 a :=
tendsto_order.2 $ and.intro
  (assume b hb, gt_mem_sets_of_Liminf_gt hg $ hi.symm ▸ hb)
  (assume b hb, lt_mem_sets_of_Limsup_lt hl $ hs.symm ▸ hb)

theorem Limsup_nhds (a : α) : Limsup (𝓝 a) = a :=
cInf_eq_of_forall_ge_of_forall_gt_exists_lt (is_bounded_le_nhds a)
  (assume a' (h : {n : α | n ≤ a'} ∈ 𝓝 a), show a ≤ a', from @mem_of_mem_nhds α _ a _ h)
  (assume b (hba : a < b), show ∃c (h : {n : α | n ≤ c} ∈ 𝓝 a), c < b, from
    match dense_or_discrete a b with
    | or.inl ⟨c, hac, hcb⟩ := ⟨c, ge_mem_nhds hac, hcb⟩
    | or.inr ⟨_, h⟩        := ⟨a, (𝓝 a).sets_of_superset (gt_mem_nhds hba) h, hba⟩
    end)

theorem Liminf_nhds : ∀ (a : α), Liminf (𝓝 a) = a := @Limsup_nhds αᵒᵈ _ _ _

/-- If a filter is converging, its limsup coincides with its limit. -/
theorem Liminf_eq_of_le_nhds {f : filter α} {a : α} [ne_bot f] (h : f ≤ 𝓝 a) : f.Liminf = a :=
have hb_ge : is_bounded (≥) f, from (is_bounded_ge_nhds a).mono h,
have hb_le : is_bounded (≤) f, from (is_bounded_le_nhds a).mono h,
le_antisymm
  (calc f.Liminf ≤ f.Limsup : Liminf_le_Limsup hb_le hb_ge
    ... ≤ (𝓝 a).Limsup :
      Limsup_le_Limsup_of_le h hb_ge.is_cobounded_flip (is_bounded_le_nhds a)
    ... = a : Limsup_nhds a)
  (calc a = (𝓝 a).Liminf : (Liminf_nhds a).symm
    ... ≤ f.Liminf :
      Liminf_le_Liminf_of_le h (is_bounded_ge_nhds a) hb_le.is_cobounded_flip)

/-- If a filter is converging, its liminf coincides with its limit. -/
theorem Limsup_eq_of_le_nhds : ∀ {f : filter α} {a : α} [ne_bot f], f ≤ 𝓝 a → f.Limsup = a :=
@Liminf_eq_of_le_nhds αᵒᵈ _ _ _

/-- If a function has a limit, then its limsup coincides with its limit. -/
theorem filter.tendsto.limsup_eq {f : filter β} {u : β → α} {a : α} [ne_bot f]
  (h : tendsto u f (𝓝 a)) : limsup u f = a :=
Limsup_eq_of_le_nhds h

/-- If a function has a limit, then its liminf coincides with its limit. -/
theorem filter.tendsto.liminf_eq {f : filter β} {u : β → α} {a : α} [ne_bot f]
  (h : tendsto u f (𝓝 a)) : liminf u f = a :=
Liminf_eq_of_le_nhds h

/-- If the liminf and the limsup of a function coincide, then the limit of the function
exists and has the same value -/
theorem tendsto_of_liminf_eq_limsup {f : filter β} {u : β → α} {a : α}
  (hinf : liminf u f = a) (hsup : limsup u f = a)
  (h : f.is_bounded_under (≤) u . is_bounded_default)
  (h' : f.is_bounded_under (≥) u . is_bounded_default) :
  tendsto u f (𝓝 a) :=
le_nhds_of_Limsup_eq_Liminf h h' hsup hinf

/-- If a number `a` is less than or equal to the `liminf` of a function `f` at some filter
and is greater than or equal to the `limsup` of `f`, then `f` tends to `a` along this filter. -/
theorem tendsto_of_le_liminf_of_limsup_le {f : filter β} {u : β → α} {a : α}
  (hinf : a ≤ liminf u f) (hsup : limsup u f ≤ a)
  (h : f.is_bounded_under (≤) u . is_bounded_default)
  (h' : f.is_bounded_under (≥) u . is_bounded_default) :
  tendsto u f (𝓝 a) :=
if hf : f = ⊥ then hf.symm ▸ tendsto_bot
else by haveI : ne_bot f := ⟨hf⟩; exact tendsto_of_liminf_eq_limsup
  (le_antisymm (le_trans (liminf_le_limsup h h') hsup) hinf)
  (le_antisymm hsup (le_trans hinf (liminf_le_limsup h h'))) h h'

/-- Assume that, for any `a < b`, a sequence can not be infinitely many times below `a` and
above `b`. If it is also ultimately bounded above and below, then it has to converge. This even
works if `a` and `b` are restricted to a dense subset.
-/
lemma tendsto_of_no_upcrossings [densely_ordered α]
  {f : filter β} {u : β → α} {s : set α} (hs : dense s)
  (H : ∀ (a ∈ s) (b ∈ s), a < b → ¬((∃ᶠ n in f, u n < a) ∧ (∃ᶠ n in f, b < u n)))
  (h : f.is_bounded_under (≤) u . is_bounded_default)
  (h' : f.is_bounded_under (≥) u . is_bounded_default) :
  ∃ (c : α), tendsto u f (𝓝 c) :=
begin
  by_cases hbot : f = ⊥, { rw hbot, exact ⟨Inf ∅, tendsto_bot⟩ },
  haveI : ne_bot f := ⟨hbot⟩,
  refine ⟨limsup u f, _⟩,
  apply tendsto_of_le_liminf_of_limsup_le _ le_rfl h h',
  by_contra' hlt,
  obtain ⟨a, ⟨⟨la, au⟩, as⟩⟩ : ∃ a, (f.liminf u < a ∧ a < f.limsup u) ∧ a ∈ s :=
    dense_iff_inter_open.1 hs (set.Ioo (f.liminf u) (f.limsup u)) is_open_Ioo
    (set.nonempty_Ioo.2 hlt),
  obtain ⟨b, ⟨⟨ab, bu⟩, bs⟩⟩ : ∃ b, (a < b ∧ b < f.limsup u) ∧ b ∈ s :=
    dense_iff_inter_open.1 hs (set.Ioo a (f.limsup u)) is_open_Ioo
    (set.nonempty_Ioo.2 au),
  have A : ∃ᶠ n in f, u n < a :=
    frequently_lt_of_liminf_lt (is_bounded.is_cobounded_ge h) la,
  have B : ∃ᶠ n in f, b < u n :=
    frequently_lt_of_lt_limsup (is_bounded.is_cobounded_le h') bu,
  exact H a as b bs ab ⟨A, B⟩,
end

end conditionally_complete_linear_order

end liminf_limsup

section monotone

variables {ι R S : Type*} {F : filter ι} [ne_bot F]
  [complete_linear_order R] [topological_space R] [order_topology R]
  [complete_linear_order S] [topological_space S] [order_topology S]

/-- An antitone function between complete linear ordered spaces sends a `filter.Limsup`
to the `filter.liminf` of the image if it is continuous at the `Limsup`. -/
lemma antitone.map_Limsup_of_continuous_at {F : filter R} [ne_bot F]
  {f : R → S} (f_decr : antitone f) (f_cont : continuous_at f (F.Limsup)) :
  f (F.Limsup) = F.liminf f :=
begin
  apply le_antisymm,
  { have A : {a : R | ∀ᶠ (n : R) in F, n ≤ a}.nonempty, from ⟨⊤, by simp⟩,
    rw [Limsup, (f_decr.map_Inf_of_continuous_at' f_cont A)],
    apply le_of_forall_lt,
    assume c hc,
    simp only [liminf, Liminf, lt_Sup_iff, eventually_map, set.mem_set_of_eq, exists_prop,
      set.mem_image, exists_exists_and_eq_and] at hc ⊢,
    rcases hc with ⟨d, hd, h'd⟩,
    refine ⟨f d, _, h'd⟩,
    filter_upwards [hd] with x hx using f_decr hx },
  { rcases eq_or_lt_of_le (bot_le : ⊥ ≤ F.Limsup) with h|Limsup_ne_bot,
    { rw ← h,
      apply liminf_le_of_frequently_le,
      apply frequently_of_forall,
      assume x,
      exact f_decr bot_le },
    by_cases h' : ∃ c, c < F.Limsup ∧ set.Ioo c F.Limsup = ∅,
    { rcases h' with ⟨c, c_lt, hc⟩,
      have B : ∃ᶠ n in F, F.Limsup ≤ n,
      { apply (frequently_lt_of_lt_Limsup (by is_bounded_default) c_lt).mono,
        assume x hx,
        by_contra',
        have : (set.Ioo c F.Limsup).nonempty := ⟨x, ⟨hx, this⟩⟩,
        simpa [hc] },
      apply liminf_le_of_frequently_le,
      exact B.mono (λ x hx, f_decr hx) },
    by_contra' H,
    obtain ⟨l, l_lt, h'l⟩ : ∃ l < F.Limsup, set.Ioc l F.Limsup ⊆ {x : R | f x < F.liminf f},
      from exists_Ioc_subset_of_mem_nhds ((tendsto_order.1 f_cont.tendsto).2 _ H)
        ⟨⊥, Limsup_ne_bot⟩,
    obtain ⟨m, l_m, m_lt⟩  : (set.Ioo l F.Limsup).nonempty,
    { contrapose! h',
      refine ⟨l, l_lt, by rwa set.not_nonempty_iff_eq_empty at h'⟩ },
    have B : F.liminf f ≤ f m,
    { apply liminf_le_of_frequently_le,
      apply (frequently_lt_of_lt_Limsup (by is_bounded_default) m_lt).mono,
      assume x hx,
      exact f_decr hx.le },
    have I : f m < F.liminf f := h'l ⟨l_m, m_lt.le⟩,
    exact lt_irrefl _ (B.trans_lt I) }
end

/-- A continuous antitone function between complete linear ordered spaces sends a `filter.limsup`
to the `filter.liminf` of the images. -/
lemma antitone.map_limsup_of_continuous_at
  {f : R → S} (f_decr : antitone f) (a : ι → R) (f_cont : continuous_at f (F.limsup a)) :
  f (F.limsup a) = F.liminf (f ∘ a) :=
f_decr.map_Limsup_of_continuous_at f_cont

/-- An antitone function between complete linear ordered spaces sends a `filter.Liminf`
to the `filter.limsup` of the image if it is continuous at the `Liminf`. -/
lemma antitone.map_Liminf_of_continuous_at {F : filter R} [ne_bot F]
  {f : R → S} (f_decr : antitone f) (f_cont : continuous_at f (F.Liminf)) :
  f (F.Liminf) = F.limsup f :=
@antitone.map_Limsup_of_continuous_at
  (order_dual R) (order_dual S) _ _ _ _ _ _ _ _ f f_decr.dual f_cont

/-- A continuous antitone function between complete linear ordered spaces sends a `filter.liminf`
to the `filter.limsup` of the images. -/
lemma antitone.map_liminf_of_continuous_at
  {f : R → S} (f_decr : antitone f) (a : ι → R) (f_cont : continuous_at f (F.liminf a)) :
  f (F.liminf a) = F.limsup (f ∘ a) :=
f_decr.map_Liminf_of_continuous_at f_cont

/-- A monotone function between complete linear ordered spaces sends a `filter.Limsup`
to the `filter.limsup` of the image if it is continuous at the `Limsup`. -/
lemma monotone.map_Limsup_of_continuous_at {F : filter R} [ne_bot F]
  {f : R → S} (f_incr : monotone f) (f_cont : continuous_at f (F.Limsup)) :
  f (F.Limsup) = F.limsup f :=
@antitone.map_Limsup_of_continuous_at R (order_dual S) _ _ _ _ _ _ _ _ f f_incr f_cont

/-- A continuous monotone function between complete linear ordered spaces sends a `filter.limsup`
to the `filter.limsup` of the images. -/
lemma monotone.map_limsup_of_continuous_at
  {f : R → S} (f_incr : monotone f) (a : ι → R) (f_cont : continuous_at f (F.limsup a)) :
  f (F.limsup a) = F.limsup (f ∘ a) :=
f_incr.map_Limsup_of_continuous_at f_cont

/-- A monotone function between complete linear ordered spaces sends a `filter.Liminf`
to the `filter.liminf` of the image if it is continuous at the `Liminf`. -/
lemma monotone.map_Liminf_of_continuous_at {F : filter R} [ne_bot F]
  {f : R → S} (f_incr : monotone f) (f_cont : continuous_at f (F.Liminf)) :
  f (F.Liminf) = F.liminf f :=
@antitone.map_Liminf_of_continuous_at R (order_dual S) _ _ _ _ _ _ _ _ f f_incr f_cont

/-- A continuous monotone function between complete linear ordered spaces sends a `filter.liminf`
to the `filter.liminf` of the images. -/
lemma monotone.map_liminf_of_continuous_at
  {f : R → S} (f_incr : monotone f) (a : ι → R) (f_cont : continuous_at f (F.liminf a)) :
  f (F.liminf a) = F.liminf (f ∘ a) :=
f_incr.map_Liminf_of_continuous_at f_cont

end monotone

section infi_and_supr

open_locale topology

open filter set

variables {ι : Type*} {R : Type*} [complete_linear_order R] [topological_space R] [order_topology R]

lemma infi_eq_of_forall_le_of_tendsto {x : R} {as : ι → R}
  (x_le : ∀ i, x ≤ as i) {F : filter ι} [filter.ne_bot F] (as_lim : filter.tendsto as F (𝓝 x)) :
  (⨅ i, as i) = x :=
begin
  refine infi_eq_of_forall_ge_of_forall_gt_exists_lt (λ i, x_le i) _,
  apply λ w x_lt_w, ‹filter.ne_bot F›.nonempty_of_mem (eventually_lt_of_tendsto_lt x_lt_w as_lim),
end

lemma supr_eq_of_forall_le_of_tendsto {x : R} {as : ι → R}
  (le_x : ∀ i, as i ≤ x) {F : filter ι} [filter.ne_bot F] (as_lim : filter.tendsto as F (𝓝 x)) :
  (⨆ i, as i) = x :=
@infi_eq_of_forall_le_of_tendsto ι (order_dual R) _ _ _ x as le_x F _ as_lim

lemma Union_Ici_eq_Ioi_of_lt_of_tendsto {ι : Type*} (x : R) {as : ι → R} (x_lt : ∀ i, x < as i)
  {F : filter ι} [filter.ne_bot F] (as_lim : filter.tendsto as F (𝓝 x)) :
  (⋃ (i : ι), Ici (as i)) = Ioi x :=
begin
  have obs : x ∉ range as,
  { intro maybe_x_is,
    rcases mem_range.mp maybe_x_is with ⟨i, hi⟩,
    simpa only [hi, lt_self_iff_false] using x_lt i, } ,
  rw ← infi_eq_of_forall_le_of_tendsto (λ i, (x_lt i).le) as_lim at *,
  exact Union_Ici_eq_Ioi_infi obs,
end

lemma Union_Iic_eq_Iio_of_lt_of_tendsto {ι : Type*} (x : R) {as : ι → R} (lt_x : ∀ i, as i < x)
  {F : filter ι} [filter.ne_bot F] (as_lim : filter.tendsto as F (𝓝 x)) :
  (⋃ (i : ι), Iic (as i)) = Iio x :=
@Union_Ici_eq_Ioi_of_lt_of_tendsto (order_dual R) _ _ _ ι x as lt_x F _ as_lim

end infi_and_supr

section indicator

open_locale big_operators

lemma limsup_eq_tendsto_sum_indicator_nat_at_top (s : ℕ → set α) :
  limsup s at_top =
    {ω | tendsto (λ n, ∑ k in finset.range n, (s (k + 1)).indicator (1 : α → ℕ) ω) at_top at_top} :=
begin
  ext ω,
  simp only [limsup_eq_infi_supr_of_nat, ge_iff_le, set.supr_eq_Union,
      set.infi_eq_Inter, set.mem_Inter, set.mem_Union, exists_prop],
  split,
  { intro hω,
    refine tendsto_at_top_at_top_of_monotone' (λ n m hnm, finset.sum_mono_set_of_nonneg
      (λ i, set.indicator_nonneg (λ _ _, zero_le_one) _) (finset.range_mono hnm)) _,
    rintro ⟨i, h⟩,
    simp only [mem_upper_bounds, set.mem_range, forall_exists_index, forall_apply_eq_imp_iff'] at h,
    induction i with k hk,
    { obtain ⟨j, hj₁, hj₂⟩ := hω 1,
      refine not_lt.2 (h $ j + 1) (lt_of_le_of_lt
        (finset.sum_const_zero.symm : 0 = ∑ k in finset.range (j + 1), 0).le _),
      refine finset.sum_lt_sum (λ m _, set.indicator_nonneg (λ _ _, zero_le_one) _)
        ⟨j - 1, finset.mem_range.2 (lt_of_le_of_lt (nat.sub_le _ _) j.lt_succ_self), _⟩,
      rw [nat.sub_add_cancel hj₁, set.indicator_of_mem hj₂],
      exact zero_lt_one },
    { rw imp_false at hk,
      push_neg at hk,
      obtain ⟨i, hi⟩ := hk,
      obtain ⟨j, hj₁, hj₂⟩ := hω (i + 1),
      replace hi : ∑ k in finset.range i, (s (k + 1)).indicator 1 ω = k + 1 := le_antisymm (h i) hi,
      refine not_lt.2 (h $ j + 1) _,
      rw [← finset.sum_range_add_sum_Ico _ (i.le_succ.trans (hj₁.trans j.le_succ)), hi],
      refine lt_add_of_pos_right _ _,
      rw (finset.sum_const_zero.symm : 0 = ∑ k in finset.Ico i (j + 1), 0),
      refine finset.sum_lt_sum (λ m _, set.indicator_nonneg (λ _ _, zero_le_one) _)
        ⟨j - 1, finset.mem_Ico.2
        ⟨(nat.le_sub_iff_right (le_trans ((le_add_iff_nonneg_left _).2 zero_le') hj₁)).2 hj₁,
          lt_of_le_of_lt (nat.sub_le _ _) j.lt_succ_self⟩, _⟩,
      rw [nat.sub_add_cancel (le_trans ((le_add_iff_nonneg_left _).2 zero_le') hj₁),
        set.indicator_of_mem hj₂],
      exact zero_lt_one } },
  { rintro hω i,
    rw [set.mem_set_of_eq, tendsto_at_top_at_top] at hω,
    by_contra hcon,
    push_neg at hcon,
    obtain ⟨j, h⟩ := hω (i + 1),
    have : ∑ k in finset.range j, (s (k + 1)).indicator 1 ω ≤ i,
    { have hle : ∀ j ≤ i, ∑ k in finset.range j, (s (k + 1)).indicator 1 ω ≤ i,
      { refine λ j hij, (finset.sum_le_card_nsmul _ _ _ _ : _ ≤ (finset.range j).card • 1).trans _,
        { exact λ m hm, set.indicator_apply_le' (λ _, le_rfl) (λ _, zero_le_one) },
        { simpa only [finset.card_range, smul_eq_mul, mul_one] } },
      by_cases hij : j < i,
      { exact hle _ hij.le },
      { rw ← finset.sum_range_add_sum_Ico _ (not_lt.1 hij),
        suffices : ∑ k in finset.Ico i j, (s (k + 1)).indicator 1 ω = 0,
        { rw [this, add_zero],
          exact hle _ le_rfl },
        rw finset.sum_eq_zero (λ m hm, _),
        exact set.indicator_of_not_mem (hcon _ $ (finset.mem_Ico.1 hm).1.trans m.le_succ) _ } },
    exact not_le.2 (lt_of_lt_of_le i.lt_succ_self $ h _ le_rfl) this }
end

lemma limsup_eq_tendsto_sum_indicator_at_top
  (R : Type*) [strict_ordered_semiring R] [archimedean R] (s : ℕ → set α) :
  limsup s at_top =
    {ω | tendsto (λ n, ∑ k in finset.range n, (s (k + 1)).indicator (1 : α → R) ω) at_top at_top} :=
begin
  rw limsup_eq_tendsto_sum_indicator_nat_at_top s,
  ext ω,
  simp only [set.mem_set_of_eq],
  rw (_ : (λ n, ∑ k in finset.range n, (s (k + 1)).indicator (1 : α → R) ω) =
    (λ n, ↑(∑ k in finset.range n, (s (k + 1)).indicator (1 : α → ℕ) ω))),
  { exact tendsto_coe_nat_at_top_iff.symm },
  { ext n,
    simp only [set.indicator, pi.one_apply, finset.sum_boole, nat.cast_id] }
end

end indicator
