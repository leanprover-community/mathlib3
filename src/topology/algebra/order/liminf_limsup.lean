/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
import order.liminf_limsup
import topology.algebra.order.basic

/-!
# Lemmas about liminf and limsup in an order topology.
-/

open filter
open_locale topological_space classical

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
  (h : tendsto u f (𝓝 a)) : limsup f u = a :=
Limsup_eq_of_le_nhds h

/-- If a function has a limit, then its liminf coincides with its limit. -/
theorem filter.tendsto.liminf_eq {f : filter β} {u : β → α} {a : α} [ne_bot f]
  (h : tendsto u f (𝓝 a)) : liminf f u = a :=
Liminf_eq_of_le_nhds h

/-- If the liminf and the limsup of a function coincide, then the limit of the function
exists and has the same value -/
theorem tendsto_of_liminf_eq_limsup {f : filter β} {u : β → α} {a : α}
  (hinf : liminf f u = a) (hsup : limsup f u = a)
  (h : f.is_bounded_under (≤) u . is_bounded_default)
  (h' : f.is_bounded_under (≥) u . is_bounded_default) :
  tendsto u f (𝓝 a) :=
le_nhds_of_Limsup_eq_Liminf h h' hsup hinf

/-- If a number `a` is less than or equal to the `liminf` of a function `f` at some filter
and is greater than or equal to the `limsup` of `f`, then `f` tends to `a` along this filter. -/
theorem tendsto_of_le_liminf_of_limsup_le {f : filter β} {u : β → α} {a : α}
  (hinf : a ≤ liminf f u) (hsup : limsup f u ≤ a)
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
  refine ⟨limsup f u, _⟩,
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
  [complete_linear_order S] [topological_space S] [order_closed_topology S]

/-- A continuous antitone function between complete linear ordered spaces sends a `filter.limsup`
to the `filter.liminf` of the images. -/
lemma antitone.map_limsup_of_continuous
  (a : ι → R) {f : R → S} (f_decr : antitone f) (f_cont : continuous f) :
  f (F.limsup a) = F.liminf (f ∘ a) :=
begin
  rw [filter.limsup_eq_Inf_Sup, filter.liminf_eq_Sup_Inf] at *,
  rw (f_decr.map_Inf_of_continuous_at' f_cont.continuous_at _),
  { apply congr_arg,
    simp only [set.image_image, function.comp_app],
    refine subset_antisymm _ _;
    { intros i hi,
      rw set.mem_image at *,
      rcases hi with ⟨I, I_mem_F, hI⟩,
      refine ⟨I, I_mem_F, _⟩,
      rw [← hI, f_decr.map_Sup_of_continuous_at' f_cont.continuous_at _, set.image_image],
      exact set.nonempty_image_iff.mpr (ne_bot.nonempty_of_mem ‹ne_bot F› I_mem_F), }, },
  { refine set.nonempty_image_iff.mpr set.nonempty_of_nonempty_subtype, },
end

/-- A continuous antitone function between complete linear ordered spaces sends a `filter.liminf`
to the `filter.limsup` of the images. -/
lemma antitone.map_liminf_of_continuous
  (a : ι → R) {f : R → S} (f_decr : antitone f) (f_cont : continuous f) :
  f (F.liminf a) = F.limsup (f ∘ a) :=
@antitone.map_limsup_of_continuous ι (order_dual R) (order_dual S)
  F _ _ _ _ _ _ _ a f f_decr.dual f_cont

/-- A continuous monotone function between complete linear ordered spaces sends a `filter.liminf`
to the `filter.liminf` of the images. -/
lemma monotone.map_liminf_of_continuous
  (a : ι → R) {f : R → S} (f_incr : monotone f) (f_cont : continuous f) :
  f (F.liminf a) = F.liminf (f ∘ a) :=
@antitone.map_liminf_of_continuous ι R (order_dual S) F _ _ _ _ _ _ _ a f f_incr f_cont

/-- A continuous monotone function between complete linear ordered spaces sends a `filter.limsup`
to the `filter.limsup` of the images. -/
lemma monotone.map_limsup_of_continuous
  (a : ι → R) {f : R → S} (f_incr : monotone f) (f_cont : continuous f) :
  f (F.limsup a) = F.limsup (f ∘ a) :=
@antitone.map_limsup_of_continuous ι R (order_dual S) F _ _ _ _ _ _ _ a f f_incr f_cont

end monotone
