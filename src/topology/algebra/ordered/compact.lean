/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Yury Kudryashov
-/
import topology.algebra.ordered.intermediate_value

/-!
# Compactness of a closed interval

In this file we prove that a closed interval in a conditionally complete linear ordered type with
order topology (or a product of such types) is compact. We also prove the extreme value theorem
(`is_compact.exists_forall_le`, `is_compact.exists_forall_ge`): a continuous function on a compact
set takes its minimum and maximum values.

We also prove that the image of a closed interval under a continuous map is a closed interval, see
`continuous_on.image_Icc`.

## Tags

compact, extreme value theorem
-/

open classical filter order_dual topological_space function set

/-!
### Compactness of a closed interval

In this section we define a typeclass `compact_Icc_space α` saying that all closed intervals in `α`
are compact. Then we provide an instance for a `conditionally_complete_linear_order` and prove that
the product (both `α × β` and an indexed product) of spaces with this property inherits the
property.

We also prove some simple lemmas about spaces with this property.
-/

/-- This typeclass says that all closed intervals in `α` are compact. This is true for all
conditionally complete linear orders with order topology and products (finite or infinite)
of such spaces. -/
class compact_Icc_space (α : Type*) [topological_space α] [preorder α] : Prop :=
(is_compact_Icc : ∀ {a b : α}, is_compact (Icc a b))

export compact_Icc_space (is_compact_Icc)

/-- A closed interval in a conditionally complete linear order is compact. -/
@[priority 100]
instance conditionally_complete_linear_order.to_compact_Icc_space
  (α : Type*) [conditionally_complete_linear_order α] [topological_space α] [order_topology α] :
  compact_Icc_space α :=
begin
  refine ⟨λ a b, _⟩,
  cases le_or_lt a b with hab hab, swap, { simp [hab] },
  refine is_compact_iff_ultrafilter_le_nhds.2 (λ f hf, _),
  contrapose! hf,
  rw [le_principal_iff],
  have hpt : ∀ x ∈ Icc a b, {x} ∉ f,
    from λ x hx hxf, hf x hx ((le_pure_iff.2 hxf).trans (pure_le_nhds x)),
  set s := {x ∈ Icc a b | Icc a x ∉ f},
  have hsb : b ∈ upper_bounds s, from λ x hx, hx.1.2,
  have sbd : bdd_above s, from ⟨b, hsb⟩,
  have ha : a ∈ s, by simp [hpt, hab],
  rcases hab.eq_or_lt with rfl|hlt, { exact ha.2 },
  set c := Sup s,
  have hsc : is_lub s c, from is_lub_cSup ⟨a, ha⟩ sbd,
  have hc : c ∈ Icc a b, from ⟨hsc.1 ha, hsc.2 hsb⟩,
  specialize hf c hc,
  have hcs : c ∈ s,
  { cases hc.1.eq_or_lt with heq hlt, { rwa ← heq },
    refine ⟨hc, λ hcf, hf (λ U hU, _)⟩,
    rcases (mem_nhds_within_Iic_iff_exists_Ioc_subset' hlt).1 (mem_nhds_within_of_mem_nhds hU)
      with ⟨x, hxc, hxU⟩,
    rcases ((hsc.frequently_mem ⟨a, ha⟩).and_eventually
      (Ioc_mem_nhds_within_Iic ⟨hxc, le_rfl⟩)).exists
      with ⟨y, ⟨hyab, hyf⟩, hy⟩,
    refine mem_of_superset(f.diff_mem_iff.2 ⟨hcf, hyf⟩) (subset.trans _ hxU),
    rw diff_subset_iff,
    exact subset.trans Icc_subset_Icc_union_Ioc
      (union_subset_union subset.rfl $ Ioc_subset_Ioc_left hy.1.le) },
  cases hc.2.eq_or_lt with heq hlt, { rw ← heq, exact hcs.2 },
  contrapose! hf,
  intros U hU,
  rcases (mem_nhds_within_Ici_iff_exists_mem_Ioc_Ico_subset hlt).1 (mem_nhds_within_of_mem_nhds hU)
    with ⟨y, hxy, hyU⟩,
  refine mem_of_superset _ hyU, clear_dependent U,
  have hy : y ∈ Icc a b, from ⟨hc.1.trans hxy.1.le, hxy.2⟩,
  by_cases hay : Icc a y ∈ f,
  { refine mem_of_superset (f.diff_mem_iff.2 ⟨f.diff_mem_iff.2 ⟨hay, hcs.2⟩, hpt y hy⟩) _,
    rw [diff_subset_iff, union_comm, Ico_union_right hxy.1.le, diff_subset_iff],
    exact Icc_subset_Icc_union_Icc },
  { exact ((hsc.1 ⟨hy, hay⟩).not_lt hxy.1).elim },
end

instance {ι : Type*} {α : ι → Type*} [Π i, preorder (α i)] [Π i, topological_space (α i)]
  [Π i, compact_Icc_space (α i)] : compact_Icc_space (Π i, α i) :=
⟨λ a b, pi_univ_Icc a b ▸ is_compact_univ_pi $ λ i, is_compact_Icc⟩

instance pi.compact_Icc_space' {α β : Type*} [preorder β] [topological_space β]
  [compact_Icc_space β] : compact_Icc_space (α → β) :=
pi.compact_Icc_space

instance {α β : Type*} [preorder α] [topological_space α] [compact_Icc_space α]
  [preorder β] [topological_space β] [compact_Icc_space β] :
  compact_Icc_space (α × β) :=
⟨λ a b, (Icc_prod_eq a b).symm ▸ is_compact_Icc.prod is_compact_Icc⟩

/-- An unordered closed interval in a conditionally complete linear order is compact. -/
lemma is_compact_interval {α : Type*} [conditionally_complete_linear_order α]
  [topological_space α] [order_topology α]{a b : α} : is_compact (interval a b) :=
is_compact_Icc

/-- A complete linear order is a compact space.

We do not register an instance for a `[compact_Icc_space α]` because this would only add instances
for products (indexed or not) of complete linear orders, and we have instances with higher priority
that cover these cases. -/
@[priority 100] -- See note [lower instance priority]
instance compact_space_of_complete_linear_order {α : Type*} [complete_linear_order α]
  [topological_space α] [order_topology α] :
  compact_space α :=
⟨by simp only [← Icc_bot_top, is_compact_Icc]⟩

section

variables {α : Type*} [preorder α] [topological_space α] [compact_Icc_space α]

instance compact_space_Icc (a b : α) : compact_space (Icc a b) :=
is_compact_iff_compact_space.mp is_compact_Icc

end

/-!
### Min and max elements of a compact set
-/

variables {α β : Type*} [conditionally_complete_linear_order α] [topological_space α]
  [order_topology α] [topological_space β]

lemma is_compact.Inf_mem {s : set α} (hs : is_compact s) (ne_s : s.nonempty) :
  Inf s ∈ s :=
hs.is_closed.cInf_mem ne_s hs.bdd_below

lemma is_compact.Sup_mem {s : set α} (hs : is_compact s) (ne_s : s.nonempty) :
  Sup s ∈ s :=
@is_compact.Inf_mem (order_dual α) _ _ _ _ hs ne_s

lemma is_compact.is_glb_Inf {s : set α} (hs : is_compact s) (ne_s : s.nonempty) :
  is_glb s (Inf s) :=
is_glb_cInf ne_s hs.bdd_below

lemma is_compact.is_lub_Sup {s : set α} (hs : is_compact s) (ne_s : s.nonempty) :
  is_lub s (Sup s) :=
@is_compact.is_glb_Inf (order_dual α) _ _ _ _ hs ne_s

lemma is_compact.is_least_Inf {s : set α} (hs : is_compact s) (ne_s : s.nonempty) :
  is_least s (Inf s) :=
⟨hs.Inf_mem ne_s, (hs.is_glb_Inf ne_s).1⟩

lemma is_compact.is_greatest_Sup {s : set α} (hs : is_compact s) (ne_s : s.nonempty) :
  is_greatest s (Sup s) :=
@is_compact.is_least_Inf (order_dual α) _ _ _ _ hs ne_s

lemma is_compact.exists_is_least {s : set α} (hs : is_compact s) (ne_s : s.nonempty) :
  ∃ x, is_least s x :=
⟨_, hs.is_least_Inf ne_s⟩

lemma is_compact.exists_is_greatest {s : set α} (hs : is_compact s) (ne_s : s.nonempty) :
  ∃ x, is_greatest s x :=
⟨_, hs.is_greatest_Sup ne_s⟩

lemma is_compact.exists_is_glb {s : set α} (hs : is_compact s) (ne_s : s.nonempty) :
  ∃ x ∈ s, is_glb s x :=
⟨_, hs.Inf_mem ne_s, hs.is_glb_Inf ne_s⟩

lemma is_compact.exists_is_lub {s : set α} (hs : is_compact s) (ne_s : s.nonempty) :
  ∃ x ∈ s, is_lub s x :=
⟨_, hs.Sup_mem ne_s, hs.is_lub_Sup ne_s⟩

lemma is_compact.exists_Inf_image_eq {s : set β} (hs : is_compact s) (ne_s : s.nonempty)
  {f : β → α} (hf : continuous_on f s) :
  ∃ x ∈ s,  Inf (f '' s) = f x :=
let ⟨x, hxs, hx⟩ := (hs.image_of_continuous_on hf).Inf_mem (ne_s.image f)
in ⟨x, hxs, hx.symm⟩

lemma is_compact.exists_Sup_image_eq :
  ∀ {s : set β}, is_compact s → s.nonempty → ∀ {f : β → α}, continuous_on f s →
  ∃ x ∈ s,  Sup (f '' s) = f x :=
@is_compact.exists_Inf_image_eq (order_dual α) _ _ _ _ _

lemma eq_Icc_of_connected_compact {s : set α} (h₁ : is_connected s) (h₂ : is_compact s) :
  s = Icc (Inf s) (Sup s) :=
eq_Icc_cInf_cSup_of_connected_bdd_closed h₁ h₂.bdd_below h₂.bdd_above h₂.is_closed

/-!
### Extreme value theorem
-/

/-- The **extreme value theorem**: a continuous function realizes its minimum on a compact set. -/
lemma is_compact.exists_forall_le {s : set β} (hs : is_compact s) (ne_s : s.nonempty)
  {f : β → α} (hf : continuous_on f s) :
  ∃x∈s, ∀y∈s, f x ≤ f y :=
begin
  rcases (hs.image_of_continuous_on hf).exists_is_least (ne_s.image f)
    with ⟨_, ⟨x, hxs, rfl⟩, hx⟩,
  exact ⟨x, hxs, ball_image_iff.1 hx⟩
end

/-- The **extreme value theorem**: a continuous function realizes its maximum on a compact set. -/
lemma is_compact.exists_forall_ge :
  ∀ {s : set β}, is_compact s → s.nonempty → ∀ {f : β → α}, continuous_on f s →
  ∃x∈s, ∀y∈s, f y ≤ f x :=
@is_compact.exists_forall_le (order_dual α) _ _ _ _ _

/-- The **extreme value theorem**: if a continuous function `f` tends to infinity away from compact
sets, then it has a global minimum. -/
lemma continuous.exists_forall_le [nonempty β] {f : β → α}
  (hf : continuous f) (hlim : tendsto f (cocompact β) at_top) :
  ∃ x, ∀ y, f x ≤ f y :=
begin
  inhabit β,
  obtain ⟨s : set β, hsc : is_compact s, hsf : ∀ x ∉ s, f (default β) ≤ f x⟩ :=
    (has_basis_cocompact.tendsto_iff at_top_basis).1 hlim (f $ default β) trivial,
  obtain ⟨x, -, hx⟩ : ∃ x ∈ insert (default β) s, ∀ y ∈ insert (default β) s, f x ≤ f y :=
    (hsc.insert (default β)).exists_forall_le (nonempty_insert _ _) hf.continuous_on,
  refine ⟨x, λ y, _⟩,
  by_cases hy : y ∈ s,
  exacts [hx y (or.inr hy), (hx _ (or.inl rfl)).trans (hsf y hy)]
end

/-- The **extreme value theorem**: if a continuous function `f` tends to negative infinity away from
compact sets, then it has a global maximum. -/
lemma continuous.exists_forall_ge [nonempty β] {f : β → α}
  (hf : continuous f) (hlim : tendsto f (cocompact β) at_bot) :
  ∃ x, ∀ y, f y ≤ f x :=
@continuous.exists_forall_le (order_dual α) _ _ _ _ _ _ _ hf hlim

/-!
### Image of a closed interval
-/

variables [densely_ordered α] [conditionally_complete_linear_order β] [order_topology β]
  {f : α → β} {a b x y : α}

open_locale interval

lemma continuous_on.image_Icc (hab : a ≤ b) (h : continuous_on f $ Icc a b) :
  f '' Icc a b = Icc (Inf $ f '' Icc a b) (Sup $ f '' Icc a b) :=
eq_Icc_of_connected_compact ⟨(nonempty_Icc.2 hab).image f, is_preconnected_Icc.image f h⟩
  (is_compact_Icc.image_of_continuous_on h)

lemma continuous_on.image_interval_eq_Icc (h : continuous_on f $ [a, b]) :
  f '' [a, b] = Icc (Inf (f '' [a, b])) (Sup (f '' [a, b])) :=
begin
  cases le_total a b with h2 h2,
  { simp_rw [interval_of_le h2] at h ⊢, exact h.image_Icc h2 },
  { simp_rw [interval_of_ge h2] at h ⊢, exact h.image_Icc h2 },
end

lemma continuous_on.image_interval (h : continuous_on f $ [a, b]) :
  f '' [a, b] = [Inf (f '' [a, b]), Sup (f '' [a, b])] :=
begin
  refine h.image_interval_eq_Icc.trans (interval_of_le _).symm,
  refine cInf_le_cSup _ _ (nonempty_interval.image _); rw h.image_interval_eq_Icc,
  exacts [bdd_below_Icc, bdd_above_Icc]
end
