/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Yury Kudryashov
-/
import topology.algebra.order.intermediate_value
import topology.local_extr

/-!
# Compactness of a closed interval

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove that a closed interval in a conditionally complete linear ordered type with
order topology (or a product of such types) is compact.

We prove the extreme value theorem (`is_compact.exists_forall_le`, `is_compact.exists_forall_ge`):
a continuous function on a compact set takes its minimum and maximum values. We provide many
variations of this theorem.

We also prove that the image of a closed interval under a continuous map is a closed interval, see
`continuous_on.image_Icc`.

## Tags

compact, extreme value theorem
-/

open filter order_dual topological_space function set
open_locale filter topology

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

/-- An unordered closed interval is compact. -/
lemma is_compact_uIcc {α : Type*} [linear_order α] [topological_space α] [compact_Icc_space α]
  {a b : α} : is_compact (uIcc a b) :=
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

variables {α β γ : Type*} [conditionally_complete_linear_order α] [topological_space α]
  [order_topology α] [topological_space β] [topological_space γ]

lemma is_compact.Inf_mem {s : set α} (hs : is_compact s) (ne_s : s.nonempty) :
  Inf s ∈ s :=
hs.is_closed.cInf_mem ne_s hs.bdd_below

lemma is_compact.Sup_mem {s : set α} (hs : is_compact s) (ne_s : s.nonempty) : Sup s ∈ s :=
@is_compact.Inf_mem αᵒᵈ _ _ _ _ hs ne_s

lemma is_compact.is_glb_Inf {s : set α} (hs : is_compact s) (ne_s : s.nonempty) :
  is_glb s (Inf s) :=
is_glb_cInf ne_s hs.bdd_below

lemma is_compact.is_lub_Sup {s : set α} (hs : is_compact s) (ne_s : s.nonempty) :
  is_lub s (Sup s) :=
@is_compact.is_glb_Inf αᵒᵈ _ _ _ _ hs ne_s

lemma is_compact.is_least_Inf {s : set α} (hs : is_compact s) (ne_s : s.nonempty) :
  is_least s (Inf s) :=
⟨hs.Inf_mem ne_s, (hs.is_glb_Inf ne_s).1⟩

lemma is_compact.is_greatest_Sup {s : set α} (hs : is_compact s) (ne_s : s.nonempty) :
  is_greatest s (Sup s) :=
@is_compact.is_least_Inf αᵒᵈ _ _ _ _ hs ne_s

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

lemma is_compact.exists_Inf_image_eq_and_le {s : set β} (hs : is_compact s) (ne_s : s.nonempty)
  {f : β → α} (hf : continuous_on f s) :
  ∃ x ∈ s, Inf (f '' s) = f x ∧ ∀ y ∈ s, f x ≤ f y :=
let ⟨x, hxs, hx⟩ := (hs.image_of_continuous_on hf).Inf_mem (ne_s.image f)
in ⟨x, hxs, hx.symm, λ y hy,
  hx.trans_le $ cInf_le (hs.image_of_continuous_on hf).bdd_below $ mem_image_of_mem f hy⟩

lemma is_compact.exists_Sup_image_eq_and_ge {s : set β} (hs : is_compact s) (ne_s : s.nonempty)
  {f : β → α} (hf : continuous_on f s) :
  ∃ x ∈ s, Sup (f '' s) = f x ∧ ∀ y ∈ s, f y ≤ f x :=
@is_compact.exists_Inf_image_eq_and_le αᵒᵈ _ _ _ _ _ _ hs ne_s _ hf

lemma is_compact.exists_Inf_image_eq {s : set β} (hs : is_compact s) (ne_s : s.nonempty)
  {f : β → α} (hf : continuous_on f s) :
  ∃ x ∈ s,  Inf (f '' s) = f x :=
let ⟨x, hxs, hx, _⟩ := hs.exists_Inf_image_eq_and_le ne_s hf in ⟨x, hxs, hx⟩

lemma is_compact.exists_Sup_image_eq :
  ∀ {s : set β}, is_compact s → s.nonempty → ∀ {f : β → α}, continuous_on f s →
  ∃ x ∈ s, Sup (f '' s) = f x :=
@is_compact.exists_Inf_image_eq αᵒᵈ _ _ _ _ _

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
@is_compact.exists_forall_le αᵒᵈ _ _ _ _ _

/-- The **extreme value theorem**: if a function `f` is continuous on a closed set `s` and it is
larger than a value in its image away from compact sets, then it has a minimum on this set. -/
lemma continuous_on.exists_forall_le' {s : set β} {f : β → α} (hf : continuous_on f s)
  (hsc : is_closed s) {x₀ : β} (h₀ : x₀ ∈ s) (hc : ∀ᶠ x in cocompact β ⊓ 𝓟 s, f x₀ ≤ f x) :
  ∃ x ∈ s, ∀ y ∈ s, f x ≤ f y :=
begin
  rcases (has_basis_cocompact.inf_principal _).eventually_iff.1 hc with ⟨K, hK, hKf⟩,
  have hsub : insert x₀ (K ∩ s) ⊆ s, from insert_subset.2 ⟨h₀, inter_subset_right _ _⟩,
  obtain ⟨x, hx, hxf⟩ : ∃ x ∈ insert x₀ (K ∩ s), ∀ y ∈ insert x₀ (K ∩ s), f x ≤ f y :=
    ((hK.inter_right hsc).insert x₀).exists_forall_le (insert_nonempty _ _) (hf.mono hsub),
  refine ⟨x, hsub hx, λ y hy, _⟩,
  by_cases hyK : y ∈ K,
  exacts [hxf _ (or.inr ⟨hyK, hy⟩), (hxf _ (or.inl rfl)).trans (hKf ⟨hyK, hy⟩)]
end

/-- The **extreme value theorem**: if a function `f` is continuous on a closed set `s` and it is
smaller than a value in its image away from compact sets, then it has a maximum on this set. -/
lemma continuous_on.exists_forall_ge' {s : set β} {f : β → α} (hf : continuous_on f s)
  (hsc : is_closed s) {x₀ : β} (h₀ : x₀ ∈ s) (hc : ∀ᶠ x in cocompact β ⊓ 𝓟 s, f x ≤ f x₀) :
  ∃ x ∈ s, ∀ y ∈ s, f y ≤ f x :=
@continuous_on.exists_forall_le' αᵒᵈ _ _ _ _ _ _ _ hf hsc _ h₀ hc

/-- The **extreme value theorem**: if a continuous function `f` is larger than a value in its range
away from compact sets, then it has a global minimum. -/
lemma _root_.continuous.exists_forall_le' {f : β → α} (hf : continuous f) (x₀ : β)
  (h : ∀ᶠ x in cocompact β, f x₀ ≤ f x) : ∃ (x : β), ∀ (y : β), f x ≤ f y :=
let ⟨x, _, hx⟩ := hf.continuous_on.exists_forall_le' is_closed_univ (mem_univ x₀)
  (by rwa [principal_univ, inf_top_eq])
in ⟨x, λ y, hx y (mem_univ y)⟩

/-- The **extreme value theorem**: if a continuous function `f` is smaller than a value in its range
away from compact sets, then it has a global maximum. -/
lemma _root_.continuous.exists_forall_ge' {f : β → α} (hf : continuous f) (x₀ : β)
  (h : ∀ᶠ x in cocompact β, f x ≤ f x₀) : ∃ (x : β), ∀ (y : β), f y ≤ f x :=
@continuous.exists_forall_le' αᵒᵈ _ _ _ _ _ _ hf x₀ h

/-- The **extreme value theorem**: if a continuous function `f` tends to infinity away from compact
sets, then it has a global minimum. -/
lemma _root_.continuous.exists_forall_le [nonempty β] {f : β → α}
  (hf : continuous f) (hlim : tendsto f (cocompact β) at_top) :
  ∃ x, ∀ y, f x ≤ f y :=
by { inhabit β, exact hf.exists_forall_le' default (hlim.eventually $ eventually_ge_at_top _) }

/-- The **extreme value theorem**: if a continuous function `f` tends to negative infinity away from
compact sets, then it has a global maximum. -/
lemma continuous.exists_forall_ge [nonempty β] {f : β → α}
  (hf : continuous f) (hlim : tendsto f (cocompact β) at_bot) :
  ∃ x, ∀ y, f y ≤ f x :=
@continuous.exists_forall_le αᵒᵈ _ _ _ _ _ _ _ hf hlim

lemma is_compact.Sup_lt_iff_of_continuous {f : β → α}
  {K : set β} (hK : is_compact K) (h0K : K.nonempty) (hf : continuous_on f K) (y : α) :
  Sup (f '' K) < y ↔ ∀ x ∈ K, f x < y :=
begin
  refine ⟨λ h x hx, (le_cSup (hK.bdd_above_image hf) $ mem_image_of_mem f hx).trans_lt h, λ h, _⟩,
  obtain ⟨x, hx, h2x⟩ := hK.exists_forall_ge h0K hf,
  refine (cSup_le (h0K.image f) _).trans_lt (h x hx),
  rintro _ ⟨x', hx', rfl⟩, exact h2x x' hx'
end

lemma is_compact.lt_Inf_iff_of_continuous {α β : Type*}
  [conditionally_complete_linear_order α] [topological_space α]
  [order_topology α] [topological_space β] {f : β → α}
  {K : set β} (hK : is_compact K) (h0K : K.nonempty) (hf : continuous_on f K) (y : α) :
  y < Inf (f '' K) ↔ ∀ x ∈ K, y < f x :=
@is_compact.Sup_lt_iff_of_continuous αᵒᵈ β _ _ _ _ _ _ hK h0K hf y

/-- A continuous function with compact support has a global minimum. -/
@[to_additive "A continuous function with compact support has a global minimum."]
lemma continuous.exists_forall_le_of_has_compact_mul_support [nonempty β] [has_one α]
  {f : β → α} (hf : continuous f) (h : has_compact_mul_support f) :
  ∃ (x : β), ∀ (y : β), f x ≤ f y :=
begin
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := (h.is_compact_range hf).exists_is_least (range_nonempty _),
  rw [mem_lower_bounds, forall_range_iff] at hx,
  exact ⟨x, hx⟩,
end

/-- A continuous function with compact support has a global maximum. -/
@[to_additive "A continuous function with compact support has a global maximum."]
lemma continuous.exists_forall_ge_of_has_compact_mul_support [nonempty β] [has_one α]
  {f : β → α} (hf : continuous f) (h : has_compact_mul_support f) :
  ∃ (x : β), ∀ (y : β), f y ≤ f x :=
@continuous.exists_forall_le_of_has_compact_mul_support αᵒᵈ _ _ _ _ _ _ _ _ hf h

lemma is_compact.continuous_Sup {f : γ → β → α}
  {K : set β} (hK : is_compact K) (hf : continuous ↿f) :
    continuous (λ x, Sup (f x '' K)) :=
begin
  rcases eq_empty_or_nonempty K with rfl|h0K,
  { simp_rw [image_empty], exact continuous_const },
  rw [continuous_iff_continuous_at],
  intro x,
  obtain ⟨y, hyK, h2y, hy⟩ :=
    hK.exists_Sup_image_eq_and_ge h0K
      (show continuous (λ y, f x y), from hf.comp $ continuous.prod.mk x).continuous_on,
  rw [continuous_at, h2y, tendsto_order],
  have := tendsto_order.mp ((show continuous (λ x, f x y), from
    hf.comp $ continuous_id.prod_mk continuous_const).tendsto x),
  refine ⟨λ z hz, _, λ z hz, _⟩,
  { refine (this.1 z hz).mono (λ x' hx', hx'.trans_le $ le_cSup _ $ mem_image_of_mem (f x') hyK),
    exact hK.bdd_above_image (hf.comp $ continuous.prod.mk x').continuous_on },
  { have h : ({x} : set γ) ×ˢ K ⊆ ↿f ⁻¹' (Iio z),
    { rintro ⟨x', y'⟩ ⟨hx', hy'⟩, cases hx', exact (hy y' hy').trans_lt hz },
    obtain ⟨u, v, hu, hv, hxu, hKv, huv⟩ :=
      generalized_tube_lemma is_compact_singleton hK (is_open_Iio.preimage hf) h,
    refine eventually_of_mem (hu.mem_nhds (singleton_subset_iff.mp hxu)) (λ x' hx', _),
    rw [hK.Sup_lt_iff_of_continuous h0K
      (show continuous (f x'), from (hf.comp $ continuous.prod.mk x')).continuous_on],
    exact λ y' hy', huv (mk_mem_prod hx' (hKv hy')) }
end

lemma is_compact.continuous_Inf {f : γ → β → α}
  {K : set β} (hK : is_compact K) (hf : continuous ↿f) :
    continuous (λ x, Inf (f x '' K)) :=
@is_compact.continuous_Sup αᵒᵈ β γ _ _ _ _ _ _ _ hK hf

namespace continuous_on
/-!
### Image of a closed interval
-/

variables [densely_ordered α] [conditionally_complete_linear_order β] [order_topology β]
  {f : α → β} {a b c : α}

open_locale interval

lemma image_Icc (hab : a ≤ b) (h : continuous_on f $ Icc a b) :
  f '' Icc a b = Icc (Inf $ f '' Icc a b) (Sup $ f '' Icc a b) :=
eq_Icc_of_connected_compact ⟨(nonempty_Icc.2 hab).image f, is_preconnected_Icc.image f h⟩
  (is_compact_Icc.image_of_continuous_on h)

lemma image_uIcc_eq_Icc (h : continuous_on f $ [a, b]) :
  f '' [a, b] = Icc (Inf (f '' [a, b])) (Sup (f '' [a, b])) :=
begin
  cases le_total a b with h2 h2,
  { simp_rw [uIcc_of_le h2] at h ⊢, exact h.image_Icc h2 },
  { simp_rw [uIcc_of_ge h2] at h ⊢, exact h.image_Icc h2 },
end

lemma image_uIcc (h : continuous_on f $ [a, b]) :
  f '' [a, b] = [Inf (f '' [a, b]), Sup (f '' [a, b])] :=
begin
  refine h.image_uIcc_eq_Icc.trans (uIcc_of_le _).symm,
  refine cInf_le_cSup _ _ (nonempty_uIcc.image _); rw h.image_uIcc_eq_Icc,
  exacts [bdd_below_Icc, bdd_above_Icc]
end

lemma Inf_image_Icc_le (h : continuous_on f $ Icc a b) (hc : c ∈ Icc a b) :
  Inf (f '' (Icc a b)) ≤ f c :=
begin
  rw h.image_Icc (nonempty_Icc.mp (set.nonempty_of_mem hc)),
  exact cInf_le bdd_below_Icc (mem_Icc.mpr ⟨cInf_le (is_compact_Icc.bdd_below_image h) ⟨c, hc, rfl⟩,
     le_cSup (is_compact_Icc.bdd_above_image h) ⟨c, hc, rfl⟩⟩),
end

lemma le_Sup_image_Icc (h : continuous_on f $ Icc a b) (hc : c ∈ Icc a b) :
  f c ≤ Sup (f '' (Icc a b)) :=
begin
  rw h.image_Icc (nonempty_Icc.mp (set.nonempty_of_mem hc)),
  exact le_cSup bdd_above_Icc (mem_Icc.mpr ⟨cInf_le (is_compact_Icc.bdd_below_image h) ⟨c, hc, rfl⟩,
     le_cSup (is_compact_Icc.bdd_above_image h) ⟨c, hc, rfl⟩⟩),
end

end continuous_on

lemma is_compact.exists_local_min_on_mem_subset {f : β → α} {s t : set β} {z : β}
  (ht : is_compact t) (hf : continuous_on f t) (hz : z ∈ t) (hfz : ∀ z' ∈ t \ s, f z < f z') :
  ∃ x ∈ s, is_local_min_on f t x :=
begin
  obtain ⟨x, hx, hfx⟩ : ∃ x ∈ t, ∀ y ∈ t, f x ≤ f y := ht.exists_forall_le ⟨z, hz⟩ hf,
  have key : ∀ ⦃y⦄, y ∈ t → (∀ z' ∈ t \ s, f y < f z') → y ∈ s := λ y hy hfy,
    by { by_contra; simpa using ((hfy y ((mem_diff y).mpr ⟨hy,h⟩))) },
  have h1 : ∀ z' ∈ t \ s, f x < f z' := λ z' hz', (hfx z hz).trans_lt (hfz z' hz'),
  have h2 : x ∈ s := key hx h1,
  refine ⟨x, h2, eventually_nhds_within_of_forall hfx⟩
end

lemma is_compact.exists_local_min_mem_open {f : β → α} {s t : set β} {z : β} (ht : is_compact t)
  (hst : s ⊆ t) (hf : continuous_on f t) (hz : z ∈ t) (hfz : ∀ z' ∈ t \ s, f z < f z')
  (hs : is_open s) :
  ∃ x ∈ s, is_local_min f x :=
begin
  obtain ⟨x, hx, hfx⟩ := ht.exists_local_min_on_mem_subset hf hz hfz,
  exact ⟨x, hx, hfx.is_local_min (filter.mem_of_superset (hs.mem_nhds hx) hst)⟩
end
