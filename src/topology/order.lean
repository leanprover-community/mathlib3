/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import topology.tactic

/-!
# Ordering on topologies and (co)induced topologies

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Topologies on a fixed type `α` are ordered, by reverse inclusion.
That is, for topologies `t₁` and `t₂` on `α`, we write `t₁ ≤ t₂`
if every set open in `t₂` is also open in `t₁`.
(One also calls `t₁` finer than `t₂`, and `t₂` coarser than `t₁`.)

Any function `f : α → β` induces
       `induced f : topological_space β → topological_space α`
and  `coinduced f : topological_space α → topological_space β`.
Continuity, the ordering on topologies and (co)induced topologies are
related as follows:
* The identity map (α, t₁) → (α, t₂) is continuous iff t₁ ≤ t₂.
* A map f : (α, t) → (β, u) is continuous
    iff             t ≤ induced f u   (`continuous_iff_le_induced`)
    iff coinduced f t ≤ u             (`continuous_iff_coinduced_le`).

Topologies on α form a complete lattice, with ⊥ the discrete topology
and ⊤ the indiscrete topology.

For a function f : α → β, (coinduced f, induced f) is a Galois connection
between topologies on α and topologies on β.

## Implementation notes

There is a Galois insertion between topologies on α (with the inclusion ordering)
and all collections of sets in α. The complete lattice structure on topologies
on α is defined as the reverse of the one obtained via this Galois insertion.

## Tags

finer, coarser, induced topology, coinduced topology

-/

open function set filter
open_locale topology filter

universes u v w

namespace topological_space
variables {α : Type u}

/-- The open sets of the least topology containing a collection of basic sets. -/
inductive generate_open (g : set (set α)) : set α → Prop
| basic  : ∀s∈g, generate_open s
| univ   : generate_open univ
| inter  : ∀s t, generate_open s → generate_open t → generate_open (s ∩ t)
| sUnion : ∀k, (∀s∈k, generate_open s) → generate_open (⋃₀ k)

/-- The smallest topological space containing the collection `g` of basic sets -/
def generate_from (g : set (set α)) : topological_space α :=
{ is_open        := generate_open g,
  is_open_univ   := generate_open.univ,
  is_open_inter  := generate_open.inter,
  is_open_sUnion := generate_open.sUnion }

lemma is_open_generate_from_of_mem {g : set (set α)} {s : set α} (hs : s ∈ g) :
  is_open[generate_from g] s :=
generate_open.basic s hs

lemma nhds_generate_from {g : set (set α)} {a : α} :
  @nhds α (generate_from g) a = (⨅s∈{s | a ∈ s ∧ s ∈ g}, 𝓟 s) :=
begin
  rw nhds_def,
  refine le_antisymm (binfi_mono $ λ s ⟨as, sg⟩, ⟨as, generate_open.basic _ sg⟩) _,
  refine le_infi₂ (λ s hs, _), cases hs with ha hs,
  induction hs,
  case basic : s hs { exact infi₂_le _ ⟨ha, hs⟩ },
  case univ : { exact le_top.trans_eq principal_univ.symm },
  case inter : s t hs' ht' hs ht { exact (le_inf (hs ha.1) (ht ha.2)).trans_eq inf_principal },
  case sUnion : S hS' hS
  { rcases ha with  ⟨t, htS, hat⟩,
    exact (hS t htS hat).trans (principal_mono.2 $ subset_sUnion_of_mem htS) }
end

lemma tendsto_nhds_generate_from {β : Type*} {m : α → β} {f : filter α} {g : set (set β)} {b : β}
  (h : ∀s∈g, b ∈ s → m ⁻¹' s ∈ f) : tendsto m f (@nhds β (generate_from g) b) :=
by rw [nhds_generate_from]; exact
  (tendsto_infi.2 $ assume s, tendsto_infi.2 $ assume ⟨hbs, hsg⟩, tendsto_principal.2 $ h s hsg hbs)

/-- Construct a topology on α given the filter of neighborhoods of each point of α. -/
protected def mk_of_nhds (n : α → filter α) : topological_space α :=
{ is_open        := λs, ∀a∈s, s ∈ n a,
  is_open_univ   := assume x h, univ_mem,
  is_open_inter  := assume s t hs ht x ⟨hxs, hxt⟩, inter_mem (hs x hxs) (ht x hxt),
  is_open_sUnion := assume s hs a ⟨x, hx, hxa⟩,
    mem_of_superset (hs x hx _ hxa) (set.subset_sUnion_of_mem hx) }

lemma nhds_mk_of_nhds (n : α → filter α) (a : α)
  (h₀ : pure ≤ n) (h₁ : ∀ a s, s ∈ n a → ∃ t ∈ n a, t ⊆ s ∧ ∀a' ∈ t, s ∈ n a') :
  @nhds α (topological_space.mk_of_nhds n) a = n a :=
begin
  letI := topological_space.mk_of_nhds n,
  refine le_antisymm (assume s hs, _) (assume s hs, _),
  { have h₀ : {b | s ∈ n b} ⊆ s := assume b hb, mem_pure.1 $ h₀ b hb,
    have h₁ : {b | s ∈ n b} ∈ 𝓝 a,
    { refine is_open.mem_nhds (assume b (hb : s ∈ n b), _) hs,
      rcases h₁ _ _ hb with ⟨t, ht, hts, h⟩,
      exact mem_of_superset ht h },
    exact mem_of_superset h₁ h₀ },
  { rcases (@mem_nhds_iff α (topological_space.mk_of_nhds n) _ _).1 hs with ⟨t, hts, ht, hat⟩,
    exact (n a).sets_of_superset (ht _ hat) hts },
end

lemma nhds_mk_of_nhds_single [decidable_eq α] {a₀ : α} {l : filter α} (h : pure a₀ ≤ l) (b : α) :
  @nhds α (topological_space.mk_of_nhds $ update pure a₀ l) b =
    (update pure a₀ l : α → filter α) b :=
begin
  refine nhds_mk_of_nhds _ _ (le_update_iff.mpr ⟨h, λ _ _, le_rfl⟩) (λ a s hs, _),
  rcases eq_or_ne a a₀ with rfl|ha,
  { refine ⟨s, hs, subset.rfl, λ b hb, _⟩,
    rcases eq_or_ne b a with rfl|hb,
    { exact hs },
    { rwa [update_noteq hb] } },
  { have hs' := hs,
    rw [update_noteq ha] at hs ⊢,
    exact ⟨{a}, rfl, singleton_subset_iff.mpr hs, forall_eq.2 hs'⟩ }
end

lemma nhds_mk_of_nhds_filter_basis (B : α → filter_basis α) (a : α) (h₀ : ∀ x (n ∈ B x), x ∈ n)
  (h₁ : ∀ x (n ∈ B x), ∃ n₁ ∈ B x, n₁ ⊆ n ∧ ∀ x' ∈ n₁, ∃ n₂ ∈ B x', n₂ ⊆ n) :
  @nhds α (topological_space.mk_of_nhds (λ x, (B x).filter)) a = (B a).filter :=
begin
  rw topological_space.nhds_mk_of_nhds;
  intros x n hn;
  obtain ⟨m, hm₁, hm₂⟩ := (B x).mem_filter_iff.mp hn,
  { exact hm₂ (h₀ _ _ hm₁), },
  { obtain ⟨n₁, hn₁, hn₂, hn₃⟩ := h₁ x m hm₁,
    refine ⟨n₁, (B x).mem_filter_of_mem hn₁, hn₂.trans hm₂, λ x' hx', (B x').mem_filter_iff.mp _⟩,
    obtain ⟨n₂, hn₄, hn₅⟩ := hn₃ x' hx',
    exact ⟨n₂, hn₄, hn₅.trans hm₂⟩, },
end

section lattice

/-- The ordering on topologies on the type `α`. `t ≤ s` if every set open in `s` is also open in `t`
(`t` is finer than `s`). -/
instance : partial_order (topological_space α) :=
{ le := λ s t, ∀ U, is_open[t] U → is_open[s] U,
  .. partial_order.lift (λ s, order_dual.to_dual (is_open[s])) (λ _ _, topological_space_eq) }

protected lemma le_def {α} {t s : topological_space α} : t ≤ s ↔ is_open[s] ≤ is_open[t] :=
iff.rfl

lemma le_generate_from_iff_subset_is_open {g : set (set α)} {t : topological_space α} :
  t ≤ topological_space.generate_from g ↔ g ⊆ {s | is_open[t] s} :=
⟨λ ht s hs, ht _ $ generate_open.basic s hs, λ hg s hs, hs.rec_on (assume v hv, hg hv)
  t.is_open_univ (assume u v _ _, t.is_open_inter u v) (assume k _, t.is_open_sUnion k)⟩

/-- If `s` equals the collection of open sets in the topology it generates, then `s` defines a
topology. -/
protected def mk_of_closure (s : set (set α)) (hs : {u | generate_open s u} = s) :
  topological_space α :=
{ is_open        := λ u, u ∈ s,
  is_open_univ   := hs ▸ topological_space.generate_open.univ,
  is_open_inter  := hs ▸ topological_space.generate_open.inter,
  is_open_sUnion := hs ▸ topological_space.generate_open.sUnion }

lemma mk_of_closure_sets {s : set (set α)} {hs : {u | generate_open s u} = s} :
  topological_space.mk_of_closure s hs = topological_space.generate_from s :=
topological_space_eq hs.symm

lemma gc_generate_from (α) :
  galois_connection (λ t : topological_space α, order_dual.to_dual {s | is_open[t] s})
    (generate_from ∘ order_dual.of_dual) :=
λ _ _, le_generate_from_iff_subset_is_open.symm

/-- The Galois coinsertion between `topological_space α` and `(set (set α))ᵒᵈ` whose lower part
  sends a topology to its collection of open subsets, and whose upper part sends a collection of
  subsets of α to the topology they generate. -/
def gci_generate_from (α : Type*) :
  galois_coinsertion (λ t : topological_space α, order_dual.to_dual {s | is_open[t] s})
    (generate_from ∘ order_dual.of_dual)  :=
{ gc        := gc_generate_from α,
  u_l_le    := assume ts s hs, generate_open.basic s hs,
  choice    := λg hg, topological_space.mk_of_closure g
    (subset.antisymm hg $ le_generate_from_iff_subset_is_open.1 $ le_rfl),
  choice_eq := assume s hs, mk_of_closure_sets }

/-- Topologies on `α` form a complete lattice, with `⊥` the discrete topology
  and `⊤` the indiscrete topology. The infimum of a collection of topologies
  is the topology generated by all their open sets, while the supremum is the
  topology whose open sets are those sets open in every member of the collection. -/
instance : complete_lattice (topological_space α) :=
(gci_generate_from α).lift_complete_lattice

@[mono] lemma generate_from_anti {α} {g₁ g₂ : set (set α)} (h : g₁ ⊆ g₂) :
  generate_from g₂ ≤ generate_from g₁ :=
(gc_generate_from _).monotone_u h

lemma generate_from_set_of_is_open (t : topological_space α) :
  generate_from {s | is_open[t] s} = t :=
(gci_generate_from α).u_l_eq t

lemma left_inverse_generate_from :
  left_inverse generate_from (λ t : topological_space α, {s | is_open[t] s}) :=
(gci_generate_from α).u_l_left_inverse

lemma generate_from_surjective :
  surjective (generate_from : set (set α) → topological_space α) :=
(gci_generate_from α).u_surjective

lemma set_of_is_open_injective : injective (λ t : topological_space α, {s | is_open[t] s}) :=
(gci_generate_from α).l_injective

end lattice

end topological_space

section lattice

variables {α : Type u} {β : Type v}

lemma is_open.mono {α} {t₁ t₂ : topological_space α} {s : set α} (hs : is_open[t₂] s)
  (h : t₁ ≤ t₂) : is_open[t₁] s := h s hs

lemma is_closed.mono {α} {t₁ t₂ : topological_space α} {s : set α} (hs : is_closed[t₂] s)
  (h : t₁ ≤ t₂) : is_closed[t₁] s :=
(@is_open_compl_iff α t₁ s).mp $ hs.is_open_compl.mono h

lemma is_open_implies_is_open_iff {a b : topological_space α} :
  (∀ s, is_open[a] s → is_open[b] s) ↔ b ≤ a :=
iff.rfl

/-- The only open sets in the indiscrete topology are the empty set and the whole space. -/
lemma topological_space.is_open_top_iff {α} (U : set α) :
  is_open[⊤] U ↔ U = ∅ ∨ U = univ :=
⟨λ h, begin
  induction h with V h _ _ _ _ ih₁ ih₂ _ _ ih,
  { cases h }, { exact or.inr rfl },
  { obtain ⟨rfl|rfl, rfl|rfl⟩ := ⟨ih₁, ih₂⟩; simp },
  { rw [sUnion_eq_empty, or_iff_not_imp_left],
    intro h, push_neg at h, obtain ⟨U, hU, hne⟩ := h,
    have := (ih U hU).resolve_left hne, subst this,
    refine sUnion_eq_univ_iff.2 (λ a, ⟨_, hU, trivial⟩) },
end, by { rintro (rfl|rfl), exacts [@is_open_empty _ ⊤, @is_open_univ _ ⊤] }⟩

/-- A topological space is discrete if every set is open, that is,
  its topology equals the discrete topology `⊥`. -/
class discrete_topology (α : Type*) [t : topological_space α] : Prop :=
(eq_bot [] : t = ⊥)

lemma discrete_topology_bot (α : Type*) : @discrete_topology α ⊥ := @discrete_topology.mk α ⊥ rfl

@[simp] lemma is_open_discrete [topological_space α] [discrete_topology α] (s : set α) :
  is_open s :=
(discrete_topology.eq_bot α).symm ▸ trivial

@[simp] lemma is_closed_discrete [topological_space α] [discrete_topology α] (s : set α) :
  is_closed s :=
is_open_compl_iff.1 $ is_open_discrete _

@[nontriviality]
lemma continuous_of_discrete_topology [topological_space α] [discrete_topology α]
  [topological_space β] {f : α → β} : continuous f :=
continuous_def.2 $ λ s hs, is_open_discrete _

@[simp] lemma nhds_discrete (α : Type*) [topological_space α] [discrete_topology α] :
  (@nhds α _) = pure :=
le_antisymm (λ _ s hs, (is_open_discrete s).mem_nhds hs) pure_le_nhds

lemma mem_nhds_discrete [topological_space α] [discrete_topology α] {x : α} {s : set α} :
  s ∈ 𝓝 x ↔ x ∈ s :=
by rw [nhds_discrete, mem_pure]

lemma le_of_nhds_le_nhds {t₁ t₂ : topological_space α} (h : ∀x, @nhds α t₁ x ≤ @nhds α t₂ x) :
  t₁ ≤ t₂ :=
begin
  intro s,
  rw [@is_open_iff_mem_nhds _ t₁, @is_open_iff_mem_nhds α t₂],
  exact λ hs a ha, h _ (hs _ ha)
end

lemma eq_of_nhds_eq_nhds {t₁ t₂ : topological_space α} (h : ∀x, @nhds α t₁ x = @nhds α t₂ x) :
  t₁ = t₂ :=
le_antisymm
  (le_of_nhds_le_nhds $ assume x, le_of_eq $ h x)
  (le_of_nhds_le_nhds $ assume x, le_of_eq $ (h x).symm)

lemma eq_bot_of_singletons_open {t : topological_space α} (h : ∀ x, is_open[t] {x}) : t = ⊥ :=
bot_unique $ λ s hs, bUnion_of_singleton s ▸ is_open_bUnion (λ x _, h x)

lemma forall_open_iff_discrete {X : Type*} [topological_space X] :
  (∀ s : set X, is_open s) ↔ discrete_topology X :=
⟨λ h, ⟨eq_bot_of_singletons_open $ λ _, h _⟩, @is_open_discrete _ _⟩

lemma singletons_open_iff_discrete {X : Type*} [topological_space X] :
  (∀ a : X, is_open ({a} : set X)) ↔ discrete_topology X :=
⟨λ h, ⟨eq_bot_of_singletons_open h⟩, λ a _, @is_open_discrete _ _ a _⟩

lemma discrete_topology_iff_singleton_mem_nhds [topological_space α] :
  discrete_topology α ↔ ∀ x : α, {x} ∈ 𝓝 x :=
by simp only [← singletons_open_iff_discrete, is_open_iff_mem_nhds, mem_singleton_iff, forall_eq]

/-- This lemma characterizes discrete topological spaces as those whose singletons are
neighbourhoods. -/
lemma discrete_topology_iff_nhds [topological_space α] :
  discrete_topology α ↔ ∀ x : α, 𝓝 x = pure x :=
by simp only [discrete_topology_iff_singleton_mem_nhds, ← nhds_ne_bot.le_pure_iff,
  le_pure_iff]

lemma discrete_topology_iff_nhds_ne [topological_space α] :
  discrete_topology α ↔ ∀ x : α, 𝓝[≠] x = ⊥ :=
by simp only [discrete_topology_iff_singleton_mem_nhds, nhds_within, inf_principal_eq_bot,
  compl_compl]

end lattice

section galois_connection
variables {α : Type*} {β : Type*} {γ : Type*}

/-- Given `f : α → β` and a topology on `β`, the induced topology on `α` is the collection of
  sets that are preimages of some open set in `β`. This is the coarsest topology that
  makes `f` continuous. -/
def topological_space.induced {α : Type u} {β : Type v} (f : α → β) (t : topological_space β) :
  topological_space α :=
{ is_open        := λs, ∃ s', is_open s' ∧ f ⁻¹' s' = s,
  is_open_univ   := ⟨univ, is_open_univ, preimage_univ⟩,
  is_open_inter  := by rintro s₁ s₂ ⟨s'₁, hs₁, rfl⟩ ⟨s'₂, hs₂, rfl⟩;
    exact ⟨s'₁ ∩ s'₂, hs₁.inter hs₂, preimage_inter⟩,
  is_open_sUnion := assume s h,
  begin
    simp only [classical.skolem] at h,
    cases h with f hf,
    apply exists.intro (⋃(x : set α) (h : x ∈ s), f x h),
    simp only [sUnion_eq_bUnion, preimage_Union, (λx h, (hf x h).right)], refine ⟨_, rfl⟩,
    exact (@is_open_Union β _ t _ $ assume i,
      show is_open (⋃h, f i h), from @is_open_Union β _ t _ $ assume h, (hf i h).left)
  end }

lemma is_open_induced_iff [t : topological_space β] {s : set α} {f : α → β} :
  is_open[t.induced f] s ↔ (∃t, is_open t ∧ f ⁻¹' t = s) :=
iff.rfl

lemma is_closed_induced_iff [t : topological_space β] {s : set α} {f : α → β} :
  is_closed[t.induced f] s ↔ (∃t, is_closed t ∧ f ⁻¹' t = s) :=
begin
  simp only [← is_open_compl_iff, is_open_induced_iff],
  exact compl_surjective.exists.trans (by simp only [preimage_compl, compl_inj_iff])
end

/-- Given `f : α → β` and a topology on `α`, the coinduced topology on `β` is defined
  such that `s:set β` is open if the preimage of `s` is open. This is the finest topology that
  makes `f` continuous. -/
def topological_space.coinduced {α : Type u} {β : Type v} (f : α → β) (t : topological_space α) :
  topological_space β :=
{ is_open        := λ s, is_open[t] (f ⁻¹' s),
  is_open_univ   := t.is_open_univ,
  is_open_inter  := λ _ _ h₁ h₂, h₁.inter h₂,
  is_open_sUnion := λ s h, by simpa only [preimage_sUnion] using is_open_bUnion h }

lemma is_open_coinduced {t : topological_space α} {s : set β} {f : α → β} :
  is_open[t.coinduced f] s ↔ is_open (f ⁻¹' s) :=
iff.rfl

lemma preimage_nhds_coinduced [topological_space α] {π : α → β} {s : set β}
  {a : α} (hs : s ∈ @nhds β (topological_space.coinduced π ‹_›) (π a)) : π ⁻¹' s ∈ 𝓝 a :=
begin
  letI := topological_space.coinduced π ‹_›,
  rcases mem_nhds_iff.mp hs with ⟨V, hVs, V_op, mem_V⟩,
  exact mem_nhds_iff.mpr ⟨π ⁻¹' V, set.preimage_mono hVs, V_op, mem_V⟩
end

variables {t t₁ t₂ : topological_space α} {t' : topological_space β} {f : α → β} {g : β → α}

lemma continuous.coinduced_le (h : @continuous α β t t' f) :
  t.coinduced f ≤ t' :=
λ s hs, (continuous_def.1 h s hs : _)

lemma coinduced_le_iff_le_induced {f : α → β} {tα : topological_space α}
  {tβ : topological_space β} :
  tα.coinduced f ≤ tβ ↔ tα ≤ tβ.induced f :=
⟨λ h s ⟨t, ht, hst⟩, hst ▸ h _ ht, λ h s hs, h _ ⟨s, hs, rfl⟩⟩

lemma continuous.le_induced (h : @continuous α β t t' f) :
  t ≤ t'.induced f :=
coinduced_le_iff_le_induced.1 h.coinduced_le

lemma gc_coinduced_induced (f : α → β) :
  galois_connection (topological_space.coinduced f) (topological_space.induced f) :=
assume f g, coinduced_le_iff_le_induced

lemma induced_mono (h : t₁ ≤ t₂) : t₁.induced g ≤ t₂.induced g :=
(gc_coinduced_induced g).monotone_u h

lemma coinduced_mono (h : t₁ ≤ t₂) : t₁.coinduced f ≤ t₂.coinduced f :=
(gc_coinduced_induced f).monotone_l h

@[simp] lemma induced_top : (⊤ : topological_space α).induced g = ⊤ :=
(gc_coinduced_induced g).u_top

@[simp] lemma induced_inf : (t₁ ⊓ t₂).induced g = t₁.induced g ⊓ t₂.induced g :=
(gc_coinduced_induced g).u_inf

@[simp] lemma induced_infi {ι : Sort w} {t : ι → topological_space α} :
  (⨅i, t i).induced g = (⨅i, (t i).induced g) :=
(gc_coinduced_induced g).u_infi

@[simp] lemma coinduced_bot : (⊥ : topological_space α).coinduced f = ⊥ :=
(gc_coinduced_induced f).l_bot

@[simp] lemma coinduced_sup : (t₁ ⊔ t₂).coinduced f = t₁.coinduced f ⊔ t₂.coinduced f :=
(gc_coinduced_induced f).l_sup

@[simp] lemma coinduced_supr {ι : Sort w} {t : ι → topological_space α} :
  (⨆i, t i).coinduced f = (⨆i, (t i).coinduced f) :=
(gc_coinduced_induced f).l_supr

lemma induced_id [t : topological_space α] : t.induced id = t :=
topological_space_eq $ funext $ assume s, propext $
  ⟨assume ⟨s', hs, h⟩, h ▸ hs, assume hs, ⟨s, hs, rfl⟩⟩

lemma induced_compose [tγ : topological_space γ]
  {f : α → β} {g : β → γ} : (tγ.induced g).induced f = tγ.induced (g ∘ f) :=
topological_space_eq $ funext $ assume s, propext $
  ⟨assume ⟨s', ⟨s, hs, h₂⟩, h₁⟩, h₁ ▸ h₂ ▸ ⟨s, hs, rfl⟩,
    assume ⟨s, hs, h⟩, ⟨preimage g s, ⟨s, hs, rfl⟩, h ▸ rfl⟩⟩

lemma induced_const [t : topological_space α] {x : α} :
  t.induced (λ y : β, x) = ⊤ :=
le_antisymm le_top (@continuous_const β α ⊤ t x).le_induced

lemma coinduced_id [t : topological_space α] : t.coinduced id = t :=
topological_space_eq rfl

lemma coinduced_compose [tα : topological_space α]
  {f : α → β} {g : β → γ} : (tα.coinduced f).coinduced g = tα.coinduced (g ∘ f) :=
topological_space_eq rfl

lemma equiv.induced_symm {α β : Type*} (e : α ≃ β) :
  topological_space.induced e.symm = topological_space.coinduced e :=
begin
  ext t U,
  split,
  { rintros ⟨V, hV, rfl⟩,
    rwa [is_open_coinduced, e.preimage_symm_preimage] },
  { exact λ hU, ⟨e ⁻¹' U, hU, e.symm_preimage_preimage _⟩ }
end

lemma equiv.coinduced_symm {α β : Type*} (e : α ≃ β) :
  topological_space.coinduced e.symm = topological_space.induced e :=
by rw [← e.symm.induced_symm, e.symm_symm]

end galois_connection

/- constructions using the complete lattice structure -/
section constructions
open topological_space

variables {α : Type u} {β : Type v}

instance inhabited_topological_space {α : Type u} : inhabited (topological_space α) :=
⟨⊥⟩

@[priority 100]
instance subsingleton.unique_topological_space [subsingleton α] :
  unique (topological_space α) :=
{ default := ⊥,
  uniq := λ t, eq_bot_of_singletons_open $ λ x, subsingleton.set_cases
    (@is_open_empty _ t) (@is_open_univ _ t) ({x} : set α) }

@[priority 100]
instance subsingleton.discrete_topology [t : topological_space α] [subsingleton α] :
  discrete_topology α :=
⟨unique.eq_default t⟩

instance : topological_space empty := ⊥
instance : discrete_topology empty := ⟨rfl⟩
instance : topological_space pempty := ⊥
instance : discrete_topology pempty := ⟨rfl⟩
instance : topological_space punit := ⊥
instance : discrete_topology punit := ⟨rfl⟩
instance : topological_space bool := ⊥
instance : discrete_topology bool := ⟨rfl⟩
instance : topological_space ℕ := ⊥
instance : discrete_topology ℕ := ⟨rfl⟩
instance : topological_space ℤ := ⊥
instance : discrete_topology ℤ := ⟨rfl⟩

instance {n} : topological_space (fin n) := ⊥
instance {n} : discrete_topology (fin n) := ⟨rfl⟩

instance sierpinski_space : topological_space Prop :=
generate_from {{true}}

lemma continuous_empty_function [topological_space α] [topological_space β] [is_empty β]
  (f : α → β) : continuous f :=
by { letI := function.is_empty f, exact continuous_of_discrete_topology }

lemma le_generate_from {t : topological_space α} { g : set (set α) } (h : ∀s∈g, is_open s) :
  t ≤ generate_from g :=
le_generate_from_iff_subset_is_open.2 h

lemma induced_generate_from_eq {α β} {b : set (set β)} {f : α → β} :
  (generate_from b).induced f = topological_space.generate_from (preimage f '' b) :=
le_antisymm
  (le_generate_from $ ball_image_iff.2 $ assume s hs, ⟨s, generate_open.basic _ hs, rfl⟩)
  (coinduced_le_iff_le_induced.1 $ le_generate_from $ assume s hs,
    generate_open.basic _ $ mem_image_of_mem _ hs)

lemma le_induced_generate_from {α β} [t : topological_space α] {b : set (set β)}
  {f : α → β} (h : ∀ (a : set β), a ∈ b → is_open (f ⁻¹' a)) : t ≤ induced f (generate_from b) :=
begin
  rw induced_generate_from_eq,
  apply le_generate_from,
  simp only [mem_image, and_imp, forall_apply_eq_imp_iff₂, exists_imp_distrib],
  exact h,
end

/-- This construction is left adjoint to the operation sending a topology on `α`
  to its neighborhood filter at a fixed point `a : α`. -/
def nhds_adjoint (a : α) (f : filter α) : topological_space α :=
{ is_open        := λs, a ∈ s → s ∈ f,
  is_open_univ   := assume s, univ_mem,
  is_open_inter  := assume s t hs ht ⟨has, hat⟩, inter_mem (hs has) (ht hat),
  is_open_sUnion := assume k hk ⟨u, hu, hau⟩, mem_of_superset (hk u hu hau)
    (subset_sUnion_of_mem hu) }

lemma gc_nhds (a : α) :
  galois_connection (nhds_adjoint a) (λt, @nhds α t a) :=
assume f t, by { rw le_nhds_iff, exact ⟨λ H s hs has, H _ has hs, λ H s has hs, H _ hs has⟩ }

lemma nhds_mono {t₁ t₂ : topological_space α} {a : α} (h : t₁ ≤ t₂) :
  @nhds α t₁ a ≤ @nhds α t₂ a := (gc_nhds a).monotone_u h

lemma le_iff_nhds {α : Type*} (t t' : topological_space α) :
  t ≤ t' ↔ ∀ x, @nhds α t x ≤ @nhds α t' x :=
⟨λ h x, nhds_mono h, le_of_nhds_le_nhds⟩

lemma nhds_adjoint_nhds {α : Type*} (a : α) (f : filter α) :
  @nhds α (nhds_adjoint a f) a = pure a ⊔ f :=
begin
  ext U,
  rw mem_nhds_iff,
  split,
  { rintros ⟨t, htU, ht, hat⟩,
    exact ⟨htU hat, mem_of_superset (ht hat) htU⟩},
  { rintros ⟨haU, hU⟩,
    exact ⟨U, subset.rfl, λ h, hU, haU⟩ }
end

lemma nhds_adjoint_nhds_of_ne {α : Type*} (a : α) (f : filter α) {b : α} (h : b ≠ a) :
  @nhds α (nhds_adjoint a f) b = pure b :=
begin
  apply le_antisymm,
  { intros U hU,
    rw mem_nhds_iff,
    use {b},
    simp only [and_true, singleton_subset_iff, mem_singleton],
    refine ⟨hU, λ ha, (h.symm ha).elim⟩ },
  { exact @pure_le_nhds α (nhds_adjoint a f) b },
end

lemma is_open_singleton_nhds_adjoint {α : Type*} {a b : α} (f : filter α) (hb : b ≠ a) :
  is_open[nhds_adjoint a f] {b} :=
begin
  rw is_open_singleton_iff_nhds_eq_pure,
  exact nhds_adjoint_nhds_of_ne a f hb
end

lemma le_nhds_adjoint_iff' {α : Type*} (a : α) (f : filter α) (t : topological_space α) :
  t ≤ nhds_adjoint a f ↔ @nhds α t a ≤ pure a ⊔ f ∧ ∀ b ≠ a, @nhds α t b = pure b :=
begin
  rw le_iff_nhds,
  split,
  { intros h,
    split,
    { specialize h a,
      rwa nhds_adjoint_nhds at h },
    { intros b hb,
      apply le_antisymm _ (pure_le_nhds b),
      specialize h b,
      rwa nhds_adjoint_nhds_of_ne a f hb at h } },
  { rintros ⟨h, h'⟩ b,
    by_cases hb : b = a,
    { rwa [hb, nhds_adjoint_nhds] },
    { simp [nhds_adjoint_nhds_of_ne a f hb, h' b hb] } }
end

lemma le_nhds_adjoint_iff {α : Type*} (a : α) (f : filter α) (t : topological_space α) :
  t ≤ nhds_adjoint a f ↔ (@nhds α t a ≤ pure a ⊔ f ∧ ∀ b, b ≠ a → is_open[t] {b}) :=
begin
  change _ ↔ _ ∧ ∀ (b : α), b ≠ a → is_open {b},
  rw [le_nhds_adjoint_iff', and.congr_right_iff],
  apply λ h, forall_congr (λ b,  _),
  rw @is_open_singleton_iff_nhds_eq_pure α t b
end

lemma nhds_infi {ι : Sort*} {t : ι → topological_space α} {a : α} :
  @nhds α (infi t) a = (⨅i, @nhds α (t i) a) := (gc_nhds a).u_infi

lemma nhds_Inf {s : set (topological_space α)} {a : α} :
  @nhds α (Inf s) a = (⨅t∈s, @nhds α t a) := (gc_nhds a).u_Inf

lemma nhds_inf {t₁ t₂ : topological_space α} {a : α} :
  @nhds α (t₁ ⊓ t₂) a = @nhds α t₁ a ⊓ @nhds α t₂ a := (gc_nhds a).u_inf

lemma nhds_top {a : α} : @nhds α ⊤ a = ⊤ := (gc_nhds a).u_top

lemma is_open_sup {t₁ t₂ : topological_space α} {s : set α} :
  is_open[t₁ ⊔ t₂] s ↔ is_open[t₁] s ∧ is_open[t₂] s :=
iff.rfl

local notation `cont` := @continuous _ _
local notation `tspace` := topological_space
open topological_space

variables {γ : Type*} {f : α → β} {ι : Sort*}

lemma continuous_iff_coinduced_le {t₁ : tspace α} {t₂ : tspace β} :
  cont t₁ t₂ f ↔ coinduced f t₁ ≤ t₂ :=
continuous_def.trans iff.rfl

lemma continuous_iff_le_induced {t₁ : tspace α} {t₂ : tspace β} :
  cont t₁ t₂ f ↔ t₁ ≤ induced f t₂ :=
iff.trans continuous_iff_coinduced_le (gc_coinduced_induced f _ _)

theorem continuous_generated_from {t : tspace α} {b : set (set β)}
  (h : ∀s∈b, is_open (f ⁻¹' s)) : cont t (generate_from b) f :=
continuous_iff_coinduced_le.2 $ le_generate_from h

@[continuity]
lemma continuous_induced_dom {t : tspace β} : cont (induced f t) t f :=
by { rw continuous_def, assume s h, exact ⟨_, h, rfl⟩ }

lemma continuous_induced_rng {g : γ → α} {t₂ : tspace β} {t₁ : tspace γ} :
  cont t₁ (induced f t₂) g ↔ cont t₁ t₂ (f ∘ g) :=
by simp only [continuous_iff_le_induced, induced_compose]

lemma continuous_coinduced_rng {t : tspace α} : cont t (coinduced f t) f :=
by { rw continuous_def, assume s h, exact h }

lemma continuous_coinduced_dom {g : β → γ} {t₁ : tspace α} {t₂ : tspace γ} :
  cont (coinduced f t₁) t₂ g ↔ cont t₁ t₂ (g ∘ f) :=
by simp only [continuous_iff_coinduced_le, coinduced_compose]

lemma continuous_le_dom {t₁ t₂ : tspace α} {t₃ : tspace β}
  (h₁ : t₂ ≤ t₁) (h₂ : cont t₁ t₃ f) : cont t₂ t₃ f :=
begin
  rw continuous_def at h₂ ⊢,
  assume s h,
  exact h₁ _ (h₂ s h)
end

lemma continuous_le_rng {t₁ : tspace α} {t₂ t₃ : tspace β}
  (h₁ : t₂ ≤ t₃) (h₂ : cont t₁ t₂ f) : cont t₁ t₃ f :=
begin
  rw continuous_def at h₂ ⊢,
  assume s h,
  exact h₂ s (h₁ s h)
end

lemma continuous_sup_dom {t₁ t₂ : tspace α} {t₃ : tspace β} :
  cont (t₁ ⊔ t₂) t₃ f ↔ cont t₁ t₃ f ∧ cont t₂ t₃ f :=
by simp only [continuous_iff_le_induced, sup_le_iff]

lemma continuous_sup_rng_left {t₁ : tspace α} {t₃ t₂ : tspace β} :
  cont t₁ t₂ f → cont t₁ (t₂ ⊔ t₃) f :=
continuous_le_rng le_sup_left

lemma continuous_sup_rng_right {t₁ : tspace α} {t₃ t₂ : tspace β} :
  cont t₁ t₃ f → cont t₁ (t₂ ⊔ t₃) f :=
continuous_le_rng le_sup_right

lemma continuous_Sup_dom {T : set (tspace α)} {t₂ : tspace β} :
  cont (Sup T) t₂ f ↔ ∀ t ∈ T, cont t t₂ f :=
by simp only [continuous_iff_le_induced, Sup_le_iff]

lemma continuous_Sup_rng {t₁ : tspace α} {t₂ : set (tspace β)} {t : tspace β}
  (h₁ : t ∈ t₂) (hf : cont t₁ t f) : cont t₁ (Sup t₂) f :=
continuous_iff_coinduced_le.2 $ le_Sup_of_le h₁ $ continuous_iff_coinduced_le.1 hf

lemma continuous_supr_dom {t₁ : ι → tspace α} {t₂ : tspace β} :
  cont (supr t₁) t₂ f ↔  ∀ i, cont (t₁ i) t₂ f :=
by simp only [continuous_iff_le_induced, supr_le_iff]

lemma continuous_supr_rng {t₁ : tspace α} {t₂ : ι → tspace β} {i : ι}
  (h : cont t₁ (t₂ i) f) : cont t₁ (supr t₂) f :=
continuous_Sup_rng ⟨i, rfl⟩ h

lemma continuous_inf_rng {t₁ : tspace α} {t₂ t₃ : tspace β} :
  cont t₁ (t₂ ⊓ t₃) f ↔ cont t₁ t₂ f ∧ cont t₁ t₃ f :=
by simp only [continuous_iff_coinduced_le, le_inf_iff]

lemma continuous_inf_dom_left {t₁ t₂ : tspace α} {t₃ : tspace β} :
  cont t₁ t₃ f → cont (t₁ ⊓ t₂) t₃ f :=
continuous_le_dom inf_le_left

lemma continuous_inf_dom_right {t₁ t₂ : tspace α} {t₃ : tspace β} :
  cont t₂ t₃ f → cont (t₁ ⊓ t₂) t₃ f :=
continuous_le_dom inf_le_right

lemma continuous_Inf_dom {t₁ : set (tspace α)} {t₂ : tspace β} {t : tspace α} (h₁ : t ∈ t₁) :
  cont t t₂ f → cont (Inf t₁) t₂ f :=
continuous_le_dom $ Inf_le h₁

lemma continuous_Inf_rng {t₁ : tspace α} {T : set (tspace β)} :
  cont t₁ (Inf T) f ↔ ∀ t ∈ T, cont t₁ t f :=
by simp only [continuous_iff_coinduced_le, le_Inf_iff]

lemma continuous_infi_dom {t₁ : ι → tspace α} {t₂ : tspace β} {i : ι} :
  cont (t₁ i) t₂ f → cont (infi t₁) t₂ f :=
continuous_le_dom $ infi_le _ _

lemma continuous_infi_rng {t₁ : tspace α} {t₂ : ι → tspace β} :
  cont t₁ (infi t₂) f ↔ ∀ i, cont t₁ (t₂ i) f :=
by simp only [continuous_iff_coinduced_le, le_infi_iff]

@[continuity] lemma continuous_bot {t : tspace β} : cont ⊥ t f :=
continuous_iff_le_induced.2 $ bot_le

@[continuity] lemma continuous_top {t : tspace α} : cont t ⊤ f :=
continuous_iff_coinduced_le.2 $ le_top

lemma continuous_id_iff_le {t t' : tspace α} : cont t t' id ↔ t ≤ t' :=
@continuous_def _ _ t t' id

lemma continuous_id_of_le {t t' : tspace α} (h : t ≤ t') : cont t t' id :=
continuous_id_iff_le.2 h

/- 𝓝 in the induced topology -/

theorem mem_nhds_induced [T : topological_space α] (f : β → α) (a : β) (s : set β) :
  s ∈ @nhds β (topological_space.induced f T) a ↔ ∃ u ∈ 𝓝 (f a), f ⁻¹' u ⊆ s :=
begin
  simp only [mem_nhds_iff, is_open_induced_iff, exists_prop, set.mem_set_of_eq],
  split,
  { rintros ⟨u, usub, ⟨v, openv, ueq⟩, au⟩,
    exact ⟨v, ⟨v, set.subset.refl v, openv, by rwa ←ueq at au⟩, by rw ueq; exact usub⟩ },
  rintros ⟨u, ⟨v, vsubu, openv, amem⟩, finvsub⟩,
  exact ⟨f ⁻¹' v, set.subset.trans (set.preimage_mono vsubu) finvsub, ⟨⟨v, openv, rfl⟩, amem⟩⟩
end

theorem nhds_induced [T : topological_space α] (f : β → α) (a : β) :
  @nhds β (topological_space.induced f T) a = comap f (𝓝 (f a)) :=
by { ext s, rw [mem_nhds_induced, mem_comap] }

lemma induced_iff_nhds_eq [tα : topological_space α] [tβ : topological_space β] (f : β → α) :
tβ = tα.induced f ↔ ∀ b, 𝓝 b = comap f (𝓝 $ f b) :=
⟨λ h a, h.symm ▸ nhds_induced f a, λ h, eq_of_nhds_eq_nhds $ λ x, by rw [h, nhds_induced]⟩

theorem map_nhds_induced_of_surjective [T : topological_space α]
    {f : β → α} (hf : surjective f) (a : β) :
  map f (@nhds β (topological_space.induced f T) a) = 𝓝 (f a) :=
by rw [nhds_induced, map_comap_of_surjective hf]

end constructions

section induced
open topological_space
variables {α : Type*} {β : Type*}
variables [t : topological_space β] {f : α → β}

theorem is_open_induced_eq {s : set α} :
  is_open[induced f t] s ↔ s ∈ preimage f '' {s | is_open s} :=
iff.rfl

theorem is_open_induced {s : set β} (h : is_open s) : is_open[induced f t] (f ⁻¹' s) :=
⟨s, h, rfl⟩

lemma map_nhds_induced_eq (a : α) : map f (@nhds α (induced f t) a) = 𝓝[range f] (f a) :=
by rw [nhds_induced, filter.map_comap, nhds_within]

lemma map_nhds_induced_of_mem {a : α} (h : range f ∈ 𝓝 (f a)) :
  map f (@nhds α (induced f t) a) = 𝓝 (f a) :=
by rw [nhds_induced, filter.map_comap_of_mem h]

lemma closure_induced [t : topological_space β] {f : α → β} {a : α} {s : set α} :
  a ∈ @closure α (topological_space.induced f t) s ↔ f a ∈ closure (f '' s) :=
by simp only [mem_closure_iff_frequently, nhds_induced, frequently_comap, mem_image, and_comm]

lemma is_closed_induced_iff' [t : topological_space β] {f : α → β} {s : set α} :
  is_closed[t.induced f] s ↔ ∀ a, f a ∈ closure (f '' s) → a ∈ s :=
by simp only [← closure_subset_iff_is_closed, subset_def, closure_induced]

end induced

section sierpinski
variables {α : Type*} [topological_space α]

@[simp] lemma is_open_singleton_true : is_open ({true} : set Prop) :=
topological_space.generate_open.basic _ (mem_singleton _)

@[simp] lemma nhds_true : 𝓝 true = pure true :=
le_antisymm (le_pure_iff.2 $ is_open_singleton_true.mem_nhds $ mem_singleton _) (pure_le_nhds _)

@[simp] lemma nhds_false : 𝓝 false = ⊤ :=
topological_space.nhds_generate_from.trans $ by simp [@and.comm (_ ∈ _)]

lemma continuous_Prop {p : α → Prop} : continuous p ↔ is_open {x | p x} :=
⟨assume h : continuous p,
  have is_open (p ⁻¹' {true}),
    from is_open_singleton_true.preimage h,
  by simpa [preimage, eq_true_iff] using this,
  assume h : is_open {x | p x},
  continuous_generated_from $ assume s (hs : s = {true}),
    by simp [hs, preimage, eq_true_iff, h]⟩

lemma is_open_iff_continuous_mem {s : set α} : is_open s ↔ continuous (λ x, x ∈ s) :=
continuous_Prop.symm

end sierpinski

section infi
variables {α : Type u} {ι : Sort v}

lemma generate_from_union (a₁ a₂ : set (set α)) :
  topological_space.generate_from (a₁ ∪ a₂) =
    topological_space.generate_from a₁ ⊓ topological_space.generate_from a₂ :=
(topological_space.gc_generate_from α).u_inf

lemma set_of_is_open_sup (t₁ t₂ : topological_space α) :
  {s | is_open[t₁ ⊔ t₂] s} = {s | is_open[t₁] s} ∩ {s | is_open[t₂] s} :=
rfl

lemma generate_from_Union {f : ι → set (set α)} :
  topological_space.generate_from (⋃ i, f i) = (⨅ i, topological_space.generate_from (f i)) :=
(topological_space.gc_generate_from α).u_infi

lemma set_of_is_open_supr {t : ι → topological_space α} :
  {s | is_open[⨆ i, t i] s} = ⋂ i, {s | is_open[t i] s} :=
(topological_space.gc_generate_from α).l_supr

lemma generate_from_sUnion {S : set (set (set α))} :
  topological_space.generate_from (⋃₀ S) = (⨅ s ∈ S, topological_space.generate_from s) :=
(topological_space.gc_generate_from α).u_Inf

lemma set_of_is_open_Sup {T : set (topological_space α)} :
  {s | is_open[Sup T] s} = ⋂ t ∈ T, {s | is_open[t] s} :=
(topological_space.gc_generate_from α).l_Sup

lemma generate_from_union_is_open (a b : topological_space α) :
  topological_space.generate_from ({s | is_open[a] s} ∪ {s | is_open[b] s}) = a ⊓ b :=
(topological_space.gci_generate_from α).u_inf_l a b

lemma generate_from_Union_is_open (f : ι → topological_space α) :
  topological_space.generate_from (⋃ i, {s | is_open[f i] s}) = ⨅ i, (f i) :=
(topological_space.gci_generate_from α).u_infi_l f

lemma generate_from_inter (a b : topological_space α) :
  topological_space.generate_from ({s | is_open[a] s} ∩ {s | is_open[b] s}) = a ⊔ b :=
(topological_space.gci_generate_from α).u_sup_l a b

lemma generate_from_Inter (f : ι → topological_space α) :
  topological_space.generate_from (⋂ i, {s | is_open[f i] s}) = ⨆ i, (f i) :=
(topological_space.gci_generate_from α).u_supr_l f

lemma generate_from_Inter_of_generate_from_eq_self (f : ι → set (set α))
  (hf : ∀ i, {s | is_open[topological_space.generate_from (f i)] s} = f i) :
  topological_space.generate_from (⋂ i, (f i)) = ⨆ i, topological_space.generate_from (f i) :=
(topological_space.gci_generate_from α).u_supr_of_lu_eq_self f hf

variables {t : ι → topological_space α}

lemma is_open_supr_iff {s : set α} : is_open[⨆ i, t i] s ↔ ∀ i, is_open[t i] s :=
show s ∈ set_of (is_open[supr t]) ↔ s ∈ {x : set α | ∀ (i : ι), is_open[t i] x},
by simp [set_of_is_open_supr]

lemma is_closed_supr_iff {s : set α} : is_closed[⨆ i, t i] s ↔ ∀ i, is_closed[t i] s :=
by simp [← is_open_compl_iff, is_open_supr_iff]

end infi
