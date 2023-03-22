/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import topology.maps
import topology.locally_finite
import order.filter.pi

/-!
# Constructions of new topological spaces from old ones

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file constructs products, sums, subtypes and quotients of topological spaces
and sets up their basic theory, such as criteria for maps into or out of these
constructions to be continuous; descriptions of the open sets, neighborhood filters,
and generators of these constructions; and their behavior with respect to embeddings
and other specific classes of maps.

## Implementation note

The constructed topologies are defined using induced and coinduced topologies
along with the complete lattice structure on topologies. Their universal properties
(for example, a map `X → Y × Z` is continuous if and only if both projections
`X → Y`, `X → Z` are) follow easily using order-theoretic descriptions of
continuity. With more work we can also extract descriptions of the open sets,
neighborhood filters and so on.

## Tags

product, sum, disjoint union, subspace, quotient space

-/

noncomputable theory

open topological_space set filter function
open_locale classical topology filter

universes u v
variables {α : Type u} {β : Type v} {γ δ ε ζ : Type*}

section constructions

instance {p : α → Prop} [t : topological_space α] : topological_space (subtype p) :=
induced coe t

instance {r : α → α → Prop} [t : topological_space α] : topological_space (quot r) :=
coinduced (quot.mk r) t

instance {s : setoid α} [t : topological_space α] : topological_space (quotient s) :=
coinduced quotient.mk t

instance [t₁ : topological_space α] [t₂ : topological_space β] : topological_space (α × β) :=
induced prod.fst t₁ ⊓ induced prod.snd t₂

instance [t₁ : topological_space α] [t₂ : topological_space β] : topological_space (α ⊕ β) :=
coinduced sum.inl t₁ ⊔ coinduced sum.inr t₂

instance {β : α → Type v} [t₂ : Πa, topological_space (β a)] : topological_space (sigma β) :=
⨆a, coinduced (sigma.mk a) (t₂ a)

instance Pi.topological_space {β : α → Type v} [t₂ : Πa, topological_space (β a)] :
  topological_space (Πa, β a) :=
⨅a, induced (λf, f a) (t₂ a)

instance ulift.topological_space [t : topological_space α] : topological_space (ulift.{v u} α) :=
t.induced ulift.down

/-!
### `additive`, `multiplicative`

The topology on those type synonyms is inherited without change.
-/

section
variables [topological_space α]

open additive multiplicative

instance : topological_space (additive α) := ‹topological_space α›
instance : topological_space (multiplicative α) := ‹topological_space α›
instance [discrete_topology α] : discrete_topology (additive α) := ‹discrete_topology α›
instance [discrete_topology α] : discrete_topology (multiplicative α) := ‹discrete_topology α›

lemma continuous_of_mul : continuous (of_mul : α → additive α) := continuous_id
lemma continuous_to_mul : continuous (to_mul : additive α → α) := continuous_id
lemma continuous_of_add : continuous (of_add : α → multiplicative α) := continuous_id
lemma continuous_to_add : continuous (to_add : multiplicative α → α) := continuous_id

lemma is_open_map_of_mul : is_open_map (of_mul : α → additive α) := is_open_map.id
lemma is_open_map_to_mul : is_open_map (to_mul : additive α → α) := is_open_map.id
lemma is_open_map_of_add : is_open_map (of_add : α → multiplicative α) := is_open_map.id
lemma is_open_map_to_add : is_open_map (to_add : multiplicative α → α) := is_open_map.id

lemma is_closed_map_of_mul : is_closed_map (of_mul : α → additive α) := is_closed_map.id
lemma is_closed_map_to_mul : is_closed_map (to_mul : additive α → α) := is_closed_map.id
lemma is_closed_map_of_add : is_closed_map (of_add : α → multiplicative α) := is_closed_map.id
lemma is_closed_map_to_add : is_closed_map (to_add : multiplicative α → α) := is_closed_map.id

lemma nhds_of_mul (a : α) : 𝓝 (of_mul a) = map of_mul (𝓝 a) := by { unfold nhds, refl, }
lemma nhds_of_add (a : α) : 𝓝 (of_add a) = map of_add (𝓝 a) := by { unfold nhds, refl, }
lemma nhds_to_mul (a : additive α) : 𝓝 (to_mul a) = map to_mul (𝓝 a) := by { unfold nhds, refl, }
lemma nhds_to_add (a : multiplicative α) : 𝓝 (to_add a) = map to_add (𝓝 a) :=
by { unfold nhds, refl, }

end

/-!
### Order dual

The topology on this type synonym is inherited without change.
-/

section
variables [topological_space α]

open order_dual

instance : topological_space αᵒᵈ := ‹topological_space α›
instance [discrete_topology α] : discrete_topology (αᵒᵈ) := ‹discrete_topology α›

lemma continuous_to_dual : continuous (to_dual : α → αᵒᵈ) := continuous_id
lemma continuous_of_dual : continuous (of_dual : αᵒᵈ → α) := continuous_id

lemma is_open_map_to_dual : is_open_map (to_dual : α → αᵒᵈ) := is_open_map.id
lemma is_open_map_of_dual : is_open_map (of_dual : αᵒᵈ → α) := is_open_map.id

lemma is_closed_map_to_dual : is_closed_map (to_dual : α → αᵒᵈ) := is_closed_map.id
lemma is_closed_map_of_dual : is_closed_map (of_dual : αᵒᵈ → α) := is_closed_map.id

lemma nhds_to_dual (a : α) : 𝓝 (to_dual a) = map to_dual (𝓝 a) := by { unfold nhds, refl, }
lemma nhds_of_dual (a : α) : 𝓝 (of_dual a) = map of_dual (𝓝 a) := by { unfold nhds, refl, }

end

lemma quotient.preimage_mem_nhds [topological_space α] [s : setoid α]
  {V : set $ quotient s} {a : α} (hs : V ∈ 𝓝 (quotient.mk a)) : quotient.mk ⁻¹' V ∈ 𝓝 a :=
preimage_nhds_coinduced hs

/-- The image of a dense set under `quotient.mk` is a dense set. -/
lemma dense.quotient [setoid α] [topological_space α] {s : set α} (H : dense s) :
  dense (quotient.mk '' s) :=
(surjective_quotient_mk α).dense_range.dense_image continuous_coinduced_rng H

/-- The composition of `quotient.mk` and a function with dense range has dense range. -/
lemma dense_range.quotient [setoid α] [topological_space α] {f : β → α} (hf : dense_range f) :
  dense_range (quotient.mk ∘ f) :=
(surjective_quotient_mk α).dense_range.comp hf continuous_coinduced_rng

instance {p : α → Prop} [topological_space α] [discrete_topology α] :
  discrete_topology (subtype p) :=
⟨bot_unique $ assume s hs,
  ⟨coe '' s, is_open_discrete _, (set.preimage_image_eq _ subtype.coe_injective)⟩⟩

instance sum.discrete_topology [topological_space α] [topological_space β]
  [hα : discrete_topology α] [hβ : discrete_topology β] : discrete_topology (α ⊕ β) :=
⟨by unfold sum.topological_space; simp [hα.eq_bot, hβ.eq_bot]⟩

instance sigma.discrete_topology {β : α → Type v} [Πa, topological_space (β a)]
  [h : Πa, discrete_topology (β a)] : discrete_topology (sigma β) :=
⟨by { unfold sigma.topological_space, simp [λ a, (h a).eq_bot] }⟩

section topα

variable [topological_space α]

/-
The 𝓝 filter and the subspace topology.
-/

theorem mem_nhds_subtype (s : set α) (a : {x // x ∈ s}) (t : set {x // x ∈ s}) :
  t ∈ 𝓝 a ↔ ∃ u ∈ 𝓝 (a : α), coe ⁻¹' u ⊆ t :=
mem_nhds_induced coe a t

theorem nhds_subtype (s : set α) (a : {x // x ∈ s}) :
  𝓝 a = comap coe (𝓝 (a : α)) :=
nhds_induced coe a

lemma nhds_within_subtype_eq_bot_iff {s t : set α} {x : s} :
  𝓝[(coe : s → α) ⁻¹' t] x = ⊥ ↔ 𝓝[t] (x : α) ⊓ 𝓟 s = ⊥ :=
by rw [inf_principal_eq_bot_iff_comap, nhds_within, nhds_within, comap_inf, comap_principal,
       nhds_induced]

lemma nhds_ne_subtype_eq_bot_iff {S : set α} {x : S} : 𝓝[{x}ᶜ] x = ⊥ ↔ 𝓝[{x}ᶜ] (x : α) ⊓ 𝓟 S = ⊥ :=
by rw [← nhds_within_subtype_eq_bot_iff, preimage_compl, ← image_singleton,
       subtype.coe_injective.preimage_image ]

lemma nhds_ne_subtype_ne_bot_iff {S : set α} {x : S} :
  (𝓝[{x}ᶜ] x).ne_bot ↔ (𝓝[{x}ᶜ] (x : α) ⊓ 𝓟 S).ne_bot :=
by rw [ne_bot_iff, ne_bot_iff, not_iff_not, nhds_ne_subtype_eq_bot_iff]

lemma discrete_topology_subtype_iff {S : set α} :
  discrete_topology S ↔ ∀ x ∈ S, 𝓝[≠] x ⊓ 𝓟 S = ⊥ :=
by simp_rw [discrete_topology_iff_nhds_ne, set_coe.forall', nhds_ne_subtype_eq_bot_iff]

end topα

/-- A type synonym equiped with the topology whose open sets are the empty set and the sets with
finite complements. -/
def cofinite_topology (α : Type*) := α

namespace cofinite_topology

/-- The identity equivalence between `α` and `cofinite_topology α`. -/
def of : α ≃ cofinite_topology α := equiv.refl α
instance [inhabited α] : inhabited (cofinite_topology α) :=
{ default := of default }

instance : topological_space (cofinite_topology α) :=
{ is_open := λ s, s.nonempty → set.finite sᶜ,
  is_open_univ := by simp,
  is_open_inter := λ s t, begin
    rintros hs ht ⟨x, hxs, hxt⟩,
    rw compl_inter,
    exact (hs ⟨x, hxs⟩).union (ht ⟨x, hxt⟩),
  end,
  is_open_sUnion := begin
    rintros s h ⟨x, t, hts, hzt⟩,
    rw set.compl_sUnion,
    exact set.finite.sInter (mem_image_of_mem _ hts) (h t hts ⟨x, hzt⟩),
  end }

lemma is_open_iff {s : set (cofinite_topology α)} :
  is_open s ↔ (s.nonempty → (sᶜ).finite) := iff.rfl

lemma is_open_iff' {s : set (cofinite_topology α)} :
  is_open s ↔ (s = ∅ ∨ (sᶜ).finite) :=
by simp only [is_open_iff, nonempty_iff_ne_empty, or_iff_not_imp_left]

lemma is_closed_iff {s : set (cofinite_topology α)} :
  is_closed s ↔ s = univ ∨ s.finite :=
by simp [← is_open_compl_iff, is_open_iff']

lemma nhds_eq (a : cofinite_topology α) : 𝓝 a = pure a ⊔ cofinite :=
begin
  ext U,
  rw mem_nhds_iff,
  split,
  { rintro ⟨V, hVU, V_op, haV⟩,
    exact mem_sup.mpr ⟨hVU haV, mem_of_superset (V_op ⟨_, haV⟩) hVU⟩ },
  { rintros ⟨hU : a ∈ U, hU' : (Uᶜ).finite⟩,
    exact ⟨U, subset.rfl, λ h, hU', hU⟩ }
end

lemma mem_nhds_iff {a : cofinite_topology α} {s : set (cofinite_topology α)} :
  s ∈ 𝓝 a ↔ a ∈ s ∧ sᶜ.finite :=
by simp [nhds_eq]

end cofinite_topology

end constructions

section prod
variables [topological_space α] [topological_space β] [topological_space γ] [topological_space δ]
  [topological_space ε] [topological_space ζ]

@[continuity] lemma continuous_fst : continuous (@prod.fst α β) :=
continuous_inf_dom_left continuous_induced_dom

/-- Postcomposing `f` with `prod.fst` is continuous -/
lemma continuous.fst {f : α → β × γ} (hf : continuous f) : continuous (λ a : α, (f a).1) :=
continuous_fst.comp hf

/-- Precomposing `f` with `prod.fst` is continuous -/
lemma continuous.fst' {f : α → γ} (hf : continuous f) : continuous (λ x : α × β, f x.fst) :=
hf.comp continuous_fst

lemma continuous_at_fst {p : α × β} : continuous_at prod.fst p :=
continuous_fst.continuous_at

/-- Postcomposing `f` with `prod.fst` is continuous at `x` -/
lemma continuous_at.fst {f : α → β × γ} {x : α} (hf : continuous_at f x) :
  continuous_at (λ a : α, (f a).1) x :=
continuous_at_fst.comp hf

/-- Precomposing `f` with `prod.fst` is continuous at `(x, y)` -/
lemma continuous_at.fst' {f : α → γ} {x : α} {y : β} (hf : continuous_at f x) :
  continuous_at (λ x : α × β, f x.fst) (x, y) :=
continuous_at.comp hf continuous_at_fst

/-- Precomposing `f` with `prod.fst` is continuous at `x : α × β` -/
lemma continuous_at.fst'' {f : α → γ} {x : α × β} (hf : continuous_at f x.fst) :
  continuous_at (λ x : α × β, f x.fst) x :=
hf.comp continuous_at_fst

@[continuity] lemma continuous_snd : continuous (@prod.snd α β) :=
continuous_inf_dom_right continuous_induced_dom

/-- Postcomposing `f` with `prod.snd` is continuous -/
lemma continuous.snd {f : α → β × γ} (hf : continuous f) : continuous (λ a : α, (f a).2) :=
continuous_snd.comp hf

/-- Precomposing `f` with `prod.snd` is continuous -/
lemma continuous.snd' {f : β → γ} (hf : continuous f) : continuous (λ x : α × β, f x.snd) :=
hf.comp continuous_snd

lemma continuous_at_snd {p : α × β} : continuous_at prod.snd p :=
continuous_snd.continuous_at

/-- Postcomposing `f` with `prod.snd` is continuous at `x` -/
lemma continuous_at.snd {f : α → β × γ} {x : α} (hf : continuous_at f x) :
  continuous_at (λ a : α, (f a).2) x :=
continuous_at_snd.comp hf

/-- Precomposing `f` with `prod.snd` is continuous at `(x, y)` -/
lemma continuous_at.snd' {f : β → γ} {x : α} {y : β} (hf : continuous_at f y) :
  continuous_at (λ x : α × β, f x.snd) (x, y) :=
continuous_at.comp hf continuous_at_snd

/-- Precomposing `f` with `prod.snd` is continuous at `x : α × β` -/
lemma continuous_at.snd'' {f : β → γ} {x : α × β} (hf : continuous_at f x.snd) :
  continuous_at (λ x : α × β, f x.snd) x :=
hf.comp continuous_at_snd

@[continuity] lemma continuous.prod_mk {f : γ → α} {g : γ → β}
  (hf : continuous f) (hg : continuous g) : continuous (λx, (f x, g x)) :=
continuous_inf_rng.2 ⟨continuous_induced_rng.2 hf, continuous_induced_rng.2 hg⟩

@[simp] lemma continuous_prod_mk {f : α → β} {g : α → γ} :
  continuous (λ x, (f x, g x)) ↔ continuous f ∧ continuous g :=
⟨λ h, ⟨h.fst, h.snd⟩, λ h, h.1.prod_mk h.2⟩

@[continuity] lemma continuous.prod.mk (a : α) : continuous (λ b : β, (a, b)) :=
continuous_const.prod_mk continuous_id'

@[continuity] lemma continuous.prod.mk_left (b : β) : continuous (λ a : α, (a, b)) :=
continuous_id'.prod_mk continuous_const

lemma continuous.comp₂ {g : α × β → γ} (hg : continuous g) {e : δ → α} (he : continuous e)
  {f : δ → β} (hf : continuous f) : continuous (λ x, g (e x, f x)) :=
hg.comp $ he.prod_mk hf

lemma continuous.comp₃ {g : α × β × γ → ε} (hg : continuous g)
  {e : δ → α} (he : continuous e) {f : δ → β} (hf : continuous f)
  {k : δ → γ} (hk : continuous k) : continuous (λ x, g (e x, f x, k x)) :=
hg.comp₂ he $ hf.prod_mk hk

lemma continuous.comp₄ {g : α × β × γ × ζ → ε} (hg : continuous g)
  {e : δ → α} (he : continuous e) {f : δ → β} (hf : continuous f)
  {k : δ → γ} (hk : continuous k) {l : δ → ζ} (hl : continuous l) :
  continuous (λ x, g (e x, f x, k x, l x)) :=
hg.comp₃ he hf $ hk.prod_mk hl

lemma continuous.prod_map {f : γ → α} {g : δ → β} (hf : continuous f) (hg : continuous g) :
  continuous (λ x : γ × δ, (f x.1, g x.2)) :=
hf.fst'.prod_mk hg.snd'

/-- A version of `continuous_inf_dom_left` for binary functions -/
lemma continuous_inf_dom_left₂ {α β γ} {f : α → β → γ}
  {ta1 ta2 : topological_space α} {tb1 tb2 : topological_space β} {tc1 : topological_space γ}
  (h : by haveI := ta1; haveI := tb1; exact continuous (λ p : α × β, f p.1 p.2)) :
  by haveI := ta1 ⊓ ta2; haveI := tb1 ⊓ tb2; exact continuous (λ p : α × β, f p.1 p.2) :=
begin
  have ha := @continuous_inf_dom_left _ _ id ta1 ta2 ta1 (@continuous_id _ (id _)),
  have hb := @continuous_inf_dom_left _ _ id tb1 tb2 tb1 (@continuous_id _ (id _)),
  have h_continuous_id := @continuous.prod_map _ _ _ _ ta1 tb1 (ta1 ⊓ ta2) (tb1 ⊓ tb2) _ _ ha hb,
  exact @continuous.comp _ _ _ (id _) (id _) _ _ _ h h_continuous_id,
end

/-- A version of `continuous_inf_dom_right` for binary functions -/
lemma continuous_inf_dom_right₂ {α β γ} {f : α → β → γ}
  {ta1 ta2 : topological_space α} {tb1 tb2 : topological_space β} {tc1 : topological_space γ}
  (h : by haveI := ta2; haveI := tb2; exact continuous (λ p : α × β, f p.1 p.2)) :
  by haveI := ta1 ⊓ ta2; haveI := tb1 ⊓ tb2; exact continuous (λ p : α × β, f p.1 p.2) :=
begin
  have ha := @continuous_inf_dom_right _ _ id ta1 ta2 ta2 (@continuous_id _ (id _)),
  have hb := @continuous_inf_dom_right _ _ id tb1 tb2 tb2 (@continuous_id _ (id _)),
  have h_continuous_id := @continuous.prod_map _ _ _ _ ta2 tb2 (ta1 ⊓ ta2) (tb1 ⊓ tb2) _ _ ha hb,
  exact @continuous.comp _ _ _ (id _) (id _) _ _ _ h h_continuous_id,
end

/-- A version of `continuous_Inf_dom` for binary functions -/
lemma continuous_Inf_dom₂ {α β γ} {f : α → β → γ}
  {tas : set (topological_space α)} {tbs : set (topological_space β)}
  {ta : topological_space α} {tb : topological_space β} {tc : topological_space γ}
  (ha : ta ∈ tas) (hb : tb ∈ tbs)
  (hf : continuous (λ p : α × β, f p.1 p.2)):
  by haveI := Inf tas; haveI := Inf tbs; exact @continuous _ _ _ tc (λ p : α × β, f p.1 p.2) :=
begin
  let t : topological_space (α × β) := prod.topological_space,
  have ha := continuous_Inf_dom ha continuous_id,
  have hb := continuous_Inf_dom hb continuous_id,
  have h_continuous_id := @continuous.prod_map _ _ _ _ ta tb (Inf tas) (Inf tbs) _ _ ha hb,
  exact @continuous.comp _ _ _ (id _) (id _) _ _ _ hf h_continuous_id,
end

lemma filter.eventually.prod_inl_nhds {p : α → Prop} {a : α}  (h : ∀ᶠ x in 𝓝 a, p x) (b : β) :
  ∀ᶠ x in 𝓝 (a, b), p (x : α × β).1 :=
continuous_at_fst h

lemma filter.eventually.prod_inr_nhds {p : β → Prop} {b : β} (h : ∀ᶠ x in 𝓝 b, p x) (a : α) :
  ∀ᶠ x in 𝓝 (a, b), p (x : α × β).2 :=
continuous_at_snd h

lemma filter.eventually.prod_mk_nhds {pa : α → Prop} {a} (ha : ∀ᶠ x in 𝓝 a, pa x)
  {pb : β → Prop} {b} (hb : ∀ᶠ y in 𝓝 b, pb y) :
  ∀ᶠ p in 𝓝 (a, b), pa (p : α × β).1 ∧ pb p.2 :=
(ha.prod_inl_nhds b).and (hb.prod_inr_nhds a)

lemma continuous_swap : continuous (prod.swap : α × β → β × α) :=
continuous_snd.prod_mk continuous_fst

lemma continuous_uncurry_left {f : α → β → γ} (a : α)
  (h : continuous (uncurry f)) : continuous (f a) :=
show continuous (uncurry f ∘ (λ b, (a, b))), from h.comp (by continuity)

lemma continuous_uncurry_right {f : α → β → γ} (b : β)
  (h : continuous (uncurry f)) : continuous (λ a, f a b) :=
show continuous (uncurry f ∘ (λ a, (a, b))), from h.comp (by continuity)

lemma continuous_curry {g : α × β → γ} (a : α)
  (h : continuous g) : continuous (curry g a) :=
show continuous (g ∘ (λ b, (a, b))), from h.comp (by continuity)

lemma is_open.prod {s : set α} {t : set β} (hs : is_open s) (ht : is_open t) :
  is_open (s ×ˢ t) :=
(hs.preimage continuous_fst).inter (ht.preimage continuous_snd)

lemma nhds_prod_eq {a : α} {b : β} : 𝓝 (a, b) = 𝓝 a ×ᶠ 𝓝 b :=
by rw [filter.prod, prod.topological_space, nhds_inf, nhds_induced, nhds_induced]

/-- If a function `f x y` is such that `y ↦ f x y` is continuous for all `x`, and `x` lives in a
discrete space, then `f` is continuous. -/
lemma continuous_uncurry_of_discrete_topology [discrete_topology α]
  {f : α → β → γ} (hf : ∀ a, continuous (f a)) : continuous (uncurry f) :=
begin
  apply continuous_iff_continuous_at.2,
  rintros ⟨a, x⟩,
  change map _ _ ≤ _,
  rw [nhds_prod_eq, nhds_discrete, filter.map_pure_prod],
  exact (hf a).continuous_at
end

lemma mem_nhds_prod_iff {a : α} {b : β} {s : set (α × β)} :
  s ∈ 𝓝 (a, b) ↔ ∃ (u ∈ 𝓝 a) (v ∈ 𝓝 b), u ×ˢ v ⊆ s :=
by rw [nhds_prod_eq, mem_prod_iff]

lemma mem_nhds_prod_iff' {a : α} {b : β} {s : set (α × β)} :
  s ∈ 𝓝 (a, b) ↔ ∃ (u : set α) (v : set β), is_open u ∧ a ∈ u ∧ is_open v ∧ b ∈ v ∧ u ×ˢ v ⊆ s :=
begin
  rw mem_nhds_prod_iff,
  split,
  { rintros ⟨u, Hu, v, Hv, h⟩,
    rcases mem_nhds_iff.1 Hu with ⟨u', u'u, u'_open, Hu'⟩,
    rcases mem_nhds_iff.1 Hv with ⟨v', v'v, v'_open, Hv'⟩,
    exact ⟨u', v', u'_open, Hu', v'_open, Hv', (set.prod_mono u'u v'v).trans h⟩ },
  { rintros ⟨u, v, u_open, au, v_open, bv, huv⟩,
    exact ⟨u, u_open.mem_nhds au, v, v_open.mem_nhds bv, huv⟩ }
end

lemma _root_.prod.tendsto_iff {α} (seq : α → β × γ) {f : filter α} (x : β × γ) :
  tendsto seq f (𝓝 x)
    ↔ tendsto (λ n, (seq n).fst) f (𝓝 x.fst) ∧ tendsto (λ n, (seq n).snd) f (𝓝 x.snd) :=
by { cases x, rw [nhds_prod_eq, filter.tendsto_prod_iff'], }

lemma filter.has_basis.prod_nhds {ιa ιb : Type*} {pa : ιa → Prop} {pb : ιb → Prop}
  {sa : ιa → set α} {sb : ιb → set β} {a : α} {b : β} (ha : (𝓝 a).has_basis pa sa)
  (hb : (𝓝 b).has_basis pb sb) :
  (𝓝 (a, b)).has_basis (λ i : ιa × ιb, pa i.1 ∧ pb i.2) (λ i, sa i.1 ×ˢ sb i.2) :=
by { rw nhds_prod_eq, exact ha.prod hb }

lemma filter.has_basis.prod_nhds' {ιa ιb : Type*} {pa : ιa → Prop} {pb : ιb → Prop}
  {sa : ιa → set α} {sb : ιb → set β} {ab : α × β} (ha : (𝓝 ab.1).has_basis pa sa)
  (hb : (𝓝 ab.2).has_basis pb sb) :
  (𝓝 ab).has_basis (λ i : ιa × ιb, pa i.1 ∧ pb i.2) (λ i, sa i.1 ×ˢ sb i.2) :=
by { cases ab, exact ha.prod_nhds hb }

instance [discrete_topology α] [discrete_topology β] : discrete_topology (α × β) :=
discrete_topology_iff_nhds.2 $ λ ⟨a, b⟩,
  by rw [nhds_prod_eq, nhds_discrete α, nhds_discrete β, filter.prod_pure_pure]

lemma prod_mem_nhds_iff {s : set α} {t : set β} {a : α} {b : β} :
  s ×ˢ t ∈ 𝓝 (a, b) ↔ s ∈ 𝓝 a ∧ t ∈ 𝓝 b :=
by rw [nhds_prod_eq, prod_mem_prod_iff]

lemma prod_mem_nhds {s : set α} {t : set β} {a : α} {b : β}
  (ha : s ∈ 𝓝 a) (hb : t ∈ 𝓝 b) : s ×ˢ t ∈ 𝓝 (a, b) :=
prod_mem_nhds_iff.2 ⟨ha, hb⟩

lemma filter.eventually.prod_nhds {p : α → Prop} {q : β → Prop} {a : α} {b : β}
  (ha : ∀ᶠ x in 𝓝 a, p x) (hb : ∀ᶠ y in 𝓝 b, q y) :
  ∀ᶠ z : α × β in 𝓝 (a, b), p z.1 ∧ q z.2 :=
prod_mem_nhds ha hb

lemma nhds_swap (a : α) (b : β) : 𝓝 (a, b) = (𝓝 (b, a)).map prod.swap :=
by rw [nhds_prod_eq, filter.prod_comm, nhds_prod_eq]; refl

lemma filter.tendsto.prod_mk_nhds {γ} {a : α} {b : β} {f : filter γ} {ma : γ → α} {mb : γ → β}
  (ha : tendsto ma f (𝓝 a)) (hb : tendsto mb f (𝓝 b)) :
  tendsto (λc, (ma c, mb c)) f (𝓝 (a, b)) :=
by rw [nhds_prod_eq]; exact filter.tendsto.prod_mk ha hb

lemma filter.eventually.curry_nhds {p : α × β → Prop} {x : α} {y : β} (h : ∀ᶠ x in 𝓝 (x, y), p x) :
  ∀ᶠ x' in 𝓝 x, ∀ᶠ y' in 𝓝 y, p (x', y') :=
by { rw [nhds_prod_eq] at h, exact h.curry }

lemma continuous_at.prod {f : α → β} {g : α → γ} {x : α}
  (hf : continuous_at f x) (hg : continuous_at g x) : continuous_at (λx, (f x, g x)) x :=
hf.prod_mk_nhds hg

lemma continuous_at.prod_map {f : α → γ} {g : β → δ} {p : α × β}
  (hf : continuous_at f p.fst) (hg : continuous_at g p.snd) :
  continuous_at (λ p : α × β, (f p.1, g p.2)) p :=
hf.fst''.prod hg.snd''

lemma continuous_at.prod_map' {f : α → γ} {g : β → δ} {x : α} {y : β}
  (hf : continuous_at f x) (hg : continuous_at g y) :
  continuous_at (λ p : α × β, (f p.1, g p.2)) (x, y) :=
hf.fst'.prod hg.snd'

lemma prod_generate_from_generate_from_eq {α β : Type*} {s : set (set α)} {t : set (set β)}
  (hs : ⋃₀ s = univ) (ht : ⋃₀ t = univ) :
  @prod.topological_space α β (generate_from s) (generate_from t) =
  generate_from {g | ∃ u ∈ s, ∃ v ∈ t, g = u ×ˢ v} :=
let G := generate_from {g | ∃ u ∈ s, ∃ v ∈ t, g = u ×ˢ v} in
le_antisymm
  (le_generate_from $ λ g ⟨u, hu, v, hv, g_eq⟩, g_eq.symm ▸
    @is_open.prod _ _ (generate_from s) (generate_from t) _ _
      (generate_open.basic _ hu) (generate_open.basic _ hv))
  (le_inf
    (coinduced_le_iff_le_induced.mp $ le_generate_from $ λ u hu,
      have (⋃ v ∈ t, u ×ˢ v) = prod.fst ⁻¹' u,
      by simp_rw [← prod_Union, ← sUnion_eq_bUnion, ht, prod_univ],
      show G.is_open (prod.fst ⁻¹' u),
      by { rw [← this], exactI is_open_Union (λ v, is_open_Union $ λ hv,
        generate_open.basic _ ⟨_, hu, _, hv, rfl⟩) })
    (coinduced_le_iff_le_induced.mp $ le_generate_from $ λ v hv,
      have (⋃ u ∈ s, u ×ˢ v) = prod.snd ⁻¹' v,
      by simp_rw [← Union_prod_const, ← sUnion_eq_bUnion, hs, univ_prod],
      show G.is_open (prod.snd ⁻¹' v),
      by { rw [← this], exactI is_open_Union (λ u, is_open_Union $ λ hu,
          generate_open.basic _ ⟨_, hu, _, hv, rfl⟩) }))

lemma prod_eq_generate_from :
  prod.topological_space =
  generate_from {g | ∃(s:set α) (t:set β), is_open s ∧ is_open t ∧ g = s ×ˢ t} :=
le_antisymm
  (le_generate_from $ λ g ⟨s, t, hs, ht, g_eq⟩, g_eq.symm ▸ hs.prod ht)
  (le_inf
    (ball_image_of_ball $ λt ht, generate_open.basic _ ⟨t, univ, by simpa [set.prod_eq] using ht⟩)
    (ball_image_of_ball $ λt ht, generate_open.basic _ ⟨univ, t, by simpa [set.prod_eq] using ht⟩))

lemma is_open_prod_iff {s : set (α × β)} : is_open s ↔
  (∀a b, (a, b) ∈ s →
    ∃ (u : set α) (v : set β), is_open u ∧ is_open v ∧ a ∈ u ∧ b ∈ v ∧ u ×ˢ v ⊆ s) :=
begin
  rw [is_open_iff_nhds],
  simp_rw [le_principal_iff, prod.forall,
    ((nhds_basis_opens _).prod_nhds (nhds_basis_opens _)).mem_iff, prod.exists, exists_prop],
  simp only [and_assoc, and.left_comm]
end

/-- A product of induced topologies is induced by the product map -/
lemma prod_induced_induced {α γ : Type*} (f : α → β) (g : γ → δ) :
  @prod.topological_space α γ (induced f ‹_›) (induced g ‹_›) =
  induced (λ p, (f p.1, g p.2)) prod.topological_space :=
by simp_rw [prod.topological_space, induced_inf, induced_compose]

lemma continuous_uncurry_of_discrete_topology_left [discrete_topology α]
  {f : α → β → γ} (h : ∀ a, continuous (f a)) : continuous (uncurry f) :=
continuous_iff_continuous_at.2 $ λ ⟨a, b⟩,
  by simp only [continuous_at, nhds_prod_eq, nhds_discrete α, pure_prod, tendsto_map'_iff, (∘),
    uncurry, (h a).tendsto]

/-- Given a neighborhood `s` of `(x, x)`, then `(x, x)` has a square open neighborhood
  that is a subset of `s`. -/
lemma exists_nhds_square {s : set (α × α)} {x : α} (hx : s ∈ 𝓝 (x, x)) :
  ∃ U : set α, is_open U ∧ x ∈ U ∧ U ×ˢ U ⊆ s :=
by simpa [nhds_prod_eq, (nhds_basis_opens x).prod_self.mem_iff, and.assoc, and.left_comm] using hx

/-- `prod.fst` maps neighborhood of `x : α × β` within the section `prod.snd ⁻¹' {x.2}`
to `𝓝 x.1`. -/
lemma map_fst_nhds_within (x : α × β) : map prod.fst (𝓝[prod.snd ⁻¹' {x.2}] x) = 𝓝 x.1 :=
begin
  refine le_antisymm (continuous_at_fst.mono_left inf_le_left) (λ s hs, _),
  rcases x with ⟨x, y⟩,
  rw [mem_map, nhds_within, mem_inf_principal, mem_nhds_prod_iff] at hs,
  rcases hs with ⟨u, hu, v, hv, H⟩,
  simp only [prod_subset_iff, mem_singleton_iff, mem_set_of_eq, mem_preimage] at H,
  exact mem_of_superset hu (λ z hz, H _ hz _ (mem_of_mem_nhds hv) rfl)
end

@[simp] lemma map_fst_nhds (x : α × β) : map prod.fst (𝓝 x) = 𝓝 x.1 :=
le_antisymm continuous_at_fst $ (map_fst_nhds_within x).symm.trans_le (map_mono inf_le_left)

/-- The first projection in a product of topological spaces sends open sets to open sets. -/
lemma is_open_map_fst : is_open_map (@prod.fst α β) :=
is_open_map_iff_nhds_le.2 $ λ x, (map_fst_nhds x).ge

/-- `prod.snd` maps neighborhood of `x : α × β` within the section `prod.fst ⁻¹' {x.1}`
to `𝓝 x.2`. -/
lemma map_snd_nhds_within (x : α × β) : map prod.snd (𝓝[prod.fst ⁻¹' {x.1}] x) = 𝓝 x.2 :=
begin
  refine le_antisymm (continuous_at_snd.mono_left inf_le_left) (λ s hs, _),
  rcases x with ⟨x, y⟩,
  rw [mem_map, nhds_within, mem_inf_principal, mem_nhds_prod_iff] at hs,
  rcases hs with ⟨u, hu, v, hv, H⟩,
  simp only [prod_subset_iff, mem_singleton_iff, mem_set_of_eq, mem_preimage] at H,
  exact mem_of_superset hv (λ z hz, H _ (mem_of_mem_nhds hu) _ hz rfl)
end

@[simp] lemma map_snd_nhds (x : α × β) : map prod.snd (𝓝 x) = 𝓝 x.2 :=
le_antisymm continuous_at_snd $ (map_snd_nhds_within x).symm.trans_le (map_mono inf_le_left)

/-- The second projection in a product of topological spaces sends open sets to open sets. -/
lemma is_open_map_snd : is_open_map (@prod.snd α β) :=
is_open_map_iff_nhds_le.2 $ λ x, (map_snd_nhds x).ge

/-- A product set is open in a product space if and only if each factor is open, or one of them is
empty -/
lemma is_open_prod_iff' {s : set α} {t : set β} :
  is_open (s ×ˢ t) ↔ (is_open s ∧ is_open t) ∨ (s = ∅) ∨ (t = ∅) :=
begin
  cases (s ×ˢ t).eq_empty_or_nonempty with h h,
  { simp [h, prod_eq_empty_iff.1 h] },
  { have st : s.nonempty ∧ t.nonempty, from prod_nonempty_iff.1 h,
    split,
    { assume H : is_open (s ×ˢ t),
      refine or.inl ⟨_, _⟩,
      show is_open s,
      { rw ← fst_image_prod s st.2,
        exact is_open_map_fst _ H },
      show is_open t,
      { rw ← snd_image_prod st.1 t,
        exact is_open_map_snd _ H } },
    { assume H,
      simp only [st.1.ne_empty, st.2.ne_empty, not_false_iff, or_false] at H,
      exact H.1.prod H.2 } }
end

lemma closure_prod_eq {s : set α} {t : set β} :
  closure (s ×ˢ t) = closure s ×ˢ closure t :=
set.ext $ assume ⟨a, b⟩,
have (𝓝 a ×ᶠ 𝓝 b) ⊓ 𝓟 (s ×ˢ t) = (𝓝 a ⊓ 𝓟 s) ×ᶠ (𝓝 b ⊓ 𝓟 t),
  by rw [←prod_inf_prod, prod_principal_principal],
by simp [closure_eq_cluster_pts, cluster_pt, nhds_prod_eq, this]; exact prod_ne_bot

lemma interior_prod_eq (s : set α) (t : set β) :
  interior (s ×ˢ t) = interior s ×ˢ interior t :=
set.ext $ λ ⟨a, b⟩, by simp only [mem_interior_iff_mem_nhds, mem_prod, prod_mem_nhds_iff]

lemma frontier_prod_eq (s : set α) (t : set β) :
  frontier (s ×ˢ t) = closure s ×ˢ frontier t ∪ frontier s ×ˢ closure t :=
by simp only [frontier, closure_prod_eq, interior_prod_eq, prod_diff_prod]

@[simp] lemma frontier_prod_univ_eq (s : set α) :
  frontier (s ×ˢ (univ : set β)) = frontier s ×ˢ univ :=
by simp [frontier_prod_eq]

@[simp] lemma frontier_univ_prod_eq (s : set β) :
  frontier ((univ : set α) ×ˢ s) = univ ×ˢ frontier s :=
by simp [frontier_prod_eq]

lemma map_mem_closure₂ {f : α → β → γ} {a : α} {b : β} {s : set α} {t : set β} {u : set γ}
  (hf : continuous (uncurry f)) (ha : a ∈ closure s) (hb : b ∈ closure t)
  (h : ∀ (a ∈ s) (b ∈ t), f a b ∈ u) :
  f a b ∈ closure u :=
have H₁ : (a, b) ∈ closure (s ×ˢ t), by simpa only [closure_prod_eq] using mk_mem_prod ha hb,
have H₂ : maps_to (uncurry f) (s ×ˢ t) u, from forall_prod_set.2 h,
H₂.closure hf H₁

lemma is_closed.prod {s₁ : set α} {s₂ : set β} (h₁ : is_closed s₁) (h₂ : is_closed s₂) :
  is_closed (s₁ ×ˢ s₂) :=
closure_eq_iff_is_closed.mp $ by simp only [h₁.closure_eq, h₂.closure_eq, closure_prod_eq]

/-- The product of two dense sets is a dense set. -/
lemma dense.prod {s : set α} {t : set β} (hs : dense s) (ht : dense t) :
  dense (s ×ˢ t) :=
λ x, by { rw closure_prod_eq, exact ⟨hs x.1, ht x.2⟩ }

/-- If `f` and `g` are maps with dense range, then `prod.map f g` has dense range. -/
lemma dense_range.prod_map {ι : Type*} {κ : Type*} {f : ι → β} {g : κ → γ}
  (hf : dense_range f) (hg : dense_range g) : dense_range (prod.map f g) :=
by simpa only [dense_range, prod_range_range_eq] using hf.prod hg

lemma inducing.prod_mk {f : α → β} {g : γ → δ} (hf : inducing f) (hg : inducing g) :
  inducing (λx:α×γ, (f x.1, g x.2)) :=
⟨by rw [prod.topological_space, prod.topological_space, hf.induced, hg.induced,
         induced_compose, induced_compose, induced_inf, induced_compose, induced_compose]⟩

lemma embedding.prod_mk {f : α → β} {g : γ → δ} (hf : embedding f) (hg : embedding g) :
  embedding (λx:α×γ, (f x.1, g x.2)) :=
{ inj := assume ⟨x₁, x₂⟩ ⟨y₁, y₂⟩, by simp; exact assume h₁ h₂, ⟨hf.inj h₁, hg.inj h₂⟩,
  ..hf.to_inducing.prod_mk hg.to_inducing }

protected lemma is_open_map.prod {f : α → β} {g : γ → δ} (hf : is_open_map f) (hg : is_open_map g) :
  is_open_map (λ p : α × γ, (f p.1, g p.2)) :=
begin
  rw [is_open_map_iff_nhds_le],
  rintros ⟨a, b⟩,
  rw [nhds_prod_eq, nhds_prod_eq, ← filter.prod_map_map_eq],
  exact filter.prod_mono (hf.nhds_le a) (hg.nhds_le b)
end

protected lemma open_embedding.prod {f : α → β} {g : γ → δ}
  (hf : open_embedding f) (hg : open_embedding g) : open_embedding (λ x : α × γ, (f x.1, g x.2)) :=
open_embedding_of_embedding_open (hf.1.prod_mk hg.1)
  (hf.is_open_map.prod hg.is_open_map)

lemma embedding_graph {f : α → β} (hf : continuous f) : embedding (λ x, (x, f x)) :=
embedding_of_embedding_compose (continuous_id.prod_mk hf) continuous_fst embedding_id

end prod

section sum
open sum
variables [topological_space α] [topological_space β] [topological_space γ] [topological_space δ]

@[continuity] lemma continuous_inl : continuous (@inl α β) :=
continuous_sup_rng_left continuous_coinduced_rng

@[continuity] lemma continuous_inr : continuous (@inr α β) :=
continuous_sup_rng_right continuous_coinduced_rng

lemma is_open_sum_iff {s : set (α ⊕ β)} :
  is_open s ↔ is_open (inl ⁻¹' s) ∧ is_open (inr ⁻¹' s) :=
iff.rfl

lemma is_open_map_inl : is_open_map (@inl α β) :=
λ u hu, by simpa [is_open_sum_iff, preimage_image_eq u sum.inl_injective]

lemma is_open_map_inr : is_open_map (@inr α β) :=
λ u hu, by simpa [is_open_sum_iff, preimage_image_eq u sum.inr_injective]

lemma open_embedding_inl : open_embedding (@inl α β) :=
open_embedding_of_continuous_injective_open continuous_inl inl_injective is_open_map_inl

lemma open_embedding_inr : open_embedding (@inr α β) :=
open_embedding_of_continuous_injective_open continuous_inr inr_injective is_open_map_inr

lemma embedding_inl : embedding (@inl α β) := open_embedding_inl.1

lemma embedding_inr : embedding (@inr α β) := open_embedding_inr.1

lemma is_open_range_inl : is_open (range (inl : α → α ⊕ β)) := open_embedding_inl.2

lemma is_open_range_inr : is_open (range (inr : β → α ⊕ β)) := open_embedding_inr.2

lemma is_closed_range_inl : is_closed (range (inl : α → α ⊕ β)) :=
by { rw [← is_open_compl_iff, compl_range_inl], exact is_open_range_inr }

lemma is_closed_range_inr : is_closed (range (inr : β → α ⊕ β)) :=
by { rw [← is_open_compl_iff, compl_range_inr], exact is_open_range_inl }

lemma closed_embedding_inl : closed_embedding (inl : α → α ⊕ β) :=
⟨embedding_inl, is_closed_range_inl⟩

lemma closed_embedding_inr : closed_embedding (inr : β → α ⊕ β) :=
⟨embedding_inr, is_closed_range_inr⟩

lemma nhds_inl (x : α) : 𝓝 (inl x : α ⊕ β) = map inl (𝓝 x) :=
(open_embedding_inl.map_nhds_eq _).symm

lemma nhds_inr (x : β) : 𝓝 (inr x : α ⊕ β) = map inr (𝓝 x) :=
(open_embedding_inr.map_nhds_eq _).symm

theorem continuous_sum_dom {f : α ⊕ β → γ} :
    continuous f ↔ continuous (f ∘ sum.inl) ∧ continuous (f ∘ sum.inr) :=
by simp only [continuous_sup_dom, continuous_coinduced_dom]

lemma continuous_sum_elim {f : α → γ} {g : β → γ} :
  continuous (sum.elim f g) ↔ continuous f ∧ continuous g :=
continuous_sum_dom

@[continuity] lemma continuous.sum_elim {f : α → γ} {g : β → γ}
  (hf : continuous f) (hg : continuous g) : continuous (sum.elim f g) :=
continuous_sum_elim.2 ⟨hf, hg⟩

@[simp] lemma continuous_sum_map {f : α → β} {g : γ → δ} :
  continuous (sum.map f g) ↔ continuous f ∧ continuous g :=
continuous_sum_elim.trans $ embedding_inl.continuous_iff.symm.and embedding_inr.continuous_iff.symm

@[continuity] lemma continuous.sum_map {f : α → β} {g : γ → δ} (hf : continuous f)
  (hg : continuous g) : continuous (sum.map f g) :=
continuous_sum_map.2 ⟨hf, hg⟩

lemma is_open_map_sum {f : α ⊕ β → γ} :
  is_open_map f ↔ is_open_map (λ a, f (inl a)) ∧ is_open_map (λ b, f (inr b)) :=
by simp only [is_open_map_iff_nhds_le, sum.forall, nhds_inl, nhds_inr, filter.map_map]

@[simp] lemma is_open_map_sum_elim {f : α → γ} {g : β → γ} :
  is_open_map (sum.elim f g) ↔ is_open_map f ∧ is_open_map g :=
by simp only [is_open_map_sum, elim_inl, elim_inr]

lemma is_open_map.sum_elim {f : α → γ} {g : β → γ} (hf : is_open_map f) (hg : is_open_map g) :
  is_open_map (sum.elim f g) :=
is_open_map_sum_elim.2 ⟨hf, hg⟩

end sum

section subtype
variables [topological_space α] [topological_space β] [topological_space γ] {p : α → Prop}

lemma inducing_coe {b : set β} : inducing (coe : b → β) := ⟨rfl⟩

lemma inducing.of_cod_restrict {f : α → β} {b : set β} (hb : ∀ a, f a ∈ b)
  (h : inducing (b.cod_restrict f hb)) : inducing f := inducing_coe.comp h

lemma embedding_subtype_coe : embedding (coe : subtype p → α) :=
⟨⟨rfl⟩, subtype.coe_injective⟩

lemma closed_embedding_subtype_coe (h : is_closed {a | p a}) :
  closed_embedding (coe : subtype p → α) :=
⟨embedding_subtype_coe, by rwa [subtype.range_coe_subtype]⟩

@[continuity] lemma continuous_subtype_val : continuous (@subtype.val α p) :=
continuous_induced_dom

lemma continuous_subtype_coe : continuous (coe : subtype p → α) :=
continuous_subtype_val

lemma continuous.subtype_coe {f : β → subtype p} (hf : continuous f) :
  continuous (λ x, (f x : α)) :=
continuous_subtype_coe.comp hf

lemma is_open.open_embedding_subtype_coe {s : set α} (hs : is_open s) :
  open_embedding (coe : s → α) :=
{ induced := rfl,
  inj := subtype.coe_injective,
  open_range := (subtype.range_coe : range coe = s).symm ▸  hs }

lemma is_open.is_open_map_subtype_coe {s : set α} (hs : is_open s) :
  is_open_map (coe : s → α) :=
hs.open_embedding_subtype_coe.is_open_map

lemma is_open_map.restrict {f : α → β} (hf : is_open_map f) {s : set α} (hs : is_open s) :
  is_open_map (s.restrict f) :=
hf.comp hs.is_open_map_subtype_coe

lemma is_closed.closed_embedding_subtype_coe {s : set α} (hs : is_closed s) :
  closed_embedding (coe : {x // x ∈ s} → α) :=
{ induced := rfl,
  inj := subtype.coe_injective,
  closed_range := (subtype.range_coe : range coe = s).symm ▸ hs }

@[continuity] lemma continuous.subtype_mk {f : β → α} (h : continuous f)
  (hp : ∀x, p (f x)) : continuous (λx, (⟨f x, hp x⟩ : subtype p)) :=
continuous_induced_rng.2 h

lemma continuous.subtype_map {f : α → β} (h : continuous f) {q : β → Prop}
  (hpq : ∀ x, p x → q (f x)) : continuous (subtype.map f hpq) :=
(h.comp continuous_subtype_coe).subtype_mk _

lemma continuous_inclusion {s t : set α} (h : s ⊆ t) : continuous (inclusion h) :=
continuous_id.subtype_map h

lemma continuous_at_subtype_coe {p : α → Prop} {a : subtype p} :
  continuous_at (coe : subtype p → α) a :=
continuous_iff_continuous_at.mp continuous_subtype_coe _

lemma subtype.dense_iff {s : set α} {t : set s} : dense t ↔ s ⊆ closure (coe '' t) :=
by { rw [inducing_coe.dense_iff, set_coe.forall], refl }

lemma map_nhds_subtype_coe_eq {a : α} (ha : p a) (h : {a | p a} ∈ 𝓝 a) :
  map (coe : subtype p → α) (𝓝 ⟨a, ha⟩) = 𝓝 a :=
map_nhds_induced_of_mem $ by simpa only [subtype.coe_mk, subtype.range_coe] using h

lemma nhds_subtype_eq_comap {a : α} {h : p a} :
  𝓝 (⟨a, h⟩ : subtype p) = comap coe (𝓝 a) :=
nhds_induced _ _

lemma tendsto_subtype_rng {β : Type*} {p : α → Prop} {b : filter β} {f : β → subtype p} :
  ∀{a:subtype p}, tendsto f b (𝓝 a) ↔ tendsto (λx, (f x : α)) b (𝓝 (a : α))
| ⟨a, ha⟩ := by rw [nhds_subtype_eq_comap, tendsto_comap_iff, subtype.coe_mk]

lemma continuous_subtype_nhds_cover {ι : Sort*} {f : α → β} {c : ι → α → Prop}
  (c_cover : ∀x:α, ∃i, {x | c i x} ∈ 𝓝 x)
  (f_cont  : ∀i, continuous (λ(x : subtype (c i)), f x)) :
  continuous f :=
continuous_iff_continuous_at.mpr $ assume x,
  let ⟨i, (c_sets : {x | c i x} ∈ 𝓝 x)⟩ := c_cover x in
  let x' : subtype (c i) := ⟨x, mem_of_mem_nhds c_sets⟩ in
  calc map f (𝓝 x) = map f (map coe (𝓝 x')) :
      congr_arg (map f) (map_nhds_subtype_coe_eq _ $ c_sets).symm
    ... = map (λx:subtype (c i), f x) (𝓝 x') : rfl
    ... ≤ 𝓝 (f x) : continuous_iff_continuous_at.mp (f_cont i) x'

lemma continuous_subtype_is_closed_cover {ι : Sort*} {f : α → β} (c : ι → α → Prop)
  (h_lf : locally_finite (λi, {x | c i x}))
  (h_is_closed : ∀i, is_closed {x | c i x})
  (h_cover : ∀x, ∃i, c i x)
  (f_cont  : ∀i, continuous (λ(x : subtype (c i)), f x)) :
  continuous f :=
continuous_iff_is_closed.mpr $
  assume s hs,
  have ∀i, is_closed ((coe : {x | c i x} → α) '' (f ∘ coe ⁻¹' s)),
    from assume i,
    (closed_embedding_subtype_coe (h_is_closed _)).is_closed_map _ (hs.preimage (f_cont i)),
  have is_closed (⋃i, (coe : {x | c i x} → α) '' (f ∘ coe ⁻¹' s)),
    from locally_finite.is_closed_Union
      (h_lf.subset $ assume i x ⟨⟨x', hx'⟩, _, heq⟩, heq ▸ hx')
      this,
  have f ⁻¹' s = (⋃i, (coe : {x | c i x} → α) '' (f ∘ coe ⁻¹' s)),
  begin
    apply set.ext,
    have : ∀ (x : α), f x ∈ s ↔ ∃ (i : ι), c i x ∧ f x ∈ s :=
      λ x, ⟨λ hx, let ⟨i, hi⟩ := h_cover x in ⟨i, hi, hx⟩,
            λ ⟨i, hi, hx⟩, hx⟩,
    simpa [and.comm, @and.left_comm (c _ _), ← exists_and_distrib_right],
  end,
  by rwa [this]

lemma closure_subtype {x : {a // p a}} {s : set {a // p a}}:
  x ∈ closure s ↔ (x : α) ∈ closure ((coe : _ → α) '' s) :=
closure_induced

lemma continuous_at_cod_restrict_iff {f : α → β} {t : set β} (h1 : ∀ x, f x ∈ t) {x : α} :
  continuous_at (cod_restrict f t h1) x ↔ continuous_at f x :=
by simp_rw [inducing_coe.continuous_at_iff, function.comp, coe_cod_restrict_apply]

alias continuous_at_cod_restrict_iff ↔ _ continuous_at.cod_restrict

lemma continuous_at.restrict {f : α → β} {s : set α} {t : set β} (h1 : maps_to f s t) {x : s}
  (h2 : continuous_at f x) : continuous_at (h1.restrict f s t) x :=
(h2.comp continuous_at_subtype_coe).cod_restrict _

lemma continuous_at.restrict_preimage {f : α → β} {s : set β} {x : f ⁻¹' s}
  (h : continuous_at f x) : continuous_at (s.restrict_preimage f) x :=
h.restrict _

@[continuity] lemma continuous.cod_restrict {f : α → β} {s : set β} (hf : continuous f)
  (hs : ∀ a, f a ∈ s) : continuous (s.cod_restrict f hs) := hf.subtype_mk hs

lemma inducing.cod_restrict {e : α → β} (he : inducing e) {s : set β} (hs : ∀ x, e x ∈ s) :
  inducing (cod_restrict e s hs) :=
inducing_of_inducing_compose (he.continuous.cod_restrict hs) continuous_subtype_coe he

lemma embedding.cod_restrict {e : α → β} (he : embedding e) (s : set β) (hs : ∀ x, e x ∈ s) :
  embedding (cod_restrict e s hs) :=
embedding_of_embedding_compose (he.continuous.cod_restrict hs) continuous_subtype_coe he

lemma embedding_inclusion {s t : set α} (h : s ⊆ t) : embedding (set.inclusion h) :=
embedding_subtype_coe.cod_restrict _ _

/-- Let `s, t ⊆ X` be two subsets of a topological space `X`.  If `t ⊆ s` and the topology induced
by `X`on `s` is discrete, then also the topology induces on `t` is discrete.  -/
lemma discrete_topology.of_subset {X : Type*} [topological_space X] {s t : set X}
  (ds : discrete_topology s) (ts : t ⊆ s) :
  discrete_topology t :=
(embedding_inclusion ts).discrete_topology

end subtype

section quotient
variables [topological_space α] [topological_space β] [topological_space γ]
variables {r : α → α → Prop} {s : setoid α}

lemma quotient_map_quot_mk : quotient_map (@quot.mk α r) :=
⟨quot.exists_rep, rfl⟩

@[continuity] lemma continuous_quot_mk : continuous (@quot.mk α r) :=
continuous_coinduced_rng

@[continuity] lemma continuous_quot_lift {f : α → β} (hr : ∀ a b, r a b → f a = f b)
  (h : continuous f) : continuous (quot.lift f hr : quot r → β) :=
continuous_coinduced_dom.2 h

lemma quotient_map_quotient_mk : quotient_map (@quotient.mk α s) :=
quotient_map_quot_mk

lemma continuous_quotient_mk : continuous (@quotient.mk α s) :=
continuous_coinduced_rng

lemma continuous.quotient_lift {f : α → β} (h : continuous f) (hs : ∀ a b, a ≈ b → f a = f b) :
  continuous (quotient.lift f hs : quotient s → β) :=
continuous_coinduced_dom.2 h

lemma continuous.quotient_lift_on' {f : α → β} (h : continuous f)
  (hs : ∀ a b, @setoid.r _ s a b → f a = f b) :
  continuous (λ x, quotient.lift_on' x f hs : quotient s → β) :=
h.quotient_lift hs

lemma continuous.quotient_map' {t : setoid β} {f : α → β} (hf : continuous f)
  (H : (s.r ⇒ t.r) f f) : continuous (quotient.map' f H) :=
(continuous_quotient_mk.comp hf).quotient_lift _

end quotient

section pi
variables {ι : Type*} {π : ι → Type*} {κ : Type*}
  [topological_space α] [∀i, topological_space (π i)] {f : α → Πi:ι, π i}

lemma continuous_pi_iff : continuous f ↔ ∀ i, continuous (λ a, f a i) :=
by simp only [continuous_infi_rng, continuous_induced_rng]

@[continuity] lemma continuous_pi (h : ∀ i, continuous (λ a, f a i)) : continuous f :=
continuous_pi_iff.2 h

@[continuity] lemma continuous_apply (i : ι) : continuous (λp:Πi, π i, p i) :=
continuous_infi_dom continuous_induced_dom

@[continuity]
lemma continuous_apply_apply {ρ : κ → ι → Type*} [∀ j i, topological_space (ρ j i)]
  (j : κ) (i : ι) : continuous (λ p : (Π j, Π i, ρ j i), p j i) :=
(continuous_apply i).comp (continuous_apply j)

lemma continuous_at_apply (i : ι) (x : Π i, π i) : continuous_at (λ p : Π i, π i, p i) x :=
(continuous_apply i).continuous_at

lemma filter.tendsto.apply {l : filter β} {f : β → Π i, π i}
  {x : Π i, π i} (h : tendsto f l (𝓝 x)) (i : ι) :
  tendsto (λ a, f a i) l (𝓝 $ x i) :=
(continuous_at_apply i _).tendsto.comp h

lemma nhds_pi {a : Πi, π i} : 𝓝 a = pi (λ i, 𝓝 (a i)) :=
by simp only [nhds_infi, nhds_induced, filter.pi]

lemma tendsto_pi_nhds {f : β → Πi, π i} {g : Πi, π i} {u : filter β} :
  tendsto f u (𝓝 g) ↔ ∀ x, tendsto (λ i, f i x) u (𝓝 (g x)) :=
by rw [nhds_pi, filter.tendsto_pi]

lemma continuous_at_pi {f : α → Π i, π i} {x : α} :
  continuous_at f x ↔ ∀ i, continuous_at (λ y, f y i) x :=
tendsto_pi_nhds

lemma filter.tendsto.update [decidable_eq ι]
  {l : filter β} {f : β → Π i, π i} {x : Π i, π i} (hf : tendsto f l (𝓝 x)) (i : ι)
  {g : β → π i} {xi : π i} (hg : tendsto g l (𝓝 xi)) :
  tendsto (λ a, update (f a) i (g a)) l (𝓝 $ update x i xi) :=
tendsto_pi_nhds.2 $ λ j, by { rcases em (j = i) with rfl|hj; simp [*, hf.apply] }

lemma continuous_at.update [decidable_eq ι] {a : α} (hf : continuous_at f a) (i : ι) {g : α → π i}
  (hg : continuous_at g a) :
  continuous_at (λ a, update (f a) i (g a)) a :=
hf.update i hg

lemma continuous.update [decidable_eq ι] (hf : continuous f) (i : ι) {g : α → π i}
  (hg : continuous g) :
  continuous (λ a, update (f a) i (g a)) :=
continuous_iff_continuous_at.2 $ λ x, hf.continuous_at.update i hg.continuous_at

/-- `function.update f i x` is continuous in `(f, x)`. -/
@[continuity] lemma continuous_update [decidable_eq ι] (i : ι) :
  continuous (λ f : (Π j, π j) × π i, update f.1 i f.2) :=
continuous_fst.update i continuous_snd

/-- `pi.mul_single i x` is continuous in `x`. -/
@[continuity, to_additive "`pi.single i x` is continuous in `x`."]
lemma continuous_mul_single [Π i, has_one (π i)] [decidable_eq ι] (i : ι) :
  continuous (λ x, (pi.mul_single i x : Π i, π i)) :=
continuous_const.update _ continuous_id

lemma filter.tendsto.fin_insert_nth {n} {π : fin (n + 1) → Type*} [Π i, topological_space (π i)]
  (i : fin (n + 1)) {f : β → π i} {l : filter β} {x : π i} (hf : tendsto f l (𝓝 x))
  {g : β → Π j : fin n, π (i.succ_above j)} {y : Π j, π (i.succ_above j)} (hg : tendsto g l (𝓝 y)) :
  tendsto (λ a, i.insert_nth (f a) (g a)) l (𝓝 $ i.insert_nth x y) :=
tendsto_pi_nhds.2 (λ j, fin.succ_above_cases i (by simpa) (by simpa using tendsto_pi_nhds.1 hg) j)

lemma continuous_at.fin_insert_nth {n} {π : fin (n + 1) → Type*} [Π i, topological_space (π i)]
  (i : fin (n + 1)) {f : α → π i} {a : α} (hf : continuous_at f a)
  {g : α → Π j : fin n, π (i.succ_above j)} (hg : continuous_at g a) :
  continuous_at (λ a, i.insert_nth (f a) (g a)) a :=
hf.fin_insert_nth i hg

lemma continuous.fin_insert_nth {n} {π : fin (n + 1) → Type*} [Π i, topological_space (π i)]
  (i : fin (n + 1)) {f : α → π i} (hf : continuous f)
  {g : α → Π j : fin n, π (i.succ_above j)} (hg : continuous g) :
  continuous (λ a, i.insert_nth (f a) (g a)) :=
continuous_iff_continuous_at.2 $ λ a, hf.continuous_at.fin_insert_nth i hg.continuous_at

lemma is_open_set_pi {i : set ι} {s : Πa, set (π a)} (hi : i.finite) (hs : ∀a∈i, is_open (s a)) :
  is_open (pi i s) :=
by rw [pi_def]; exact (is_open_bInter hi $ assume a ha, (hs _ ha).preimage (continuous_apply _))

lemma is_open_pi_iff {s : set (Π a, π a)} :
  is_open s ↔
  (∀ f, f ∈ s → ∃ (I : finset ι) (u : Π a, set (π a)),
    (∀ a, a ∈ I → is_open (u a) ∧ f a ∈ u a) ∧ (I : set ι).pi u ⊆ s) :=
begin
  rw is_open_iff_nhds,
  simp_rw [le_principal_iff, nhds_pi, filter.mem_pi', mem_nhds_iff, exists_prop],
  refine ball_congr (λ a h, ⟨_, _⟩),
  { rintros ⟨I, t, ⟨h1, h2⟩⟩,
    refine ⟨I, λ a, eval a '' ((I : set ι).pi (λ a, (h1 a).some)), (λ i hi, _), _⟩,
    { simp_rw set.eval_image_pi (finset.mem_coe.mpr hi)
        (pi_nonempty_iff.mpr (λ i, ⟨_, λ _, (h1 i).some_spec.2.2⟩)),
      exact (h1 i).some_spec.2, },
    { refine subset.trans
        (set.pi_mono (λ i hi, (set.eval_image_pi_subset hi).trans (h1 i).some_spec.1)) h2, }},
  { rintros ⟨I, t, ⟨h1, h2⟩⟩,
    refine ⟨I, λ a, ite (a ∈ I) (t a) (set.univ), (λ i, _), _⟩,
    { by_cases hi : i ∈ I,
      { use t i,
        rw if_pos hi,
        exact ⟨subset.rfl, (h1 i) hi⟩, },
      { use set.univ,
        rw if_neg hi,
        exact ⟨subset.rfl, is_open_univ, mem_univ _⟩, }},
    { rw ← set.univ_pi_ite,
      simp only [ ← ite_and, ← finset.mem_coe, and_self, set.univ_pi_ite, h2], }}
end

lemma is_open_pi_iff' [finite ι]  {s : set (Π a, π a)} :
  is_open s ↔
  (∀ f, f ∈ s → ∃ (u : Π a, set (π a)), (∀ a, is_open (u a) ∧ f a ∈ u a) ∧ set.univ.pi u ⊆ s) :=
begin
  casesI nonempty_fintype ι,
  rw is_open_iff_nhds,
  simp_rw [le_principal_iff, nhds_pi, filter.mem_pi', mem_nhds_iff, exists_prop],
  refine ball_congr (λ a h, ⟨_, _⟩),
  { rintros ⟨I, t, ⟨h1, h2⟩⟩,
    refine ⟨λ i, (h1 i).some, ⟨λ i, (h1 i).some_spec.2,
        (set.pi_mono (λ i _, (h1 i).some_spec.1)).trans (subset.trans _ h2)⟩⟩,
    rw ← set.pi_inter_compl (I : set ι),
    exact inter_subset_left _ _, },
  { exact λ ⟨u, ⟨h1, _⟩⟩, ⟨finset.univ, u, ⟨λ i, ⟨u i, ⟨rfl.subset, h1 i⟩⟩,
      by rwa finset.coe_univ⟩⟩, }
end

lemma is_closed_set_pi {i : set ι} {s : Πa, set (π a)} (hs : ∀a∈i, is_closed (s a)) :
  is_closed (pi i s) :=
by rw [pi_def];
  exact (is_closed_Inter $ λ a, is_closed_Inter $ λ ha, (hs _ ha).preimage (continuous_apply _))

lemma mem_nhds_of_pi_mem_nhds {I : set ι} {s : Π i, set (π i)} (a : Π i, π i) (hs : I.pi s ∈ 𝓝 a)
  {i : ι} (hi : i ∈ I) :
  s i ∈ 𝓝 (a i) :=
by { rw nhds_pi at hs, exact mem_of_pi_mem_pi hs hi }

lemma set_pi_mem_nhds {i : set ι} {s : Π a, set (π a)}
  {x : Π a, π a} (hi : i.finite) (hs : ∀ a ∈ i, s a ∈ 𝓝 (x a)) :
  pi i s ∈ 𝓝 x :=
by { rw [pi_def, bInter_mem hi], exact λ a ha, (continuous_apply a).continuous_at (hs a ha) }

lemma set_pi_mem_nhds_iff {I : set ι} (hI : I.finite) {s : Π i, set (π i)} (a : Π i, π i) :
  I.pi s ∈ 𝓝 a ↔ ∀ (i : ι), i ∈ I → s i ∈ 𝓝 (a i) :=
by { rw [nhds_pi, pi_mem_pi_iff hI], apply_instance }

lemma interior_pi_set {I : set ι} (hI : I.finite) {s : Π i, set (π i)} :
  interior (pi I s) = I.pi (λ i, interior (s i)) :=
by { ext a, simp only [set.mem_pi, mem_interior_iff_mem_nhds, set_pi_mem_nhds_iff hI] }

lemma exists_finset_piecewise_mem_of_mem_nhds [decidable_eq ι]
  {s : set (Π a, π a)} {x : Π a, π a} (hs : s ∈ 𝓝 x) (y : Π a, π a) :
  ∃ I : finset ι, I.piecewise x y ∈ s :=
begin
  simp only [nhds_pi, filter.mem_pi'] at hs,
  rcases hs with ⟨I, t, htx, hts⟩,
  refine ⟨I, hts $ λ i hi, _⟩,
  simpa [finset.mem_coe.1 hi] using mem_of_mem_nhds (htx i)
end

lemma pi_eq_generate_from :
  Pi.topological_space =
  generate_from {g | ∃(s:Πa, set (π a)) (i : finset ι), (∀a∈i, is_open (s a)) ∧ g = pi ↑i s} :=
le_antisymm
  (le_generate_from $ assume g ⟨s, i, hi, eq⟩, eq.symm ▸ is_open_set_pi (finset.finite_to_set _) hi)
  (le_infi $ assume a s ⟨t, ht, s_eq⟩, generate_open.basic _ $
    ⟨update (λa, univ) a t, {a}, by simpa using ht, s_eq ▸ by ext f; simp [set.pi]⟩)

lemma pi_generate_from_eq {π : ι → Type*} {g : Πa, set (set (π a))} :
  @Pi.topological_space ι π (λa, generate_from (g a)) =
  generate_from {t | ∃(s:Πa, set (π a)) (i : finset ι), (∀a∈i, s a ∈ g a) ∧ t = pi ↑i s} :=
let G := {t | ∃(s:Πa, set (π a)) (i : finset ι), (∀a∈i, s a ∈ g a) ∧ t = pi ↑i s} in
begin
  rw [pi_eq_generate_from],
  refine le_antisymm (generate_from_anti _) (le_generate_from _),
  exact assume s ⟨t, i, ht, eq⟩, ⟨t, i, assume a ha, generate_open.basic _ (ht a ha), eq⟩,
  { rintros s ⟨t, i, hi, rfl⟩,
    rw [pi_def],
    apply is_open_bInter (finset.finite_to_set _),
    assume a ha, show ((generate_from G).coinduced (λf:Πa, π a, f a)).is_open (t a),
    refine le_generate_from _ _ (hi a ha),
    exact assume s hs, generate_open.basic _ ⟨update (λa, univ) a s, {a}, by simp [hs]⟩ }
end

lemma pi_generate_from_eq_finite {π : ι → Type*} {g : Πa, set (set (π a))} [finite ι]
  (hg : ∀a, ⋃₀ g a = univ) :
  @Pi.topological_space ι π (λa, generate_from (g a)) =
  generate_from {t | ∃(s:Πa, set (π a)), (∀a, s a ∈ g a) ∧ t = pi univ s} :=
begin
  casesI nonempty_fintype ι,
  rw [pi_generate_from_eq],
  refine le_antisymm (generate_from_anti _) (le_generate_from _),
  { rintro s ⟨t, ht, rfl⟩, exact ⟨t, finset.univ, by simp [ht]⟩ },
  { rintros s ⟨t, i, ht, rfl⟩,
    apply is_open_iff_forall_mem_open.2 _,
    assume f hf,
    choose c hc using show ∀a, ∃s, s ∈ g a ∧ f a ∈ s,
    { assume a, have : f a ∈ ⋃₀ g a, { rw [hg], apply mem_univ }, simpa },
    refine ⟨pi univ (λa, if a ∈ i then t a else (c : Πa, set (π a)) a), _, _, _⟩,
    { simp [pi_if] },
    { refine generate_open.basic _ ⟨_, assume a, _, rfl⟩,
      by_cases a ∈ i; simp [*, set.pi] at * },
    { have : f ∈ pi {a | a ∉ i} c, { simp [*, set.pi] at * },
      simpa [pi_if, hf] } }
end

/-- Suppose `π i` is a family of topological spaces indexed by `i : ι`, and `X` is a type
endowed with a family of maps `f i : X → π i` for every `i : ι`, hence inducing a
map `g : X → Π i, π i`. This lemma shows that infimum of the topologies on `X` induced by
the `f i` as `i : ι` varies is simply the topology on `X` induced by `g : X → Π i, π i`
where `Π i, π i` is endowed with the usual product topology. -/
lemma inducing_infi_to_pi {X : Type*} (f : Π i, X → π i) :
  @inducing X (Π i, π i) (⨅ i, induced (f i) infer_instance) _ (λ x i, f i x) :=
begin
  constructor,
  erw induced_infi,
  congr' 1,
  funext,
  erw induced_compose,
end

variables [finite ι] [∀ i, discrete_topology (π i)]

/-- A finite product of discrete spaces is discrete. -/
instance Pi.discrete_topology : discrete_topology (Π i, π i) :=
singletons_open_iff_discrete.mp (λ x,
begin
  rw show {x} = ⋂ i, {y : Π i, π i | y i = x i},
  { ext, simp only [funext_iff, set.mem_singleton_iff, set.mem_Inter, set.mem_set_of_eq] },
  exact is_open_Inter (λ i, (continuous_apply i).is_open_preimage {x i} (is_open_discrete {x i}))
end)

end pi

section sigma
variables {ι κ : Type*} {σ : ι → Type*} {τ : κ → Type*}
  [Π i, topological_space (σ i)] [Π k, topological_space (τ k)] [topological_space α]

@[continuity]
lemma continuous_sigma_mk {i : ι} : continuous (@sigma.mk ι σ i) :=
continuous_supr_rng continuous_coinduced_rng

lemma is_open_sigma_iff {s : set (sigma σ)} : is_open s ↔ ∀ i, is_open (sigma.mk i ⁻¹' s) :=
by simp only [is_open_supr_iff, is_open_coinduced]

lemma is_closed_sigma_iff {s : set (sigma σ)} : is_closed s ↔ ∀ i, is_closed (sigma.mk i ⁻¹' s) :=
by simp only [← is_open_compl_iff, is_open_sigma_iff, preimage_compl]

lemma is_open_map_sigma_mk {i : ι} : is_open_map (@sigma.mk ι σ i) :=
begin
  intros s hs,
  rw is_open_sigma_iff,
  intro j,
  rcases eq_or_ne j i with (rfl|hne),
  { rwa set.preimage_image_eq _ sigma_mk_injective },
  { rw [preimage_image_sigma_mk_of_ne hne],
    exact is_open_empty }
end

lemma is_open_range_sigma_mk {i : ι} : is_open (set.range (@sigma.mk ι σ i)) :=
is_open_map_sigma_mk.is_open_range

lemma is_closed_map_sigma_mk {i : ι} : is_closed_map (@sigma.mk ι σ i) :=
begin
  intros s hs,
  rw is_closed_sigma_iff,
  intro j,
  rcases eq_or_ne j i with (rfl|hne),
  { rwa set.preimage_image_eq _ sigma_mk_injective },
  { rw [preimage_image_sigma_mk_of_ne hne],
    exact is_closed_empty }
end

lemma is_closed_range_sigma_mk {i : ι} : is_closed (set.range (@sigma.mk ι σ i)) :=
is_closed_map_sigma_mk.closed_range

lemma open_embedding_sigma_mk {i : ι} : open_embedding (@sigma.mk ι σ i) :=
open_embedding_of_continuous_injective_open
  continuous_sigma_mk sigma_mk_injective is_open_map_sigma_mk

lemma closed_embedding_sigma_mk {i : ι} : closed_embedding (@sigma.mk ι σ i) :=
closed_embedding_of_continuous_injective_closed
  continuous_sigma_mk sigma_mk_injective is_closed_map_sigma_mk

lemma embedding_sigma_mk {i : ι} : embedding (@sigma.mk ι σ i) :=
closed_embedding_sigma_mk.1

lemma sigma.nhds_mk (i : ι) (x : σ i) : 𝓝 (⟨i, x⟩ : sigma σ) = map (sigma.mk i) (𝓝 x) :=
(open_embedding_sigma_mk.map_nhds_eq x).symm

lemma sigma.nhds_eq (x : sigma σ) : 𝓝 x = map (sigma.mk x.1) (𝓝 x.2) :=
by { cases x, apply sigma.nhds_mk }

lemma comap_sigma_mk_nhds (i : ι) (x : σ i) : comap (sigma.mk i) (𝓝 ⟨i, x⟩) = 𝓝 x :=
(embedding_sigma_mk.to_inducing.nhds_eq_comap _).symm

lemma is_open_sigma_fst_preimage (s : set ι) :  is_open (sigma.fst ⁻¹' s : set (Σ a, σ a)) :=
begin
  rw [← bUnion_of_singleton s, preimage_Union₂],
  simp only [← range_sigma_mk],
  exact is_open_bUnion (λ _ _, is_open_range_sigma_mk)
end

/-- A map out of a sum type is continuous iff its restriction to each summand is. -/
@[simp] lemma continuous_sigma_iff {f : sigma σ → α} :
  continuous f ↔ ∀ i, continuous (λ a, f ⟨i, a⟩) :=
by simp only [continuous_supr_dom, continuous_coinduced_dom]

/-- A map out of a sum type is continuous if its restriction to each summand is. -/
@[continuity] lemma continuous_sigma {f : sigma σ → α} (hf : ∀ i, continuous (λ a, f ⟨i, a⟩)) :
  continuous f :=
continuous_sigma_iff.2 hf

@[simp] lemma continuous_sigma_map {f₁ : ι → κ} {f₂ : Π i, σ i → τ (f₁ i)} :
  continuous (sigma.map f₁ f₂) ↔ ∀ i, continuous (f₂ i) :=
continuous_sigma_iff.trans $ by simp only [sigma.map, embedding_sigma_mk.continuous_iff]

@[continuity] lemma continuous.sigma_map {f₁ : ι → κ} {f₂ : Π i, σ i → τ (f₁ i)}
  (hf : ∀ i, continuous (f₂ i)) :
  continuous (sigma.map f₁ f₂) :=
continuous_sigma_map.2 hf

lemma is_open_map_sigma {f : sigma σ → α} : is_open_map f ↔ ∀ i, is_open_map (λ a, f ⟨i, a⟩) :=
by simp only [is_open_map_iff_nhds_le, sigma.forall, sigma.nhds_eq, map_map]

lemma is_open_map_sigma_map {f₁ : ι → κ} {f₂ : Π i, σ i → τ (f₁ i)} :
  is_open_map (sigma.map f₁ f₂) ↔ ∀ i, is_open_map (f₂ i) :=
is_open_map_sigma.trans $ forall_congr $
  λ i, (@open_embedding_sigma_mk _ _ _ (f₁ i)).is_open_map_iff.symm

lemma inducing_sigma_map {f₁ : ι → κ} {f₂ : Π i, σ i → τ (f₁ i)} (h₁ : injective f₁) :
  inducing (sigma.map f₁ f₂) ↔ ∀ i, inducing (f₂ i) :=
by simp only [inducing_iff_nhds, sigma.forall, sigma.nhds_mk, sigma.map, ← map_sigma_mk_comap h₁,
  map_inj sigma_mk_injective]

lemma embedding_sigma_map {f₁ : ι → κ} {f₂ : Π i, σ i → τ (f₁ i)} (h : injective f₁) :
  embedding (sigma.map f₁ f₂) ↔ ∀ i, embedding (f₂ i) :=
by simp only [embedding_iff, injective.sigma_map, inducing_sigma_map h, forall_and_distrib,
  h.sigma_map_iff]

lemma open_embedding_sigma_map {f₁ : ι → κ} {f₂ : Π i, σ i → τ (f₁ i)} (h : injective f₁) :
  open_embedding (sigma.map f₁ f₂) ↔ ∀ i, open_embedding (f₂ i) :=
by simp only [open_embedding_iff_embedding_open, is_open_map_sigma_map, embedding_sigma_map h,
  forall_and_distrib]

end sigma

section ulift

@[continuity] lemma continuous_ulift_down [topological_space α] :
  continuous (ulift.down : ulift.{v u} α → α) :=
continuous_induced_dom

@[continuity] lemma continuous_ulift_up [topological_space α] :
  continuous (ulift.up : α → ulift.{v u} α) :=
continuous_induced_rng.2 continuous_id

lemma embedding_ulift_down [topological_space α] :
  embedding (ulift.down : ulift.{v u} α → α) :=
⟨⟨rfl⟩, ulift.down_injective⟩

instance [topological_space α] [discrete_topology α] : discrete_topology (ulift α) :=
embedding_ulift_down.discrete_topology

end ulift
