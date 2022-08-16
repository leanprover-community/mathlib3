/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import topology.subset_properties
import topology.connected
import topology.nhds_set
import topology.inseparable

/-!
# Separation properties of topological spaces.

This file defines the predicate `separated`, and common separation axioms
(under the Kolmogorov classification).

## Main definitions

* `separated`: Two `set`s are separated if they are contained in disjoint open sets.
* `t0_space`: A T₀/Kolmogorov space is a space where, for every two points `x ≠ y`,
  there is an open set that contains one, but not the other.
* `t1_space`: A T₁/Fréchet space is a space where every singleton set is closed.
  This is equivalent to, for every pair `x ≠ y`, there existing an open set containing `x`
  but not `y` (`t1_space_iff_exists_open` shows that these conditions are equivalent.)
* `t2_space`: A T₂/Hausdorff space is a space where, for every two points `x ≠ y`,
  there is two disjoint open sets, one containing `x`, and the other `y`.
* `t2_5_space`: A T₂.₅/Urysohn space is a space where, for every two points `x ≠ y`,
  there is two open sets, one containing `x`, and the other `y`, whose closures are disjoint.
* `t3_space`: A T₃ space, is one where given any closed `C` and `x ∉ C`,
  there is disjoint open sets containing `x` and `C` respectively. In `mathlib`, T₃ implies T₂.₅.
* `normal_space`: A T₄ space (sometimes referred to as normal, but authors vary on
  whether this includes T₂; `mathlib` does), is one where given two disjoint closed sets,
  we can find two open sets that separate them. In `mathlib`, T₄ implies T₃.

## Main results

### T₀ spaces

* `is_closed.exists_closed_singleton` Given a closed set `S` in a compact T₀ space,
  there is some `x ∈ S` such that `{x}` is closed.
* `exists_open_singleton_of_open_finset` Given an open `finset` `S` in a T₀ space,
  there is some `x ∈ S` such that `{x}` is open.

### T₁ spaces

* `is_closed_map_const`: The constant map is a closed map.
* `discrete_of_t1_of_finite`: A finite T₁ space must have the discrete topology.

### T₂ spaces

* `t2_iff_nhds`: A space is T₂ iff the neighbourhoods of distinct points generate the bottom filter.
* `t2_iff_is_closed_diagonal`: A space is T₂ iff the `diagonal` of `α` (that is, the set of all
  points of the form `(a, a) : α × α`) is closed under the product topology.
* `finset_disjoint_finset_opens_of_t2`: Any two disjoint finsets are `separated`.
* Most topological constructions preserve Hausdorffness;
  these results are part of the typeclass inference system (e.g. `embedding.t2_space`)
* `set.eq_on.closure`: If two functions are equal on some set `s`, they are equal on its closure.
* `is_compact.is_closed`: All compact sets are closed.
* `locally_compact_of_compact_nhds`: If every point has a compact neighbourhood,
  then the space is locally compact.
* `tot_sep_of_zero_dim`: If `α` has a clopen basis, it is a `totally_separated_space`.
* `loc_compact_t2_tot_disc_iff_tot_sep`: A locally compact T₂ space is totally disconnected iff
  it is totally separated.

If the space is also compact:

* `normal_of_compact_t2`: A compact T₂ space is a `normal_space`.
* `connected_components_eq_Inter_clopen`: The connected component of a point
  is the intersection of all its clopen neighbourhoods.
* `compact_t2_tot_disc_iff_tot_sep`: Being a `totally_disconnected_space`
  is equivalent to being a `totally_separated_space`.
* `connected_components.t2`: `connected_components α` is T₂ for `α` T₂ and compact.

### T₃ spaces

* `disjoint_nested_nhds`: Given two points `x ≠ y`, we can find neighbourhoods `x ∈ V₁ ⊆ U₁` and
  `y ∈ V₂ ⊆ U₂`, with the `Vₖ` closed and the `Uₖ` open, such that the `Uₖ` are disjoint.

### Discrete spaces

* `discrete_topology_iff_nhds`: Discrete topological spaces are those whose neighbourhood
  filters are the `pure` filter (which is the principal filter at a singleton).
* `induced_bot`/`discrete_topology_induced`: The pullback of the discrete topology
  under an inclusion is the discrete topology.

## References

https://en.wikipedia.org/wiki/Separation_axiom
-/

open function set filter topological_space
open_locale topological_space filter classical

universes u v
variables {α : Type u} {β : Type v} [topological_space α]

section separation

/--
`separated` is a predicate on pairs of sub`set`s of a topological space.  It holds if the two
sub`set`s are contained in disjoint open sets.
-/
def separated : set α → set α → Prop :=
  λ (s t : set α), ∃ U V : (set α), (is_open U) ∧ is_open V ∧
  (s ⊆ U) ∧ (t ⊆ V) ∧ disjoint U V

namespace separated

open separated

@[symm] lemma symm {s t : set α} : separated s t → separated t s :=
λ ⟨U, V, oU, oV, aU, bV, UV⟩, ⟨V, U, oV, oU, bV, aU, disjoint.symm UV⟩

lemma comm (s t : set α) : separated s t ↔ separated t s :=
⟨symm, symm⟩

lemma preimage [topological_space β] {f : α → β} {s t : set β} (h : separated s t)
  (hf : continuous f) : separated (f ⁻¹' s) (f ⁻¹' t) :=
let ⟨U, V, oU, oV, sU, tV, UV⟩ := h in
⟨f ⁻¹' U, f ⁻¹' V, oU.preimage hf, oV.preimage hf, preimage_mono sU, preimage_mono tV,
  UV.preimage f⟩

protected lemma disjoint {s t : set α} (h : separated s t) : disjoint s t :=
let ⟨U, V, hU, hV, hsU, htV, hd⟩ := h in hd.mono hsU htV

lemma disjoint_closure_left {s t : set α} (h : separated s t) : disjoint (closure s) t :=
let ⟨U, V, hU, hV, hsU, htV, hd⟩ := h
in (hd.closure_left hV).mono (closure_mono hsU) htV

lemma disjoint_closure_right {s t : set α} (h : separated s t) : disjoint s (closure t) :=
h.symm.disjoint_closure_left.symm

lemma empty_right (a : set α) : separated a ∅ :=
⟨_, _, is_open_univ, is_open_empty, λ a h, mem_univ a, λ a h, by cases h, disjoint_empty _⟩

lemma empty_left (a : set α) : separated ∅ a :=
(empty_right _).symm

lemma mono {s₁ s₂ t₁ t₂ : set α} (h : separated s₂ t₂) (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) :
  separated s₁ t₁ :=
let ⟨U, V, hU, hV, hsU, htV, hd⟩ := h in ⟨U, V, hU, hV, hs.trans hsU, ht.trans htV, hd⟩

lemma union_left {a b c : set α} : separated a c → separated b c → separated (a ∪ b) c :=
λ ⟨U, V, oU, oV, aU, bV, UV⟩ ⟨W, X, oW, oX, aW, bX, WX⟩,
  ⟨U ∪ W, V ∩ X, is_open.union oU oW, is_open.inter oV oX,
    union_subset_union aU aW, subset_inter bV bX, set.disjoint_union_left.mpr
    ⟨disjoint_of_subset_right (inter_subset_left _ _) UV,
      disjoint_of_subset_right (inter_subset_right _ _) WX⟩⟩

lemma union_right {a b c : set α} (ab : separated a b) (ac : separated a c) :
  separated a (b ∪ c) :=
(ab.symm.union_left ac.symm).symm

end separated

/-- A T₀ space, also known as a Kolmogorov space, is a topological space such that for every pair
`x ≠ y`, there is an open set containing one but not the other. We formulate the definition in terms
of the `inseparable` relation.  -/
class t0_space (α : Type u) [topological_space α] : Prop :=
(t0 : ∀ ⦃x y : α⦄, inseparable x y → x = y)

lemma t0_space_iff_inseparable (α : Type u) [topological_space α] :
  t0_space α ↔ ∀ (x y : α), inseparable x y → x = y :=
⟨λ ⟨h⟩, h, λ h, ⟨h⟩⟩

lemma t0_space_iff_not_inseparable (α : Type u) [topological_space α] :
  t0_space α ↔ ∀ (x y : α), x ≠ y → ¬inseparable x y :=
by simp only [t0_space_iff_inseparable, ne.def, not_imp_not]

lemma inseparable.eq [t0_space α] {x y : α} (h : inseparable x y) : x = y :=
t0_space.t0 h

lemma t0_space_iff_nhds_injective (α : Type u) [topological_space α] :
  t0_space α ↔ injective (𝓝 : α → filter α) :=
t0_space_iff_inseparable α

lemma nhds_injective [t0_space α] : injective (𝓝 : α → filter α) :=
(t0_space_iff_nhds_injective α).1 ‹_›

@[simp] lemma nhds_eq_nhds_iff [t0_space α] {a b : α} : 𝓝 a = 𝓝 b ↔ a = b :=
nhds_injective.eq_iff

lemma t0_space_iff_exists_is_open_xor_mem (α : Type u) [topological_space α] :
  t0_space α ↔ ∀ x y, x ≠ y → ∃ U:set α, is_open U ∧ (xor (x ∈ U) (y ∈ U)) :=
by simp only [t0_space_iff_not_inseparable, xor_iff_not_iff, not_forall, exists_prop,
  inseparable_iff_forall_open]

lemma exists_is_open_xor_mem [t0_space α] {x y : α} (h : x ≠ y) :
  ∃ U : set α, is_open U ∧ xor (x ∈ U) (y ∈ U) :=
(t0_space_iff_exists_is_open_xor_mem α).1 ‹_› x y h

/-- Specialization forms a partial order on a t0 topological space. -/
def specialization_order (α : Type*) [topological_space α] [t0_space α] : partial_order α :=
{ .. specialization_preorder α,
  .. partial_order.lift (order_dual.to_dual ∘ 𝓝) nhds_injective }

instance : t0_space (separation_quotient α) :=
⟨λ x' y', quotient.induction_on₂' x' y' $
  λ x y h, separation_quotient.mk_eq_mk.2 $ separation_quotient.inducing_mk.inseparable_iff.1 h⟩

theorem minimal_nonempty_closed_subsingleton [t0_space α] {s : set α} (hs : is_closed s)
  (hmin : ∀ t ⊆ s, t.nonempty → is_closed t → t = s) :
  s.subsingleton :=
begin
  refine λ x hx y hy, of_not_not (λ hxy, _),
  rcases exists_is_open_xor_mem hxy with ⟨U, hUo, hU⟩,
  wlog h : x ∈ U ∧ y ∉ U := hU using [x y, y x], cases h with hxU hyU,
  have : s \ U = s := hmin (s \ U) (diff_subset _ _) ⟨y, hy, hyU⟩ (hs.sdiff hUo),
  exact (this.symm.subset hx).2 hxU
end

theorem minimal_nonempty_closed_eq_singleton [t0_space α] {s : set α} (hs : is_closed s)
  (hne : s.nonempty) (hmin : ∀ t ⊆ s, t.nonempty → is_closed t → t = s) :
  ∃ x, s = {x} :=
exists_eq_singleton_iff_nonempty_subsingleton.2 ⟨hne, minimal_nonempty_closed_subsingleton hs hmin⟩

/-- Given a closed set `S` in a compact T₀ space,
there is some `x ∈ S` such that `{x}` is closed. -/
theorem is_closed.exists_closed_singleton {α : Type*} [topological_space α]
  [t0_space α] [compact_space α] {S : set α} (hS : is_closed S) (hne : S.nonempty) :
  ∃ (x : α), x ∈ S ∧ is_closed ({x} : set α) :=
begin
  obtain ⟨V, Vsub, Vne, Vcls, hV⟩ := hS.exists_minimal_nonempty_closed_subset hne,
  rcases minimal_nonempty_closed_eq_singleton Vcls Vne hV with ⟨x, rfl⟩,
  exact ⟨x, Vsub (mem_singleton x), Vcls⟩
end

theorem minimal_nonempty_open_subsingleton [t0_space α] {s : set α} (hs : is_open s)
  (hmin : ∀ t ⊆ s, t.nonempty → is_open t → t = s) :
  s.subsingleton :=
begin
  refine λ x hx y hy, of_not_not (λ hxy, _),
  rcases exists_is_open_xor_mem hxy with ⟨U, hUo, hU⟩,
  wlog h : x ∈ U ∧ y ∉ U := hU using [x y, y x], cases h with hxU hyU,
  have : s ∩ U = s := hmin (s ∩ U) (inter_subset_left _ _) ⟨x, hx, hxU⟩ (hs.inter hUo),
  exact hyU (this.symm.subset hy).2
end

theorem minimal_nonempty_open_eq_singleton [t0_space α] {s : set α} (hs : is_open s)
  (hne : s.nonempty) (hmin : ∀ t ⊆ s, t.nonempty → is_open t → t = s) :
  ∃ x, s = {x} :=
exists_eq_singleton_iff_nonempty_subsingleton.2 ⟨hne, minimal_nonempty_open_subsingleton hs hmin⟩

/-- Given an open finite set `S` in a T₀ space, there is some `x ∈ S` such that `{x}` is open. -/
theorem exists_open_singleton_of_open_finite [t0_space α] {s : set α} (hfin : s.finite)
  (hne : s.nonempty) (ho : is_open s) :
  ∃ x ∈ s, is_open ({x} : set α) :=
begin
  lift s to finset α using hfin,
  induction s using finset.strong_induction_on with s ihs,
  rcases em (∃ t ⊂ s, t.nonempty ∧ is_open (t : set α)) with ⟨t, hts, htne, hto⟩|ht,
  { rcases ihs t hts htne hto with ⟨x, hxt, hxo⟩,
    exact ⟨x, hts.1 hxt, hxo⟩ },
  { rcases minimal_nonempty_open_eq_singleton ho hne _ with ⟨x, hx⟩,
    { exact ⟨x, hx.symm ▸ rfl, hx ▸ ho⟩ },
    refine λ t hts htne hto, of_not_not (λ hts', ht _),
    lift t to finset α using s.finite_to_set.subset hts,
    exact ⟨t, ssubset_iff_subset_ne.2 ⟨hts, mt finset.coe_inj.2 hts'⟩, htne, hto⟩ }
end

theorem exists_open_singleton_of_fintype [t0_space α] [finite α] [nonempty α] :
  ∃ x : α, is_open ({x} : set α) :=
let ⟨x, _, h⟩ := exists_open_singleton_of_open_finite (set.to_finite _) univ_nonempty
  is_open_univ in ⟨x, h⟩

lemma t0_space_of_injective_of_continuous [topological_space β] {f : α → β}
  (hf : function.injective f) (hf' : continuous f) [t0_space β] : t0_space α :=
⟨λ x y h, hf $ (h.map hf').eq⟩

protected lemma embedding.t0_space [topological_space β] [t0_space β] {f : α → β}
  (hf : embedding f) : t0_space α :=
t0_space_of_injective_of_continuous hf.inj hf.continuous

instance subtype.t0_space [t0_space α] {p : α → Prop} : t0_space (subtype p) :=
embedding_subtype_coe.t0_space

theorem t0_space_iff_or_not_mem_closure (α : Type u) [topological_space α] :
  t0_space α ↔ (∀ a b : α, a ≠ b → (a ∉ closure ({b} : set α) ∨ b ∉ closure ({a} : set α))) :=
by simp only [t0_space_iff_not_inseparable, inseparable_iff_mem_closure, not_and_distrib]

instance [topological_space β] [t0_space α] [t0_space β] : t0_space (α × β) :=
⟨λ x y h, prod.ext (h.map continuous_fst).eq (h.map continuous_snd).eq⟩

instance {ι : Type*} {π : ι → Type*} [Π i, topological_space (π i)] [Π i, t0_space (π i)] :
  t0_space (Π i, π i) :=
⟨λ x y h, funext $ λ i, (h.map (continuous_apply i)).eq⟩

lemma t0_space.of_cover (h : ∀ x y, inseparable x y → ∃ s : set α, x ∈ s ∧ y ∈ s ∧ t0_space s) :
  t0_space α :=
begin
  refine ⟨λ x y hxy, _⟩,
  rcases h x y hxy with ⟨s, hxs, hys, hs⟩, resetI,
  lift x to s using hxs, lift y to s using hys,
  rw ← subtype_inseparable_iff at hxy,
  exact congr_arg coe hxy.eq
end

lemma t0_space.of_open_cover (h : ∀ x, ∃ s : set α, x ∈ s ∧ is_open s ∧ t0_space s) : t0_space α :=
t0_space.of_cover $ λ x y hxy,
  let ⟨s, hxs, hso, hs⟩ := h x in ⟨s, hxs, (hxy.mem_open_iff hso).1 hxs, hs⟩

/-- A T₁ space, also known as a Fréchet space, is a topological space
  where every singleton set is closed. Equivalently, for every pair
  `x ≠ y`, there is an open set containing `x` and not `y`. -/
class t1_space (α : Type u) [topological_space α] : Prop :=
(t1 : ∀x, is_closed ({x} : set α))

lemma is_closed_singleton [t1_space α] {x : α} : is_closed ({x} : set α) :=
t1_space.t1 x

lemma is_open_compl_singleton [t1_space α] {x : α} : is_open ({x}ᶜ : set α) :=
is_closed_singleton.is_open_compl

lemma is_open_ne [t1_space α] {x : α} : is_open {y | y ≠ x} :=
is_open_compl_singleton

lemma ne.nhds_within_compl_singleton [t1_space α] {x y : α} (h : x ≠ y) :
  𝓝[{y}ᶜ] x = 𝓝 x :=
is_open_ne.nhds_within_eq h

lemma ne.nhds_within_diff_singleton [t1_space α] {x y : α} (h : x ≠ y) (s : set α) :
  𝓝[s \ {y}] x = 𝓝[s] x :=
begin
  rw [diff_eq, inter_comm, nhds_within_inter_of_mem],
  exact mem_nhds_within_of_mem_nhds (is_open_ne.mem_nhds h)
end

protected lemma set.finite.is_closed [t1_space α] {s : set α} (hs : set.finite s) :
  is_closed s :=
begin
  rw ← bUnion_of_singleton s,
  exact is_closed_bUnion hs (λ i hi, is_closed_singleton)
end

lemma topological_space.is_topological_basis.exists_mem_of_ne
  [t1_space α] {b : set (set α)} (hb : is_topological_basis b) {x y : α} (h : x ≠ y) :
  ∃ a ∈ b, x ∈ a ∧ y ∉ a :=
begin
  rcases hb.is_open_iff.1 is_open_ne x h with ⟨a, ab, xa, ha⟩,
  exact ⟨a, ab, xa, λ h, ha h rfl⟩,
end

lemma filter.coclosed_compact_le_cofinite [t1_space α] :
  filter.coclosed_compact α ≤ filter.cofinite :=
λ s hs, compl_compl s ▸ hs.is_compact.compl_mem_coclosed_compact_of_is_closed hs.is_closed

variable (α)

/-- In a `t1_space`, relatively compact sets form a bornology. Its cobounded filter is
`filter.coclosed_compact`. See also `bornology.in_compact` the bornology of sets contained
in a compact set. -/
def bornology.relatively_compact [t1_space α] : bornology α :=
{ cobounded := filter.coclosed_compact α,
  le_cofinite := filter.coclosed_compact_le_cofinite }

variable {α}

lemma bornology.relatively_compact.is_bounded_iff [t1_space α] {s : set α} :
  @bornology.is_bounded _ (bornology.relatively_compact α) s ↔ is_compact (closure s) :=
begin
  change sᶜ ∈ filter.coclosed_compact α ↔ _,
  rw filter.mem_coclosed_compact,
  split,
  { rintros ⟨t, ht₁, ht₂, hst⟩,
    rw compl_subset_compl at hst,
    exact compact_of_is_closed_subset ht₂ is_closed_closure (closure_minimal hst ht₁) },
  { intros h,
    exact ⟨closure s, is_closed_closure, h, compl_subset_compl.mpr subset_closure⟩ }
end

protected lemma finset.is_closed [t1_space α] (s : finset α) : is_closed (s : set α) :=
s.finite_to_set.is_closed

lemma t1_space_tfae (α : Type u) [topological_space α] :
  tfae [t1_space α,
    ∀ x, is_closed ({x} : set α),
    ∀ x, is_open ({x}ᶜ : set α),
    continuous (@cofinite_topology.of α),
    ∀ ⦃x y : α⦄, x ≠ y → {y}ᶜ ∈ 𝓝 x,
    ∀ ⦃x y : α⦄, x ≠ y → ∃ s ∈ 𝓝 x, y ∉ s,
    ∀ ⦃x y : α⦄, x ≠ y → ∃ (U : set α) (hU : is_open U), x ∈ U ∧ y ∉ U,
    ∀ ⦃x y : α⦄, x ≠ y → disjoint (𝓝 x) (pure y),
    ∀ ⦃x y : α⦄, x ≠ y → disjoint (pure x) (𝓝 y),
    ∀ ⦃x y : α⦄, x ⤳ y → x = y] :=
begin
  tfae_have : 1 ↔ 2, from ⟨λ h, h.1, λ h, ⟨h⟩⟩,
  tfae_have : 2 ↔ 3, by simp only [is_open_compl_iff],
  tfae_have : 5 ↔ 3,
  { refine forall_swap.trans _,
    simp only [is_open_iff_mem_nhds, mem_compl_iff, mem_singleton_iff] },
  tfae_have : 5 ↔ 6,
    by simp only [← subset_compl_singleton_iff, exists_mem_subset_iff],
  tfae_have : 5 ↔ 7,
    by simp only [(nhds_basis_opens _).mem_iff, subset_compl_singleton_iff, exists_prop, and.assoc,
      and.left_comm],
  tfae_have : 5 ↔ 8,
    by simp only [← principal_singleton, disjoint_principal_right],
  tfae_have : 8 ↔ 9, from forall_swap.trans (by simp only [disjoint.comm, ne_comm]),
  tfae_have : 1 → 4,
  { simp only [continuous_def, cofinite_topology.is_open_iff'],
    rintro H s (rfl|hs),
    exacts [is_open_empty, compl_compl s ▸ (@set.finite.is_closed _ _ H _ hs).is_open_compl] },
  tfae_have : 4 → 2,
    from λ h x, (cofinite_topology.is_closed_iff.2 $ or.inr (finite_singleton _)).preimage h,
  tfae_have : 2 ↔ 10,
  { simp only [← closure_subset_iff_is_closed, specializes_iff_mem_closure, subset_def,
      mem_singleton_iff, eq_comm] },
  tfae_finish
end

lemma t1_space_iff_continuous_cofinite_of {α : Type*} [topological_space α] :
  t1_space α ↔ continuous (@cofinite_topology.of α) :=
(t1_space_tfae α).out 0 3

lemma cofinite_topology.continuous_of [t1_space α] : continuous (@cofinite_topology.of α) :=
t1_space_iff_continuous_cofinite_of.mp ‹_›

lemma t1_space_iff_exists_open : t1_space α ↔
  ∀ (x y), x ≠ y → (∃ (U : set α) (hU : is_open U), x ∈ U ∧ y ∉ U) :=
(t1_space_tfae α).out 0 6

lemma t1_space_iff_disjoint_pure_nhds : t1_space α ↔ ∀ ⦃x y : α⦄, x ≠ y → disjoint (pure x) (𝓝 y) :=
(t1_space_tfae α).out 0 8

lemma t1_space_iff_disjoint_nhds_pure : t1_space α ↔ ∀ ⦃x y : α⦄, x ≠ y → disjoint (𝓝 x) (pure y) :=
(t1_space_tfae α).out 0 7

lemma t1_space_iff_specializes_imp_eq : t1_space α ↔ ∀ ⦃x y : α⦄, x ⤳ y → x = y :=
(t1_space_tfae α).out 0 9

lemma disjoint_pure_nhds [t1_space α] {x y : α} (h : x ≠ y) : disjoint (pure x) (𝓝 y) :=
t1_space_iff_disjoint_pure_nhds.mp ‹_› h

lemma disjoint_nhds_pure [t1_space α] {x y : α} (h : x ≠ y) : disjoint (𝓝 x) (pure y) :=
t1_space_iff_disjoint_nhds_pure.mp ‹_› h

lemma specializes.eq [t1_space α] {x y : α} (h : x ⤳ y) : x = y :=
t1_space_iff_specializes_imp_eq.1 ‹_› h

@[simp] lemma specializes_iff_eq [t1_space α] {x y : α} : x ⤳ y ↔ x = y :=
⟨specializes.eq, λ h, h ▸ specializes_rfl⟩

instance {α : Type*} : t1_space (cofinite_topology α) :=
t1_space_iff_continuous_cofinite_of.mpr continuous_id

lemma t1_space_antitone {α : Type*} : antitone (@t1_space α) :=
begin
  simp only [antitone, t1_space_iff_continuous_cofinite_of, continuous_iff_le_induced],
  exact λ t₁ t₂ h, h.trans
end

lemma continuous_within_at_update_of_ne [t1_space α] [decidable_eq α] [topological_space β]
  {f : α → β} {s : set α} {x y : α} {z : β} (hne : y ≠ x) :
  continuous_within_at (function.update f x z) s y ↔ continuous_within_at f s y :=
eventually_eq.congr_continuous_within_at
  (mem_nhds_within_of_mem_nhds $ mem_of_superset (is_open_ne.mem_nhds hne) $
    λ y' hy', function.update_noteq hy' _ _)
  (function.update_noteq hne _ _)

lemma continuous_at_update_of_ne [t1_space α] [decidable_eq α] [topological_space β]
  {f : α → β} {x y : α} {z : β} (hne : y ≠ x) :
  continuous_at (function.update f x z) y ↔ continuous_at f y :=
by simp only [← continuous_within_at_univ, continuous_within_at_update_of_ne hne]

lemma continuous_on_update_iff [t1_space α] [decidable_eq α] [topological_space β]
  {f : α → β} {s : set α} {x : α} {y : β} :
  continuous_on (function.update f x y) s ↔
    continuous_on f (s \ {x}) ∧ (x ∈ s → tendsto f (𝓝[s \ {x}] x) (𝓝 y)) :=
begin
  rw [continuous_on, ← and_forall_ne x, and_comm],
  refine and_congr ⟨λ H z hz, _, λ H z hzx hzs, _⟩ (forall_congr $ λ hxs, _),
  { specialize H z hz.2 hz.1,
    rw continuous_within_at_update_of_ne hz.2 at H,
    exact H.mono (diff_subset _ _) },
  { rw continuous_within_at_update_of_ne hzx,
    refine (H z ⟨hzs, hzx⟩).mono_of_mem (inter_mem_nhds_within _ _),
    exact is_open_ne.mem_nhds hzx },
  { exact continuous_within_at_update_same }
end

lemma t1_space_of_injective_of_continuous [topological_space β] {f : α → β}
  (hf : function.injective f) (hf' : continuous f) [t1_space β] : t1_space α :=
t1_space_iff_specializes_imp_eq.2 $ λ x y h, hf (h.map hf').eq

protected lemma embedding.t1_space [topological_space β] [t1_space β] {f : α → β}
  (hf : embedding f) : t1_space α :=
t1_space_of_injective_of_continuous hf.inj hf.continuous

instance subtype.t1_space {α : Type u} [topological_space α] [t1_space α] {p : α → Prop} :
  t1_space (subtype p) :=
embedding_subtype_coe.t1_space

instance [topological_space β] [t1_space α] [t1_space β] : t1_space (α × β) :=
⟨λ ⟨a, b⟩, @singleton_prod_singleton _ _ a b ▸ is_closed_singleton.prod is_closed_singleton⟩

instance {ι : Type*} {π : ι → Type*} [Π i, topological_space (π i)] [Π i, t1_space (π i)] :
  t1_space (Π i, π i) :=
⟨λ f, univ_pi_singleton f ▸ is_closed_set_pi (λ i hi, is_closed_singleton)⟩

@[priority 100] -- see Note [lower instance priority]
instance t1_space.t0_space [t1_space α] : t0_space α := ⟨λ x y h, h.specializes.eq⟩

@[simp] lemma compl_singleton_mem_nhds_iff [t1_space α] {x y : α} : {x}ᶜ ∈ 𝓝 y ↔ y ≠ x :=
is_open_compl_singleton.mem_nhds_iff

lemma compl_singleton_mem_nhds [t1_space α] {x y : α} (h : y ≠ x) : {x}ᶜ ∈ 𝓝 y :=
compl_singleton_mem_nhds_iff.mpr h

@[simp] lemma closure_singleton [t1_space α] {a : α} :
  closure ({a} : set α) = {a} :=
is_closed_singleton.closure_eq

lemma set.subsingleton.closure [t1_space α] {s : set α} (hs : s.subsingleton) :
  (closure s).subsingleton :=
hs.induction_on (by simp) $ λ x, by simp

@[simp] lemma subsingleton_closure [t1_space α] {s : set α} :
  (closure s).subsingleton ↔ s.subsingleton :=
⟨λ h, h.anti subset_closure, λ h, h.closure⟩

lemma is_closed_map_const {α β} [topological_space α] [topological_space β] [t1_space β] {y : β} :
  is_closed_map (function.const α y) :=
is_closed_map.of_nonempty $ λ s hs h2s, by simp_rw [h2s.image_const, is_closed_singleton]

lemma bInter_basis_nhds [t1_space α] {ι : Sort*} {p : ι → Prop} {s : ι → set α} {x : α}
  (h : (𝓝 x).has_basis p s) : (⋂ i (h : p i), s i) = {x} :=
begin
  simp only [eq_singleton_iff_unique_mem, mem_Inter],
  refine ⟨λ i hi, mem_of_mem_nhds $ h.mem_of_mem hi, λ y hy, _⟩,
  contrapose! hy,
  rcases h.mem_iff.1 (compl_singleton_mem_nhds hy.symm) with ⟨i, hi, hsub⟩,
  exact ⟨i, hi, λ h, hsub h rfl⟩
end

@[simp] lemma pure_le_nhds_iff [t1_space α] {a b : α} : pure a ≤ 𝓝 b ↔ a = b :=
begin
  refine ⟨λ h, _, λ h, h ▸ pure_le_nhds a⟩,
  by_contra hab,
  simpa only [mem_pure, mem_compl_iff, mem_singleton, not_true] using
    h (compl_singleton_mem_nhds $ ne.symm hab)
end

@[simp] lemma nhds_le_nhds_iff [t1_space α] {a b : α} : 𝓝 a ≤ 𝓝 b ↔ a = b :=
⟨λ h, pure_le_nhds_iff.mp $ (pure_le_nhds a).trans h, λ h, h ▸ le_rfl⟩

@[simp] lemma compl_singleton_mem_nhds_set_iff [t1_space α] {x : α} {s : set α} :
  {x}ᶜ ∈ 𝓝ˢ s ↔ x ∉ s :=
by rwa [is_open_compl_singleton.mem_nhds_set, subset_compl_singleton_iff]

@[simp] lemma nhds_set_le_iff [t1_space α] {s t : set α} : 𝓝ˢ s ≤ 𝓝ˢ t ↔ s ⊆ t :=
begin
  refine ⟨_, λ h, monotone_nhds_set h⟩,
  simp_rw [filter.le_def], intros h x hx,
  specialize h {x}ᶜ,
  simp_rw [compl_singleton_mem_nhds_set_iff] at h,
  by_contra hxt,
  exact h hxt hx,
end

@[simp] lemma nhds_set_inj_iff [t1_space α] {s t : set α} : 𝓝ˢ s = 𝓝ˢ t ↔ s = t :=
by { simp_rw [le_antisymm_iff], exact and_congr nhds_set_le_iff nhds_set_le_iff }

lemma injective_nhds_set [t1_space α] : function.injective (𝓝ˢ : set α → filter α) :=
λ s t hst, nhds_set_inj_iff.mp hst

lemma strict_mono_nhds_set [t1_space α] : strict_mono (𝓝ˢ : set α → filter α) :=
monotone_nhds_set.strict_mono_of_injective injective_nhds_set

@[simp] lemma nhds_le_nhds_set [t1_space α] {s : set α} {x : α} : 𝓝 x ≤ 𝓝ˢ s ↔ x ∈ s :=
by rw [← nhds_set_singleton, nhds_set_le_iff, singleton_subset_iff]

/-- Removing a non-isolated point from a dense set, one still obtains a dense set. -/
lemma dense.diff_singleton [t1_space α] {s : set α} (hs : dense s) (x : α) [ne_bot (𝓝[≠] x)] :
  dense (s \ {x}) :=
hs.inter_of_open_right (dense_compl_singleton x) is_open_compl_singleton

/-- Removing a finset from a dense set in a space without isolated points, one still
obtains a dense set. -/
lemma dense.diff_finset [t1_space α] [∀ (x : α), ne_bot (𝓝[≠] x)]
  {s : set α} (hs : dense s) (t : finset α) :
  dense (s \ t) :=
begin
  induction t using finset.induction_on with x s hxs ih hd,
  { simpa using hs },
  { rw [finset.coe_insert, ← union_singleton, ← diff_diff],
    exact ih.diff_singleton _, }
end

/-- Removing a finite set from a dense set in a space without isolated points, one still
obtains a dense set. -/
lemma dense.diff_finite [t1_space α] [∀ (x : α), ne_bot (𝓝[≠] x)]
  {s : set α} (hs : dense s) {t : set α} (ht : t.finite) :
  dense (s \ t) :=
begin
  convert hs.diff_finset ht.to_finset,
  exact (finite.coe_to_finset _).symm,
end

/-- If a function to a `t1_space` tends to some limit `b` at some point `a`, then necessarily
`b = f a`. -/
lemma eq_of_tendsto_nhds [topological_space β] [t1_space β] {f : α → β} {a : α} {b : β}
  (h : tendsto f (𝓝 a) (𝓝 b)) : f a = b :=
by_contra $ assume (hfa : f a ≠ b),
have fact₁ : {f a}ᶜ ∈ 𝓝 b := compl_singleton_mem_nhds hfa.symm,
have fact₂ : tendsto f (pure a) (𝓝 b) := h.comp (tendsto_id'.2 $ pure_le_nhds a),
fact₂ fact₁ (eq.refl $ f a)

/-- To prove a function to a `t1_space` is continuous at some point `a`, it suffices to prove that
`f` admits *some* limit at `a`. -/
lemma continuous_at_of_tendsto_nhds [topological_space β] [t1_space β] {f : α → β} {a : α} {b : β}
  (h : tendsto f (𝓝 a) (𝓝 b)) : continuous_at f a :=
show tendsto f (𝓝 a) (𝓝 $ f a), by rwa eq_of_tendsto_nhds h

lemma tendsto_const_nhds_iff [t1_space α] {l : filter α} [ne_bot l] {c d : α} :
  tendsto (λ x, c) l (𝓝 d) ↔ c = d :=
by simp_rw [tendsto, filter.map_const, pure_le_nhds_iff]

/-- If the punctured neighborhoods of a point form a nontrivial filter, then any neighborhood is
infinite. -/
lemma infinite_of_mem_nhds {α} [topological_space α] [t1_space α] (x : α) [hx : ne_bot (𝓝[≠] x)]
  {s : set α} (hs : s ∈ 𝓝 x) : set.infinite s :=
begin
  intro hsf,
  have A : {x} ⊆ s, by simp only [singleton_subset_iff, mem_of_mem_nhds hs],
  have B : is_closed (s \ {x}) := (hsf.subset (diff_subset _ _)).is_closed,
  have C : (s \ {x})ᶜ ∈ 𝓝 x, from B.is_open_compl.mem_nhds (λ h, h.2 rfl),
  have D : {x} ∈ 𝓝 x, by simpa only [← diff_eq, diff_diff_cancel_left A] using inter_mem hs C,
  rwa [← mem_interior_iff_mem_nhds, interior_singleton] at D
end

lemma discrete_of_t1_of_finite {X : Type*} [topological_space X] [t1_space X] [finite X] :
  discrete_topology X :=
begin
  apply singletons_open_iff_discrete.mp,
  intros x,
  rw [← is_closed_compl_iff],
  exact (set.to_finite _).is_closed
end

lemma singleton_mem_nhds_within_of_mem_discrete {s : set α} [discrete_topology s]
  {x : α} (hx : x ∈ s) :
  {x} ∈ 𝓝[s] x :=
begin
  have : ({⟨x, hx⟩} : set s) ∈ 𝓝 (⟨x, hx⟩ : s), by simp [nhds_discrete],
  simpa only [nhds_within_eq_map_subtype_coe hx, image_singleton]
    using @image_mem_map _ _ _ (coe : s → α) _ this
end

/-- The neighbourhoods filter of `x` within `s`, under the discrete topology, is equal to
the pure `x` filter (which is the principal filter at the singleton `{x}`.) -/
lemma nhds_within_of_mem_discrete {s : set α} [discrete_topology s] {x : α} (hx : x ∈ s) :
  𝓝[s] x = pure x :=
le_antisymm (le_pure_iff.2 $ singleton_mem_nhds_within_of_mem_discrete hx) (pure_le_nhds_within hx)

lemma filter.has_basis.exists_inter_eq_singleton_of_mem_discrete
  {ι : Type*} {p : ι → Prop} {t : ι → set α} {s : set α} [discrete_topology s] {x : α}
  (hb : (𝓝 x).has_basis p t) (hx : x ∈ s) :
  ∃ i (hi : p i), t i ∩ s = {x} :=
begin
  rcases (nhds_within_has_basis hb s).mem_iff.1 (singleton_mem_nhds_within_of_mem_discrete hx)
    with ⟨i, hi, hix⟩,
  exact ⟨i, hi, subset.antisymm hix $ singleton_subset_iff.2
    ⟨mem_of_mem_nhds $ hb.mem_of_mem hi, hx⟩⟩
end

/-- A point `x` in a discrete subset `s` of a topological space admits a neighbourhood
that only meets `s` at `x`.  -/
lemma nhds_inter_eq_singleton_of_mem_discrete {s : set α} [discrete_topology s]
  {x : α} (hx : x ∈ s) :
  ∃ U ∈ 𝓝 x, U ∩ s = {x} :=
by simpa using (𝓝 x).basis_sets.exists_inter_eq_singleton_of_mem_discrete hx

/-- For point `x` in a discrete subset `s` of a topological space, there is a set `U`
such that
1. `U` is a punctured neighborhood of `x` (ie. `U ∪ {x}` is a neighbourhood of `x`),
2. `U` is disjoint from `s`.
-/
lemma disjoint_nhds_within_of_mem_discrete {s : set α} [discrete_topology s] {x : α} (hx : x ∈ s) :
  ∃ U ∈ 𝓝[≠] x, disjoint U s :=
let ⟨V, h, h'⟩ := nhds_inter_eq_singleton_of_mem_discrete hx in
  ⟨{x}ᶜ ∩ V, inter_mem_nhds_within _ h,
    (disjoint_iff_inter_eq_empty.mpr (by { rw [inter_assoc, h', compl_inter_self] }))⟩

/-- Let `X` be a topological space and let `s, t ⊆ X` be two subsets.  If there is an inclusion
`t ⊆ s`, then the topological space structure on `t` induced by `X` is the same as the one
obtained by the induced topological space structure on `s`. -/
lemma topological_space.subset_trans {X : Type*} [tX : topological_space X]
  {s t : set X} (ts : t ⊆ s) :
  (subtype.topological_space : topological_space t) =
    (subtype.topological_space : topological_space s).induced (set.inclusion ts) :=
begin
  change tX.induced ((coe : s → X) ∘ (set.inclusion ts)) =
    topological_space.induced (set.inclusion ts) (tX.induced _),
  rw ← induced_compose,
end

/-- This lemma characterizes discrete topological spaces as those whose singletons are
neighbourhoods. -/
lemma discrete_topology_iff_nhds {X : Type*} [topological_space X] :
  discrete_topology X ↔ (nhds : X → filter X) = pure :=
begin
  split,
  { introI hX,
    exact nhds_discrete X },
  { intro h,
    constructor,
    apply eq_of_nhds_eq_nhds,
    simp [h, nhds_bot] }
end

/-- The topology pulled-back under an inclusion `f : X → Y` from the discrete topology (`⊥`) is the
discrete topology.
This version does not assume the choice of a topology on either the source `X`
nor the target `Y` of the inclusion `f`. -/
lemma induced_bot {X Y : Type*} {f : X → Y} (hf : function.injective f) :
  topological_space.induced f ⊥ = ⊥ :=
eq_of_nhds_eq_nhds (by simp [nhds_induced, ← set.image_singleton, hf.preimage_image, nhds_bot])

/-- The topology induced under an inclusion `f : X → Y` from the discrete topological space `Y`
is the discrete topology on `X`. -/
lemma discrete_topology_induced {X Y : Type*} [tY : topological_space Y] [discrete_topology Y]
  {f : X → Y} (hf : function.injective f) : @discrete_topology X (topological_space.induced f tY) :=
begin
  constructor,
  rw discrete_topology.eq_bot Y,
  exact induced_bot hf
end

/-- Let `s, t ⊆ X` be two subsets of a topological space `X`.  If `t ⊆ s` and the topology induced
by `X`on `s` is discrete, then also the topology induces on `t` is discrete.  -/
lemma discrete_topology.of_subset {X : Type*} [topological_space X] {s t : set X}
  (ds : discrete_topology s) (ts : t ⊆ s) :
  discrete_topology t :=
begin
  rw [topological_space.subset_trans ts, ds.eq_bot],
  exact {eq_bot := induced_bot (set.inclusion_injective ts)}
end

/-- A T₂ space, also known as a Hausdorff space, is one in which for every
  `x ≠ y` there exists disjoint open sets around `x` and `y`. This is
  the most widely used of the separation axioms. -/
@[mk_iff] class t2_space (α : Type u) [topological_space α] : Prop :=
(t2 : ∀ x y, x ≠ y → ∃ u v : set α, is_open u ∧ is_open v ∧ x ∈ u ∧ y ∈ v ∧ disjoint u v)

/-- Two different points can be separated by open sets. -/
lemma t2_separation [t2_space α] {x y : α} (h : x ≠ y) :
  ∃ u v : set α, is_open u ∧ is_open v ∧ x ∈ u ∧ y ∈ v ∧ disjoint u v :=
t2_space.t2 x y h

lemma t2_space_iff_disjoint_nhds : t2_space α ↔ ∀ x y : α, x ≠ y → disjoint (𝓝 x) (𝓝 y) :=
begin
  refine (t2_space_iff α).trans (forall₃_congr $ λ x y hne, _),
  simp only [(nhds_basis_opens x).disjoint_iff (nhds_basis_opens y), exists_prop,
    ← exists_and_distrib_left, and.assoc, and_comm, and.left_comm]
end

@[simp] lemma disjoint_nhds_nhds [t2_space α] {x y : α} : disjoint (𝓝 x) (𝓝 y) ↔ x ≠ y :=
⟨λ hd he, by simpa [he, nhds_ne_bot.ne] using hd, t2_space_iff_disjoint_nhds.mp ‹_› x y⟩

/-- A finite set can be separated by open sets. -/
lemma t2_separation_finset [t2_space α] (s : finset α) :
  ∃ f : α → set α, set.pairwise_disjoint ↑s f ∧ ∀ x ∈ s, x ∈ f x ∧ is_open (f x) :=
finset.induction_on s (by simp) begin
  rintros t s ht ⟨f, hf, hf'⟩,
  have hty : ∀ y : s, t ≠ y := by { rintros y rfl, exact ht y.2 },
  choose u v hu hv htu hxv huv using λ {x} (h : t ≠ x), t2_separation h,
  refine ⟨λ x, if ht : t = x then ⋂ y : s, u (hty y) else f x ∩ v ht, _, _⟩,
  { rintros x hx₁ y hy₁ hxy a ⟨hx, hy⟩,
    rw [finset.mem_coe, finset.mem_insert, eq_comm] at hx₁ hy₁,
    rcases eq_or_ne t x with rfl | hx₂;
    rcases eq_or_ne t y with rfl | hy₂,
    { exact hxy rfl },
    { simp_rw [dif_pos rfl, mem_Inter] at hx,
      simp_rw [dif_neg hy₂] at hy,
      exact huv hy₂ ⟨hx ⟨y, hy₁.resolve_left hy₂⟩, hy.2⟩ },
    { simp_rw [dif_neg hx₂] at hx,
      simp_rw [dif_pos rfl, mem_Inter] at hy,
      exact huv hx₂ ⟨hy ⟨x, hx₁.resolve_left hx₂⟩, hx.2⟩ },
    { simp_rw [dif_neg hx₂] at hx,
      simp_rw [dif_neg hy₂] at hy,
      exact hf (hx₁.resolve_left hx₂) (hy₁.resolve_left hy₂) hxy ⟨hx.1, hy.1⟩ } },
  { intros x hx,
    split_ifs with ht,
    { refine ⟨mem_Inter.2 (λ y, _), is_open_Inter (λ y, hu (hty y))⟩,
      rw ←ht,
      exact htu (hty y) },
    { have hx := hf' x ((finset.mem_insert.1 hx).resolve_left (ne.symm ht)),
      exact ⟨⟨hx.1, hxv ht⟩, is_open.inter hx.2 (hv ht)⟩ } }
end

@[priority 100] -- see Note [lower instance priority]
instance t2_space.t1_space [t2_space α] : t1_space α :=
t1_space_iff_disjoint_pure_nhds.mpr $ λ x y hne, (disjoint_nhds_nhds.2 hne).mono_left $
  pure_le_nhds _

/-- A space is T₂ iff the neighbourhoods of distinct points generate the bottom filter. -/
lemma t2_iff_nhds : t2_space α ↔ ∀ {x y : α}, ne_bot (𝓝 x ⊓ 𝓝 y) → x = y :=
by simp only [t2_space_iff_disjoint_nhds, disjoint_iff, ne_bot_iff, ne.def, not_imp_comm]

lemma eq_of_nhds_ne_bot [t2_space α] {x y : α} (h : ne_bot (𝓝 x ⊓ 𝓝 y)) : x = y :=
t2_iff_nhds.mp ‹_› h

lemma t2_space_iff_nhds : t2_space α ↔ ∀ {x y : α}, x ≠ y → ∃ (U ∈ 𝓝 x) (V ∈ 𝓝 y), disjoint U V :=
by simp only [t2_space_iff_disjoint_nhds, filter.disjoint_iff]

lemma t2_separation_nhds [t2_space α] {x y : α} (h : x ≠ y) :
  ∃ u v, u ∈ 𝓝 x ∧ v ∈ 𝓝 y ∧ disjoint u v :=
let ⟨u, v, open_u, open_v, x_in, y_in, huv⟩ := t2_separation h in
⟨u, v, open_u.mem_nhds x_in, open_v.mem_nhds y_in, huv⟩

lemma t2_separation_compact_nhds [locally_compact_space α] [t2_space α] {x y : α} (h : x ≠ y) :
  ∃ u v, u ∈ 𝓝 x ∧ v ∈ 𝓝 y ∧ is_compact u ∧ is_compact v ∧ disjoint u v :=
by simpa only [exists_prop, ← exists_and_distrib_left, and_comm, and.assoc, and.left_comm]
  using ((compact_basis_nhds x).disjoint_iff (compact_basis_nhds y)).1 (disjoint_nhds_nhds.2 h)

lemma t2_iff_ultrafilter :
  t2_space α ↔ ∀ {x y : α} (f : ultrafilter α), ↑f ≤ 𝓝 x → ↑f ≤ 𝓝 y → x = y :=
t2_iff_nhds.trans $ by simp only [←exists_ultrafilter_iff, and_imp, le_inf_iff, exists_imp_distrib]

lemma t2_iff_is_closed_diagonal : t2_space α ↔ is_closed (diagonal α) :=
by simp only [t2_space_iff_disjoint_nhds, ← is_open_compl_iff, is_open_iff_mem_nhds, prod.forall,
  nhds_prod_eq, compl_diagonal_mem_prod, mem_compl_iff, mem_diagonal_iff]

lemma is_closed_diagonal [t2_space α] : is_closed (diagonal α) :=
t2_iff_is_closed_diagonal.mp ‹_›

section separated

open separated finset

lemma finset_disjoint_finset_opens_of_t2 [t2_space α] :
  ∀ (s t : finset α), disjoint s t → separated (s : set α) t :=
begin
  refine induction_on_union _ (λ a b hi d, (hi d.symm).symm) (λ a d, empty_right a) (λ a b ab, _) _,
  { obtain ⟨U, V, oU, oV, aU, bV, UV⟩ := t2_separation (finset.disjoint_singleton.1 ab),
    refine ⟨U, V, oU, oV, _, _, UV⟩;
    exact singleton_subset_set_iff.mpr ‹_› },
  { intros a b c ac bc d,
    apply_mod_cast union_left (ac (disjoint_of_subset_left (a.subset_union_left b) d)) (bc _),
    exact disjoint_of_subset_left (a.subset_union_right b) d },
end

lemma point_disjoint_finset_opens_of_t2 [t2_space α] {x : α} {s : finset α} (h : x ∉ s) :
  separated ({x} : set α) s :=
by exact_mod_cast finset_disjoint_finset_opens_of_t2 {x} s (finset.disjoint_singleton_left.mpr h)

end separated

lemma tendsto_nhds_unique [t2_space α] {f : β → α} {l : filter β} {a b : α}
  [ne_bot l] (ha : tendsto f l (𝓝 a)) (hb : tendsto f l (𝓝 b)) : a = b :=
eq_of_nhds_ne_bot $ ne_bot_of_le $ le_inf ha hb

lemma tendsto_nhds_unique' [t2_space α] {f : β → α} {l : filter β} {a b : α}
  (hl : ne_bot l) (ha : tendsto f l (𝓝 a)) (hb : tendsto f l (𝓝 b)) : a = b :=
eq_of_nhds_ne_bot $ ne_bot_of_le $ le_inf ha hb

lemma tendsto_nhds_unique_of_eventually_eq [t2_space α] {f g : β → α} {l : filter β} {a b : α}
  [ne_bot l] (ha : tendsto f l (𝓝 a)) (hb : tendsto g l (𝓝 b)) (hfg : f =ᶠ[l] g) :
  a = b :=
tendsto_nhds_unique (ha.congr' hfg) hb

lemma tendsto_nhds_unique_of_frequently_eq [t2_space α] {f g : β → α} {l : filter β} {a b : α}
  (ha : tendsto f l (𝓝 a)) (hb : tendsto g l (𝓝 b)) (hfg : ∃ᶠ x in l, f x = g x) :
  a = b :=
have ∃ᶠ z : α × α in 𝓝 (a, b), z.1 = z.2 := (ha.prod_mk_nhds hb).frequently hfg,
not_not.1 $ λ hne, this (is_closed_diagonal.is_open_compl.mem_nhds hne)

/-- A T₂.₅ space, also known as a Urysohn space, is a topological space
  where for every pair `x ≠ y`, there are two open sets, with the intersection of closures
  empty, one containing `x` and the other `y` . -/
class t2_5_space (α : Type u) [topological_space α]: Prop :=
(t2_5 : ∀ x y  (h : x ≠ y), ∃ (U V: set α), is_open U ∧  is_open V ∧
                                            disjoint (closure U) (closure V) ∧ x ∈ U ∧ y ∈ V)

@[priority 100] -- see Note [lower instance priority]
instance t2_5_space.t2_space [t2_5_space α] : t2_space α :=
⟨λ x y hxy,
  let ⟨U, V, hU, hV, hUV, hh⟩ := t2_5_space.t2_5 x y hxy in
  ⟨U, V, hU, hV, hh.1, hh.2, hUV.mono subset_closure subset_closure⟩⟩

section lim
variables [t2_space α] {f : filter α}

/-!
### Properties of `Lim` and `lim`

In this section we use explicit `nonempty α` instances for `Lim` and `lim`. This way the lemmas
are useful without a `nonempty α` instance.
-/

lemma Lim_eq {a : α} [ne_bot f] (h : f ≤ 𝓝 a) :
  @Lim _ _ ⟨a⟩ f = a :=
tendsto_nhds_unique (le_nhds_Lim ⟨a, h⟩) h

lemma Lim_eq_iff [ne_bot f] (h : ∃ (a : α), f ≤ nhds a) {a} : @Lim _ _ ⟨a⟩ f = a ↔ f ≤ 𝓝 a :=
⟨λ c, c ▸ le_nhds_Lim h, Lim_eq⟩

lemma ultrafilter.Lim_eq_iff_le_nhds [compact_space α] {x : α} {F : ultrafilter α} :
  F.Lim = x ↔ ↑F ≤ 𝓝 x :=
⟨λ h, h ▸ F.le_nhds_Lim, Lim_eq⟩

lemma is_open_iff_ultrafilter' [compact_space α] (U : set α) :
  is_open U ↔ (∀ F : ultrafilter α, F.Lim ∈ U → U ∈ F.1) :=
begin
  rw is_open_iff_ultrafilter,
  refine ⟨λ h F hF, h F.Lim hF F F.le_nhds_Lim, _⟩,
  intros cond x hx f h,
  rw [← (ultrafilter.Lim_eq_iff_le_nhds.2 h)] at hx,
  exact cond _ hx
end

lemma filter.tendsto.lim_eq {a : α} {f : filter β} [ne_bot f] {g : β → α} (h : tendsto g f (𝓝 a)) :
  @lim _ _ _ ⟨a⟩ f g = a :=
Lim_eq h

lemma filter.lim_eq_iff {f : filter β} [ne_bot f] {g : β → α} (h : ∃ a, tendsto g f (𝓝 a)) {a} :
  @lim _ _ _ ⟨a⟩ f g = a ↔ tendsto g f (𝓝 a) :=
⟨λ c, c ▸ tendsto_nhds_lim h, filter.tendsto.lim_eq⟩

lemma continuous.lim_eq [topological_space β] {f : β → α} (h : continuous f) (a : β) :
  @lim _ _ _ ⟨f a⟩ (𝓝 a) f = f a :=
(h.tendsto a).lim_eq

@[simp] lemma Lim_nhds (a : α) : @Lim _ _ ⟨a⟩ (𝓝 a) = a :=
Lim_eq le_rfl

@[simp] lemma lim_nhds_id (a : α) : @lim _ _ _ ⟨a⟩ (𝓝 a) id = a :=
Lim_nhds a

@[simp] lemma Lim_nhds_within {a : α} {s : set α} (h : a ∈ closure s) :
  @Lim _ _ ⟨a⟩ (𝓝[s] a) = a :=
by haveI : ne_bot (𝓝[s] a) := mem_closure_iff_cluster_pt.1 h;
exact Lim_eq inf_le_left

@[simp] lemma lim_nhds_within_id {a : α} {s : set α} (h : a ∈ closure s) :
  @lim _ _ _ ⟨a⟩ (𝓝[s] a) id = a :=
Lim_nhds_within h

end lim

/-!
### `t2_space` constructions

We use two lemmas to prove that various standard constructions generate Hausdorff spaces from
Hausdorff spaces:

* `separated_by_continuous` says that two points `x y : α` can be separated by open neighborhoods
  provided that there exists a continuous map `f : α → β` with a Hausdorff codomain such that
  `f x ≠ f y`. We use this lemma to prove that topological spaces defined using `induced` are
  Hausdorff spaces.

* `separated_by_open_embedding` says that for an open embedding `f : α → β` of a Hausdorff space
  `α`, the images of two distinct points `x y : α`, `x ≠ y` can be separated by open neighborhoods.
  We use this lemma to prove that topological spaces defined using `coinduced` are Hausdorff spaces.
-/

@[priority 100] -- see Note [lower instance priority]
instance discrete_topology.to_t2_space {α : Type*} [topological_space α] [discrete_topology α] :
  t2_space α :=
⟨λ x y h, ⟨{x}, {y}, is_open_discrete _, is_open_discrete _, rfl, rfl, disjoint_singleton.2 h⟩⟩

lemma separated_by_continuous {α : Type*} {β : Type*}
  [topological_space α] [topological_space β] [t2_space β]
  {f : α → β} (hf : continuous f) {x y : α} (h : f x ≠ f y) :
  ∃u v : set α, is_open u ∧ is_open v ∧ x ∈ u ∧ y ∈ v ∧ disjoint u v :=
let ⟨u, v, uo, vo, xu, yv, uv⟩ := t2_separation h in
⟨f ⁻¹' u, f ⁻¹' v, uo.preimage hf, vo.preimage hf, xu, yv, uv.preimage _⟩

lemma separated_by_open_embedding {α β : Type*} [topological_space α] [topological_space β]
  [t2_space α] {f : α → β} (hf : open_embedding f) {x y : α} (h : x ≠ y) :
  ∃ u v : set β, is_open u ∧ is_open v ∧ f x ∈ u ∧ f y ∈ v ∧ disjoint u v :=
let ⟨u, v, uo, vo, xu, yv, uv⟩ := t2_separation h in
⟨f '' u, f '' v, hf.is_open_map _ uo, hf.is_open_map _ vo,
  mem_image_of_mem _ xu, mem_image_of_mem _ yv, disjoint_image_of_injective hf.inj uv⟩

instance {α : Type*} {p : α → Prop} [t : topological_space α] [t2_space α] : t2_space (subtype p) :=
⟨assume x y h, separated_by_continuous continuous_subtype_val (mt subtype.eq h)⟩

instance {α : Type*} {β : Type*} [t₁ : topological_space α] [t2_space α]
  [t₂ : topological_space β] [t2_space β] : t2_space (α × β) :=
⟨assume ⟨x₁,x₂⟩ ⟨y₁,y₂⟩ h,
  or.elim (not_and_distrib.mp (mt prod.ext_iff.mpr h))
    (λ h₁, separated_by_continuous continuous_fst h₁)
    (λ h₂, separated_by_continuous continuous_snd h₂)⟩

lemma embedding.t2_space [topological_space β] [t2_space β] {f : α → β} (hf : embedding f) :
  t2_space α :=
⟨λ x y h, separated_by_continuous hf.continuous (hf.inj.ne h)⟩

instance {α : Type*} {β : Type*} [t₁ : topological_space α] [t2_space α]
  [t₂ : topological_space β] [t2_space β] : t2_space (α ⊕ β) :=
begin
  constructor,
  rintros (x|x) (y|y) h,
  { replace h : x ≠ y := λ c, (c.subst h) rfl,
    exact separated_by_open_embedding open_embedding_inl h },
  { exact ⟨_, _, is_open_range_inl, is_open_range_inr, ⟨x, rfl⟩, ⟨y, rfl⟩,
      is_compl_range_inl_range_inr.disjoint⟩ },
  { exact ⟨_, _, is_open_range_inr, is_open_range_inl, ⟨x, rfl⟩, ⟨y, rfl⟩,
      is_compl_range_inl_range_inr.disjoint.symm⟩ },
  { replace h : x ≠ y := λ c, (c.subst h) rfl,
    exact separated_by_open_embedding open_embedding_inr h }
end

instance Pi.t2_space {α : Type*} {β : α → Type v} [t₂ : Πa, topological_space (β a)]
  [∀a, t2_space (β a)] :
  t2_space (Πa, β a) :=
⟨assume x y h,
  let ⟨i, hi⟩ := not_forall.mp (mt funext h) in
  separated_by_continuous (continuous_apply i) hi⟩

instance sigma.t2_space {ι : Type*} {α : ι → Type*} [Πi, topological_space (α i)]
  [∀a, t2_space (α a)] :
  t2_space (Σi, α i) :=
begin
  constructor,
  rintros ⟨i, x⟩ ⟨j, y⟩ neq,
  rcases em (i = j) with (rfl|h),
  { replace neq : x ≠ y := λ c, (c.subst neq) rfl,
    exact separated_by_open_embedding open_embedding_sigma_mk neq },
  { exact ⟨_, _, is_open_range_sigma_mk, is_open_range_sigma_mk, ⟨x, rfl⟩, ⟨y, rfl⟩, by tidy⟩ }
end

variables [topological_space β]

lemma is_closed_eq [t2_space α] {f g : β → α}
  (hf : continuous f) (hg : continuous g) : is_closed {x:β | f x = g x} :=
continuous_iff_is_closed.mp (hf.prod_mk hg) _ is_closed_diagonal

lemma is_open_ne_fun [t2_space α] {f g : β → α}
  (hf : continuous f) (hg : continuous g) : is_open {x:β | f x ≠ g x} :=
is_open_compl_iff.mpr $ is_closed_eq hf hg

/-- If two continuous maps are equal on `s`, then they are equal on the closure of `s`. See also
`set.eq_on.of_subset_closure` for a more general version. -/
lemma set.eq_on.closure [t2_space α] {s : set β} {f g : β → α} (h : eq_on f g s)
  (hf : continuous f) (hg : continuous g) :
  eq_on f g (closure s) :=
closure_minimal h (is_closed_eq hf hg)

/-- If two continuous functions are equal on a dense set, then they are equal. -/
lemma continuous.ext_on [t2_space α] {s : set β} (hs : dense s) {f g : β → α}
  (hf : continuous f) (hg : continuous g) (h : eq_on f g s) :
  f = g :=
funext $ λ x, h.closure hf hg (hs x)

/-- If `f x = g x` for all `x ∈ s` and `f`, `g` are continuous on `t`, `s ⊆ t ⊆ closure s`, then
`f x = g x` for all `x ∈ t`. See also `set.eq_on.closure`. -/
lemma set.eq_on.of_subset_closure [t2_space α] {s t : set β} {f g : β → α} (h : eq_on f g s)
  (hf : continuous_on f t) (hg : continuous_on g t) (hst : s ⊆ t) (hts : t ⊆ closure s) :
  eq_on f g t :=
begin
  intros x hx,
  haveI : (𝓝[s] x).ne_bot, from mem_closure_iff_cluster_pt.mp (hts hx),
  exact tendsto_nhds_unique_of_eventually_eq ((hf x hx).mono_left $ nhds_within_mono _ hst)
    ((hg x hx).mono_left $ nhds_within_mono _ hst) (h.eventually_eq_of_mem self_mem_nhds_within)
end

lemma function.left_inverse.closed_range [t2_space α] {f : α → β} {g : β → α}
  (h : function.left_inverse f g) (hf : continuous f) (hg : continuous g) :
  is_closed (range g) :=
have eq_on (g ∘ f) id (closure $ range g),
  from h.right_inv_on_range.eq_on.closure (hg.comp hf) continuous_id,
is_closed_of_closure_subset $ λ x hx,
calc x = g (f x) : (this hx).symm
   ... ∈ _ : mem_range_self _

lemma function.left_inverse.closed_embedding [t2_space α] {f : α → β} {g : β → α}
  (h : function.left_inverse f g) (hf : continuous f) (hg : continuous g) :
  closed_embedding g :=
⟨h.embedding hf hg, h.closed_range hf hg⟩

lemma compact_compact_separated [t2_space α] {s t : set α}
  (hs : is_compact s) (ht : is_compact t) (hst : disjoint s t) :
  ∃ u v, is_open u ∧ is_open v ∧ s ⊆ u ∧ t ⊆ v ∧ disjoint u v :=
by simp only [prod_subset_compl_diagonal_iff_disjoint.symm] at ⊢ hst;
   exact generalized_tube_lemma hs ht is_closed_diagonal.is_open_compl hst

/-- In a `t2_space`, every compact set is closed. -/
lemma is_compact.is_closed [t2_space α] {s : set α} (hs : is_compact s) : is_closed s :=
is_open_compl_iff.1 $ is_open_iff_forall_mem_open.mpr $ assume x hx,
  let ⟨u, v, uo, vo, su, xv, uv⟩ :=
    compact_compact_separated hs is_compact_singleton (disjoint_singleton_right.2 hx) in
⟨v, (uv.mono_left $ show s ≤ u, from su).subset_compl_left, vo, by simpa using xv⟩

@[simp] lemma filter.coclosed_compact_eq_cocompact [t2_space α] :
  coclosed_compact α = cocompact α :=
by simp [coclosed_compact, cocompact, infi_and', and_iff_right_of_imp is_compact.is_closed]

@[simp] lemma bornology.relatively_compact_eq_in_compact [t2_space α] :
  bornology.relatively_compact α = bornology.in_compact α :=
by rw bornology.ext_iff; exact filter.coclosed_compact_eq_cocompact

/-- If `V : ι → set α` is a decreasing family of compact sets then any neighborhood of
`⋂ i, V i` contains some `V i`. This is a version of `exists_subset_nhd_of_compact'` where we
don't need to assume each `V i` closed because it follows from compactness since `α` is
assumed to be Hausdorff. -/
lemma exists_subset_nhd_of_compact [t2_space α] {ι : Type*} [nonempty ι] {V : ι → set α}
  (hV : directed (⊇) V) (hV_cpct : ∀ i, is_compact (V i)) {U : set α}
  (hU : ∀ x ∈ ⋂ i, V i, U ∈ 𝓝 x) : ∃ i, V i ⊆ U :=
exists_subset_nhd_of_compact' hV hV_cpct (λ i, (hV_cpct i).is_closed) hU

lemma compact_exhaustion.is_closed [t2_space α] (K : compact_exhaustion α) (n : ℕ) :
  is_closed (K n) :=
(K.is_compact n).is_closed

lemma is_compact.inter [t2_space α] {s t : set α} (hs : is_compact s) (ht : is_compact t) :
  is_compact (s ∩ t) :=
hs.inter_right $ ht.is_closed

lemma compact_closure_of_subset_compact [t2_space α] {s t : set α} (ht : is_compact t) (h : s ⊆ t) :
  is_compact (closure s) :=
compact_of_is_closed_subset ht is_closed_closure (closure_minimal h ht.is_closed)

@[simp]
lemma exists_compact_superset_iff [t2_space α] {s : set α} :
  (∃ K, is_compact K ∧ s ⊆ K) ↔ is_compact (closure s) :=
⟨λ ⟨K, hK, hsK⟩, compact_closure_of_subset_compact hK hsK, λ h, ⟨closure s, h, subset_closure⟩⟩

lemma image_closure_of_compact [t2_space β]
  {s : set α} (hs : is_compact (closure s)) {f : α → β} (hf : continuous_on f (closure s)) :
  f '' closure s = closure (f '' s) :=
subset.antisymm hf.image_closure $ closure_minimal (image_subset f subset_closure)
  (hs.image_of_continuous_on hf).is_closed

/-- If a compact set is covered by two open sets, then we can cover it by two compact subsets. -/
lemma is_compact.binary_compact_cover [t2_space α] {K U V : set α} (hK : is_compact K)
  (hU : is_open U) (hV : is_open V) (h2K : K ⊆ U ∪ V) :
  ∃ K₁ K₂ : set α, is_compact K₁ ∧ is_compact K₂ ∧ K₁ ⊆ U ∧ K₂ ⊆ V ∧ K = K₁ ∪ K₂ :=
begin
  obtain ⟨O₁, O₂, h1O₁, h1O₂, h2O₁, h2O₂, hO⟩ := compact_compact_separated (hK.diff hU) (hK.diff hV)
    (by rwa [disjoint_iff_inter_eq_empty, diff_inter_diff, diff_eq_empty]),
  exact ⟨_, _, hK.diff h1O₁, hK.diff h1O₂, by rwa [diff_subset_comm], by rwa [diff_subset_comm],
    by rw [← diff_inter, hO.inter_eq, diff_empty]⟩
end

lemma continuous.is_closed_map [compact_space α] [t2_space β] {f : α → β} (h : continuous f) :
  is_closed_map f :=
λ s hs, (hs.is_compact.image h).is_closed

lemma continuous.closed_embedding [compact_space α] [t2_space β] {f : α → β} (h : continuous f)
  (hf : function.injective f) : closed_embedding f :=
closed_embedding_of_continuous_injective_closed h hf h.is_closed_map

section
open finset function
/-- For every finite open cover `Uᵢ` of a compact set, there exists a compact cover `Kᵢ ⊆ Uᵢ`. -/
lemma is_compact.finite_compact_cover [t2_space α] {s : set α} (hs : is_compact s)
  {ι} (t : finset ι) (U : ι → set α) (hU : ∀ i ∈ t, is_open (U i)) (hsC : s ⊆ ⋃ i ∈ t, U i) :
  ∃ K : ι → set α, (∀ i, is_compact (K i)) ∧ (∀i, K i ⊆ U i) ∧ s = ⋃ i ∈ t, K i :=
begin
  classical,
  induction t using finset.induction with x t hx ih generalizing U hU s hs hsC,
  { refine ⟨λ _, ∅, λ i, is_compact_empty, λ i, empty_subset _, _⟩,
    simpa only [subset_empty_iff, Union_false, Union_empty] using hsC },
  simp only [finset.set_bUnion_insert] at hsC,
  simp only [finset.mem_insert] at hU,
  have hU' : ∀ i ∈ t, is_open (U i) := λ i hi, hU i (or.inr hi),
  rcases hs.binary_compact_cover (hU x (or.inl rfl)) (is_open_bUnion hU') hsC
    with ⟨K₁, K₂, h1K₁, h1K₂, h2K₁, h2K₂, hK⟩,
  rcases ih U hU' h1K₂ h2K₂ with ⟨K, h1K, h2K, h3K⟩,
  refine ⟨update K x K₁, _, _, _⟩,
  { intros i, by_cases hi : i = x,
    { simp only [update_same, hi, h1K₁] },
    { rw [← ne.def] at hi, simp only [update_noteq hi, h1K] }},
  { intros i, by_cases hi : i = x,
    { simp only [update_same, hi, h2K₁] },
    { rw [← ne.def] at hi, simp only [update_noteq hi, h2K] }},
  { simp only [set_bUnion_insert_update _ hx, hK, h3K] }
end
end

lemma locally_compact_of_compact_nhds [t2_space α] (h : ∀ x : α, ∃ s, s ∈ 𝓝 x ∧ is_compact s) :
  locally_compact_space α :=
⟨assume x n hn,
  let ⟨u, un, uo, xu⟩ := mem_nhds_iff.mp hn in
  let ⟨k, kx, kc⟩ := h x in
  -- K is compact but not necessarily contained in N.
  -- K \ U is again compact and doesn't contain x, so
  -- we may find open sets V, W separating x from K \ U.
  -- Then K \ W is a compact neighborhood of x contained in U.
  let ⟨v, w, vo, wo, xv, kuw, vw⟩ := compact_compact_separated is_compact_singleton (kc.diff uo)
      (disjoint_singleton_left.2 $ λ h, h.2 xu) in
  have wn : wᶜ ∈ 𝓝 x, from
   mem_nhds_iff.mpr ⟨v, vw.subset_compl_right, vo, singleton_subset_iff.mp xv⟩,
  ⟨k \ w,
   filter.inter_mem kx wn,
   subset.trans (diff_subset_comm.mp kuw) un,
   kc.diff wo⟩⟩

@[priority 100] -- see Note [lower instance priority]
instance locally_compact_of_compact [t2_space α] [compact_space α] : locally_compact_space α :=
locally_compact_of_compact_nhds (assume x, ⟨univ, is_open_univ.mem_nhds trivial, compact_univ⟩)

/-- In a locally compact T₂ space, every point has an open neighborhood with compact closure -/
lemma exists_open_with_compact_closure [locally_compact_space α] [t2_space α] (x : α) :
  ∃ (U : set α), is_open U ∧ x ∈ U ∧ is_compact (closure U) :=
begin
  rcases exists_compact_mem_nhds x with ⟨K, hKc, hxK⟩,
  rcases mem_nhds_iff.1 hxK with ⟨t, h1t, h2t, h3t⟩,
  exact ⟨t, h2t, h3t, compact_closure_of_subset_compact hKc h1t⟩
end

/--
In a locally compact T₂ space, every compact set has an open neighborhood with compact closure.
-/
lemma exists_open_superset_and_is_compact_closure [locally_compact_space α] [t2_space α]
  {K : set α} (hK : is_compact K) : ∃ V, is_open V ∧ K ⊆ V ∧ is_compact (closure V) :=
begin
  rcases exists_compact_superset hK with ⟨K', hK', hKK'⟩,
  refine ⟨interior K', is_open_interior, hKK',
    compact_closure_of_subset_compact hK' interior_subset⟩,
end

lemma is_preirreducible_iff_subsingleton [t2_space α] (S : set α) :
  is_preirreducible S ↔ S.subsingleton :=
begin
  refine ⟨λ h x hx y hy, _, set.subsingleton.is_preirreducible⟩,
  by_contradiction e,
  obtain ⟨U, V, hU, hV, hxU, hyV, h'⟩ := t2_separation e,
  exact ((h U V hU hV ⟨x, hx, hxU⟩ ⟨y, hy, hyV⟩).mono $ inter_subset_right _ _).not_disjoint h',
end

lemma is_irreducible_iff_singleton [t2_space α] (S : set α) :
  is_irreducible S ↔ ∃ x, S = {x} :=
by rw [is_irreducible, is_preirreducible_iff_subsingleton,
  exists_eq_singleton_iff_nonempty_subsingleton]

end separation

section t3

/-- A T₃ space is a T₀ space in which for every closed `C` and `x ∉ C`, there exist
  disjoint open sets containing `x` and `C` respectively. -/
class t3_space (α : Type u) [topological_space α] extends t0_space α : Prop :=
(regular : ∀{s:set α} {a}, is_closed s → a ∉ s → ∃t, is_open t ∧ s ⊆ t ∧ 𝓝[t] a = ⊥)

@[priority 100] -- see Note [lower instance priority]
instance t3_space.t1_space [t3_space α] : t1_space α :=
begin
  rw t1_space_iff_exists_open,
  intros x y hxy,
  obtain ⟨U, hU, h⟩ := exists_is_open_xor_mem hxy,
  cases h,
  { exact ⟨U, hU, h⟩ },
  { obtain ⟨R, hR, hh⟩ := t3_space.regular (is_closed_compl_iff.mpr hU) (not_not.mpr h.1),
    obtain ⟨V, hV, hhh⟩ := mem_nhds_iff.1 (filter.inf_principal_eq_bot.1 hh.2),
    exact ⟨R, hR, hh.1 (mem_compl h.2), hV hhh.2⟩ }
end

lemma nhds_is_closed [t3_space α] {a : α} {s : set α} (h : s ∈ 𝓝 a) :
  ∃ t ∈ 𝓝 a, t ⊆ s ∧ is_closed t :=
let ⟨s', h₁, h₂, h₃⟩ := mem_nhds_iff.mp h in
have ∃t, is_open t ∧ s'ᶜ ⊆ t ∧ 𝓝[t] a = ⊥,
  from t3_space.regular h₂.is_closed_compl (not_not_intro h₃),
let ⟨t, ht₁, ht₂, ht₃⟩ := this in
⟨tᶜ,
  mem_of_eq_bot $ by rwa [compl_compl],
  subset.trans (compl_subset_comm.1 ht₂) h₁,
  is_closed_compl_iff.mpr ht₁⟩

lemma closed_nhds_basis [t3_space α] (a : α) :
  (𝓝 a).has_basis (λ s : set α, s ∈ 𝓝 a ∧ is_closed s) id :=
⟨λ t, ⟨λ t_in, let ⟨s, s_in, h_st, h⟩ := nhds_is_closed t_in in ⟨s, ⟨s_in, h⟩, h_st⟩,
       λ ⟨s, ⟨s_in, hs⟩, hst⟩, mem_of_superset s_in hst⟩⟩

lemma topological_space.is_topological_basis.exists_closure_subset [t3_space α]
  {B : set (set α)} (hB : topological_space.is_topological_basis B) {a : α} {s : set α}
  (h : s ∈ 𝓝 a) :
  ∃ t ∈ B, a ∈ t ∧ closure t ⊆ s :=
begin
  rcases nhds_is_closed h with ⟨t, hat, hts, htc⟩,
  rcases hB.mem_nhds_iff.1 hat with ⟨u, huB, hau, hut⟩,
  exact ⟨u, huB, hau, (closure_minimal hut htc).trans hts⟩
end

lemma topological_space.is_topological_basis.nhds_basis_closure [t3_space α]
  {B : set (set α)} (hB : topological_space.is_topological_basis B) (a : α) :
  (𝓝 a).has_basis (λ s : set α, a ∈ s ∧ s ∈ B) closure :=
⟨λ s, ⟨λ h, let ⟨t, htB, hat, hts⟩ := hB.exists_closure_subset h in ⟨t, ⟨hat, htB⟩, hts⟩,
  λ ⟨t, ⟨hat, htB⟩, hts⟩, mem_of_superset (hB.mem_nhds htB hat) (subset_closure.trans hts)⟩⟩

protected lemma embedding.t3_space [topological_space β] [t3_space β] {f : α → β}
  (hf : embedding f) : t3_space α :=
{ to_t0_space := hf.t0_space,
  regular :=
  begin
    intros s a hs ha,
    rcases hf.to_inducing.is_closed_iff.1 hs with ⟨s, hs', rfl⟩,
    rcases t3_space.regular hs' ha with ⟨t, ht, hst, hat⟩,
    refine ⟨f ⁻¹' t, ht.preimage hf.continuous, preimage_mono hst, _⟩,
    rw [nhds_within, hf.to_inducing.nhds_eq_comap, ← comap_principal, ← comap_inf,
        ← nhds_within, hat, comap_bot]
  end }

instance subtype.t3_space [t3_space α] {p : α → Prop} : t3_space (subtype p) :=
embedding_subtype_coe.t3_space

variable (α)
@[priority 100] -- see Note [lower instance priority]
instance t3_space.t2_space [t3_space α] : t2_space α :=
⟨λ x y hxy,
let ⟨s, hs, hys, hxs⟩ := t3_space.regular is_closed_singleton
    (mt mem_singleton_iff.1 hxy),
  ⟨t, hxt, u, hsu, htu⟩ := empty_mem_iff_bot.2 hxs,
  ⟨v, hvt, hv, hxv⟩ := mem_nhds_iff.1 hxt in
⟨v, s, hv, hs, hxv, singleton_subset_iff.1 hys,
  (disjoint_iff_inter_eq_empty.2 htu.symm).mono hvt hsu⟩⟩

@[priority 100] -- see Note [lower instance priority]
instance t3_space.t2_5_space [t3_space α] : t2_5_space α :=
⟨λ x y hxy,
let ⟨U, V, hU, hV, hh_1, hh_2, hUV⟩ := t2_separation hxy,
  hxcV := not_not.mpr (interior_maximal hUV.subset_compl_right hU hh_1),
  ⟨R, hR, hh⟩ := t3_space.regular is_closed_closure (by rwa closure_eq_compl_interior_compl),
  ⟨A, hA, hhh⟩ := mem_nhds_iff.1 (filter.inf_principal_eq_bot.1 hh.2) in
⟨A, V, hhh.1, hV, disjoint_compl_left.mono_left ((closure_minimal hA hR.is_closed_compl).trans $
  compl_subset_compl.mpr hh.1), hhh.2, hh_2⟩⟩

variable {α}

/-- Given two points `x ≠ y`, we can find neighbourhoods `x ∈ V₁ ⊆ U₁` and `y ∈ V₂ ⊆ U₂`,
with the `Vₖ` closed and the `Uₖ` open, such that the `Uₖ` are disjoint. -/
lemma disjoint_nested_nhds [t3_space α] {x y : α} (h : x ≠ y) :
  ∃ (U₁ V₁ ∈ 𝓝 x) (U₂ V₂ ∈ 𝓝 y), is_closed V₁ ∧ is_closed V₂ ∧ is_open U₁ ∧ is_open U₂ ∧
  V₁ ⊆ U₁ ∧ V₂ ⊆ U₂ ∧ disjoint U₁ U₂ :=
begin
  rcases t2_separation h with ⟨U₁, U₂, U₁_op, U₂_op, x_in, y_in, H⟩,
  rcases nhds_is_closed (is_open.mem_nhds U₁_op x_in) with ⟨V₁, V₁_in, h₁, V₁_closed⟩,
  rcases nhds_is_closed (is_open.mem_nhds U₂_op y_in) with ⟨V₂, V₂_in, h₂, V₂_closed⟩,
  use [U₁, mem_of_superset V₁_in h₁, V₁, V₁_in,
       U₂, mem_of_superset V₂_in h₂, V₂, V₂_in],
  tauto
end

/--
In a locally compact T₃ space, given a compact set `K` inside an open set `U`, we can find a
compact set `K'` between these sets: `K` is inside the interior of `K'` and `K' ⊆ U`.
-/
lemma exists_compact_between [locally_compact_space α] [t3_space α]
  {K U : set α} (hK : is_compact K) (hU : is_open U) (hKU : K ⊆ U) :
  ∃ K', is_compact K' ∧ K ⊆ interior K' ∧ K' ⊆ U :=
begin
  choose C hxC hCU hC using λ x : K, nhds_is_closed (hU.mem_nhds $ hKU x.2),
  choose L hL hxL using λ x : K, exists_compact_mem_nhds (x : α),
  have : K ⊆ ⋃ x, interior (L x) ∩ interior (C x), from
  λ x hx, mem_Union.mpr ⟨⟨x, hx⟩,
    ⟨mem_interior_iff_mem_nhds.mpr (hxL _), mem_interior_iff_mem_nhds.mpr (hxC _)⟩⟩,
  rcases hK.elim_finite_subcover _ _ this with ⟨t, ht⟩,
  { refine ⟨⋃ x ∈ t, L x ∩ C x, t.compact_bUnion (λ x _, (hL x).inter_right (hC x)), λ x hx, _, _⟩,
    { obtain ⟨y, hyt, hy : x ∈ interior (L y) ∩ interior (C y)⟩ := mem_Union₂.mp (ht hx),
      rw [← interior_inter] at hy,
      refine interior_mono (subset_bUnion_of_mem hyt) hy },
    { simp_rw [Union_subset_iff], rintro x -, exact (inter_subset_right _ _).trans (hCU _) } },
  { exact λ _, is_open_interior.inter is_open_interior }
end

/--
In a locally compact regular space, given a compact set `K` inside an open set `U`, we can find a
open set `V` between these sets with compact closure: `K ⊆ V` and the closure of `V` is inside `U`.
-/
lemma exists_open_between_and_is_compact_closure [locally_compact_space α] [t3_space α]
  {K U : set α} (hK : is_compact K) (hU : is_open U) (hKU : K ⊆ U) :
  ∃ V, is_open V ∧ K ⊆ V ∧ closure V ⊆ U ∧ is_compact (closure V) :=
begin
  rcases exists_compact_between hK hU hKU with ⟨V, hV, hKV, hVU⟩,
  refine ⟨interior V, is_open_interior, hKV,
    (closure_minimal interior_subset hV.is_closed).trans hVU,
    compact_closure_of_subset_compact hV interior_subset⟩,
end

end t3

section normality

/-- A T₄ space, also known as a normal space (although this condition sometimes
  omits T₂), is one in which for every pair of disjoint closed sets `C` and `D`,
  there exist disjoint open sets containing `C` and `D` respectively. -/
class normal_space (α : Type u) [topological_space α] extends t1_space α : Prop :=
(normal : ∀ s t : set α, is_closed s → is_closed t → disjoint s t →
  ∃ u v, is_open u ∧ is_open v ∧ s ⊆ u ∧ t ⊆ v ∧ disjoint u v)

theorem normal_separation [normal_space α] {s t : set α}
  (H1 : is_closed s) (H2 : is_closed t) (H3 : disjoint s t) :
  ∃ u v, is_open u ∧ is_open v ∧ s ⊆ u ∧ t ⊆ v ∧ disjoint u v :=
normal_space.normal s t H1 H2 H3

theorem normal_exists_closure_subset [normal_space α] {s t : set α} (hs : is_closed s)
  (ht : is_open t) (hst : s ⊆ t) :
  ∃ u, is_open u ∧ s ⊆ u ∧ closure u ⊆ t :=
begin
  have : disjoint s tᶜ, from λ x ⟨hxs, hxt⟩, hxt (hst hxs),
  rcases normal_separation hs (is_closed_compl_iff.2 ht) this
    with ⟨s', t', hs', ht', hss', htt', hs't'⟩,
  refine ⟨s', hs', hss',
    subset.trans (closure_minimal _ (is_closed_compl_iff.2 ht')) (compl_subset_comm.1 htt')⟩,
  exact λ x hxs hxt, hs't' ⟨hxs, hxt⟩
end

@[priority 100] -- see Note [lower instance priority]
instance normal_space.t3_space [normal_space α] : t3_space α :=
{ regular := λ s x hs hxs, let ⟨u, v, hu, hv, hsu, hxv, huv⟩ :=
    normal_separation hs is_closed_singleton
      (λ _ ⟨hx, hy⟩, hxs $ mem_of_eq_of_mem (eq_of_mem_singleton hy).symm hx) in
    ⟨u, hu, hsu, filter.empty_mem_iff_bot.1 $ filter.mem_inf_iff.2
      ⟨v, is_open.mem_nhds hv (singleton_subset_iff.1 hxv), u, filter.mem_principal_self u,
       by rwa [eq_comm, inter_comm, ← disjoint_iff_inter_eq_empty]⟩⟩ }

-- We can't make this an instance because it could cause an instance loop.
lemma normal_of_compact_t2 [compact_space α] [t2_space α] : normal_space α :=
⟨λ s t hs ht, compact_compact_separated hs.is_compact ht.is_compact⟩

protected lemma closed_embedding.normal_space [topological_space β] [normal_space β] {f : α → β}
  (hf : closed_embedding f) : normal_space α :=
{ to_t1_space := hf.to_embedding.t1_space,
  normal :=
  begin
    intros s t hs ht hst,
    rcases normal_space.normal (f '' s) (f '' t) (hf.is_closed_map s hs) (hf.is_closed_map t ht)
      (disjoint_image_of_injective hf.inj hst) with ⟨u, v, hu, hv, hsu, htv, huv⟩,
    rw image_subset_iff at hsu htv,
    exact ⟨f ⁻¹' u, f ⁻¹' v, hu.preimage hf.continuous, hv.preimage hf.continuous,
            hsu, htv, huv.preimage f⟩
  end }

variable (α)

/-- A T₃ topological space with second countable topology is a normal space.
This lemma is not an instance to avoid a loop. -/
lemma normal_space_of_t3_second_countable [second_countable_topology α] [t3_space α] :
  normal_space α :=
begin
  have key : ∀ {s t : set α}, is_closed t → disjoint s t →
    ∃ U : set (countable_basis α), (s ⊆ ⋃ u ∈ U, ↑u) ∧
      (∀ u ∈ U, disjoint (closure ↑u) t) ∧
      ∀ n : ℕ, is_closed (⋃ (u ∈ U) (h : encodable.encode u ≤ n), closure (u : set α)),
  { intros s t hc hd,
    rw disjoint_left at hd,
    have : ∀ x ∈ s, ∃ U ∈ countable_basis α, x ∈ U ∧ disjoint (closure U) t,
    { intros x hx,
      rcases (is_basis_countable_basis α).exists_closure_subset (hc.is_open_compl.mem_nhds (hd hx))
        with ⟨u, hu, hxu, hut⟩,
      exact ⟨u, hu, hxu, disjoint_left.2 hut⟩ },
    choose! U hu hxu hd,
    set V : s → countable_basis α := maps_to.restrict _ _ _ hu,
    refine ⟨range V, _, forall_range_iff.2 $ subtype.forall.2 hd, λ n, _⟩,
    { rw bUnion_range,
      exact λ x hx, mem_Union.2 ⟨⟨x, hx⟩, hxu x hx⟩ },
    { simp only [← supr_eq_Union, supr_and'],
      exact is_closed_bUnion (((finite_le_nat n).preimage_embedding (encodable.encode' _)).subset $
        inter_subset_right _ _) (λ u hu, is_closed_closure) } },
  refine ⟨λ s t hs ht hd, _⟩,
  rcases key ht hd with ⟨U, hsU, hUd, hUc⟩,
  rcases key hs hd.symm with ⟨V, htV, hVd, hVc⟩,
  refine ⟨⋃ u ∈ U, ↑u \ ⋃ (v ∈ V) (hv : encodable.encode v ≤ encodable.encode u), closure ↑v,
    ⋃ v ∈ V, ↑v \ ⋃ (u ∈ U) (hu : encodable.encode u ≤ encodable.encode v), closure ↑u,
    is_open_bUnion $ λ u hu, (is_open_of_mem_countable_basis u.2).sdiff (hVc _),
    is_open_bUnion $ λ v hv, (is_open_of_mem_countable_basis v.2).sdiff (hUc _),
    λ x hx, _, λ x hx, _, _⟩,
  { rcases mem_Union₂.1 (hsU hx) with ⟨u, huU, hxu⟩,
    refine mem_bUnion huU ⟨hxu, _⟩,
    simp only [mem_Union],
    rintro ⟨v, hvV, -, hxv⟩,
    exact hVd v hvV ⟨hxv, hx⟩ },
  { rcases mem_Union₂.1 (htV hx) with ⟨v, hvV, hxv⟩,
    refine mem_bUnion hvV ⟨hxv, _⟩,
    simp only [mem_Union],
    rintro ⟨u, huU, -, hxu⟩,
    exact hUd u huU ⟨hxu, hx⟩ },
  { simp only [disjoint_left, mem_Union, mem_diff, not_exists, not_and, not_forall, not_not],
    rintro a ⟨u, huU, hau, haV⟩ v hvV hav,
    cases le_total (encodable.encode u) (encodable.encode v) with hle hle,
    exacts [⟨u, huU, hle, subset_closure hau⟩, (haV _ hvV hle $ subset_closure hav).elim] }
end

end normality

/-- In a compact t2 space, the connected component of a point equals the intersection of all
its clopen neighbourhoods. -/
lemma connected_component_eq_Inter_clopen [t2_space α] [compact_space α] (x : α) :
  connected_component x = ⋂ Z : {Z : set α // is_clopen Z ∧ x ∈ Z}, Z :=
begin
  apply eq_of_subset_of_subset connected_component_subset_Inter_clopen,
  -- Reduce to showing that the clopen intersection is connected.
  refine is_preconnected.subset_connected_component _ (mem_Inter.2 (λ Z, Z.2.2)),
  -- We do this by showing that any disjoint cover by two closed sets implies
  -- that one of these closed sets must contain our whole thing.
  -- To reduce to the case where the cover is disjoint on all of `α` we need that `s` is closed
  have hs : @is_closed α _ (⋂ (Z : {Z : set α // is_clopen Z ∧ x ∈ Z}), Z) :=
    is_closed_Inter (λ Z, Z.2.1.2),
  rw (is_preconnected_iff_subset_of_fully_disjoint_closed hs),
  intros a b ha hb hab ab_disj,
  haveI := @normal_of_compact_t2 α _ _ _,
  -- Since our space is normal, we get two larger disjoint open sets containing the disjoint
  -- closed sets. If we can show that our intersection is a subset of any of these we can then
  -- "descend" this to show that it is a subset of either a or b.
  rcases normal_separation ha hb ab_disj with ⟨u, v, hu, hv, hau, hbv, huv⟩,
  -- If we can find a clopen set around x, contained in u ∪ v, we get a disjoint decomposition
  -- Z = Z ∩ u ∪ Z ∩ v of clopen sets. The intersection of all clopen neighbourhoods will then lie
  -- in whichever of u or v x lies in and hence will be a subset of either a or b.
  suffices : ∃ (Z : set α), is_clopen Z ∧ x ∈ Z ∧ Z ⊆ u ∪ v,
  { cases this with Z H,
    have H1 := is_clopen_inter_of_disjoint_cover_clopen H.1 H.2.2 hu hv huv,
    rw [union_comm] at H,
    have H2 := is_clopen_inter_of_disjoint_cover_clopen H.1 H.2.2 hv hu huv.symm,
    by_cases (x ∈ u),
    -- The x ∈ u case.
    { left,
      suffices : (⋂ (Z : {Z : set α // is_clopen Z ∧ x ∈ Z}), ↑Z) ⊆ u,
      { replace hab : (⋂ (Z : {Z // is_clopen Z ∧ x ∈ Z}), ↑Z) ≤ a ∪ b := hab,
        replace this : (⋂ (Z : {Z // is_clopen Z ∧ x ∈ Z}), ↑Z) ≤ u := this,
        exact disjoint.left_le_of_le_sup_right hab (huv.mono this hbv) },
      { apply subset.trans _ (inter_subset_right Z u),
        apply Inter_subset (λ Z : {Z : set α // is_clopen Z ∧ x ∈ Z}, ↑Z)
          ⟨Z ∩ u, H1, mem_inter H.2.1 h⟩ } },
    -- If x ∉ u, we get x ∈ v since x ∈ u ∪ v. The rest is then like the x ∈ u case.
    have h1 : x ∈ v,
    { cases (mem_union x u v).1 (mem_of_subset_of_mem (subset.trans hab
        (union_subset_union hau hbv)) (mem_Inter.2 (λ i, i.2.2))) with h1 h1,
      { exfalso, exact h h1},
      { exact h1} },
    right,
    suffices : (⋂ (Z : {Z : set α // is_clopen Z ∧ x ∈ Z}), ↑Z) ⊆ v,
    { replace this : (⋂ (Z : {Z // is_clopen Z ∧ x ∈ Z}), ↑Z) ≤ v := this,
      exact (huv.symm.mono this hau).left_le_of_le_sup_left hab },
    { apply subset.trans _ (inter_subset_right Z v),
      apply Inter_subset (λ Z : {Z : set α // is_clopen Z ∧ x ∈ Z}, ↑Z)
        ⟨Z ∩ v, H2, mem_inter H.2.1 h1⟩ } },
  -- Now we find the required Z. We utilize the fact that X \ u ∪ v will be compact,
  -- so there must be some finite intersection of clopen neighbourhoods of X disjoint to it,
  -- but a finite intersection of clopen sets is clopen so we let this be our Z.
  have H1 := (hu.union hv).is_closed_compl.is_compact.inter_Inter_nonempty
    (λ Z : {Z : set α // is_clopen Z ∧ x ∈ Z}, Z) (λ Z, Z.2.1.2),
  rw [←not_disjoint_iff_nonempty_inter, imp_not_comm, not_forall] at H1,
  cases H1 (disjoint_compl_left_iff_subset.2 $ hab.trans $ union_subset_union hau hbv) with Zi H2,
  refine ⟨(⋂ (U ∈ Zi), subtype.val U), _, _, _⟩,
  { exact is_clopen_bInter_finset (λ Z hZ, Z.2.1) },
  { exact mem_Inter₂.2 (λ Z hZ, Z.2.2) },
  { rwa [←disjoint_compl_left_iff_subset, disjoint_iff_inter_eq_empty, ←not_nonempty_iff_eq_empty] }
end

section profinite

variables [t2_space α]

/-- A Hausdorff space with a clopen basis is totally separated. -/
lemma tot_sep_of_zero_dim (h : is_topological_basis {s : set α | is_clopen s}) :
  totally_separated_space α :=
begin
  constructor,
  rintros x - y - hxy,
  obtain ⟨u, v, hu, hv, xu, yv, disj⟩ := t2_separation hxy,
  obtain ⟨w, hw : is_clopen w, xw, wu⟩ := (is_topological_basis.mem_nhds_iff h).1
    (is_open.mem_nhds hu xu),
  refine ⟨w, wᶜ, hw.1, hw.compl.1, xw, λ h, disj ⟨wu h, yv⟩, _, disjoint_compl_right⟩,
  rw set.union_compl_self,
end

variables [compact_space α]

/-- A compact Hausdorff space is totally disconnected if and only if it is totally separated, this
  is also true for locally compact spaces. -/
theorem compact_t2_tot_disc_iff_tot_sep :
  totally_disconnected_space α ↔ totally_separated_space α :=
begin
  split,
  { intro h, constructor,
    rintros x - y -,
    contrapose!,
    intros hyp,
    suffices : x ∈ connected_component y,
      by simpa [totally_disconnected_space_iff_connected_component_singleton.1 h y,
                mem_singleton_iff],
    rw [connected_component_eq_Inter_clopen, mem_Inter],
    rintro ⟨w : set α, hw : is_clopen w, hy : y ∈ w⟩,
    by_contra hx,
    exact hyp wᶜ w hw.2.is_open_compl hw.1 hx hy (@is_compl_compl _ w _).symm.2
      disjoint_compl_left },
  apply totally_separated_space.totally_disconnected_space,
end

variables [totally_disconnected_space α]

lemma nhds_basis_clopen (x : α) : (𝓝 x).has_basis (λ s : set α, x ∈ s ∧ is_clopen s) id :=
⟨λ U, begin
  split,
  { have : connected_component x = {x},
      from totally_disconnected_space_iff_connected_component_singleton.mp ‹_› x,
    rw connected_component_eq_Inter_clopen at this,
    intros hU,
    let N := {Z // is_clopen Z ∧ x ∈ Z},
    suffices : ∃ Z : N, Z.val ⊆ U,
    { rcases this with ⟨⟨s, hs, hs'⟩, hs''⟩,
      exact ⟨s, ⟨hs', hs⟩, hs''⟩ },
    haveI : nonempty N := ⟨⟨univ, is_clopen_univ, mem_univ x⟩⟩,
    have hNcl : ∀ Z : N, is_closed Z.val := (λ Z, Z.property.1.2),
    have hdir : directed superset (λ Z : N, Z.val),
    { rintros ⟨s, hs, hxs⟩ ⟨t, ht, hxt⟩,
      exact ⟨⟨s ∩ t, hs.inter ht, ⟨hxs, hxt⟩⟩, inter_subset_left s t, inter_subset_right s t⟩ },
    have h_nhd: ∀ y ∈ (⋂ Z : N, Z.val), U ∈ 𝓝 y,
    { intros y y_in,
      erw [this, mem_singleton_iff] at y_in,
      rwa y_in },
    exact exists_subset_nhd_of_compact_space hdir hNcl h_nhd },
  { rintro ⟨V, ⟨hxV, V_op, -⟩, hUV : V ⊆ U⟩,
    rw mem_nhds_iff,
    exact ⟨V, hUV, V_op, hxV⟩ }
end⟩

lemma is_topological_basis_clopen : is_topological_basis {s : set α | is_clopen s} :=
begin
  apply is_topological_basis_of_open_of_nhds (λ U (hU : is_clopen U), hU.1),
  intros x U hxU U_op,
  have : U ∈ 𝓝 x,
  from is_open.mem_nhds U_op hxU,
  rcases (nhds_basis_clopen x).mem_iff.mp this with ⟨V, ⟨hxV, hV⟩, hVU : V ⊆ U⟩,
  use V,
  tauto
end

/-- Every member of an open set in a compact Hausdorff totally disconnected space
  is contained in a clopen set contained in the open set.  -/
lemma compact_exists_clopen_in_open {x : α} {U : set α} (is_open : is_open U) (memU : x ∈ U) :
    ∃ (V : set α) (hV : is_clopen V), x ∈ V ∧ V ⊆ U :=
  (is_topological_basis.mem_nhds_iff is_topological_basis_clopen).1 (is_open.mem_nhds memU)

end profinite

section locally_compact

variables {H : Type*} [topological_space H] [locally_compact_space H] [t2_space H]

/-- A locally compact Hausdorff totally disconnected space has a basis with clopen elements. -/
lemma loc_compact_Haus_tot_disc_of_zero_dim [totally_disconnected_space H] :
  is_topological_basis {s : set H | is_clopen s} :=
begin
  refine is_topological_basis_of_open_of_nhds (λ u hu, hu.1) _,
  rintros x U memU hU,
  obtain ⟨s, comp, xs, sU⟩ := exists_compact_subset hU memU,
  obtain ⟨t, h, ht, xt⟩ := mem_interior.1 xs,
  let u : set s := (coe : s → H)⁻¹' (interior s),
  have u_open_in_s : is_open u := is_open_interior.preimage continuous_subtype_coe,
  let X : s := ⟨x, h xt⟩,
  have Xu : X ∈ u := xs,
  haveI : compact_space s := is_compact_iff_compact_space.1 comp,
  obtain ⟨V : set s, clopen_in_s, Vx, V_sub⟩ := compact_exists_clopen_in_open u_open_in_s Xu,
  have V_clopen : is_clopen ((coe : s → H) '' V),
  { refine ⟨_, (comp.is_closed.closed_embedding_subtype_coe.closed_iff_image_closed).1
               clopen_in_s.2⟩,
    let v : set u := (coe : u → s)⁻¹' V,
    have : (coe : u → H) = (coe : s → H) ∘ (coe : u → s) := rfl,
    have f0 : embedding (coe : u → H) := embedding_subtype_coe.comp embedding_subtype_coe,
    have f1 : open_embedding (coe : u → H),
    { refine ⟨f0, _⟩,
      { have : set.range (coe : u → H) = interior s,
        { rw [this, set.range_comp, subtype.range_coe, subtype.image_preimage_coe],
          apply set.inter_eq_self_of_subset_left interior_subset, },
        rw this,
        apply is_open_interior } },
    have f2 : is_open v := clopen_in_s.1.preimage continuous_subtype_coe,
    have f3 : (coe : s → H) '' V = (coe : u → H) '' v,
    { rw [this, image_comp coe coe, subtype.image_preimage_coe,
          inter_eq_self_of_subset_left V_sub] },
    rw f3,
    apply f1.is_open_map v f2 },
  refine ⟨coe '' V, V_clopen, by simp [Vx, h xt], _⟩,
  transitivity s,
  { simp },
  assumption
end

/-- A locally compact Hausdorff space is totally disconnected
  if and only if it is totally separated. -/
theorem loc_compact_t2_tot_disc_iff_tot_sep :
  totally_disconnected_space H ↔ totally_separated_space H :=
begin
  split,
  { introI h,
    exact tot_sep_of_zero_dim loc_compact_Haus_tot_disc_of_zero_dim, },
  apply totally_separated_space.totally_disconnected_space,
end

end locally_compact

/-- `connected_components α` is Hausdorff when `α` is Hausdorff and compact -/
instance connected_components.t2 [t2_space α] [compact_space α] :
  t2_space (connected_components α) :=
begin
  -- Proof follows that of: https://stacks.math.columbia.edu/tag/0900
  -- Fix 2 distinct connected components, with points a and b
  refine ⟨connected_components.surjective_coe.forall₂.2 $ λ a b ne, _⟩,
  rw connected_components.coe_ne_coe at ne,
  have h := connected_component_disjoint ne,
  -- write ↑b as the intersection of all clopen subsets containing it
  rw [connected_component_eq_Inter_clopen b, disjoint_iff_inter_eq_empty] at h,
  -- Now we show that this can be reduced to some clopen containing `↑b` being disjoint to `↑a`
  obtain ⟨U, V, hU, ha, hb, rfl⟩ : ∃ (U : set α) (V : set (connected_components α)), is_clopen U ∧
    connected_component a ∩ U = ∅ ∧ connected_component b ⊆ U ∧ coe ⁻¹' V = U,
  { cases is_closed_connected_component.is_compact.elim_finite_subfamily_closed _ _ h with fin_a ha,
    swap, { exact λ Z, Z.2.1.2 },
    -- This clopen and its complement will separate the connected components of `a` and `b`
    set U : set α := (⋂ (i : {Z // is_clopen Z ∧ b ∈ Z}) (H : i ∈ fin_a), i),
    have hU : is_clopen U := is_clopen_bInter_finset (λ i j, i.2.1),
    exact ⟨U, coe '' U, hU, ha, subset_Inter₂ (λ Z _, Z.2.1.connected_component_subset Z.2.2),
      (connected_components_preimage_image U).symm ▸ hU.bUnion_connected_component_eq⟩ },
  rw connected_components.quotient_map_coe.is_clopen_preimage at hU,
  refine ⟨Vᶜ, V, hU.compl.is_open, hU.is_open, _, hb mem_connected_component, disjoint_compl_left⟩,
  exact λ h, flip set.nonempty.ne_empty ha ⟨a, mem_connected_component, h⟩,
end
