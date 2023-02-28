/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Alistair Tucker
-/
import order.complete_lattice_intervals
import topology.order.basic

/-!
# Intermediate Value Theorem

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove the Intermediate Value Theorem: if `f : α → β` is a function defined on a
connected set `s` that takes both values `≤ a` and values `≥ a` on `s`, then it is equal to `a` at
some point of `s`. We also prove that intervals in a dense conditionally complete order are
preconnected and any preconnected set is an interval. Then we specialize IVT to functions continuous
on intervals.

## Main results

* `is_preconnected_I??` : all intervals `I??` are preconnected,
* `is_preconnected.intermediate_value`, `intermediate_value_univ` : Intermediate Value Theorem for
  connected sets and connected spaces, respectively;
* `intermediate_value_Icc`, `intermediate_value_Icc'`: Intermediate Value Theorem for functions
  on closed intervals.

### Miscellaneous facts

* `is_closed.Icc_subset_of_forall_mem_nhds_within` : “Continuous induction” principle;
  if `s ∩ [a, b]` is closed, `a ∈ s`, and for each `x ∈ [a, b) ∩ s` some of its right neighborhoods
  is included `s`, then `[a, b] ⊆ s`.
* `is_closed.Icc_subset_of_forall_exists_gt`, `is_closed.mem_of_ge_of_forall_exists_gt` : two
  other versions of the “continuous induction” principle.

## Tags

intermediate value theorem, connected space, connected set
-/

open filter order_dual topological_space function set
open_locale topology filter

universes u v w

/-!
### Intermediate value theorem on a (pre)connected space

In this section we prove the following theorem (see `is_preconnected.intermediate_value₂`): if `f`
and `g` are two functions continuous on a preconnected set `s`, `f a ≤ g a` at some `a ∈ s` and
`g b ≤ f b` at some `b ∈ s`, then `f c = g c` at some `c ∈ s`. We prove several versions of this
statement, including the classical IVT that corresponds to a constant function `g`.
-/

section

variables {X : Type u} {α : Type v} [topological_space X]
  [linear_order α] [topological_space α] [order_closed_topology α]

/-- Intermediate value theorem for two functions: if `f` and `g` are two continuous functions
on a preconnected space and `f a ≤ g a` and `g b ≤ f b`, then for some `x` we have `f x = g x`. -/
lemma intermediate_value_univ₂ [preconnected_space X] {a b : X} {f g : X → α} (hf : continuous f)
  (hg : continuous g) (ha : f a ≤ g a) (hb : g b ≤ f b) :
  ∃ x, f x = g x :=
begin
  obtain ⟨x, h, hfg, hgf⟩ : (univ ∩ {x | f x ≤ g x ∧ g x ≤ f x}).nonempty,
    from is_preconnected_closed_iff.1 preconnected_space.is_preconnected_univ _ _
      (is_closed_le hf hg) (is_closed_le hg hf) (λ x hx, le_total _ _) ⟨a, trivial, ha⟩
      ⟨b, trivial, hb⟩,
  exact ⟨x, le_antisymm hfg hgf⟩
end

lemma intermediate_value_univ₂_eventually₁ [preconnected_space X] {a : X} {l : filter X} [ne_bot l]
  {f g : X → α} (hf : continuous f) (hg : continuous g) (ha : f a ≤ g a) (he : g ≤ᶠ[l] f) :
  ∃ x, f x = g x :=
let ⟨c, hc⟩ := he.frequently.exists in intermediate_value_univ₂ hf hg ha hc

lemma intermediate_value_univ₂_eventually₂ [preconnected_space X] {l₁ l₂ : filter X}
  [ne_bot l₁] [ne_bot l₂] {f g : X → α} (hf : continuous f) (hg : continuous g)
  (he₁ : f ≤ᶠ[l₁] g ) (he₂ : g ≤ᶠ[l₂] f) :
  ∃ x, f x = g x :=
let ⟨c₁, hc₁⟩ := he₁.frequently.exists, ⟨c₂, hc₂⟩ := he₂.frequently.exists in
intermediate_value_univ₂ hf hg hc₁ hc₂

/-- Intermediate value theorem for two functions: if `f` and `g` are two functions continuous
on a preconnected set `s` and for some `a b ∈ s` we have `f a ≤ g a` and `g b ≤ f b`,
then for some `x ∈ s` we have `f x = g x`. -/
lemma is_preconnected.intermediate_value₂ {s : set X} (hs : is_preconnected s)
  {a b : X} (ha : a ∈ s) (hb : b ∈ s) {f g : X → α}
  (hf : continuous_on f s) (hg : continuous_on g s) (ha' : f a ≤ g a) (hb' : g b ≤ f b) :
  ∃ x ∈ s, f x = g x :=
let ⟨x, hx⟩ := @intermediate_value_univ₂ s α _ _ _ _ (subtype.preconnected_space hs) ⟨a, ha⟩ ⟨b, hb⟩
  _ _ (continuous_on_iff_continuous_restrict.1 hf) (continuous_on_iff_continuous_restrict.1 hg)
  ha' hb'
in ⟨x, x.2, hx⟩

lemma is_preconnected.intermediate_value₂_eventually₁ {s : set X} (hs : is_preconnected s)
  {a : X} {l : filter X} (ha : a ∈ s) [ne_bot l] (hl : l ≤ 𝓟 s) {f g : X → α}
  (hf : continuous_on f s) (hg : continuous_on g s) (ha' : f a ≤ g a) (he : g ≤ᶠ[l] f) :
  ∃ x ∈ s, f x = g x :=
begin
  rw continuous_on_iff_continuous_restrict at hf hg,
  obtain ⟨b, h⟩ := @intermediate_value_univ₂_eventually₁ _ _ _ _ _ _ (subtype.preconnected_space hs)
    ⟨a, ha⟩ _ (comap_coe_ne_bot_of_le_principal hl) _ _ hf hg ha' (he.comap _),
  exact ⟨b, b.prop, h⟩,
end

lemma is_preconnected.intermediate_value₂_eventually₂ {s : set X} (hs : is_preconnected s)
  {l₁ l₂ : filter X} [ne_bot l₁] [ne_bot l₂] (hl₁ : l₁ ≤ 𝓟 s) (hl₂ : l₂ ≤ 𝓟 s) {f g : X → α}
  (hf : continuous_on f s) (hg : continuous_on g s) (he₁ : f ≤ᶠ[l₁] g) (he₂ : g ≤ᶠ[l₂] f) :
  ∃ x ∈ s, f x = g x :=
begin
  rw continuous_on_iff_continuous_restrict at hf hg,
  obtain ⟨b, h⟩ := @intermediate_value_univ₂_eventually₂ _ _ _ _ _ _ (subtype.preconnected_space hs)
    _ _ (comap_coe_ne_bot_of_le_principal hl₁) (comap_coe_ne_bot_of_le_principal hl₂)
    _ _ hf hg (he₁.comap _) (he₂.comap _),
  exact ⟨b, b.prop, h⟩,
end

/-- **Intermediate Value Theorem** for continuous functions on connected sets. -/
lemma is_preconnected.intermediate_value {s : set X} (hs : is_preconnected s)
  {a b : X} (ha : a ∈ s) (hb : b ∈ s) {f : X → α} (hf : continuous_on f s) :
  Icc (f a) (f b) ⊆ f '' s :=
λ x hx, mem_image_iff_bex.2 $ hs.intermediate_value₂ ha hb hf continuous_on_const hx.1 hx.2

lemma is_preconnected.intermediate_value_Ico {s : set X} (hs : is_preconnected s)
  {a : X} {l : filter X} (ha : a ∈ s) [ne_bot l] (hl : l ≤ 𝓟 s) {f : X → α}
  (hf : continuous_on f s) {v : α} (ht : tendsto f l (𝓝 v)) :
  Ico (f a) v ⊆ f '' s :=
λ y h, bex_def.1 $ hs.intermediate_value₂_eventually₁ ha hl
  hf continuous_on_const h.1 (eventually_ge_of_tendsto_gt h.2 ht)

lemma is_preconnected.intermediate_value_Ioc {s : set X} (hs : is_preconnected s)
  {a : X} {l : filter X} (ha : a ∈ s) [ne_bot l] (hl : l ≤ 𝓟 s) {f : X → α}
  (hf : continuous_on f s) {v : α} (ht : tendsto f l (𝓝 v)) :
  Ioc v (f a) ⊆ f '' s :=
λ y h, bex_def.1 $ bex.imp_right (λ x _, eq.symm) $ hs.intermediate_value₂_eventually₁ ha hl
  continuous_on_const hf h.2 (eventually_le_of_tendsto_lt h.1 ht)

lemma is_preconnected.intermediate_value_Ioo {s : set X} (hs : is_preconnected s)
  {l₁ l₂ : filter X} [ne_bot l₁] [ne_bot l₂] (hl₁ : l₁ ≤ 𝓟 s) (hl₂ : l₂ ≤ 𝓟 s) {f : X → α}
  (hf : continuous_on f s) {v₁ v₂ : α} (ht₁ : tendsto f l₁ (𝓝 v₁)) (ht₂ : tendsto f l₂ (𝓝 v₂)) :
  Ioo v₁ v₂ ⊆ f '' s :=
λ y h, bex_def.1 $ hs.intermediate_value₂_eventually₂ hl₁ hl₂
  hf continuous_on_const (eventually_le_of_tendsto_lt h.1 ht₁) (eventually_ge_of_tendsto_gt h.2 ht₂)

lemma is_preconnected.intermediate_value_Ici {s : set X} (hs : is_preconnected s)
  {a : X} {l : filter X} (ha : a ∈ s) [ne_bot l] (hl : l ≤ 𝓟 s) {f : X → α}
  (hf : continuous_on f s) (ht : tendsto f l at_top) :
  Ici (f a) ⊆ f '' s :=
λ y h, bex_def.1 $ hs.intermediate_value₂_eventually₁ ha hl
  hf continuous_on_const h (tendsto_at_top.1 ht y)

lemma is_preconnected.intermediate_value_Iic {s : set X} (hs : is_preconnected s)
  {a : X} {l : filter X} (ha : a ∈ s) [ne_bot l] (hl : l ≤ 𝓟 s) {f : X → α}
  (hf : continuous_on f s) (ht : tendsto f l at_bot) :
  Iic (f a) ⊆ f '' s :=
λ y h, bex_def.1 $ bex.imp_right (λ x _, eq.symm) $ hs.intermediate_value₂_eventually₁ ha hl
  continuous_on_const hf h (tendsto_at_bot.1 ht y)

lemma is_preconnected.intermediate_value_Ioi {s : set X} (hs : is_preconnected s)
  {l₁ l₂ : filter X} [ne_bot l₁] [ne_bot l₂] (hl₁ : l₁ ≤ 𝓟 s) (hl₂ : l₂ ≤ 𝓟 s) {f : X → α}
  (hf : continuous_on f s) {v : α} (ht₁ : tendsto f l₁ (𝓝 v)) (ht₂ : tendsto f l₂ at_top) :
  Ioi v ⊆ f '' s :=
λ y h, bex_def.1 $ hs.intermediate_value₂_eventually₂ hl₁ hl₂
  hf continuous_on_const (eventually_le_of_tendsto_lt h ht₁) (tendsto_at_top.1 ht₂ y)

lemma is_preconnected.intermediate_value_Iio {s : set X} (hs : is_preconnected s)
  {l₁ l₂ : filter X} [ne_bot l₁] [ne_bot l₂] (hl₁ : l₁ ≤ 𝓟 s) (hl₂ : l₂ ≤ 𝓟 s) {f : X → α}
  (hf : continuous_on f s) {v : α} (ht₁ : tendsto f l₁ at_bot) (ht₂ : tendsto f l₂ (𝓝 v)) :
  Iio v ⊆ f '' s :=
λ y h, bex_def.1 $ hs.intermediate_value₂_eventually₂ hl₁ hl₂
  hf continuous_on_const (tendsto_at_bot.1 ht₁ y) (eventually_ge_of_tendsto_gt h ht₂)

lemma is_preconnected.intermediate_value_Iii {s : set X} (hs : is_preconnected s)
  {l₁ l₂ : filter X} [ne_bot l₁] [ne_bot l₂] (hl₁ : l₁ ≤ 𝓟 s) (hl₂ : l₂ ≤ 𝓟 s) {f : X → α}
  (hf : continuous_on f s) (ht₁ : tendsto f l₁ at_bot) (ht₂ : tendsto f l₂ at_top) :
  univ ⊆ f '' s :=
λ y h, bex_def.1 $ hs.intermediate_value₂_eventually₂ hl₁ hl₂
  hf continuous_on_const (tendsto_at_bot.1 ht₁ y) (tendsto_at_top.1 ht₂ y)

/-- **Intermediate Value Theorem** for continuous functions on connected spaces. -/
lemma intermediate_value_univ [preconnected_space X] (a b : X) {f : X → α} (hf : continuous f) :
  Icc (f a) (f b) ⊆ range f :=
λ x hx, intermediate_value_univ₂ hf continuous_const hx.1 hx.2

/-- **Intermediate Value Theorem** for continuous functions on connected spaces. -/
lemma mem_range_of_exists_le_of_exists_ge [preconnected_space X] {c : α} {f : X → α}
  (hf : continuous f) (h₁ : ∃ a, f a ≤ c) (h₂ : ∃ b, c ≤ f b) :
  c ∈ range f :=
let ⟨a, ha⟩ := h₁, ⟨b, hb⟩ := h₂ in intermediate_value_univ a b hf ⟨ha, hb⟩

/-!
### (Pre)connected sets in a linear order

In this section we prove the following results:

* `is_preconnected.ord_connected`: any preconnected set `s` in a linear order is `ord_connected`,
  i.e. `a ∈ s` and `b ∈ s` imply `Icc a b ⊆ s`;

* `is_preconnected.mem_intervals`: any preconnected set `s` in a conditionally complete linear order
  is one of the intervals `set.Icc`, `set.`Ico`, `set.Ioc`, `set.Ioo`, ``set.Ici`, `set.Iic`,
  `set.Ioi`, `set.Iio`; note that this is false for non-complete orders: e.g., in `ℝ \ {0}`, the set
  of positive numbers cannot be represented as `set.Ioi _`.

-/

/-- If a preconnected set contains endpoints of an interval, then it includes the whole interval. -/
lemma is_preconnected.Icc_subset {s : set α} (hs : is_preconnected s)
  {a b : α} (ha : a ∈ s) (hb : b ∈ s) :
  Icc a b ⊆ s :=
by simpa only [image_id] using hs.intermediate_value ha hb continuous_on_id

lemma is_preconnected.ord_connected {s : set α} (h : is_preconnected s) :
  ord_connected s :=
⟨λ x hx y hy, h.Icc_subset hx hy⟩

/-- If a preconnected set contains endpoints of an interval, then it includes the whole interval. -/
lemma is_connected.Icc_subset {s : set α} (hs : is_connected s)
  {a b : α} (ha : a ∈ s) (hb : b ∈ s) :
  Icc a b ⊆ s :=
hs.2.Icc_subset ha hb

/-- If preconnected set in a linear order space is unbounded below and above, then it is the whole
space. -/
lemma is_preconnected.eq_univ_of_unbounded {s : set α} (hs : is_preconnected s) (hb : ¬bdd_below s)
  (ha : ¬bdd_above s) :
  s = univ :=
begin
  refine eq_univ_of_forall (λ x, _),
  obtain ⟨y, ys, hy⟩ : ∃ y ∈ s, y < x := not_bdd_below_iff.1 hb x,
  obtain ⟨z, zs, hz⟩ : ∃ z ∈ s, x < z := not_bdd_above_iff.1 ha x,
  exact hs.Icc_subset ys zs ⟨le_of_lt hy, le_of_lt hz⟩
end

end

variables {α : Type u} {β : Type v} {γ : Type w}
  [conditionally_complete_linear_order α] [topological_space α] [order_topology α]
  [conditionally_complete_linear_order β] [topological_space β] [order_topology β]
  [nonempty γ]

/-- A bounded connected subset of a conditionally complete linear order includes the open interval
`(Inf s, Sup s)`. -/
lemma is_connected.Ioo_cInf_cSup_subset {s : set α} (hs : is_connected s) (hb : bdd_below s)
  (ha : bdd_above s) :
  Ioo (Inf s) (Sup s) ⊆ s :=
λ x hx, let ⟨y, ys, hy⟩ := (is_glb_lt_iff (is_glb_cInf hs.nonempty hb)).1 hx.1 in
let ⟨z, zs, hz⟩ := (lt_is_lub_iff (is_lub_cSup hs.nonempty ha)).1 hx.2 in
hs.Icc_subset ys zs ⟨le_of_lt hy, le_of_lt hz⟩

lemma eq_Icc_cInf_cSup_of_connected_bdd_closed {s : set α} (hc : is_connected s) (hb : bdd_below s)
  (ha : bdd_above s) (hcl : is_closed s) :
  s = Icc (Inf s) (Sup s) :=
subset.antisymm (subset_Icc_cInf_cSup hb ha) $
  hc.Icc_subset (hcl.cInf_mem hc.nonempty hb) (hcl.cSup_mem hc.nonempty ha)

lemma is_preconnected.Ioi_cInf_subset {s : set α} (hs : is_preconnected s) (hb : bdd_below s)
  (ha : ¬bdd_above s) :
  Ioi (Inf s) ⊆ s :=
begin
  have sne : s.nonempty := @nonempty_of_not_bdd_above α _ s ⟨Inf ∅⟩ ha,
  intros x hx,
  obtain ⟨y, ys, hy⟩ : ∃ y ∈ s, y < x := (is_glb_lt_iff (is_glb_cInf sne hb)).1 hx,
  obtain ⟨z, zs, hz⟩ : ∃ z ∈ s, x < z := not_bdd_above_iff.1 ha x,
  exact hs.Icc_subset ys zs ⟨le_of_lt hy, le_of_lt hz⟩
end

lemma is_preconnected.Iio_cSup_subset {s : set α} (hs : is_preconnected s) (hb : ¬bdd_below s)
  (ha : bdd_above s) :
  Iio (Sup s) ⊆ s :=
@is_preconnected.Ioi_cInf_subset αᵒᵈ _ _ _ s hs ha hb

/-- A preconnected set in a conditionally complete linear order is either one of the intervals
`[Inf s, Sup s]`, `[Inf s, Sup s)`, `(Inf s, Sup s]`, `(Inf s, Sup s)`, `[Inf s, +∞)`,
`(Inf s, +∞)`, `(-∞, Sup s]`, `(-∞, Sup s)`, `(-∞, +∞)`, or `∅`. The converse statement requires
`α` to be densely ordererd. -/
lemma is_preconnected.mem_intervals {s : set α} (hs : is_preconnected s) :
  s ∈ ({Icc (Inf s) (Sup s), Ico (Inf s) (Sup s), Ioc (Inf s) (Sup s), Ioo (Inf s) (Sup s),
    Ici (Inf s), Ioi (Inf s), Iic (Sup s), Iio (Sup s), univ, ∅} : set (set α)) :=
begin
  rcases s.eq_empty_or_nonempty with rfl|hne,
  { apply_rules [or.inr, mem_singleton] },
  have hs' : is_connected s := ⟨hne, hs⟩,
  by_cases hb : bdd_below s; by_cases ha : bdd_above s,
  { rcases mem_Icc_Ico_Ioc_Ioo_of_subset_of_subset (hs'.Ioo_cInf_cSup_subset hb ha)
      (subset_Icc_cInf_cSup hb ha) with hs|hs|hs|hs,
    { exact (or.inl hs) },
    { exact (or.inr $ or.inl hs) },
    { exact (or.inr $ or.inr $ or.inl hs) },
    { exact (or.inr $ or.inr $ or.inr $ or.inl hs) } },
  { refine (or.inr $ or.inr $ or.inr $ or.inr _),
    cases mem_Ici_Ioi_of_subset_of_subset (hs.Ioi_cInf_subset hb ha) (λ x hx, cInf_le hb hx)
      with hs hs,
    { exact or.inl hs },
    { exact or.inr (or.inl hs) } },
  { iterate 6 { apply or.inr },
    cases mem_Iic_Iio_of_subset_of_subset (hs.Iio_cSup_subset hb ha) (λ x hx, le_cSup ha hx)
      with hs hs,
    { exact or.inl hs },
    { exact or.inr (or.inl hs) } },
  { iterate 8 { apply or.inr },
    exact or.inl (hs.eq_univ_of_unbounded hb ha) }
end

/-- A preconnected set is either one of the intervals `Icc`, `Ico`, `Ioc`, `Ioo`, `Ici`, `Ioi`,
`Iic`, `Iio`, or `univ`, or `∅`. The converse statement requires `α` to be densely ordered. Though
one can represent `∅` as `(Inf s, Inf s)`, we include it into the list of possible cases to improve
readability. -/
lemma set_of_is_preconnected_subset_of_ordered :
  {s : set α | is_preconnected s} ⊆
    -- bounded intervals
    (range (uncurry Icc) ∪ range (uncurry Ico) ∪ range (uncurry Ioc) ∪ range (uncurry Ioo)) ∪
    -- unbounded intervals and `univ`
    (range Ici ∪ range Ioi ∪ range Iic ∪ range Iio ∪ {univ, ∅}) :=
begin
  intros s hs,
  rcases hs.mem_intervals with hs|hs|hs|hs|hs|hs|hs|hs|hs|hs,
  { exact (or.inl $ or.inl $ or.inl $ or.inl ⟨(Inf s, Sup s), hs.symm⟩) },
  { exact (or.inl $ or.inl $ or.inl $ or.inr ⟨(Inf s, Sup s), hs.symm⟩) },
  { exact (or.inl $ or.inl $ or.inr ⟨(Inf s, Sup s), hs.symm⟩) },
  { exact (or.inl $ or.inr ⟨(Inf s, Sup s), hs.symm⟩) },
  { exact (or.inr $ or.inl $ or.inl $ or.inl $ or.inl ⟨Inf s, hs.symm⟩) },
  { exact (or.inr $ or.inl $ or.inl $ or.inl $ or.inr ⟨Inf s, hs.symm⟩) },
  { exact (or.inr $ or.inl $ or.inl  $ or.inr ⟨Sup s, hs.symm⟩) },
  { exact (or.inr $ or.inl $  or.inr ⟨Sup s, hs.symm⟩) },
  { exact (or.inr $ or.inr $ or.inl hs) },
  { exact (or.inr $ or.inr $ or.inr hs) }
end

/-!
### Intervals are connected

In this section we prove that a closed interval (hence, any `ord_connected` set) in a dense
conditionally complete linear order is preconnected.
-/

/-- A "continuous induction principle" for a closed interval: if a set `s` meets `[a, b]`
on a closed subset, contains `a`, and the set `s ∩ [a, b)` has no maximal point, then `b ∈ s`. -/
lemma is_closed.mem_of_ge_of_forall_exists_gt {a b : α} {s : set α} (hs : is_closed (s ∩ Icc a b))
  (ha : a ∈ s) (hab : a ≤ b) (hgt : ∀ x ∈ s ∩ Ico a b, (s ∩ Ioc x b).nonempty) :
  b ∈ s :=
begin
  let S := s ∩ Icc a b,
  replace ha : a ∈ S, from ⟨ha, left_mem_Icc.2 hab⟩,
  have Sbd : bdd_above S, from ⟨b, λ z hz, hz.2.2⟩,
  let c := Sup (s ∩ Icc a b),
  have c_mem : c ∈ S, from hs.cSup_mem ⟨_, ha⟩ Sbd,
  have c_le : c ≤ b, from cSup_le ⟨_, ha⟩ (λ x hx, hx.2.2),
  cases eq_or_lt_of_le c_le with hc hc, from hc ▸ c_mem.1,
  exfalso,
  rcases hgt c ⟨c_mem.1, c_mem.2.1, hc⟩ with ⟨x, xs, cx, xb⟩,
  exact not_lt_of_le (le_cSup Sbd ⟨xs, le_trans (le_cSup Sbd ha) (le_of_lt cx), xb⟩) cx
end

/-- A "continuous induction principle" for a closed interval: if a set `s` meets `[a, b]`
on a closed subset, contains `a`, and for any `a ≤ x < y ≤ b`, `x ∈ s`, the set `s ∩ (x, y]`
is not empty, then `[a, b] ⊆ s`. -/
lemma is_closed.Icc_subset_of_forall_exists_gt {a b : α} {s : set α} (hs : is_closed (s ∩ Icc a b))
  (ha : a ∈ s) (hgt : ∀ x ∈ s ∩ Ico a b, ∀ y ∈ Ioi x, (s ∩ Ioc x y).nonempty) :
  Icc a b ⊆ s :=
begin
  assume y hy,
  have : is_closed (s ∩ Icc a y),
  { suffices : s ∩ Icc a y = s ∩ Icc a b ∩ Icc a y,
    { rw this, exact is_closed.inter hs is_closed_Icc },
    rw [inter_assoc],
    congr,
    exact (inter_eq_self_of_subset_right $ Icc_subset_Icc_right hy.2).symm },
  exact is_closed.mem_of_ge_of_forall_exists_gt this ha hy.1
    (λ x hx, hgt x ⟨hx.1, Ico_subset_Ico_right hy.2 hx.2⟩ y hx.2.2)
end

variables [densely_ordered α] {a b : α}

/-- A "continuous induction principle" for a closed interval: if a set `s` meets `[a, b]`
on a closed subset, contains `a`, and for any `x ∈ s ∩ [a, b)` the set `s` includes some open
neighborhood of `x` within `(x, +∞)`, then `[a, b] ⊆ s`. -/
lemma is_closed.Icc_subset_of_forall_mem_nhds_within {a b : α} {s : set α}
  (hs : is_closed (s ∩ Icc a b)) (ha : a ∈ s)
  (hgt : ∀ x ∈ s ∩ Ico a b, s ∈ 𝓝[>] x) :
  Icc a b ⊆ s :=
begin
  apply hs.Icc_subset_of_forall_exists_gt ha,
  rintros x ⟨hxs, hxab⟩ y hyxb,
  have : s ∩ Ioc x y ∈ 𝓝[>] x,
    from inter_mem (hgt x ⟨hxs, hxab⟩) (Ioc_mem_nhds_within_Ioi ⟨le_rfl, hyxb⟩),
  exact (nhds_within_Ioi_self_ne_bot' ⟨b, hxab.2⟩).nonempty_of_mem this
end

lemma is_preconnected_Icc_aux (x y : α) (s t : set α) (hxy : x ≤ y)
  (hs : is_closed s) (ht : is_closed t) (hab : Icc a b ⊆ s ∪ t)
  (hx : x ∈ Icc a b ∩ s) (hy : y ∈ Icc a b ∩ t) : (Icc a b ∩ (s ∩ t)).nonempty :=
begin
  have xyab : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1.1 hy.1.2,
  by_contradiction hst,
  suffices : Icc x y ⊆ s,
    from hst ⟨y, xyab $ right_mem_Icc.2 hxy, this $ right_mem_Icc.2 hxy, hy.2⟩,
  apply (is_closed.inter hs is_closed_Icc).Icc_subset_of_forall_mem_nhds_within hx.2,
  rintros z ⟨zs, hz⟩,
  have zt : z ∈ tᶜ, from λ zt, hst ⟨z, xyab $ Ico_subset_Icc_self hz, zs, zt⟩,
  have : tᶜ ∩ Ioc z y ∈ 𝓝[>] z,
  { rw [← nhds_within_Ioc_eq_nhds_within_Ioi hz.2],
    exact mem_nhds_within.2 ⟨tᶜ, ht.is_open_compl, zt, subset.refl _⟩},
  apply mem_of_superset this,
  have : Ioc z y ⊆ s ∪ t, from λ w hw, hab (xyab ⟨le_trans hz.1 (le_of_lt hw.1), hw.2⟩),
  exact λ w ⟨wt, wzy⟩, (this wzy).elim id (λ h, (wt h).elim)
end

/-- A closed interval in a densely ordered conditionally complete linear order is preconnected. -/
lemma is_preconnected_Icc : is_preconnected (Icc a b) :=
is_preconnected_closed_iff.2
begin
  rintros s t hs ht hab ⟨x, hx⟩ ⟨y, hy⟩,
  -- This used to use `wlog`, but it was causing timeouts.
  cases le_total x y,
  { exact is_preconnected_Icc_aux x y s t h hs ht hab hx hy, },
  { rw inter_comm s t,
    rw union_comm s t at hab,
    exact is_preconnected_Icc_aux y x t s h ht hs hab hy hx, },
end

lemma is_preconnected_uIcc : is_preconnected (uIcc a b) := is_preconnected_Icc

lemma set.ord_connected.is_preconnected {s : set α} (h : s.ord_connected) :
  is_preconnected s :=
is_preconnected_of_forall_pair $ λ x hx y hy, ⟨uIcc x y, h.uIcc_subset hx hy,
  left_mem_uIcc, right_mem_uIcc, is_preconnected_uIcc⟩

lemma is_preconnected_iff_ord_connected {s : set α} :
  is_preconnected s ↔ ord_connected s :=
⟨is_preconnected.ord_connected, set.ord_connected.is_preconnected⟩

lemma is_preconnected_Ici : is_preconnected (Ici a) := ord_connected_Ici.is_preconnected
lemma is_preconnected_Iic : is_preconnected (Iic a) := ord_connected_Iic.is_preconnected
lemma is_preconnected_Iio : is_preconnected (Iio a) := ord_connected_Iio.is_preconnected
lemma is_preconnected_Ioi : is_preconnected (Ioi a) := ord_connected_Ioi.is_preconnected
lemma is_preconnected_Ioo : is_preconnected (Ioo a b) := ord_connected_Ioo.is_preconnected
lemma is_preconnected_Ioc : is_preconnected (Ioc a b) := ord_connected_Ioc.is_preconnected
lemma is_preconnected_Ico : is_preconnected (Ico a b) := ord_connected_Ico.is_preconnected

lemma is_connected_Ici : is_connected (Ici a) := ⟨nonempty_Ici, is_preconnected_Ici⟩

lemma is_connected_Iic : is_connected (Iic a) := ⟨nonempty_Iic, is_preconnected_Iic⟩

lemma is_connected_Ioi [no_max_order α] : is_connected (Ioi a) :=
⟨nonempty_Ioi, is_preconnected_Ioi⟩

lemma is_connected_Iio [no_min_order α] : is_connected (Iio a) :=
⟨nonempty_Iio, is_preconnected_Iio⟩

lemma is_connected_Icc (h : a ≤ b) : is_connected (Icc a b) :=
⟨nonempty_Icc.2 h, is_preconnected_Icc⟩

lemma is_connected_Ioo (h : a < b) : is_connected (Ioo a b) :=
⟨nonempty_Ioo.2 h, is_preconnected_Ioo⟩

lemma is_connected_Ioc (h : a < b) : is_connected (Ioc a b) :=
⟨nonempty_Ioc.2 h, is_preconnected_Ioc⟩

lemma is_connected_Ico (h : a < b) : is_connected (Ico a b) :=
⟨nonempty_Ico.2 h, is_preconnected_Ico⟩

@[priority 100]
instance ordered_connected_space : preconnected_space α :=
⟨ord_connected_univ.is_preconnected⟩

/-- In a dense conditionally complete linear order, the set of preconnected sets is exactly
the set of the intervals `Icc`, `Ico`, `Ioc`, `Ioo`, `Ici`, `Ioi`, `Iic`, `Iio`, `(-∞, +∞)`,
or `∅`. Though one can represent `∅` as `(Inf s, Inf s)`, we include it into the list of
possible cases to improve readability. -/
lemma set_of_is_preconnected_eq_of_ordered :
  {s : set α | is_preconnected s} =
    -- bounded intervals
    (range (uncurry Icc) ∪ range (uncurry Ico) ∪ range (uncurry Ioc) ∪ range (uncurry Ioo)) ∪
    -- unbounded intervals and `univ`
    (range Ici ∪ range Ioi ∪ range Iic ∪ range Iio ∪ {univ, ∅}) :=
begin
  refine subset.antisymm set_of_is_preconnected_subset_of_ordered _,
  simp only [subset_def, -mem_range, forall_range_iff, uncurry, or_imp_distrib, forall_and_distrib,
    mem_union, mem_set_of_eq, insert_eq, mem_singleton_iff, forall_eq, forall_true_iff, and_true,
    is_preconnected_Icc, is_preconnected_Ico, is_preconnected_Ioc,
    is_preconnected_Ioo, is_preconnected_Ioi, is_preconnected_Iio, is_preconnected_Ici,
    is_preconnected_Iic, is_preconnected_univ, is_preconnected_empty],
end

/-!
### Intermediate Value Theorem on an interval

In this section we prove several versions of the Intermediate Value Theorem for a function
continuous on an interval.
-/

variables {δ : Type*} [linear_order δ] [topological_space δ] [order_closed_topology δ]

/-- **Intermediate Value Theorem** for continuous functions on closed intervals, case
`f a ≤ t ≤ f b`.-/
lemma intermediate_value_Icc {a b : α} (hab : a ≤ b) {f : α → δ} (hf : continuous_on f (Icc a b)) :
  Icc (f a) (f b) ⊆ f '' (Icc a b) :=
is_preconnected_Icc.intermediate_value (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) hf

/-- **Intermediate Value Theorem** for continuous functions on closed intervals, case
`f a ≥ t ≥ f b`.-/
lemma intermediate_value_Icc' {a b : α} (hab : a ≤ b) {f : α → δ} (hf : continuous_on f (Icc a b)) :
  Icc (f b) (f a) ⊆ f '' (Icc a b) :=
is_preconnected_Icc.intermediate_value (right_mem_Icc.2 hab) (left_mem_Icc.2 hab) hf

/-- **Intermediate Value Theorem** for continuous functions on closed intervals, unordered case. -/
lemma intermediate_value_uIcc {a b : α} {f : α → δ} (hf : continuous_on f (uIcc a b)) :
  uIcc (f a) (f b) ⊆ f '' uIcc a b :=
by cases le_total (f a) (f b); simp [*, is_preconnected_uIcc.intermediate_value]

lemma intermediate_value_Ico {a b : α} (hab : a ≤ b) {f : α → δ} (hf : continuous_on f (Icc a b)) :
  Ico (f a) (f b) ⊆ f '' (Ico a b) :=
or.elim (eq_or_lt_of_le hab) (λ he y h, absurd h.2 (not_lt_of_le (he ▸ h.1)))
(λ hlt, @is_preconnected.intermediate_value_Ico _ _ _ _ _ _ _ (is_preconnected_Ico)
  _ _ ⟨refl a, hlt⟩ (right_nhds_within_Ico_ne_bot hlt) inf_le_right _ (hf.mono Ico_subset_Icc_self)
  _ ((hf.continuous_within_at ⟨hab, refl b⟩).mono Ico_subset_Icc_self))

lemma intermediate_value_Ico' {a b : α} (hab : a ≤ b) {f : α → δ} (hf : continuous_on f (Icc a b)) :
  Ioc (f b) (f a) ⊆ f '' (Ico a b) :=
or.elim (eq_or_lt_of_le hab) (λ he y h, absurd h.1 (not_lt_of_le (he ▸ h.2)))
(λ hlt, @is_preconnected.intermediate_value_Ioc _ _ _ _ _ _ _ (is_preconnected_Ico)
  _ _ ⟨refl a, hlt⟩ (right_nhds_within_Ico_ne_bot hlt) inf_le_right _ (hf.mono Ico_subset_Icc_self)
  _ ((hf.continuous_within_at ⟨hab, refl b⟩).mono Ico_subset_Icc_self))

lemma intermediate_value_Ioc {a b : α} (hab : a ≤ b) {f : α → δ} (hf : continuous_on f (Icc a b)) :
  Ioc (f a) (f b) ⊆ f '' (Ioc a b) :=
or.elim (eq_or_lt_of_le hab) (λ he y h, absurd h.2 (not_le_of_lt (he ▸ h.1)))
(λ hlt, @is_preconnected.intermediate_value_Ioc _ _ _ _ _ _ _ (is_preconnected_Ioc)
  _ _ ⟨hlt, refl b⟩ (left_nhds_within_Ioc_ne_bot hlt) inf_le_right _ (hf.mono Ioc_subset_Icc_self)
  _ ((hf.continuous_within_at ⟨refl a, hab⟩).mono Ioc_subset_Icc_self))

lemma intermediate_value_Ioc' {a b : α} (hab : a ≤ b) {f : α → δ} (hf : continuous_on f (Icc a b)) :
  Ico (f b) (f a) ⊆ f '' (Ioc a b) :=
or.elim (eq_or_lt_of_le hab) (λ he y h, absurd h.1 (not_le_of_lt (he ▸ h.2)))
(λ hlt, @is_preconnected.intermediate_value_Ico _ _ _ _ _ _ _ (is_preconnected_Ioc)
  _ _ ⟨hlt, refl b⟩ (left_nhds_within_Ioc_ne_bot hlt) inf_le_right _ (hf.mono Ioc_subset_Icc_self)
  _ ((hf.continuous_within_at ⟨refl a, hab⟩).mono Ioc_subset_Icc_self))

lemma intermediate_value_Ioo {a b : α} (hab : a ≤ b) {f : α → δ} (hf : continuous_on f (Icc a b)) :
  Ioo (f a) (f b) ⊆ f '' (Ioo a b) :=
or.elim (eq_or_lt_of_le hab) (λ he y h, absurd h.2 (not_lt_of_lt (he ▸ h.1)))
(λ hlt, @is_preconnected.intermediate_value_Ioo _ _ _ _ _ _ _ (is_preconnected_Ioo)
  _ _ (left_nhds_within_Ioo_ne_bot hlt) (right_nhds_within_Ioo_ne_bot hlt)
  inf_le_right inf_le_right _ (hf.mono Ioo_subset_Icc_self)
  _ _ ((hf.continuous_within_at ⟨refl a, hab⟩).mono Ioo_subset_Icc_self)
  ((hf.continuous_within_at ⟨hab, refl b⟩).mono Ioo_subset_Icc_self))

lemma intermediate_value_Ioo' {a b : α} (hab : a ≤ b) {f : α → δ} (hf : continuous_on f (Icc a b)) :
  Ioo (f b) (f a) ⊆ f '' (Ioo a b) :=
or.elim (eq_or_lt_of_le hab) (λ he y h, absurd h.1 (not_lt_of_lt (he ▸ h.2)))
(λ hlt, @is_preconnected.intermediate_value_Ioo _ _ _ _ _ _ _ (is_preconnected_Ioo)
  _ _ (right_nhds_within_Ioo_ne_bot hlt) (left_nhds_within_Ioo_ne_bot hlt)
  inf_le_right inf_le_right _ (hf.mono Ioo_subset_Icc_self)
  _ _ ((hf.continuous_within_at ⟨hab, refl b⟩).mono Ioo_subset_Icc_self)
  ((hf.continuous_within_at ⟨refl a, hab⟩).mono Ioo_subset_Icc_self))

/-- **Intermediate value theorem**: if `f` is continuous on an order-connected set `s` and `a`,
`b` are two points of this set, then `f` sends `s` to a superset of `Icc (f x) (f y)`. -/
lemma continuous_on.surj_on_Icc {s : set α} [hs : ord_connected s] {f : α → δ}
  (hf : continuous_on f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) :
  surj_on f s (Icc (f a) (f b)) :=
hs.is_preconnected.intermediate_value ha hb hf

/-- **Intermediate value theorem**: if `f` is continuous on an order-connected set `s` and `a`,
`b` are two points of this set, then `f` sends `s` to a superset of `[f x, f y]`. -/
lemma continuous_on.surj_on_uIcc {s : set α} [hs : ord_connected s] {f : α → δ}
  (hf : continuous_on f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) :
  surj_on f s (uIcc (f a) (f b)) :=
by cases le_total (f a) (f b) with hab hab; simp [hf.surj_on_Icc, *]

/-- A continuous function which tendsto `at_top` `at_top` and to `at_bot` `at_bot` is surjective. -/
lemma continuous.surjective {f : α → δ} (hf : continuous f) (h_top : tendsto f at_top at_top)
  (h_bot : tendsto f at_bot at_bot) :
  function.surjective f :=
λ p, mem_range_of_exists_le_of_exists_ge hf
  (h_bot.eventually (eventually_le_at_bot p)).exists
  (h_top.eventually (eventually_ge_at_top p)).exists

/-- A continuous function which tendsto `at_bot` `at_top` and to `at_top` `at_bot` is surjective. -/
lemma continuous.surjective' {f : α → δ} (hf : continuous f) (h_top : tendsto f at_bot at_top)
  (h_bot : tendsto f at_top at_bot) :
  function.surjective f :=
@continuous.surjective αᵒᵈ _ _ _ _ _ _ _ _ _ hf h_top h_bot

/-- If a function `f : α → β` is continuous on a nonempty interval `s`, its restriction to `s`
tends to `at_bot : filter β` along `at_bot : filter ↥s` and tends to `at_top : filter β` along
`at_top : filter ↥s`, then the restriction of `f` to `s` is surjective. We formulate the
conclusion as `surj_on f s univ`. -/
lemma continuous_on.surj_on_of_tendsto {f : α → δ} {s : set α} [ord_connected s]
  (hs : s.nonempty) (hf : continuous_on f s) (hbot : tendsto (λ x : s, f x) at_bot at_bot)
  (htop : tendsto (λ x : s, f x) at_top at_top) :
  surj_on f s univ :=
by haveI := classical.inhabited_of_nonempty hs.to_subtype;
  exact (surj_on_iff_surjective.2 $
    (continuous_on_iff_continuous_restrict.1 hf).surjective htop hbot)

/-- If a function `f : α → β` is continuous on a nonempty interval `s`, its restriction to `s`
tends to `at_top : filter β` along `at_bot : filter ↥s` and tends to `at_bot : filter β` along
`at_top : filter ↥s`, then the restriction of `f` to `s` is surjective. We formulate the
conclusion as `surj_on f s univ`. -/
lemma continuous_on.surj_on_of_tendsto' {f : α → δ} {s : set α} [ord_connected s]
  (hs : s.nonempty) (hf : continuous_on f s) (hbot : tendsto (λ x : s, f x) at_bot at_top)
  (htop : tendsto (λ x : s, f x) at_top at_bot) :
  surj_on f s univ :=
@continuous_on.surj_on_of_tendsto α _ _ _ _ δᵒᵈ _ _ _ _ _ _ hs hf hbot htop
