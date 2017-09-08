/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Theory of topological monoids, groups and rings.
-/

import topology.topological_space topology.continuity topology.uniform_space
  algebra.big_operators
open lattice filter topological_space
local attribute [instance] classical.decidable_inhabited classical.prop_decidable

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

section linear_order
variables [decidable_linear_order α] {a b c: α}

lemma max_lt_iff : max a b < c ↔ (a < c ∧ b < c) :=
⟨assume h, ⟨lt_of_le_of_lt (le_max_left _ _) h, lt_of_le_of_lt (le_max_right _ _) h⟩,
  assume ⟨h₁, h₂⟩, max_lt h₁ h₂⟩

lemma lt_min_iff : a < min b c ↔ (a < b ∧ a < c) :=
⟨assume h, ⟨lt_of_lt_of_le h (min_le_left _ _), lt_of_lt_of_le h (min_le_right _ _)⟩,
  assume ⟨h₁, h₂⟩, lt_min h₁ h₂⟩

end linear_order

section complete_lattice

lemma binfi_inf {α : Type*} {ι : Sort*} {p : ι → Prop} [complete_lattice α]
  {f : Πi, p i → α} {a : α} {i : ι} (hi : p i) :
  (⨅i (h : p i), f i h) ⊓ a = (⨅ i (h : p i), f i h ⊓ a) :=
le_antisymm
  (le_infi $ assume i, le_infi $ assume hi,
    le_inf (inf_le_left_of_le $ infi_le_of_le i $ infi_le _ _) inf_le_right)
  (le_inf (infi_le_infi $ assume i, infi_le_infi $ assume hi, inf_le_left)
     (infi_le_of_le i $ infi_le_of_le hi $ inf_le_right))

end complete_lattice

lemma dense_or_discrete [linear_order α] {a₁ a₂ : α} (h : a₁ < a₂) :
  (∃a, a₁ < a ∧ a < a₂) ∨ ((∀a>a₁, a ≥ a₂) ∧ (∀a<a₂, a ≤ a₁)) :=
or_iff_not_imp_left.2 $ assume h,
  ⟨assume a ha₁, le_of_not_gt $ assume ha₂, h ⟨a, ha₁, ha₂⟩,
    assume a ha₂, le_of_not_gt $ assume ha₁, h ⟨a, ha₁, ha₂⟩⟩

section topological_add_monoid

class topological_add_monoid (α : Type u) [topological_space α] [add_monoid α] : Prop :=
(continuous_add : continuous (λp:α×α, p.1 + p.2))

section
variables [topological_space α] [add_monoid α]

lemma continuous_add' [topological_add_monoid α] : continuous (λp:α×α, p.1 + p.2) :=
topological_add_monoid.continuous_add α

lemma continuous_add [topological_add_monoid α] [topological_space β] {f : β → α} {g : β → α}
  (hf : continuous f) (hg : continuous g) : continuous (λx, f x + g x) :=
continuous_compose (continuous_prod_mk hf hg) continuous_add'

lemma tendsto_add' [topological_add_monoid α] {a b : α} :
  tendsto (λp:α×α, p.fst + p.snd) (nhds (a, b)) (nhds (a + b)) :=
continuous_iff_tendsto.mp (topological_add_monoid.continuous_add α) (a, b)

lemma tendsto_add [topological_add_monoid α] {f : β → α} {g : β → α} {x : filter β} {a b : α}
  (hf : tendsto f x (nhds a)) (hg : tendsto g x (nhds b)) : tendsto (λx, f x + g x) x (nhds (a + b)) :=
tendsto_compose (tendsto_prod_mk hf hg) (by rw [←nhds_prod_eq]; exact tendsto_add')
end

section
variables [topological_space α] [add_comm_monoid α]

lemma tendsto_sum [topological_add_monoid α] {f : γ → β → α} {x : filter β} {a : γ → α} {s : finset γ} :
  (∀c∈s, tendsto (f c) x (nhds (a c))) → tendsto (λb, s.sum (λc, f c b)) x (nhds (s.sum a)) :=
s.induction_on (by simp; exact tendsto_const_nhds) $ assume b s,
  by simp [or_imp_distrib, forall_and_distrib, tendsto_add] {contextual := tt}

end

end topological_add_monoid

section topological_add_group
class topological_add_group (α : Type u) [topological_space α] [add_group α]
  extends topological_add_monoid α : Prop :=
(continuous_neg : continuous (λa:α, -a))

variables [topological_space α] [add_group α]

lemma continuous_neg' [topological_add_group α] : continuous (λx:α, - x) :=
topological_add_group.continuous_neg α

lemma continuous_neg [topological_add_group α] [topological_space β] {f : β → α}
  (hf : continuous f) : continuous (λx, - f x) :=
continuous_compose hf continuous_neg'

lemma tendsto_neg [topological_add_group α] {f : β → α} {x : filter β} {a : α}
  (hf : tendsto f x (nhds a)) : tendsto (λx, - f x) x (nhds (- a)) :=
tendsto_compose hf (continuous_iff_tendsto.mp (topological_add_group.continuous_neg α) a)

lemma continuous_sub [topological_add_group α] [topological_space β] {f : β → α} {g : β → α}
  (hf : continuous f) (hg : continuous g) : continuous (λx, f x - g x) :=
by simp; exact continuous_add hf (continuous_neg hg)

lemma tendsto_sub [topological_add_group α] {f : β → α} {g : β → α} {x : filter β} {a b : α}
  (hf : tendsto f x (nhds a)) (hg : tendsto g x (nhds b)) : tendsto (λx, f x - g x) x (nhds (a - b)) :=
by simp; exact tendsto_add hf (tendsto_neg hg)

end topological_add_group

section uniform_add_group
class uniform_add_group (α : Type u) [uniform_space α] [add_group α] : Prop :=
(uniform_continuous_sub : uniform_continuous (λp:α×α, p.1 - p.2))

variables [uniform_space α] [add_group α]

lemma uniform_continuous_sub' [uniform_add_group α] : uniform_continuous (λp:α×α, p.1 - p.2) :=
uniform_add_group.uniform_continuous_sub α

lemma uniform_continuous_sub [uniform_add_group α] [uniform_space β] {f : β → α} {g : β → α}
  (hf : uniform_continuous f) (hg : uniform_continuous g) : uniform_continuous (λx, f x - g x) :=
uniform_continuous_compose (uniform_continuous_prod_mk hf hg) uniform_continuous_sub'

lemma uniform_continuous_neg [uniform_add_group α] [uniform_space β] {f : β → α}
  (hf : uniform_continuous f) : uniform_continuous (λx, - f x) :=
have uniform_continuous (λx, 0 - f x),
  from uniform_continuous_sub uniform_continuous_const hf,
by simp * at *

lemma uniform_continuous_neg' [uniform_add_group α] : uniform_continuous (λx:α, - x) :=
uniform_continuous_neg uniform_continuous_id

lemma uniform_continuous_add [uniform_add_group α] [uniform_space β] {f : β → α} {g : β → α}
  (hf : uniform_continuous f) (hg : uniform_continuous g) : uniform_continuous (λx, f x + g x) :=
have uniform_continuous (λx, f x - - g x),
  from uniform_continuous_sub hf $ uniform_continuous_neg hg,
by simp * at *

lemma uniform_continuous_add' [uniform_add_group α] : uniform_continuous (λp:α×α, p.1 + p.2) :=
uniform_continuous_add uniform_continuous_fst uniform_continuous_snd

instance uniform_add_group.to_topological_add_group [uniform_add_group α] : topological_add_group α :=
{ continuous_add := continuous_of_uniform uniform_continuous_add',
  continuous_neg := continuous_of_uniform uniform_continuous_neg' }

end uniform_add_group

section topological_semiring
class topological_semiring (α : Type u) [topological_space α] [semiring α]
  extends topological_add_monoid α : Prop :=
(continuous_mul : continuous (λp:α×α, p.1 * p.2))

variables [topological_space α] [semiring α]

lemma continuous_mul [topological_semiring α] [topological_space β] {f : β → α} {g : β → α}
  (hf : continuous f) (hg : continuous g) : continuous (λx, f x * g x) :=
continuous_compose (continuous_prod_mk hf hg) (topological_semiring.continuous_mul α)

lemma tendsto_mul [topological_semiring α] {f : β → α} {g : β → α} {x : filter β} {a b : α}
  (hf : tendsto f x (nhds a)) (hg : tendsto g x (nhds b)) : tendsto (λx, f x * g x) x (nhds (a * b)) :=
have tendsto (λp:α×α, p.fst * p.snd) (nhds (a, b)) (nhds (a * b)),
  from continuous_iff_tendsto.mp (topological_semiring.continuous_mul α) (a, b),
tendsto_compose (tendsto_prod_mk hf hg) (by rw [nhds_prod_eq] at this; exact this)

end topological_semiring

class topological_ring (α : Type u) [topological_space α] [ring α]
  extends topological_add_monoid α : Prop :=
(continuous_mul : continuous (λp:α×α, p.1 * p.2))
(continuous_neg : continuous (λa:α, -a))

instance topological_ring.to_topological_semiring
  [topological_space α] [ring α] [t : topological_ring α] : topological_semiring α :=
{ t.to_topological_add_monoid with continuous_mul := t.continuous_mul }

instance topological_ring.to_topological_add_group
  [topological_space α] [ring α] [t : topological_ring α] : topological_add_group α :=
{ t.to_topological_add_monoid with continuous_neg := t.continuous_neg }

/- (Partially) ordered topology
Also called: partially ordered spaces (pospaces).

Usually ordered topology is used for a topology on linear ordered spaces, where the open intervals
are open sets. This is a generalization as for each linear order where open interals are open sets,
the order relation is closed. -/
class ordered_topology (α : Type*) [t : topological_space α] [partial_order α] : Prop :=
(is_closed_le' : is_closed (λp:α×α, p.1 ≤ p.2))

section ordered_topology

section partial_order
variables [topological_space α] [partial_order α] [t : ordered_topology α]
include t

lemma is_closed_le [topological_space β] {f g : β → α} (hf : continuous f) (hg : continuous g) :
  is_closed {b | f b ≤ g b} :=
continuous_iff_is_closed.mp (continuous_prod_mk hf hg) _ t.is_closed_le'

lemma is_closed_le' {a : α} : is_closed {b | b ≤ a} :=
is_closed_le continuous_id continuous_const

lemma is_closed_ge' {a : α} : is_closed {b | a ≤ b} :=
is_closed_le continuous_const continuous_id

lemma le_of_tendsto [topological_space β] {f g : β → α} {b : filter β} {a₁ a₂ : α} (hb : b ≠ ⊥)
  (hf : tendsto f b (nhds a₁)) (hg : tendsto g b (nhds a₂)) (h : {b | f b ≤ g b} ∈ b.sets) :
  a₁ ≤ a₂ :=
have tendsto (λb, (f b, g b)) b (nhds (a₁, a₂)),
  by rw [nhds_prod_eq]; exact tendsto_prod_mk hf hg,
show (a₁, a₂) ∈ {p:α×α | p.1 ≤ p.2},
  from mem_of_closed_of_tendsto hb this t.is_closed_le' h

private lemma is_closed_eq : is_closed {p : α × α | p.1 = p.2 } :=
by simp [le_antisymm_iff];
   exact is_closed_inter t.is_closed_le' (is_closed_le continuous_snd continuous_fst)

instance ordered_topology.to_t2_space : t2_space α :=
{ t2 :=
  have is_open {p : α × α | p.1 ≠ p.2 }, from is_closed_eq,
  assume a b h,
  let ⟨u, v, hu, hv, ha, hb, h⟩ := is_open_prod_iff.mp this a b h in
  ⟨u, v, hu, hv, ha, hb,
    set.eq_empty_of_forall_not_mem $ assume a ⟨h₁, h₂⟩,
    have a ≠ a, from @h (a, a) ⟨h₁, h₂⟩,
    this rfl⟩ }

end partial_order

section linear_order
variables [topological_space α] [linear_order α] [t : ordered_topology α]
include t

lemma is_open_lt [topological_space β] {f g : β → α} (hf : continuous f) (hg : continuous g) :
  is_open {b | f b < g b} :=
by simp [lt_iff_not_ge]; exact is_closed_le hg hf

end linear_order

end ordered_topology

/-- Topologies generated by the open intervals.
This is restricted to linear orders. Only then it is guaranteed that they are also a ordered
topology.
-/
class orderable_topology (α : Type*) [t : topological_space α] [partial_order α] : Prop :=
(topology_eq_generate_intervals :
  t = generate_from {s | ∃a, s = {b : α | a < b} ∨ s = {b : α | b < a}})

section orderable_topology

section partial_order
variables [topological_space α] [partial_order α] [t : orderable_topology α]
include t

lemma is_open_iff_generate_intervals {s : set α} :
  is_open s ↔ generate_open {s | ∃a, s = {b : α | a < b} ∨ s = {b : α | b < a}} s :=
by rw [t.topology_eq_generate_intervals]; refl

lemma is_open_lt' (a : α) : is_open {b:α | a < b} :=
by rw [@is_open_iff_generate_intervals α _ _ t]; exact generate_open.basic _ ⟨a, or.inl rfl⟩

lemma is_open_gt' (a : α) : is_open {b:α | b < a} :=
by rw [@is_open_iff_generate_intervals α _ _ t]; exact generate_open.basic _ ⟨a, or.inr rfl⟩

lemma nhds_eq_orderable {a : α} :
  nhds a = (⨅b<a, principal {c | b < c}) ⊓ (⨅b>a, principal {c | c < b}) :=
by rw [t.topology_eq_generate_intervals, nhds_generate_from];
from le_antisymm
  (le_inf
    (le_infi $ assume b, le_infi $ assume hb,
      infi_le_of_le {c : α | b < c} $ infi_le _ ⟨hb, b, or.inl rfl⟩)
    (le_infi $ assume b, le_infi $ assume hb,
      infi_le_of_le {c : α | c < b} $ infi_le _ ⟨hb, b, or.inr rfl⟩))
  (le_infi $ assume s, le_infi $ assume ⟨ha, b, hs⟩,
    match s, ha, hs with
    | _, h, (or.inl rfl) := inf_le_left_of_le $ infi_le_of_le b $ infi_le _ h
    | _, h, (or.inr rfl) := inf_le_right_of_le $ infi_le_of_le b $ infi_le _ h
    end)

lemma tendsto_orderable {f : β → α} {a : α} {x : filter β}
  (h₁ : ∀a'<a, {b | a' < f b } ∈ x.sets) (h₂ : ∀a'>a, {b | a' > f b } ∈ x.sets) :
  tendsto f x (nhds a) :=
by rw [@nhds_eq_orderable α _ _];
from tendsto_inf
  (tendsto_infi $ assume b, tendsto_infi $ assume hb, tendsto_principal $ h₁ b hb)
  (tendsto_infi $ assume b, tendsto_infi $ assume hb, tendsto_principal $ h₂ b hb)

lemma nhds_orderable_unbounded {a : α} (hu : ∃u, a < u) (hl : ∃l, l < a) :
  nhds a = (⨅l (h₂ : l < a) u (h₂ : a < u), principal {x | l < x ∧ x < u }) :=
let ⟨u, hu⟩ := hu, ⟨l, hl⟩ := hl in
calc nhds a = (⨅b<a, principal {c | b < c}) ⊓ (⨅b>a, principal {c | c < b}) : nhds_eq_orderable
  ... = (⨅b<a, principal {c | b < c} ⊓ (⨅b>a, principal {c | c < b})) :
    binfi_inf hl
  ... = (⨅l<a, (⨅u>a, principal {c | c < u} ⊓ principal {c | l < c})) :
    begin
      congr, apply funext, intro x,
      congr, apply funext, intro hx,
      rw [inf_comm],
      apply binfi_inf hu
    end
  ... = _ : by simp; refl

lemma tendsto_orderable_unbounded {f : β → α} {a : α} {x : filter β}
  (hu : ∃u, a < u) (hl : ∃l, l < a) (h : ∀l u, l < a → a < u → {b | l < f b ∧ f b < u } ∈ x.sets) :
  tendsto f x (nhds a) :=
by rw [nhds_orderable_unbounded hu hl];
from (tendsto_infi $ assume l, tendsto_infi $ assume hl,
  tendsto_infi $ assume u, tendsto_infi $ assume hu, tendsto_principal $ h l u hl hu)

end partial_order

lemma nhds_top_orderable [topological_space α] [order_top α] [orderable_topology α] :
  nhds (⊤:α) = (⨅l (h₂ : l < ⊤), principal {x | l < x}) :=
by rw [@nhds_eq_orderable α _ _]; simp [(>)]

lemma nhds_bot_orderable [topological_space α] [order_bot α] [orderable_topology α] :
  nhds (⊥:α) = (⨅l (h₂ : ⊥ < l), principal {x | x < l}) :=
by rw [@nhds_eq_orderable α _ _]; simp

section linear_order

variables [topological_space α] [decidable_linear_order α] [t : orderable_topology α]
include t

lemma mem_nhds_lattice_unbounded {a : α} {s : set α} (hu : ∃u, a < u) (hl : ∃l, l < a) :
  s ∈ (nhds a).sets ↔ (∃l u, l < a ∧ a < u ∧ ∀b, l < b → b < u → b ∈ s) :=
let ⟨l, hl'⟩ := hl, ⟨u, hu'⟩ := hu in
have nhds a = (⨅p : {l // l < a} × {u // a < u}, principal {x | p.1.val < x ∧ x < p.2.val }),
  by simp [nhds_orderable_unbounded hu hl, infi_subtype, infi_prod],
iff.intro
  (assume hs, by rw [this] at hs; from infi_sets_induct hs
    begin simp; exact ⟨l, u, hu', hl'⟩ end
    begin
      intro p, cases p with p₁ p₂, cases p₁ with l hl, cases p₂ with u hu,
      simp [set.subset_def],
      exact assume s₁ s₂ hs₁ l' u' hu' hl' hs₂,
        ⟨max l l', min u u', by simp [*, lt_min_iff, max_lt_iff] {contextual := tt}⟩
    end
    (assume s₁ s₂ h ⟨l, u, h₁, h₂, h₃⟩, ⟨l, u, h₁, h₂, assume b hu hl, h $ h₃ _ hu hl⟩))
  (assume ⟨l, u, hl, hu, h⟩,
    by rw [this]; exact mem_infi_sets ⟨⟨l, hl⟩, ⟨u, hu⟩⟩ (assume b ⟨h₁, h₂⟩, h b h₁ h₂))

lemma order_separated {a₁ a₂ : α} (h : a₁ < a₂) :
  ∃u v : set α, is_open u ∧ is_open v ∧ a₁ ∈ u ∧ a₂ ∈ v ∧ (∀b₁∈u, ∀b₂∈v, b₁ < b₂) :=
match dense_or_discrete h with
| or.inl ⟨a, ha₁, ha₂⟩ := ⟨{a' | a' < a}, {a' | a < a'}, is_open_gt' a, is_open_lt' a, ha₁, ha₂,
    assume b₁ h₁ b₂ h₂, lt_trans h₁ h₂⟩
| or.inr ⟨h₁, h₂⟩ := ⟨{a | a < a₂}, {a | a₁ < a}, is_open_gt' a₂, is_open_lt' a₁, h, h,
    assume b₁ hb₁ b₂ hb₂,
    calc b₁ ≤ a₁ : h₂ _ hb₁
      ... < a₂ : h
      ... ≤ b₂ : h₁ _ hb₂⟩
end

instance orderable_topology.to_ordered_topology : ordered_topology α :=
{ is_closed_le' :=
    is_open_prod_iff.mpr $ assume a₁ a₂ (h : ¬ a₁ ≤ a₂),
      have h : a₂ < a₁, from lt_of_not_ge h,
      let ⟨u, v, hu, hv, ha₁, ha₂, h⟩ := order_separated h in
      ⟨v, u, hv, hu, ha₂, ha₁, assume ⟨b₁, b₂⟩ ⟨h₁, h₂⟩, not_le_of_gt $ h b₂ h₂ b₁ h₁⟩ }

end linear_order

end orderable_topology
