/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Theory of topological monoids, groups and rings.
-/

import algebra.big_operators
  analysis.topology.topological_space analysis.topology.continuity analysis.topology.uniform_space

open classical set lattice filter topological_space
local attribute [instance] classical.prop_decidable

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

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
finset.induction_on s (by simp; exact tendsto_const_nhds) $ assume b s,
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

lemma continuous_sub' [topological_add_group α] : continuous (λp:α×α, p.1 - p.2) :=
continuous_sub continuous_fst continuous_snd

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
  [topological_space α] [ring α] [t : topological_ring α] : topological_semiring α := {..t}

instance topological_ring.to_topological_add_group
  [topological_space α] [ring α] [t : topological_ring α] : topological_add_group α := {..t}

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

lemma le_of_tendsto {f g : β → α} {b : filter β} {a₁ a₂ : α} (hb : b ≠ ⊥)
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
    set.eq_empty_iff_forall_not_mem.2 $ assume a ⟨h₁, h₂⟩,
    have a ≠ a, from @h (a, a) ⟨h₁, h₂⟩,
    this rfl⟩ }

@[simp] lemma closure_le_eq [topological_space β] {f g : β → α} (hf : continuous f) (hg : continuous g):
  closure {b | f b ≤ g b} = {b | f b ≤ g b} :=
closure_eq_iff_is_closed.mpr $ is_closed_le hf hg
end partial_order

section linear_order
variables [topological_space α] [linear_order α] [t : ordered_topology α]
include t

lemma is_open_lt [topological_space β] {f g : β → α} (hf : continuous f) (hg : continuous g) :
  is_open {b | f b < g b} :=
by simp [lt_iff_not_ge, -not_le]; exact is_closed_le hg hf

lemma is_open_Ioo {a b : α} : is_open (Ioo a b) :=
is_open_and (is_open_lt continuous_const continuous_id) (is_open_lt continuous_id continuous_const)

lemma is_open_Iio {a : α} : is_open (Iio a) :=
is_open_lt continuous_id continuous_const

end linear_order

section decidable_linear_order
variables [topological_space α] [decidable_linear_order α] [t : ordered_topology α]
  [topological_space β] {f g : β → α}
include t

section
variables (hf : continuous f) (hg : continuous g)
include hf hg

lemma frontier_le_subset_eq : frontier {b | f b ≤ g b} ⊆ {b | f b = g b} :=
assume b ⟨hb₁, hb₂⟩,
le_antisymm
  (by simpa [closure_le_eq hf hg] using hb₁)
  (not_lt.1 $ assume hb : f b < g b,
    have {b | f b < g b} ⊆ interior {b | f b ≤ g b},
      from (subset_interior_iff_subset_of_open $ is_open_lt hf hg).mpr $ assume x, le_of_lt,
    have b ∈ interior {b | f b ≤ g b}, from this hb,
    by exact hb₂ this)

lemma continuous_max : continuous (λb, max (f b) (g b)) :=
have ∀b∈frontier {b | f b ≤ g b}, g b = f b, from assume b hb, (frontier_le_subset_eq hf hg hb).symm,
continuous_if this hg hf

lemma continuous_min : continuous (λb, min (f b) (g b)) :=
have ∀b∈frontier {b | f b ≤ g b}, f b = g b, from assume b hb, frontier_le_subset_eq hf hg hb,
continuous_if this hf hg

end

lemma tendsto_max {b : filter β} {a₁ a₂ : α} (hf : tendsto f b (nhds a₁)) (hg : tendsto g b (nhds a₂)) :
  tendsto (λb, max (f b) (g b)) b (nhds (max a₁ a₂)) :=
show tendsto ((λp:α×α, max p.1 p.2) ∘ (λb, (f b, g b))) b (nhds (max a₁ a₂)),
  from tendsto_compose (tendsto_prod_mk hf hg) $
    begin
      rw [←nhds_prod_eq],
      from continuous_iff_tendsto.mp (continuous_max continuous_fst continuous_snd) _
    end

lemma tendsto_min {b : filter β} {a₁ a₂ : α} (hf : tendsto f b (nhds a₁)) (hg : tendsto g b (nhds a₂)) :
  tendsto (λb, min (f b) (g b)) b (nhds (min a₁ a₂)) :=
show tendsto ((λp:α×α, min p.1 p.2) ∘ (λb, (f b, g b))) b (nhds (min a₁ a₂)),
  from tendsto_compose (tendsto_prod_mk hf hg) $
    begin
      rw [←nhds_prod_eq],
      from continuous_iff_tendsto.mp (continuous_min continuous_fst continuous_snd) _
    end

end decidable_linear_order

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

lemma lt_mem_nhds {a b : α} (h : a < b) : {b | a < b} ∈ (nhds b).sets :=
mem_nhds_sets (is_open_lt' _) h

lemma le_mem_nhds {a b : α} (h : a < b) : {b | a ≤ b} ∈ (nhds b).sets :=
(nhds b).upwards_sets (lt_mem_nhds h) $ assume b hb, le_of_lt hb

lemma gt_mem_nhds {a b : α} (h : a < b) : {a | a < b} ∈ (nhds a).sets :=
mem_nhds_sets (is_open_gt' _) h

lemma ge_mem_nhds {a b : α} (h : a < b) : {a | a ≤ b} ∈ (nhds a).sets :=
(nhds a).upwards_sets (gt_mem_nhds h) $ assume b hb, le_of_lt hb

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
      congr, funext x,
      congr, funext hx,
      rw [inf_comm],
      apply binfi_inf hu
    end
  ... = _ : by simp [inter_comm]; refl

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

variables [topological_space α] [ord : decidable_linear_order α] [t : orderable_topology α]
include t

lemma mem_nhds_orderable_dest {a : α} {s : set α} (hs : s ∈ (nhds a).sets) :
  ((∃u, u>a) → ∃u, a < u ∧ ∀b, a ≤ b → b < u → b ∈ s) ∧
  ((∃l, l<a) → ∃l, l < a ∧ ∀b, l < b → b ≤ a → b ∈ s) :=
let ⟨t₁, ht₁, t₂, ht₂, hts⟩ :=
  mem_inf_sets.mp $ by rw [@nhds_eq_orderable α _ _ _] at hs; exact hs in
have ht₁ : ((∃l, l<a) → ∃l, l < a ∧ ∀b, l < b → b ∈ t₁) ∧ (∀b, a ≤ b → b ∈ t₁),
  from infi_sets_induct ht₁
    (by simp {contextual := tt})
    (assume a' s₁ s₂ hs₁ ⟨hs₂, hs₃⟩,
      begin
        by_cases a' < a,
        { simp [h] at hs₁,
          exact ⟨assume hx, let ⟨u, hu₁, hu₂⟩ := hs₂ hx in
            ⟨max u a', max_lt hu₁ h, assume b hb,
              ⟨hs₁ $ lt_of_le_of_lt (le_max_right _ _) hb,
                hu₂ _ $ lt_of_le_of_lt (le_max_left _ _) hb⟩⟩,
            assume b hb, ⟨hs₁ $ lt_of_lt_of_le h hb, hs₃ _ hb⟩⟩ },
        { simp [h] at hs₁, simp [hs₁],
          exact ⟨by simpa using hs₂, hs₃⟩ }
      end)
    (assume s₁ s₂ h ih, and.intro
      (assume hx, let ⟨u, hu₁, hu₂⟩ := ih.left hx in ⟨u, hu₁, assume b hb, h $ hu₂ _ hb⟩)
      (assume b hb, h $ ih.right _ hb)),
have ht₂ : ((∃u, u>a) → ∃u, a < u ∧ ∀b, b < u → b ∈ t₂) ∧ (∀b, b ≤ a → b ∈ t₂),
  from infi_sets_induct ht₂
    (by simp {contextual := tt})
    (assume a' s₁ s₂ hs₁ ⟨hs₂, hs₃⟩,
      begin
        by_cases a' > a,
        { simp [h] at hs₁,
          exact ⟨assume hx, let ⟨u, hu₁, hu₂⟩ := hs₂ hx in
            ⟨min u a', lt_min hu₁ h, assume b hb,
              ⟨hs₁ $ lt_of_lt_of_le hb (min_le_right _ _),
                hu₂ _ $ lt_of_lt_of_le hb (min_le_left _ _)⟩⟩,
            assume b hb, ⟨hs₁ $ lt_of_le_of_lt hb h, hs₃ _ hb⟩⟩ },
        { simp [h] at hs₁, simp [hs₁],
          exact ⟨by simpa using hs₂, hs₃⟩ }
      end)
    (assume s₁ s₂ h ih, and.intro
      (assume hx, let ⟨u, hu₁, hu₂⟩ := ih.left hx in ⟨u, hu₁, assume b hb, h $ hu₂ _ hb⟩)
      (assume b hb, h $ ih.right _ hb)),
and.intro
  (assume hx, let ⟨u, hu, h⟩ := ht₂.left hx in ⟨u, hu, assume b hb hbu, hts ⟨ht₁.right b hb, h _ hbu⟩⟩)
  (assume hx, let ⟨l, hl, h⟩ := ht₁.left hx in ⟨l, hl, assume b hbl hb, hts ⟨h _ hbl, ht₂.right b hb⟩⟩)

lemma mem_nhds_unbounded {a : α} {s : set α} (hu : ∃u, a < u) (hl : ∃l, l < a) :
  s ∈ (nhds a).sets ↔ (∃l u, l < a ∧ a < u ∧ ∀b, l < b → b < u → b ∈ s) :=
let ⟨l, hl'⟩ := hl, ⟨u, hu'⟩ := hu in
have nhds a = (⨅p : {l // l < a} × {u // a < u}, principal {x | p.1.val < x ∧ x < p.2.val }),
  by simp [nhds_orderable_unbounded hu hl, infi_subtype, infi_prod],
iff.intro
  (assume hs, by rw [this] at hs; from infi_sets_induct hs
    ⟨l, u, hl', hu', by simp⟩
    begin
      intro p, cases p with p₁ p₂, cases p₁ with l hl, cases p₂ with u hu,
      simp [set.subset_def],
      intros s₁ s₂ hs₁ l' hl' u' hu' hs₂,
      refine ⟨max l l', _, min u u', _⟩;
      simp [*, lt_min_iff, max_lt_iff] {contextual := tt}
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

instance orderable_topology.t2_space : t2_space α := by apply_instance

instance orderable_topology.regular_space : regular_space α :=
{ regular := assume s a hs ha,
    have -s ∈ (nhds a).sets, from mem_nhds_sets hs ha,
    let ⟨h₁, h₂⟩ := mem_nhds_orderable_dest this in
    have ∃t:set α, is_open t ∧ (∀l∈ s, l < a → l ∈ t) ∧ nhds a ⊓ principal t = ⊥,
      from by_cases
        (assume h : ∃l, l < a,
          let ⟨l, hl, h⟩ := h₂ h in
          match dense_or_discrete hl with
          | or.inl ⟨b, hb₁, hb₂⟩ := ⟨{a | a < b}, is_open_gt' _,
              assume c hcs hca, show c < b,
                from lt_of_not_ge $ assume hbc, h c (lt_of_lt_of_le hb₁ hbc) (le_of_lt hca) hcs,
              inf_principal_eq_bot $ (nhds a).upwards_sets (mem_nhds_sets (is_open_lt' _) hb₂) $
                assume x (hx : b < x), show ¬ x < b, from not_lt.2 $ le_of_lt hx⟩
          | or.inr ⟨h₁, h₂⟩ := ⟨{a' | a' < a}, is_open_gt' _, assume b hbs hba, hba,
              inf_principal_eq_bot $ (nhds a).upwards_sets (mem_nhds_sets (is_open_lt' _) hl) $
                assume x (hx : l < x), show ¬ x < a, from not_lt.2 $ h₁ _ hx⟩
          end)
        (assume : ¬ ∃l, l < a, ⟨∅, is_open_empty, assume l _ hl, (this ⟨l, hl⟩).elim,
          by rw [principal_empty, inf_bot_eq]⟩),
    let ⟨t₁, ht₁o, ht₁s, ht₁a⟩ := this in
    have ∃t:set α, is_open t ∧ (∀u∈ s, u>a → u ∈ t) ∧ nhds a ⊓ principal t = ⊥,
      from by_cases
        (assume h : ∃u, u > a,
          let ⟨u, hu, h⟩ := h₁ h in
          match dense_or_discrete hu with
          | or.inl ⟨b, hb₁, hb₂⟩ := ⟨{a | b < a}, is_open_lt' _,
              assume c hcs hca, show c > b,
                from lt_of_not_ge $ assume hbc, h c (le_of_lt hca) (lt_of_le_of_lt hbc hb₂) hcs,
              inf_principal_eq_bot $ (nhds a).upwards_sets (mem_nhds_sets (is_open_gt' _) hb₁) $
                assume x (hx : b > x), show ¬ x > b, from not_lt.2 $ le_of_lt hx⟩
          | or.inr ⟨h₁, h₂⟩ := ⟨{a' | a' > a}, is_open_lt' _, assume b hbs hba, hba,
              inf_principal_eq_bot $ (nhds a).upwards_sets (mem_nhds_sets (is_open_gt' _) hu) $
                assume x (hx : u > x), show ¬ x > a, from not_lt.2 $ h₂ _ hx⟩
          end)
        (assume : ¬ ∃u, u > a, ⟨∅, is_open_empty, assume l _ hl, (this ⟨l, hl⟩).elim,
          by rw [principal_empty, inf_bot_eq]⟩),
    let ⟨t₂, ht₂o, ht₂s, ht₂a⟩ := this in
    ⟨t₁ ∪ t₂, is_open_union ht₁o ht₂o,
      assume x hx,
      have x ≠ a, from assume eq, ha $ eq ▸ hx,
      (ne_iff_lt_or_gt.mp this).imp (ht₁s _ hx) (ht₂s _ hx),
      by rw [←sup_principal, inf_sup_left, ht₁a, ht₂a, bot_sup_eq]⟩,
  ..orderable_topology.t2_space }

end linear_order

section order_topology

variables [topological_space α] [topological_space β]
  [decidable_linear_order α] [decidable_linear_order β] [orderable_topology α] [orderable_topology β]

lemma nhds_principal_ne_bot_of_is_lub {a : α} {s : set α} (ha : is_lub s a) (hs : s ≠ ∅) :
  nhds a ⊓ principal s ≠ ⊥ :=
let ⟨a', ha'⟩ := exists_mem_of_ne_empty hs in
forall_sets_neq_empty_iff_neq_bot.mp $ assume t ht,
  let ⟨t₁, ht₁, t₂, ht₂, ht⟩ := mem_inf_sets.mp ht in
  let ⟨hu, hl⟩ := mem_nhds_orderable_dest ht₁ in
  by_cases
    (assume h : a = a',
      have a ∈ t₁, from mem_of_nhds ht₁,
      have a ∈ t₂, from ht₂ $ by rwa [h],
      ne_empty_iff_exists_mem.mpr ⟨a, ht ⟨‹a ∈ t₁›, ‹a ∈ t₂›⟩⟩)
    (assume : a ≠ a',
      have a' < a, from lt_of_le_of_ne (ha.left _ ‹a' ∈ s›) this.symm,
      let ⟨l, hl, hlt₁⟩ := hl ⟨a', this⟩ in
      have ∃a'∈s, l < a',
        from classical.by_contradiction $ assume : ¬ ∃a'∈s, l < a',
          have ∀a'∈s, a' ≤ l, from assume a ha, not_lt.1 $ assume ha', this ⟨a, ha, ha'⟩,
          have ¬ l < a, from not_lt.2 $ ha.right _ this,
          this ‹l < a›,
      let ⟨a', ha', ha'l⟩ := this in
      have a' ∈ t₁, from hlt₁ _ ‹l < a'›  $ ha.left _ ha',
      ne_empty_iff_exists_mem.mpr ⟨a', ht ⟨‹a' ∈ t₁›, ht₂ ‹a' ∈ s›⟩⟩)

lemma nhds_principal_ne_bot_of_is_glb {a : α} {s : set α} (ha : is_glb s a) (hs : s ≠ ∅) :
  nhds a ⊓ principal s ≠ ⊥ :=
let ⟨a', ha'⟩ := exists_mem_of_ne_empty hs in
forall_sets_neq_empty_iff_neq_bot.mp $ assume t ht,
  let ⟨t₁, ht₁, t₂, ht₂, ht⟩ := mem_inf_sets.mp ht in
  let ⟨hu, hl⟩ := mem_nhds_orderable_dest ht₁ in
  by_cases
    (assume h : a = a',
      have a ∈ t₁, from mem_of_nhds ht₁,
      have a ∈ t₂, from ht₂ $ by rwa [h],
      ne_empty_iff_exists_mem.mpr ⟨a, ht ⟨‹a ∈ t₁›, ‹a ∈ t₂›⟩⟩)
    (assume : a ≠ a',
      have a < a', from lt_of_le_of_ne (ha.left _ ‹a' ∈ s›) this,
      let ⟨u, hu, hut₁⟩ := hu ⟨a', this⟩ in
      have ∃a'∈s, a' < u,
        from classical.by_contradiction $ assume : ¬ ∃a'∈s, a' < u,
          have ∀a'∈s, u ≤ a', from assume a ha, not_lt.1 $ assume ha', this ⟨a, ha, ha'⟩,
          have ¬ a < u, from not_lt.2 $ ha.right _ this,
          this ‹a < u›,
      let ⟨a', ha', ha'l⟩ := this in
      have a' ∈ t₁, from hut₁ _ (ha.left _ ha') ‹a' < u›,
      ne_empty_iff_exists_mem.mpr ⟨a', ht ⟨‹a' ∈ t₁›, ht₂ ‹a' ∈ s›⟩⟩)

lemma is_lub_of_mem_nhds {s : set α} {a : α} {f : filter α}
  (hsa : a ∈ upper_bounds s) (hsf : s ∈ f.sets) (hfa : f ⊓ nhds a ≠ ⊥) : is_lub s a :=
⟨hsa, assume b hb,
  not_lt.1 $ assume hba,
  have s ∩ {a | b < a} ∈ (f ⊓ nhds a).sets,
    from inter_mem_inf_sets hsf (mem_nhds_sets (is_open_lt' _) hba),
  let ⟨x, ⟨hxs, hxb⟩⟩ := inhabited_of_mem_sets hfa this in
  have b < b, from lt_of_lt_of_le hxb $ hb _ hxs,
  lt_irrefl b this⟩

lemma is_glb_of_mem_nhds {s : set α} {a : α} {f : filter α}
  (hsa : a ∈ lower_bounds s) (hsf : s ∈ f.sets) (hfa : f ⊓ nhds a ≠ ⊥) : is_glb s a :=
⟨hsa, assume b hb,
  not_lt.1 $ assume hba,
  have s ∩ {a | a < b} ∈ (f ⊓ nhds a).sets,
    from inter_mem_inf_sets hsf (mem_nhds_sets (is_open_gt' _) hba),
  let ⟨x, ⟨hxs, hxb⟩⟩ := inhabited_of_mem_sets hfa this in
  have b < b, from lt_of_le_of_lt (hb _ hxs) hxb,
  lt_irrefl b this⟩

lemma is_lub_of_is_lub_of_tendsto {f : α → β} {s : set α} {a : α} {b : β}
  (hf : ∀x∈s, ∀y∈s, x ≤ y → f x ≤ f y) (ha : is_lub s a) (hs : s ≠ ∅)
  (hb : tendsto f (nhds a ⊓ principal s) (nhds b)) : is_lub (f '' s) b :=
have hnbot : (nhds a ⊓ principal s) ≠ ⊥, from nhds_principal_ne_bot_of_is_lub ha hs,
have ∀a'∈s, ¬ b < f a',
  from assume a' ha' h,
  have {x | x < f a'} ∈ (nhds b).sets, from mem_nhds_sets (is_open_gt' _) h,
  let ⟨t₁, ht₁, t₂, ht₂, hs⟩ := mem_inf_sets.mp (hb this) in
  by_cases
    (assume h : a = a',
      have a ∈ t₁ ∩ t₂, from ⟨mem_of_nhds ht₁, ht₂ $ by rwa [h]⟩,
      have f a < f a', from hs this,
      lt_irrefl (f a') $ by rwa [h] at this)
    (assume h : a ≠ a',
      have a' < a, from lt_of_le_of_ne (ha.left _ ha') h.symm,
      have {x | a' < x} ∈ (nhds a).sets, from mem_nhds_sets (is_open_lt' _) this,
      have {x | a' < x} ∩ t₁ ∈ (nhds a).sets, from inter_mem_sets this ht₁,
      have ({x | a' < x} ∩ t₁) ∩ s ∈ (nhds a ⊓ principal s).sets,
        from inter_mem_inf_sets this (subset.refl s),
      let ⟨x, ⟨hx₁, hx₂⟩, hx₃⟩ := inhabited_of_mem_sets hnbot this in
      have hxa' : f x < f a', from hs ⟨hx₂, ht₂ hx₃⟩,
      have ha'x : f a' ≤ f x, from hf _ ha' _ hx₃ $ le_of_lt hx₁,
      lt_irrefl _ (lt_of_le_of_lt ha'x hxa')),
and.intro
  (assume b' ⟨a', ha', h_eq⟩, h_eq ▸ not_lt.1 $ this _ ha')
  (assume b' hb', le_of_tendsto hnbot hb tendsto_const_nhds $
      mem_inf_sets_of_right $ assume x hx, hb' _ $ mem_image_of_mem _ hx)

lemma is_glb_of_is_glb_of_tendsto {f : α → β} {s : set α} {a : α} {b : β}
  (hf : ∀x∈s, ∀y∈s, x ≤ y → f x ≤ f y) (ha : is_glb s a) (hs : s ≠ ∅)
  (hb : tendsto f (nhds a ⊓ principal s) (nhds b)) : is_glb (f '' s) b :=
have hnbot : (nhds a ⊓ principal s) ≠ ⊥, from nhds_principal_ne_bot_of_is_glb ha hs,
have ∀a'∈s, ¬ b > f a',
  from assume a' ha' h,
  have {x | x > f a'} ∈ (nhds b).sets, from mem_nhds_sets (is_open_lt' _) h,
  let ⟨t₁, ht₁, t₂, ht₂, hs⟩ := mem_inf_sets.mp (hb this) in
  by_cases
    (assume h : a = a',
      have a ∈ t₁ ∩ t₂, from ⟨mem_of_nhds ht₁, ht₂ $ by rwa [h]⟩,
      have f a > f a', from hs this,
      lt_irrefl (f a') $ by rwa [h] at this)
    (assume h : a ≠ a',
      have a' > a, from lt_of_le_of_ne (ha.left _ ha') h,
      have {x | a' > x} ∈ (nhds a).sets, from mem_nhds_sets (is_open_gt' _) this,
      have {x | a' > x} ∩ t₁ ∈ (nhds a).sets, from inter_mem_sets this ht₁,
      have ({x | a' > x} ∩ t₁) ∩ s ∈ (nhds a ⊓ principal s).sets,
        from inter_mem_inf_sets this (subset.refl s),
      let ⟨x, ⟨hx₁, hx₂⟩, hx₃⟩ := inhabited_of_mem_sets hnbot this in
      have hxa' : f x > f a', from hs ⟨hx₂, ht₂ hx₃⟩,
      have ha'x : f a' ≥ f x, from hf _ hx₃ _ ha' $ le_of_lt hx₁,
      lt_irrefl _ (lt_of_lt_of_le hxa' ha'x)),
and.intro
  (assume b' ⟨a', ha', h_eq⟩, h_eq ▸ not_lt.1 $ this _ ha')
  (assume b' hb', le_of_tendsto hnbot tendsto_const_nhds hb $
      mem_inf_sets_of_right $ assume x hx, hb' _ $ mem_image_of_mem _ hx)

lemma is_glb_of_is_lub_of_tendsto {f : α → β} {s : set α} {a : α} {b : β}
  (hf : ∀x∈s, ∀y∈s, x ≤ y → f y ≤ f x) (ha : is_lub s a) (hs : s ≠ ∅)
  (hb : tendsto f (nhds a ⊓ principal s) (nhds b)) : is_glb (f '' s) b :=
have hnbot : (nhds a ⊓ principal s) ≠ ⊥, from nhds_principal_ne_bot_of_is_lub ha hs,
have ∀a'∈s, ¬ b > f a',
  from assume a' ha' h,
  have {x | x > f a'} ∈ (nhds b).sets, from mem_nhds_sets (is_open_lt' _) h,
  let ⟨t₁, ht₁, t₂, ht₂, hs⟩ := mem_inf_sets.mp (hb this) in
  by_cases
    (assume h : a = a',
      have a ∈ t₁ ∩ t₂, from ⟨mem_of_nhds ht₁, ht₂ $ by rwa [h]⟩,
      have f a > f a', from hs this,
      lt_irrefl (f a') $ by rwa [h] at this)
    (assume h : a ≠ a',
      have a' < a, from lt_of_le_of_ne (ha.left _ ha') h.symm,
      have {x | a' < x} ∈ (nhds a).sets, from mem_nhds_sets (is_open_lt' _) this,
      have {x | a' < x} ∩ t₁ ∈ (nhds a).sets, from inter_mem_sets this ht₁,
      have ({x | a' < x} ∩ t₁) ∩ s ∈ (nhds a ⊓ principal s).sets,
        from inter_mem_inf_sets this (subset.refl s),
      let ⟨x, ⟨hx₁, hx₂⟩, hx₃⟩ := inhabited_of_mem_sets hnbot this in
      have hxa' : f x > f a', from hs ⟨hx₂, ht₂ hx₃⟩,
      have ha'x : f a' ≥ f x, from hf _ ha' _ hx₃ $ le_of_lt hx₁,
      lt_irrefl _ (lt_of_lt_of_le hxa' ha'x)),
and.intro
  (assume b' ⟨a', ha', h_eq⟩, h_eq ▸ not_lt.1 $ this _ ha')
  (assume b' hb', le_of_tendsto hnbot tendsto_const_nhds hb $
      mem_inf_sets_of_right $ assume x hx, hb' _ $ mem_image_of_mem _ hx)

end order_topology

end orderable_topology

lemma orderable_topology_of_nhds_abs
  {α : Type*} [decidable_linear_ordered_comm_group α] [topological_space α]
  (h_nhds : ∀a:α, nhds a = (⨅r>0, principal {b | abs (a - b) < r})) : orderable_topology α :=
orderable_topology.mk $ eq_of_nhds_eq_nhds $ assume a:α, le_antisymm_iff.mpr
begin
  simp [infi_and, topological_space.nhds_generate_from,
        h_nhds, le_infi_iff, -le_principal_iff, and_comm],
  refine ⟨λ s ha b hs, _, λ r hr, _⟩,
  { rcases hs with rfl | rfl,
    { refine infi_le_of_le (a - b)
        (infi_le_of_le (lt_sub_left_of_add_lt $ by simpa using ha) $
          principal_mono.mpr $ assume c (hc : abs (a - c) < a - b), _),
      have : a - c < a - b := lt_of_le_of_lt (le_abs_self _) hc,
      exact lt_of_neg_lt_neg (lt_of_add_lt_add_left this) },
    { refine infi_le_of_le (b - a)
        (infi_le_of_le (lt_sub_left_of_add_lt $ by simpa using ha) $
          principal_mono.mpr $ assume c (hc : abs (a - c) < b - a), _),
      have : abs (c - a) < b - a, {rw abs_sub; simpa using hc},
      have : c - a < b - a := lt_of_le_of_lt (le_abs_self _) this,
      exact lt_of_add_lt_add_right this } },
  { have h : {b | abs (a + -b) < r} = {b | a - r < b} ∩ {b | b < a + r},
      from set.ext (assume b,
        by simp [abs_lt, -sub_eq_add_neg, (sub_eq_add_neg _ _).symm, sub_lt, lt_sub_iff, and_comm]),
    rw [h, ← inf_principal],
    apply le_inf _ _,
    { exact infi_le_of_le {b : α | a - r < b} (infi_le_of_le (sub_lt_self a hr) $
        infi_le_of_le (a - r) $ infi_le _ (or.inl rfl)) },
    { exact infi_le_of_le {b : α | b < a + r} (infi_le_of_le (lt_add_of_pos_right _ hr) $
        infi_le_of_le (a + r) $ infi_le _ (or.inr rfl)) } }
end
