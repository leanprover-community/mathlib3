/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

Theory of topological monoids, groups and rings.

TODO: generalize `topological_monoid` and `topological_add_monoid` to semigroups, or add a type class
`topological_operator α (*)`.
-/

import algebra.big_operators
import order.liminf_limsup
import analysis.topology.topological_space analysis.topology.continuity analysis.topology.uniform_space

open classical set lattice filter topological_space
local attribute [instance] classical.prop_decidable

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

lemma dense_or_discrete [linear_order α] {a₁ a₂ : α} (h : a₁ < a₂) :
  (∃a, a₁ < a ∧ a < a₂) ∨ ((∀a>a₁, a ≥ a₂) ∧ (∀a<a₂, a ≤ a₁)) :=
classical.or_iff_not_imp_left.2 $ assume h,
  ⟨assume a ha₁, le_of_not_gt $ assume ha₂, h ⟨a, ha₁, ha₂⟩,
    assume a ha₂, le_of_not_gt $ assume ha₁, h ⟨a, ha₁, ha₂⟩⟩

section topological_monoid

/-- A topological monoid is a monoid in which the multiplication is continuous as a function
`α × α → α`. -/
class topological_monoid (α : Type u) [topological_space α] [monoid α] : Prop :=
(continuous_mul : continuous (λp:α×α, p.1 * p.2))

section
variables [topological_space α] [monoid α] [topological_monoid α]

lemma continuous_mul' : continuous (λp:α×α, p.1 * p.2) :=
topological_monoid.continuous_mul α

lemma continuous_mul [topological_space β] {f : β → α} {g : β → α}
  (hf : continuous f) (hg : continuous g) :
  continuous (λx, f x * g x) :=
(hf.prod_mk hg).comp continuous_mul'

lemma tendsto_mul' {a b : α} : tendsto (λp:α×α, p.fst * p.snd) (nhds (a, b)) (nhds (a * b)) :=
continuous_iff_tendsto.mp (topological_monoid.continuous_mul α) (a, b)

lemma tendsto_mul {f : β → α} {g : β → α} {x : filter β} {a b : α}
  (hf : tendsto f x (nhds a)) (hg : tendsto g x (nhds b)) :
  tendsto (λx, f x * g x) x (nhds (a * b)) :=
(hf.prod_mk hg).comp (by rw [←nhds_prod_eq]; exact tendsto_mul')

lemma tendsto_list_prod {f : γ → β → α} {x : filter β} {a : γ → α} :
  ∀l:list γ, (∀c∈l, tendsto (f c) x (nhds (a c))) →
    tendsto (λb, (l.map (λc, f c b)).prod) x (nhds ((l.map a).prod))
| []       _ := by simp [tendsto_const_nhds]
| (f :: l) h :=
  begin
    simp,
    exact tendsto_mul
      (h f (list.mem_cons_self _ _))
      (tendsto_list_prod l (assume c hc, h c (list.mem_cons_of_mem _ hc)))
  end

lemma continuous_list_prod [topological_space β] {f : γ → β → α} (l : list γ)
  (h : ∀c∈l, continuous (f c)) :
  continuous (λa, (l.map (λc, f c a)).prod) :=
continuous_iff_tendsto.2 $ assume x, tendsto_list_prod l $ assume c hc,
  continuous_iff_tendsto.1 (h c hc) x

end

section
variables [topological_space α] [comm_monoid α] [topological_monoid α]

lemma tendsto_multiset_prod {f : γ → β → α} {x : filter β} {a : γ → α} (s : multiset γ) :
  (∀c∈s, tendsto (f c) x (nhds (a c))) →
    tendsto (λb, (s.map (λc, f c b)).prod) x (nhds ((s.map a).prod)) :=
quot.induction_on s $ by simp; exact tendsto_list_prod

lemma tendsto_finset_prod {f : γ → β → α} {x : filter β} {a : γ → α} (s : finset γ) :
  (∀c∈s, tendsto (f c) x (nhds (a c))) → tendsto (λb, s.prod (λc, f c b)) x (nhds (s.prod a)) :=
tendsto_multiset_prod _

lemma continuous_multiset_prod [topological_space β] {f : γ → β → α} (s : multiset γ) :
  (∀c∈s, continuous (f c)) → continuous (λa, (s.map (λc, f c a)).prod) :=
quot.induction_on s $ by simp; exact continuous_list_prod

lemma continuous_finset_prod [topological_space β] {f : γ → β → α} (s : finset γ) :
  (∀c∈s, continuous (f c)) → continuous (λa, s.prod (λc, f c a)) :=
continuous_multiset_prod _

end

end topological_monoid

section topological_add_monoid

/-- A topological (additive) monoid is a monoid in which the addition is
  continuous as a function `α × α → α`. -/
class topological_add_monoid (α : Type u) [topological_space α] [add_monoid α] : Prop :=
(continuous_add : continuous (λp:α×α, p.1 + p.2))

section
variables [topological_space α] [add_monoid α] [topological_add_monoid α]

lemma continuous_add' : continuous (λp:α×α, p.1 + p.2) :=
topological_add_monoid.continuous_add α

lemma continuous_add [topological_space β] {f : β → α} {g : β → α}
  (hf : continuous f) (hg : continuous g) : continuous (λx, f x + g x) :=
(hf.prod_mk hg).comp continuous_add'

lemma tendsto_add' {a b : α} : tendsto (λp:α×α, p.fst + p.snd) (nhds (a, b)) (nhds (a + b)) :=
continuous_iff_tendsto.mp (topological_add_monoid.continuous_add α) (a, b)

lemma tendsto_add {f : β → α} {g : β → α} {x : filter β} {a b : α}
  (hf : tendsto f x (nhds a)) (hg : tendsto g x (nhds b)) :
  tendsto (λx, f x + g x) x (nhds (a + b)) :=
(hf.prod_mk hg).comp (by rw [←nhds_prod_eq]; exact tendsto_add')

lemma tendsto_list_sum {f : γ → β → α} {x : filter β} {a : γ → α} :
  ∀l:list γ, (∀c∈l, tendsto (f c) x (nhds (a c))) →
    tendsto (λb, (l.map (λc, f c b)).sum) x (nhds ((l.map a).sum))
| []       _ := by simp [tendsto_const_nhds]
| (f :: l) h :=
  begin
    simp,
    exact tendsto_add
      (h f (list.mem_cons_self _ _))
      (tendsto_list_sum l (assume c hc, h c (list.mem_cons_of_mem _ hc)))
  end

lemma continuous_list_sum [topological_space β] {f : γ → β → α} (l : list γ)
  (h : ∀c∈l, continuous (f c)) : continuous (λa, (l.map (λc, f c a)).sum) :=
continuous_iff_tendsto.2 $ assume x, tendsto_list_sum l $ assume c hc,
  continuous_iff_tendsto.1 (h c hc) x

end

section
variables [topological_space α] [add_comm_monoid α] [topological_add_monoid α]

lemma tendsto_multiset_sum {f : γ → β → α} {x : filter β} {a : γ → α} (s : multiset γ) :
  (∀c∈s, tendsto (f c) x (nhds (a c))) →
    tendsto (λb, (s.map (λc, f c b)).sum) x (nhds ((s.map a).sum)) :=
quot.induction_on s $ by simp; exact tendsto_list_sum

lemma tendsto_finset_sum {f : γ → β → α} {x : filter β} {a : γ → α} (s : finset γ) :
  (∀c∈s, tendsto (f c) x (nhds (a c))) → tendsto (λb, s.sum (λc, f c b)) x (nhds (s.sum a)) :=
tendsto_multiset_sum _

lemma continuous_multiset_sum [topological_space β] {f : γ → β → α} (s : multiset γ) :
  (∀c∈s, continuous (f c)) → continuous (λa, (s.map (λc, f c a)).sum) :=
quot.induction_on s $ by simp; exact continuous_list_sum

lemma continuous_finset_sum [topological_space β] {f : γ → β → α} (s : finset γ) :
  (∀c∈s, continuous (f c)) → continuous (λa, s.sum (λc, f c a)) :=
continuous_multiset_sum _

end
end topological_add_monoid

section topological_add_group
/-- A topological (additive) group is a group in which the addition and
  negation operations are continuous. -/
class topological_add_group (α : Type u) [topological_space α] [add_group α]
  extends topological_add_monoid α : Prop :=
(continuous_neg : continuous (λa:α, -a))

variables [topological_space α] [add_group α]

lemma continuous_neg' [topological_add_group α] : continuous (λx:α, - x) :=
topological_add_group.continuous_neg α

lemma continuous_neg [topological_add_group α] [topological_space β] {f : β → α}
  (hf : continuous f) : continuous (λx, - f x) :=
hf.comp continuous_neg'

lemma tendsto_neg [topological_add_group α] {f : β → α} {x : filter β} {a : α}
  (hf : tendsto f x (nhds a)) : tendsto (λx, - f x) x (nhds (- a)) :=
hf.comp (continuous_iff_tendsto.mp (topological_add_group.continuous_neg α) a)

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
/-- A uniform (additive) group is a group in which the addition and negation are
  uniformly continuous. -/
class uniform_add_group (α : Type u) [uniform_space α] [add_group α] : Prop :=
(uniform_continuous_sub : uniform_continuous (λp:α×α, p.1 - p.2))

theorem uniform_add_group.mk' {α} [uniform_space α] [add_group α]
  (h₁ : uniform_continuous (λp:α×α, p.1 + p.2))
  (h₂ : uniform_continuous (λp:α, -p)) : uniform_add_group α :=
⟨(uniform_continuous_fst.prod_mk (uniform_continuous_snd.comp h₂)).comp h₁⟩

variables [uniform_space α] [add_group α]

lemma uniform_continuous_sub' [uniform_add_group α] : uniform_continuous (λp:α×α, p.1 - p.2) :=
uniform_add_group.uniform_continuous_sub α

lemma uniform_continuous_sub [uniform_add_group α] [uniform_space β] {f : β → α} {g : β → α}
  (hf : uniform_continuous f) (hg : uniform_continuous g) : uniform_continuous (λx, f x - g x) :=
(hf.prod_mk hg).comp uniform_continuous_sub'

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
{ continuous_add := uniform_continuous_add'.continuous,
  continuous_neg := uniform_continuous_neg'.continuous }

end uniform_add_group

/-- A topological semiring is a semiring where addition and multiplication are continuous. -/
class topological_semiring (α : Type u) [topological_space α] [semiring α]
  extends topological_add_monoid α, topological_monoid α : Prop

/-- A topological ring is a ring where the ring operations are continuous. -/
class topological_ring (α : Type u) [topological_space α] [ring α]
  extends topological_add_monoid α, topological_monoid α : Prop :=
(continuous_neg : continuous (λa:α, -a))

instance topological_ring.to_topological_semiring
  [topological_space α] [ring α] [t : topological_ring α] : topological_semiring α := {..t}

instance topological_ring.to_topological_add_group
  [topological_space α] [ring α] [t : topological_ring α] : topological_add_group α := {..t}

/-- (Partially) ordered topology
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
continuous_iff_is_closed.mp (hf.prod_mk hg) _ t.is_closed_le'

lemma is_closed_le' (a : α) : is_closed {b | b ≤ a} :=
is_closed_le continuous_id continuous_const

lemma is_closed_ge' (a : α) : is_closed {b | a ≤ b} :=
is_closed_le continuous_const continuous_id

lemma is_closed_Icc {a b : α} : is_closed (Icc a b) :=
is_closed_inter (is_closed_ge' a) (is_closed_le' b)

lemma le_of_tendsto {f g : β → α} {b : filter β} {a₁ a₂ : α} (hb : b ≠ ⊥)
  (hf : tendsto f b (nhds a₁)) (hg : tendsto g b (nhds a₂)) (h : {b | f b ≤ g b} ∈ b.sets) :
  a₁ ≤ a₂ :=
have tendsto (λb, (f b, g b)) b (nhds (a₁, a₂)),
  by rw [nhds_prod_eq]; exact hf.prod_mk hg,
show (a₁, a₂) ∈ {p:α×α | p.1 ≤ p.2},
  from mem_of_closed_of_tendsto hb this t.is_closed_le' h

private lemma is_closed_eq : is_closed {p : α × α | p.1 = p.2} :=
by simp [le_antisymm_iff];
   exact is_closed_inter t.is_closed_le' (is_closed_le continuous_snd continuous_fst)

instance ordered_topology.to_t2_space : t2_space α :=
{ t2 :=
  have is_open {p : α × α | p.1 ≠ p.2}, from is_closed_eq,
  assume a b h,
  let ⟨u, v, hu, hv, ha, hb, h⟩ := is_open_prod_iff.mp this a b h in
  ⟨u, v, hu, hv, ha, hb,
    set.eq_empty_iff_forall_not_mem.2 $ assume a ⟨h₁, h₂⟩,
    have a ≠ a, from @h (a, a) ⟨h₁, h₂⟩,
    this rfl⟩ }

@[simp] lemma closure_le_eq [topological_space β] {f g : β → α} (hf : continuous f) (hg : continuous g) :
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
  from (hf.prod_mk hg).comp
    begin
      rw [←nhds_prod_eq],
      from continuous_iff_tendsto.mp (continuous_max continuous_fst continuous_snd) _
    end

lemma tendsto_min {b : filter β} {a₁ a₂ : α} (hf : tendsto f b (nhds a₁)) (hg : tendsto g b (nhds a₂)) :
  tendsto (λb, min (f b) (g b)) b (nhds (min a₁ a₂)) :=
show tendsto ((λp:α×α, min p.1 p.2) ∘ (λb, (f b, g b))) b (nhds (min a₁ a₂)),
  from (hf.prod_mk hg).comp
    begin
      rw [←nhds_prod_eq],
      from continuous_iff_tendsto.mp (continuous_min continuous_fst continuous_snd) _
    end

end decidable_linear_order

end ordered_topology

/-- Topologies generated by the open intervals.

  This is restricted to linear orders. Only then it is guaranteed that they are also a ordered
  topology. -/
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

lemma tendsto_orderable {f : β → α} {a : α} {x : filter β} :
  tendsto f x (nhds a) ↔ (∀a'<a, {b | a' < f b} ∈ x.sets) ∧ (∀a'>a, {b | a' > f b} ∈ x.sets) :=
by simp [@nhds_eq_orderable α _ _, tendsto_inf, tendsto_infi, tendsto_principal]

/-- Also known as squeeze or sandwich theorem. -/
lemma tendsto_of_tendsto_of_tendsto_of_le_of_le {f g h : β → α} {b : filter β} {a : α}
  (hg : tendsto g b (nhds a)) (hh : tendsto h b (nhds a))
  (hgf : {b | g b ≤ f b} ∈ b.sets) (hfh : {b | f b ≤ h b} ∈ b.sets) :
  tendsto f b (nhds a) :=
tendsto_orderable.2
  ⟨assume a' h',
    have {b : β | a' < g b} ∈ b.sets, from (tendsto_orderable.1 hg).left a' h',
    by filter_upwards [this, hgf] assume a, lt_of_lt_of_le,
    assume a' h',
    have {b : β | h b < a'} ∈ b.sets, from (tendsto_orderable.1 hh).right a' h',
    by filter_upwards [this, hfh] assume a h₁ h₂, lt_of_le_of_lt h₂ h₁⟩

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
from (tendsto_infi.2 $ assume l, tendsto_infi.2 $ assume hl,
  tendsto_infi.2 $ assume u, tendsto_infi.2 $ assume hu, tendsto_principal.2 $ h l u hl hu)

end partial_order

theorem induced_orderable_topology' {α : Type u} {β : Type v}
  [partial_order α] [ta : topological_space β] [partial_order β] [orderable_topology β]
  (f : α → β) (hf : ∀ {x y}, f x < f y ↔ x < y)
  (H₁ : ∀ {a x}, x < f a → ∃ b < a, x ≤ f b)
  (H₂ : ∀ {a x}, f a < x → ∃ b > a, f b ≤ x) :
  @orderable_topology _ (induced f ta) _ :=
begin
  letI := induced f ta,
  refine ⟨eq_of_nhds_eq_nhds (λ a, _)⟩,
  rw [nhds_induced_eq_vmap, nhds_generate_from, @nhds_eq_orderable β _ _], apply le_antisymm,
  { rw [← map_le_iff_le_vmap],
    refine le_inf _ _; refine le_infi (λ x, le_infi $ λ h, le_principal_iff.2 _); simp,
    { rcases H₁ h with ⟨b, ab, xb⟩,
      refine mem_infi_sets _ (mem_infi_sets ⟨ab, b, or.inl rfl⟩ (mem_principal_sets.2 _)),
      exact λ c hc, lt_of_le_of_lt xb (hf.2 hc) },
    { rcases H₂ h with ⟨b, ab, xb⟩,
      refine mem_infi_sets _ (mem_infi_sets ⟨ab, b, or.inr rfl⟩ (mem_principal_sets.2 _)),
      exact λ c hc, lt_of_lt_of_le (hf.2 hc) xb } },
  refine le_infi (λ s, le_infi $ λ hs, le_principal_iff.2 _),
  rcases hs with ⟨ab, b, rfl|rfl⟩,
  { exact mem_vmap_sets.2 ⟨{x | f b < x},
      mem_inf_sets_of_left $ mem_infi_sets _ $ mem_infi_sets (hf.2 ab) $ mem_principal_self _,
      λ x, hf.1⟩ },
  { exact mem_vmap_sets.2 ⟨{x | x < f b},
      mem_inf_sets_of_right $ mem_infi_sets _ $ mem_infi_sets (hf.2 ab) $ mem_principal_self _,
      λ x, hf.1⟩ }
end

theorem induced_orderable_topology {α : Type u} {β : Type v}
  [partial_order α] [ta : topological_space β] [partial_order β] [orderable_topology β]
  (f : α → β) (hf : ∀ {x y}, f x < f y ↔ x < y)
  (H : ∀ {x y}, x < y → ∃ a, x < f a ∧ f a < y) :
  @orderable_topology _ (induced f ta) _ :=
induced_orderable_topology' f @hf
  (λ a x xa, let ⟨b, xb, ba⟩ := H xa in ⟨b, hf.1 ba, le_of_lt xb⟩)
  (λ a x ax, let ⟨b, ab, bx⟩ := H ax in ⟨b, hf.1 ab, le_of_lt bx⟩)

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
      intro p, rcases p with ⟨⟨l, hl⟩, ⟨u, hu⟩⟩,
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

lemma preimage_neg [add_group α] : preimage (has_neg.neg : α → α) = image (has_neg.neg : α → α) :=
(image_eq_preimage_of_inverse neg_neg neg_neg).symm

lemma filter.map_neg [add_group α] : map (has_neg.neg : α → α) = vmap (has_neg.neg : α → α) :=
funext $ assume f, map_eq_vmap_of_inverse (funext neg_neg) (funext neg_neg)

section topological_add_group

variables [topological_space α] [ordered_comm_group α] [orderable_topology α] [topological_add_group α]

lemma neg_preimage_closure {s : set α} : (λr:α, -r) ⁻¹' closure s = closure ((λr:α, -r) '' s) :=
have (λr:α, -r) ∘ (λr:α, -r) = id, from funext neg_neg,
by rw [preimage_neg]; exact
  (subset.antisymm (image_closure_subset_closure_image continuous_neg') $
    calc closure ((λ (r : α), -r) '' s) = (λr, -r) '' ((λr, -r) '' closure ((λ (r : α), -r) '' s)) :
        by rw [←image_comp, this, image_id]
      ... ⊆ (λr, -r) '' closure ((λr, -r) '' ((λ (r : α), -r) '' s)) :
        mono_image $ image_closure_subset_closure_image continuous_neg'
      ... = _ : by rw [←image_comp, this, image_id])

end topological_add_group

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

section liminf_limsup

section ordered_topology
variables [semilattice_sup α] [topological_space α] [orderable_topology α]

lemma is_bounded_le_nhds (a : α) : (nhds a).is_bounded (≤) :=
match forall_le_or_exists_lt_sup a with
| or.inl h := ⟨a, univ_mem_sets' h⟩
| or.inr ⟨b, hb⟩ := ⟨b, ge_mem_nhds hb⟩
end

lemma is_bounded_under_le_of_tendsto {f : filter β} {u : β → α} {a : α}
  (h : tendsto u f (nhds a)) : f.is_bounded_under (≤) u :=
is_bounded_of_le h (is_bounded_le_nhds a)

lemma is_cobounded_ge_nhds (a : α) : (nhds a).is_cobounded (≥) :=
is_cobounded_of_is_bounded nhds_neq_bot (is_bounded_le_nhds a)

lemma is_cobounded_under_ge_of_tendsto {f : filter β} {u : β → α} {a : α}
  (hf : f ≠ ⊥) (h : tendsto u f (nhds a)) : f.is_cobounded_under (≥) u :=
is_cobounded_of_is_bounded (map_ne_bot hf) (is_bounded_under_le_of_tendsto h)

end ordered_topology

section ordered_topology
variables [semilattice_inf α] [topological_space α] [orderable_topology α]

lemma is_bounded_ge_nhds (a : α) : (nhds a).is_bounded (≥) :=
match forall_le_or_exists_lt_inf a with
| or.inl h := ⟨a, univ_mem_sets' h⟩
| or.inr ⟨b, hb⟩ := ⟨b, le_mem_nhds hb⟩
end

lemma is_bounded_under_ge_of_tendsto {f : filter β} {u : β → α} {a : α}
  (h : tendsto u f (nhds a)) : f.is_bounded_under (≥) u :=
is_bounded_of_le h (is_bounded_ge_nhds a)

lemma is_cobounded_le_nhds (a : α) : (nhds a).is_cobounded (≤) :=
is_cobounded_of_is_bounded nhds_neq_bot (is_bounded_ge_nhds a)

lemma is_cobounded_under_le_of_tendsto {f : filter β} {u : β → α} {a : α}
  (hf : f ≠ ⊥) (h : tendsto u f (nhds a)) : f.is_cobounded_under (≤) u :=
is_cobounded_of_is_bounded (map_ne_bot hf) (is_bounded_under_ge_of_tendsto h)

end ordered_topology

section conditionally_complete_linear_order
variables [conditionally_complete_linear_order α] [topological_space α] [orderable_topology α]

theorem lt_mem_sets_of_Limsup_lt {f : filter α} {b} (h : f.is_bounded (≤)) (l : f.Limsup < b) :
  {a | a < b} ∈ f.sets :=
let ⟨c, (h : {a : α | a ≤ c} ∈ f.sets), hcb⟩ :=
  exists_lt_of_cInf_lt (ne_empty_iff_exists_mem.2 h) l in
f.upwards_sets h $ assume a hac, lt_of_le_of_lt hac hcb

theorem gt_mem_sets_of_Liminf_gt {f : filter α} {b} (h : f.is_bounded (≥)) (l : f.Liminf > b) :
  {a | a > b} ∈ f.sets :=
let ⟨c, (h : {a : α | c ≤ a} ∈ f.sets), hbc⟩ :=
  exists_lt_of_lt_cSup (ne_empty_iff_exists_mem.2 h) l in
f.upwards_sets h $ assume a hca, lt_of_lt_of_le hbc hca

/-- If the liminf and the limsup of a filter coincide, then this filter converges to
their common value, at least if the filter is eventually bounded above and below. -/
theorem le_nhds_of_Limsup_eq_Liminf {f : filter α} {a : α}
  (hl : f.is_bounded (≤)) (hg : f.is_bounded (≥)) (hs : f.Limsup = a) (hi : f.Liminf = a) :
  f ≤ nhds a :=
tendsto_orderable.2 $ and.intro
  (assume b hb, gt_mem_sets_of_Liminf_gt hg $ hi.symm ▸ hb)
  (assume b hb, lt_mem_sets_of_Limsup_lt hl $ hs.symm ▸ hb)

theorem Limsup_nhds (a : α) : Limsup (nhds a) = a :=
cInf_intro (ne_empty_iff_exists_mem.2 $ is_bounded_le_nhds a)
  (assume a' (h : {n : α | n ≤ a'} ∈ (nhds a).sets), show a ≤ a', from @mem_of_nhds α _ a _ h)
  (assume b (hba : a < b), show ∃c (h : {n : α | n ≤ c} ∈ (nhds a).sets), c < b, from
    match dense_or_discrete hba with
    | or.inl ⟨c, hac, hcb⟩ := ⟨c, ge_mem_nhds hac, hcb⟩
    | or.inr ⟨_, h⟩        := ⟨a, (nhds a).upwards_sets (gt_mem_nhds hba) h, hba⟩
    end)

theorem Liminf_nhds (a : α) : Liminf (nhds a) = a :=
cSup_intro (ne_empty_iff_exists_mem.2 $ is_bounded_ge_nhds a)
  (assume a' (h : {n : α | a' ≤ n} ∈ (nhds a).sets), show a' ≤ a, from mem_of_nhds h)
  (assume b (hba : b < a), show ∃c (h : {n : α | c ≤ n} ∈ (nhds a).sets), b < c, from
    match dense_or_discrete hba with
    | or.inl ⟨c, hbc, hca⟩ := ⟨c, le_mem_nhds hca, hbc⟩
    | or.inr ⟨h, _⟩        := ⟨a, (nhds a).upwards_sets (lt_mem_nhds hba) h, hba⟩
    end)

/-- If a filter is converging, its limsup coincides with its limit. -/
theorem Liminf_eq_of_le_nhds {f : filter α} {a : α} (hf : f ≠ ⊥) (h : f ≤ nhds a) : f.Liminf = a :=
have hb_ge : is_bounded (≥) f, from is_bounded_of_le h (is_bounded_ge_nhds a),
have hb_le : is_bounded (≤) f, from is_bounded_of_le h (is_bounded_le_nhds a),
le_antisymm
  (calc f.Liminf ≤ f.Limsup : Liminf_le_Limsup hf hb_le hb_ge
    ... ≤ (nhds a).Limsup :
      Limsup_le_Limsup_of_le h (is_cobounded_of_is_bounded hf hb_ge) (is_bounded_le_nhds a)
    ... = a : Limsup_nhds a)
  (calc a = (nhds a).Liminf : (Liminf_nhds a).symm
    ... ≤ f.Liminf :
      Liminf_le_Liminf_of_le h (is_bounded_ge_nhds a) (is_cobounded_of_is_bounded hf hb_le))

/-- If a filter is converging, its liminf coincides with its limit. -/
theorem Limsup_eq_of_le_nhds {f : filter α} {a : α} (hf : f ≠ ⊥) (h : f ≤ nhds a) : f.Limsup = a :=
have hb_ge : is_bounded (≥) f, from is_bounded_of_le h (is_bounded_ge_nhds a),
le_antisymm
  (calc f.Limsup ≤ (nhds a).Limsup :
    Limsup_le_Limsup_of_le h (is_cobounded_of_is_bounded hf hb_ge) (is_bounded_le_nhds a)
    ... = a : Limsup_nhds a)
  (calc a = f.Liminf : (Liminf_eq_of_le_nhds hf h).symm
    ... ≤ f.Limsup : Liminf_le_Limsup hf (is_bounded_of_le h (is_bounded_le_nhds a)) hb_ge)

end conditionally_complete_linear_order

end liminf_limsup

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
        by simp [abs_lt, -sub_eq_add_neg, (sub_eq_add_neg _ _).symm,
          sub_lt, lt_sub_iff_add_lt, and_comm, sub_lt_iff_lt_add']),
    rw [h, ← inf_principal],
    apply le_inf _ _,
    { exact infi_le_of_le {b : α | a - r < b} (infi_le_of_le (sub_lt_self a hr) $
        infi_le_of_le (a - r) $ infi_le _ (or.inl rfl)) },
    { exact infi_le_of_le {b : α | b < a + r} (infi_le_of_le (lt_add_of_pos_right _ hr) $
        infi_le_of_le (a + r) $ infi_le _ (or.inr rfl)) } }
end
