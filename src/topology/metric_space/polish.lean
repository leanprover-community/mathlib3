/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import topology.metric_space.pi_nat
import topology.metric_space.isometry
import topology.metric_space.gluing
import analysis.normed.field.basic

/-!
# Polish spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A topological space is Polish if its topology is second-countable and there exists a compatible
complete metric. This is the class of spaces that is well-behaved with respect to measure theory.
In this file, we establish the basic properties of Polish spaces.

## Main definitions and results

* `polish_space α` is a mixin typeclass on a topological space, requiring that the topology is
  second-countable and compatible with a complete metric. To endow the space with such a metric,
  use in a proof `letI := upgrade_polish_space α`.
  We register an instance from complete second-countable metric spaces to Polish spaces, not the
  other way around.
* We register that countable products and sums of Polish spaces are Polish.
* `is_closed.polish_space`: a closed subset of a Polish space is Polish.
* `is_open.polish_space`: an open subset of a Polish space is Polish.
* `exists_nat_nat_continuous_surjective`: any nonempty Polish space is the continuous image
  of the fundamental Polish space `ℕ → ℕ`.

A fundamental property of Polish spaces is that one can put finer topologies, still Polish,
with additional properties:

* `exists_polish_space_forall_le`: on a topological space, consider countably many topologies
  `t n`, all Polish and finer than the original topology. Then there exists another Polish
  topology which is finer than all the `t n`.
* `is_clopenable s` is a property of a subset `s` of a topological space, requiring that there
  exists a finer topology, which is Polish, for which `s` becomes open and closed. We show that
  this property is satisfied for open sets, closed sets, for complements, and for countable unions.
  Once Borel-measurable sets are defined in later files, it will follow that any Borel-measurable
  set is clopenable. Once the Lusin-Souslin theorem is proved using analytic sets, we will even
  show that a set is clopenable if and only if it is Borel-measurable, see
  `is_clopenable_iff_measurable_set`.
-/

noncomputable theory
open_locale classical topology filter
open topological_space set metric filter function

variables {α : Type*} {β : Type*}

/-! ### Basic properties of Polish spaces -/

/-- A Polish space is a topological space with second countable topology, that can be endowed
with a metric for which it is complete.
We register an instance from complete second countable metric space to polish space, and not the
other way around as this is the most common use case.

To endow a Polish space with a complete metric space structure, do `letI := upgrade_polish_space α`.
-/
class polish_space (α : Type*) [h : topological_space α] : Prop :=
(second_countable [] : second_countable_topology α)
(complete : ∃ m : metric_space α, m.to_uniform_space.to_topological_space = h ∧
  @complete_space α m.to_uniform_space)

/-- A convenience class, for a Polish space endowed with a complete metric. No instance of this
class should be registered: It should be used as `letI := upgrade_polish_space α` to endow a Polish
space with a complete metric. -/
class upgraded_polish_space (α : Type*) extends metric_space α, second_countable_topology α,
  complete_space α

@[priority 100]
instance polish_space_of_complete_second_countable
  [m : metric_space α] [h : second_countable_topology α] [h' : complete_space α] :
  polish_space α :=
{ second_countable := h,
  complete := ⟨m, rfl, h'⟩ }

/-- Construct on a Polish space a metric (compatible with the topology) which is complete. -/
def polish_space_metric (α : Type*) [ht : topological_space α] [h : polish_space α] :
  metric_space α :=
h.complete.some.replace_topology h.complete.some_spec.1.symm

lemma complete_polish_space_metric (α : Type*) [ht : topological_space α] [h : polish_space α] :
  @complete_space α (polish_space_metric α).to_uniform_space :=
begin
  convert h.complete.some_spec.2,
  exact metric_space.replace_topology_eq _ _
end

/-- This definition endows a Polish space with a complete metric. Use it as:
`letI := upgrade_polish_space α`. -/
def upgrade_polish_space (α : Type*) [ht : topological_space α] [h : polish_space α] :
  upgraded_polish_space α :=
begin
  letI := polish_space_metric α,
  exact { .. complete_polish_space_metric α, .. polish_space.second_countable α }
end

namespace polish_space

@[priority 100]
instance t2_space (α : Type*) [topological_space α] [polish_space α] : t2_space α :=
by { letI := upgrade_polish_space α, apply_instance }

/-- A countable product of Polish spaces is Polish. -/
instance pi_countable {ι : Type*} [countable ι] {E : ι → Type*}
  [∀ i, topological_space (E i)] [∀ i, polish_space (E i)] :
  polish_space (Π i, E i) :=
begin
  casesI nonempty_encodable ι,
  letI := λ i, upgrade_polish_space (E i),
  letI : metric_space (Π i, E i) := pi_countable.metric_space,
  apply_instance,
end

/-- Without this instance, `polish_space (ℕ → ℕ)` is not found by typeclass inference. -/
instance nat_fun [topological_space α] [polish_space α] :
  polish_space (ℕ → α) :=
by apply_instance

/-- A countable disjoint union of Polish spaces is Polish. -/
instance sigma {ι : Type*} [countable ι]
  {E : ι → Type*} [∀ n, topological_space (E n)] [∀ n, polish_space (E n)] :
  polish_space (Σ n, E n) :=
begin
  letI := λ n, upgrade_polish_space (E n),
  letI : metric_space (Σ n, E n) := sigma.metric_space,
  haveI : complete_space (Σ n, E n) := sigma.complete_space,
  apply_instance
end

/-- The disjoint union of two Polish spaces is Polish. -/
instance sum [topological_space α] [polish_space α] [topological_space β] [polish_space β] :
  polish_space (α ⊕ β) :=
begin
  letI := upgrade_polish_space α,
  letI := upgrade_polish_space β,
  letI : metric_space (α ⊕ β) := metric_space_sum,
  apply_instance
end

/-- Any nonempty Polish space is the continuous image of the fundamental space `ℕ → ℕ`. -/
lemma exists_nat_nat_continuous_surjective
  (α : Type*) [topological_space α] [polish_space α] [nonempty α] :
  ∃ (f : (ℕ → ℕ) → α), continuous f ∧ surjective f :=
begin
  letI := upgrade_polish_space α,
  exact exists_nat_nat_continuous_surjective_of_complete_space α
end

/-- Given a closed embedding into a Polish space, the source space is also Polish. -/
lemma _root_.closed_embedding.polish_space [topological_space α] [topological_space β]
  [polish_space β] {f : α → β} (hf : closed_embedding f) :
  polish_space α :=
begin
  letI := upgrade_polish_space β,
  letI : metric_space α := hf.to_embedding.comap_metric_space f,
  haveI : second_countable_topology α := hf.to_embedding.second_countable_topology,
  haveI : complete_space α,
  { rw complete_space_iff_is_complete_range hf.to_embedding.to_isometry.uniform_inducing,
    apply is_closed.is_complete,
    exact hf.closed_range },
  apply_instance
end

/-- Pulling back a Polish topology under an equiv gives again a Polish topology. -/
lemma _root_.equiv.polish_space_induced [t : topological_space β] [polish_space β]
  (f : α ≃ β) :
  @polish_space α (t.induced f) :=
begin
  letI : topological_space α := t.induced f,
  exact (f.to_homeomorph_of_inducing ⟨rfl⟩).closed_embedding.polish_space,
end

/-- A closed subset of a Polish space is also Polish. -/
lemma _root_.is_closed.polish_space {α : Type*} [topological_space α] [polish_space α] {s : set α}
  (hs : is_closed s) :
  polish_space s :=
(is_closed.closed_embedding_subtype_coe hs).polish_space

/-- A sequence of type synonyms of a given type `α`, useful in the proof of
`exists_polish_space_forall_le` to endow each copy with a different topology. -/
@[nolint unused_arguments has_nonempty_instance]
def aux_copy (α : Type*) {ι : Type*} (i : ι) : Type* := α

/-- Given a Polish space, and countably many finer Polish topologies, there exists another Polish
topology which is finer than all of them. -/
lemma exists_polish_space_forall_le {ι : Type*} [countable ι]
  [t : topological_space α] [p : polish_space α]
  (m : ι → topological_space α) (hm : ∀ n, m n ≤ t) (h'm : ∀ n, @polish_space α (m n)) :
  ∃ (t' : topological_space α), (∀ n, t' ≤ m n) ∧ (t' ≤ t) ∧ @polish_space α t' :=
begin
  rcases is_empty_or_nonempty ι with hι|hι,
  { exact ⟨t, λ i, (is_empty.elim hι i : _), le_rfl, p⟩ },
  unfreezingI { inhabit ι },
  /- Consider the product of infinitely many copies of `α`, each endowed with the topology `m n`.
  This is a Polish space, as a product of Polish spaces. Pulling back this topology under the
  diagonal embedding of `α`, one gets a Polish topology which is finer than all the `m n`. -/
  letI : ∀ (n : ι), topological_space (aux_copy α n) := λ n, m n,
  haveI : ∀ (n : ι), polish_space (aux_copy α n) := λ n, h'm n,
  letI T : topological_space (Π (n : ι), aux_copy α n) := by apply_instance,
  let f : α → Π (n : ι), aux_copy α n := λ x n, x,
  -- show that the induced topology is finer than all the `m n`.
  have T_le_m : ∀ n, T.induced f ≤ m n,
  { assume n s hs,
    refine ⟨set.pi ({n} : set ι) (λ i, s), _, _⟩,
    { apply is_open_set_pi (finite_singleton _),
      assume a ha,
      rw mem_singleton_iff.1 ha,
      exact hs },
    { ext x,
      simp only [singleton_pi, mem_preimage] } },
  refine ⟨T.induced f, λ n, T_le_m n, (T_le_m default).trans (hm default), _⟩,
  -- show that the new topology is Polish, as the pullback of a Polish topology under a closed
  -- embedding.
  have A : range f = ⋂ n, {x | x n = x default},
  { ext x,
    split,
    { rintros ⟨y, rfl⟩,
      exact mem_Inter.2 (λ n, by simp only [mem_set_of_eq]) },
    { assume hx,
      refine ⟨x default, _⟩,
      ext1 n,
      symmetry,
      exact (mem_Inter.1 hx n : _) } },
  have f_closed : is_closed (range f),
  { rw A,
    apply is_closed_Inter (λ n, _),
    have C : ∀ (i : ι), continuous (λ (x : Π n, aux_copy α n), (id (x i) : α)),
    { assume i,
      apply continuous.comp _ (continuous_apply i),
      apply continuous_def.2 (λ s hs, _),
      exact hm i s hs },
    apply is_closed_eq (C n) (C default) },
  have K : @_root_.embedding _ _ (T.induced f) T f,
  { apply function.injective.embedding_induced,
    assume x y hxy,
    have : f x default = f y default, by rw hxy,
    exact this },
  have L : @closed_embedding _ _ (T.induced f) T f,
  { split,
    { exact K },
    { exact f_closed } },
  exact @closed_embedding.polish_space _ _ (T.induced f) T (by apply_instance) _ L
end

/-!
### An open subset of a Polish space is Polish

To prove this fact, one needs to construct another metric, giving rise to the same topology,
for which the open subset is complete. This is not obvious, as for instance `(0,1) ⊆ ℝ` is not
complete for the usual metric of `ℝ`: one should build a new metric that blows up close to the
boundary.
-/

section complete_copy

variables [metric_space α] {s : set α}

/-- A type synonym for a subset `s` of a metric space, on which we will construct another metric
for which it will be complete. -/
@[nolint has_nonempty_instance]
def complete_copy {α : Type*} (s : set α) : Type* := s

/-- A distance on a subset `s` of a metric space, designed to make it complete if `s` is open.
It is given by `dist' x y = dist x y + |1 / dist x sᶜ - 1 / dist y sᶜ|`, where the second term
blows up close to the boundary to ensure that Cauchy sequences for `dist'` remain well
inside `s`. -/
def has_dist_complete_copy (s : set α) : has_dist (complete_copy s) :=
⟨λ x y, dist x.1 y.1 + abs (1 / inf_dist x.1 sᶜ - 1 / inf_dist y.1 sᶜ)⟩

local attribute [instance] has_dist_complete_copy

lemma dist_complete_copy_eq (x y : complete_copy s) :
  dist x y = dist x.1 y.1 + abs (1/inf_dist x.1 sᶜ - 1 / inf_dist y.1 sᶜ) := rfl

lemma dist_le_dist_complete_copy (x y : complete_copy s) :
  dist x.1 y.1 ≤ dist x y :=
(le_add_iff_nonneg_right _).2 (abs_nonneg _)

/-- A metric space structure on a subset `s` of a metric space, designed to make it complete
if `s` is open. It is given by `dist' x y = dist x y + |1 / dist x sᶜ - 1 / dist y sᶜ|`, where the
second term blows up close to the boundary to ensure that Cauchy sequences for `dist'` remain well
inside `s`. -/
def complete_copy_metric_space (s : set α) : metric_space (complete_copy s) :=
{ dist_self := λ x, by simp [dist_complete_copy_eq],
  dist_comm := λ x y, by simp [dist_complete_copy_eq, dist_comm, abs_sub_comm],
  dist_triangle := λ x y z, calc
    dist x z = dist x.1 z.1 + abs (1 / inf_dist x.1 sᶜ - 1 / inf_dist z.1 sᶜ) : rfl
    ... ≤ (dist x.1 y.1 + dist y.1 z.1) +
      (abs (1 / inf_dist x.1 sᶜ - 1 / inf_dist y.1 sᶜ)
      + abs (1 / inf_dist y.1 sᶜ - 1 / inf_dist z.1 sᶜ)) :
    begin
      rw [← real.dist_eq, ← real.dist_eq, ← real.dist_eq],
      exact add_le_add (dist_triangle _ _ _) (dist_triangle _ _ _)
    end
    ... = dist x y + dist y z : by { rw [dist_complete_copy_eq, dist_complete_copy_eq], abel },
  eq_of_dist_eq_zero :=
  begin
    assume x y hxy,
    apply subtype.coe_injective,
    refine dist_le_zero.1 _,
    rw ← hxy,
    exact dist_le_dist_complete_copy x y
  end }

local attribute [instance] complete_copy_metric_space

/-- The identity between the type synonym `complete_copy s` (with its modified metric) and the
original subtype `s` is a homeomorphism. -/
def complete_copy_id_homeo (hs : is_open s) (h's : sᶜ.nonempty) : complete_copy s ≃ₜ s :=
{ to_fun := id,
  inv_fun := id,
  left_inv := λ x, rfl,
  right_inv := λ x, rfl,
  continuous_to_fun :=
  begin
    have : lipschitz_with 1 (λ (x : complete_copy s), (id x : s)),
    { apply lipschitz_with.mk_one,
      exact dist_le_dist_complete_copy },
    exact this.continuous,
  end,
  continuous_inv_fun :=
  begin
    apply continuous_iff_continuous_at.2 (λ x, _),
    suffices H : tendsto (λ (b : s), dist b.1 x.1
      + |1 / inf_dist b.1 sᶜ - 1 / inf_dist x.1 sᶜ|) (𝓝 x)
      (𝓝 (dist x.1 x.1 + abs (1 / inf_dist x.1 sᶜ - 1 / inf_dist x.1 sᶜ))),
    { rw [continuous_at, tendsto_iff_dist_tendsto_zero],
      simpa only [sub_self, abs_zero, add_zero, dist_self] using H },
    have I : 0 < inf_dist x.val sᶜ,
    { rw ← hs.is_closed_compl.not_mem_iff_inf_dist_pos h's,
      simp },
    apply tendsto.add,
    { apply continuous.tendsto, exact continuous_subtype_coe.dist continuous_const },
    { refine (tendsto.sub_const _ _).abs,
      refine tendsto.div tendsto_const_nhds _ I.ne',
      exact ((continuous_inf_dist_pt _).comp continuous_subtype_coe).tendsto _ }
  end }

lemma complete_space_complete_copy [complete_space α] (hs : is_open s) (h's : sᶜ.nonempty) :
  complete_space (complete_copy s) :=
begin
  refine metric.complete_of_convergent_controlled_sequences (λ n, (1/2)^n) (by simp) _,
  assume u hu,
  have A : cauchy_seq (λ n, (u n).1),
  { apply cauchy_seq_of_le_tendsto_0 (λ (n : ℕ), (1/2)^n) (λ n m N hNn hNm, _) _,
    { exact (dist_le_dist_complete_copy (u n) (u m)).trans (hu N n m hNn hNm).le },
    { exact tendsto_pow_at_top_nhds_0_of_lt_1 (by norm_num) (by norm_num) } },
  obtain ⟨x, xlim⟩ : ∃ x, tendsto (λ n, (u n).1) at_top (𝓝 x),
  { haveI : nonempty α := ⟨(u 0).1⟩,
    exact ⟨_, A.tendsto_lim⟩ },
  suffices xs : x ∈ s,
  { refine ⟨⟨x, xs⟩, _⟩,
    have L : tendsto (λ n, (id ⟨(u n).1, (u n).2⟩ : s)) at_top (𝓝 (⟨x, xs⟩)),
    { apply embedding_subtype_coe.tendsto_nhds_iff.2, exact xlim },
    convert ((complete_copy_id_homeo hs h's).symm.continuous.tendsto _).comp L,
    ext1 n,
    simp [complete_copy_id_homeo] },
  obtain ⟨C, hC⟩ : ∃ C, ∀ n, 1 / inf_dist (u n).1 sᶜ < C,
  { refine ⟨(1/2)^0 + dist (1 / inf_dist (u 0).1 sᶜ) 0, λ n, _⟩,
    calc 1 / inf_dist (u n).val sᶜ ≤ dist (1 / inf_dist (u n).val sᶜ) 0 :
      by { rw real.dist_0_eq_abs, exact le_abs_self _ }
    ... ≤ dist (1 / inf_dist (u n).1 sᶜ) (1 / inf_dist (u 0).1 sᶜ)
          + dist (1 / inf_dist (u 0).1 sᶜ) 0 : dist_triangle _ _ _
    ... ≤ (dist (u n).1 (u 0).1 + dist (1 / inf_dist (u n).1 sᶜ) (1 / inf_dist (u 0).1 sᶜ))
          + dist (1 / inf_dist (u 0).1 sᶜ) 0 :
      add_le_add (le_add_of_nonneg_left dist_nonneg) le_rfl
    ... = dist (u n) (u 0) +  dist (1 / inf_dist (u 0).1 sᶜ) 0 : rfl
    ... < (1/2)^0 + dist (1 / inf_dist (u 0).1 sᶜ) 0 :
      add_lt_add_right (hu 0 n 0 (zero_le _) le_rfl) _ },
  have Cpos : 0 < C,
  { apply lt_of_le_of_lt _ (hC 0),
    simp [inf_dist_nonneg] },
  have I : ∀ n, 1/C ≤ inf_dist (u n).1 sᶜ,
  { assume n,
    have : 0 < inf_dist (u n).val sᶜ,
    { apply (hs.is_closed_compl.not_mem_iff_inf_dist_pos h's).1, simp },
    rw div_le_iff' Cpos,
    exact (div_le_iff this).1 (hC n).le },
  have I' : 1/C ≤ inf_dist x sᶜ,
  { have : tendsto (λ n, inf_dist (u n).1 sᶜ) at_top (𝓝 (inf_dist x sᶜ)) :=
      ((continuous_inf_dist_pt sᶜ).tendsto x).comp xlim,
    exact ge_of_tendsto' this I },
  suffices : x ∉ sᶜ, by simpa,
  apply (hs.is_closed_compl.not_mem_iff_inf_dist_pos h's).2 (lt_of_lt_of_le _ I'),
  simp [Cpos],
end

/-- An open subset of a Polish space is also Polish. -/
lemma _root_.is_open.polish_space {α : Type*} [topological_space α] [polish_space α] {s : set α}
  (hs : is_open s) :
  polish_space s :=
begin
  rcases eq_empty_or_nonempty sᶜ with h's|h's,
  { simp at h's,
    apply is_closed.polish_space,
    rw h's,
    exact is_closed_univ },
  { letI := upgrade_polish_space α,
    haveI : complete_space (complete_copy s) := complete_space_complete_copy hs h's,
    haveI : second_countable_topology (complete_copy s) :=
      (complete_copy_id_homeo hs h's).embedding.second_countable_topology,
    exact (complete_copy_id_homeo hs h's).symm.closed_embedding.polish_space }
end

end complete_copy

/-! ### Clopenable sets in Polish spaces -/

/-- A set in a topological space is clopenable if there exists a finer Polish topology for which
this set is open and closed. It turns out that this notion is equivalent to being Borel-measurable,
but this is nontrivial (see `is_clopenable_iff_measurable_set`). -/
def is_clopenable [t : topological_space α] (s : set α) : Prop :=
∃ (t' : topological_space α), t' ≤ t ∧ @polish_space α t' ∧ is_closed[t'] s ∧ is_open[t'] s

/-- Given a closed set `s` in a Polish space, one can construct a finer Polish topology for
which `s` is both open and closed. -/
lemma _root_.is_closed.is_clopenable [topological_space α] [polish_space α] {s : set α}
  (hs : is_closed s) : is_clopenable s :=
begin
  /- Both sets `s` and `sᶜ` admit a Polish topology. So does their disjoint union `s ⊕ sᶜ`.
  Pulling back this topology by the canonical bijection with `α` gives the desired Polish
  topology in which `s` is both open and closed. -/
  haveI : polish_space s := hs.polish_space,
  let t : set α := sᶜ,
  haveI : polish_space t := hs.is_open_compl.polish_space,
  let f : α ≃ (s ⊕ t) := (equiv.set.sum_compl s).symm,
  letI T : topological_space (s ⊕ t) := by apply_instance,
  let t' : topological_space α := T.induced f,
  let g := @equiv.to_homeomorph_of_inducing  _ _ t' T f { induced := rfl },
  have A : g ⁻¹' (range (sum.inl : s → s ⊕ t)) = s,
  { ext x,
    by_cases h : x ∈ s,
    { simp only [equiv.set.sum_compl_symm_apply_of_mem, h, mem_preimage, equiv.to_fun_as_coe,
        mem_range_self, equiv.to_homeomorph_of_inducing_apply]},
    { simp only [equiv.set.sum_compl_symm_apply_of_not_mem, h, not_false_iff, mem_preimage,
        equiv.to_homeomorph_of_inducing_apply, equiv.to_fun_as_coe, mem_range, exists_false]} },
  refine ⟨t', _, f.polish_space_induced, _, _⟩,
  { assume u hu,
    change ∃ (s' : set (↥s ⊕ ↥t)), T.is_open s' ∧ f ⁻¹' s' = u,
    refine ⟨f.symm ⁻¹' u, _, by simp only [equiv.symm_symm, equiv.symm_preimage_preimage]⟩,
    refine is_open_sum_iff.2 ⟨_, _⟩,
    { have : is_open ((coe : s → α) ⁻¹' u) := is_open.preimage continuous_subtype_coe hu,
      have : sum.inl ⁻¹' (⇑(f.symm) ⁻¹' u) = (coe : s → α) ⁻¹' u,
        by { ext x, simp only [equiv.symm_symm, mem_preimage, equiv.set.sum_compl_apply_inl] },
      rwa this },
    { have : is_open ((coe : t → α) ⁻¹' u) := is_open.preimage continuous_subtype_coe hu,
      have : sum.inr ⁻¹' (⇑(f.symm) ⁻¹' u) = (coe : t → α) ⁻¹' u,
        by { ext x, simp only [equiv.symm_symm, mem_preimage, equiv.set.sum_compl_apply_inr] },
      rwa this } },
  { have : is_closed[t'] (g ⁻¹' (range (sum.inl : s → s ⊕ t))),
    { apply is_closed.preimage,
      { exact @homeomorph.continuous _ _ t' _ g },
      { exact is_closed_range_inl } },
    convert this,
    exact A.symm },
  { have : is_open[t'] (g ⁻¹' (range (sum.inl : s → s ⊕ t))),
    { apply is_open.preimage,
      { exact @homeomorph.continuous _ _ t' _ g },
      { exact is_open_range_inl } },
    convert this,
    exact A.symm },
end

lemma is_clopenable.compl [topological_space α] {s : set α} (hs : is_clopenable s) :
  is_clopenable sᶜ :=
begin
  rcases hs with ⟨t, t_le, t_polish, h, h'⟩,
  exact ⟨t, t_le, t_polish, @is_open.is_closed_compl α t s h', @is_closed.is_open_compl α t s h⟩,
end

lemma _root_.is_open.is_clopenable [topological_space α] [polish_space α] {s : set α}
  (hs : is_open s) : is_clopenable s :=
by simpa using hs.is_closed_compl.is_clopenable.compl

lemma is_clopenable.Union [t : topological_space α] [polish_space α] {s : ℕ → set α}
  (hs : ∀ n, is_clopenable (s n)) :
  is_clopenable (⋃ n, s n) :=
begin
  choose m mt m_polish m_closed m_open using hs,
  obtain ⟨t', t'm, -, t'_polish⟩ :
    ∃ (t' : topological_space α), (∀ (n : ℕ), t' ≤ m n) ∧ (t' ≤ t) ∧ @polish_space α t' :=
      exists_polish_space_forall_le m mt m_polish,
  have A : is_open[t'] (⋃ n, s n),
  { apply is_open_Union,
    assume n,
    apply t'm n,
    exact m_open n },
  obtain ⟨t'', t''_le, t''_polish, h1, h2⟩ :
    ∃ (t'' : topological_space α), t'' ≤ t' ∧ @polish_space α t''
      ∧ is_closed[t''] (⋃ n, s n) ∧ is_open[t''] (⋃ n, s n) :=
        @is_open.is_clopenable α t' t'_polish _ A,
  exact ⟨t'', t''_le.trans ((t'm 0).trans (mt 0)), t''_polish, h1, h2⟩,
end

end polish_space
