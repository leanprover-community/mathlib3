/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import topology.metric_space.pi_nat

/-!
# Polish spaces

-/

noncomputable theory
open_locale classical topological_space filter
open topological_space set metric filter function


/-- A Polish space is a topological space with second countable topology, that can be endowed
with a metric for which it is complete.
We register an instance from complete second countable metric space to polish space, and not the
other way around as this is the most common use case.

To endow a Polish space with a complete metric space structure, use
```
letI : metric_space α := polish_space_metric α,
haveI : complete_space α := complete_polish_space_metric α,
haveI : second_countable_topology α := polish_space.second_countable α,
```
-/
class polish_space (α : Type*) [h : topological_space α] : Prop :=
(second_countable [] : second_countable_topology α)
(complete : ∃ m : metric_space α, m.to_uniform_space.to_topological_space = h ∧
  @complete_space α m.to_uniform_space)

@[priority 100]
instance polish_space_of_complete_second_countable
  {α : Type*} [m : metric_space α] [h : second_countable_topology α] [h' : complete_space α] :
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

/-- A countable product of Polish spaces is Polish. -/
instance polish_space.pi {E : ℕ → Type*} [∀ n, topological_space (E n)] [∀ n, polish_space (E n)] :
  polish_space (Π n, E n) :=
begin
  letI : ∀ n, metric_space (E n) := λ n, polish_space_metric (E n),
  haveI : ∀ n, complete_space (E n) := λ n, complete_polish_space_metric (E n),
  haveI : ∀ n, second_countable_topology (E n) := λ n, polish_space.second_countable (E n),
  letI m : metric_space (Π n, E n) := pi_nat_nondiscrete.metric_space E,
  apply_instance,
end

/-- A countable union of Polish spaces is Polish-/
instance polish_space.sigma
  {E : ℕ → Type*} [∀ n, topological_space (E n)] [∀ n, polish_space (E n)] :
  polish_space (Σ n, E n) :=
begin
  letI : ∀ n, metric_space (E n) := λ n, polish_space_metric (E n),
  haveI : ∀ n, complete_space (E n) := λ n, complete_polish_space_metric (E n),
  haveI : ∀ n, second_countable_topology (E n) := λ n, polish_space.second_countable (E n),

  letI : topological_space (Σ n, E n) := sigma.topological_space,
  sorry,

end

/-- Without this instance, `polish_space (ℕ → ℕ)` is not found by typeclass inference. -/
instance polish_space.fun {α : Type*} [topological_space α] [polish_space α] :
  polish_space (ℕ → α) :=
by apply_instance

/-- Any nonempty Polish space is the continuous image of the fundamental space `ℕ → ℕ`. -/
lemma exists_nat_nat_continuous_surjective_of_polish_space
  (α : Type*) [topological_space α] [polish_space α] [nonempty α] :
  ∃ (f : (ℕ → ℕ) → α), continuous f ∧ surjective f :=
begin
  letI : metric_space α := polish_space_metric α,
  haveI : complete_space α := complete_polish_space_metric α,
  haveI : second_countable_topology α := polish_space.second_countable α,
  exact exists_nat_nat_continuous_surjective_of_complete_space α
end

lemma homeomorph.polish_space {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [polish_space α] (f : α ≃ₜ β) : polish_space β :=
begin
  letI : metric_space α := polish_space_metric α,
  haveI : complete_space α := complete_polish_space_metric α,
  haveI : second_countable_topology α := polish_space.second_countable α,
  refine ⟨f.symm.embedding.second_countable_topology, _⟩,
end

/-- A closed subset of a Polish space is also Polish. -/
lemma is_closed.polish_space {α : Type*} [topological_space α] [polish_space α] {s : set α}
  (hs : is_closed s) :
  polish_space s :=
begin
  letI : metric_space α := polish_space_metric α,
  haveI : complete_space α := complete_polish_space_metric α,
  haveI : second_countable_topology α := polish_space.second_countable α,
  haveI : complete_space s,
  { rw complete_space_coe_iff_is_complete,
    exact hs.is_complete },
  apply_instance,
end

section complete_copy

variables {α : Type*} [metric_space α] {s : set α}

def complete_copy (s : set α) : Type* := s

def has_dist_complete_copy (s : set α) : has_dist (complete_copy s) :=
⟨λ x y, dist x.1 y.1 + abs (1 / inf_dist x.1 sᶜ - 1 / inf_dist y.1 sᶜ)⟩

local attribute [instance] has_dist_complete_copy

lemma dist_complete_copy_eq (x y : complete_copy s) :
  dist x y = dist x.1 y.1 + abs (1/inf_dist x.1 sᶜ - 1 / inf_dist y.1 sᶜ) := rfl

lemma dist_le_dist_complete_copy (x y : complete_copy s) :
  dist x.1 y.1 ≤ dist x y :=
(le_add_iff_nonneg_right _).2 (abs_nonneg _)

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
lemma is_open.polish_space {α : Type*} [topological_space α] [polish_space α] {s : set α}
  (hs : is_open s) :
  polish_space s :=
begin
  rcases eq_empty_or_nonempty sᶜ with h's|h's,
  { simp at h's,
    apply is_closed.polish_space,
    rw h's,
    exact is_closed_univ },
  { letI : metric_space α := polish_space_metric α,
    haveI : complete_space α := complete_polish_space_metric α,
    haveI : second_countable_topology α := polish_space.second_countable α,
    haveI : complete_space (complete_copy s) := complete_space_complete_copy hs h's,
    haveI : second_countable_topology (complete_copy s) :=
      (complete_copy_id_homeo hs h's).embedding.second_countable_topology,
    exact (complete_copy_id_homeo hs h's).polish_space }
end

end complete_copy



/-- Given a closed set `s` in a Polish space, one can construct a new topology with the same Borel
sets for which `s` is both open and closed. -/
lemma frou {α : Type*} (t : topological_space α) (hp : @polish_space α t) (s : set α)
  (hs : @is_closed α t s) :
  ∃ (t' : topological_space α) (ht' : @polish_space α t'), @is_closed α t' s ∧ @is_open α t' s
    ∧ t ≤ t' :=
begin

end

#exit


namespace measure_theory

variables {α : Type*} [topological_space α]

/-- An analytic set is a set which is the continuous image of some Polish space. There are several
equivalent characterizations of this definition. For the definition, we pick one that avoids
universe issues: a set is analytic if and only if it is a continuous image of `ℕ → ℕ` (or if it
is empty). The above more usual characterization is given
in `analytic_set_iff_exists_polish_space_range`.

Warning: these are analytic sets in the context of descriptive set theory (which is why they are
registered in the namespace `measure_theory`). They have nothing to do with analytic sets in the
context of complex analysis. -/
@[irreducible] def analytic_set (s : set α) : Prop :=
s = ∅ ∨ ∃ (f : (ℕ → ℕ) → α), continuous f ∧ range f = s

lemma analytic_set_empty :
  analytic_set (∅ : set α) :=
by { rw analytic_set, exact or.inl rfl }

lemma analytic_set_of_polish_space_range
  {β : Type*} [topological_space β] [polish_space β] (f : β → α) {s : set α}
  (f_cont : continuous f) (hf : range f = s) :
  analytic_set s :=
begin
  casesI is_empty_or_nonempty β,
  { have : s = ∅, by rw [← hf, range_eq_empty],
    rw [this, analytic_set],
    exact or.inl rfl },
  { rw analytic_set,
    obtain ⟨g, g_cont, hg⟩ : ∃ (g : (ℕ → ℕ) → β), continuous g ∧ surjective g :=
      exists_nat_nat_continuous_surjective_of_polish_space β,
    right,
    refine ⟨f ∘ g, f_cont.comp g_cont, _⟩,
    rwa hg.range_comp }
end

/-- A set is analytic if and only if it is the continuous image of some Polish space. -/
theorem analytic_set_iff_exists_polish_space_range {s : set α} :
  analytic_set s ↔ ∃ (β : Type) (h : topological_space β) (h' : @polish_space β h) (f : β → α),
    @continuous _ _ h _ f ∧ range f = s :=
begin
  split,
  { assume h,
    rw analytic_set at h,
    cases h,
    { refine ⟨empty, by apply_instance, by apply_instance, empty.elim, continuous_bot, _⟩,
      rw h,
      exact range_eq_empty _ },
    { exact ⟨ℕ → ℕ, by apply_instance, by apply_instance, h⟩ } },
  { rintros ⟨β, h, h', f, f_cont, f_range⟩,
    resetI,
    exact analytic_set_of_polish_space_range f f_cont f_range }
end

/-- A countable intersection of analytic sets is analytic. -/
theorem analytic_set.Inter [t2_space α] {s : ℕ → set α} (hs : ∀ n, analytic_set (s n)) :
  analytic_set (⋂ n, s n) :=
begin
  /- For the proof, write each `s n` as the continuous image under a map `f n` of a
  Polish space `β n`. The product space `γ = Π n, β n` is also Polish, and so is the subset
  `t` of sequences `x n` for which `f n (x n)` is independent of `n`. The set `t` is Polish, and the
  range of `x ↦ f 0 (x 0)` on `t` is exactly `⋂ n, s n`, so this set is analytic. -/
  choose β hβ h'β f f_cont f_range using λ n, analytic_set_iff_exists_polish_space_range.1 (hs n),
  resetI,
  let γ := Π n, β n,
  let t : set γ := ⋂ n, {x | f n (x n) = f 0 (x 0)},
  have t_closed : is_closed t,
  { apply is_closed_Inter,
    assume n,
    exact is_closed_eq ((f_cont n).comp (continuous_apply n))
      ((f_cont 0).comp (continuous_apply 0)) },
  haveI : polish_space t := t_closed.polish_space,
  let F : t → α := λ x, f 0 ((x : γ) 0),
  have F_cont : continuous F := (f_cont 0).comp ((continuous_apply 0).comp continuous_subtype_coe),
  have F_range : range F = ⋂ (n : ℕ), s n,
  { apply subset.antisymm,
    { rintros y ⟨x, rfl⟩,
      apply mem_Inter.2 (λ n, _),
      have : f n ((x : γ) n) = F x := (mem_Inter.1 x.2 n : _),
      rw [← this, ← f_range n],
      exact mem_range_self _ },
    { assume y hy,
      have A : ∀ n, ∃ (x : β n), f n x = y,
      { assume n,
        rw [← mem_range, f_range n],
        exact mem_Inter.1 hy n },
      choose x hx using A,
      have xt : x ∈ t,
      { apply mem_Inter.2 (λ n, _),
        simp [hx] },
        refine ⟨⟨x, xt⟩, _⟩,
        exact hx 0 } },
  exact analytic_set_of_polish_space_range F F_cont F_range,
end

/-- A countable union of analytic sets is analytic. -/
theorem analytic_set.Union {s : ℕ → set α} (hs : ∀ n, analytic_set (s n)) :
  analytic_set (⋃ n, s n) :=
begin
  /- For the proof, write each `s n` as the continuous image under a map `f n` of a
  Polish space `β n`. The union space `γ = Σ n, β n` is also Polish, and the map `F : γ → α` which
  coincides with `f n` on `β n` sends it to `⋃ n, s n`. -/
  choose β hβ h'β f f_cont f_range using λ n, analytic_set_iff_exists_polish_space_range.1 (hs n),
  resetI,
  let γ := Σ n, β n,
  let F : γ → α := by { rintros ⟨n, x⟩, exact f n x },
  have F_cont : continuous F := continuous_sigma f_cont,
  have F_range : range F = ⋃ n, s n,
  { rw [range_sigma_eq_Union_range],
    congr,
    ext1 n,
    rw ← f_range n },
  exact analytic_set_of_polish_space_range F F_cont F_range,
end

end measure_theory
