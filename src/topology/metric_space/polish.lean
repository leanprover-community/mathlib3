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

instance polish_space.pi {E : ℕ → Type*} [∀ n, topological_space (E n)] [∀ n, polish_space (E n)] :
  polish_space (Π n, E n) :=
begin
  letI : ∀ n, metric_space (E n) := λ n, polish_space_metric (E n),
  haveI : ∀ n, complete_space (E n) := λ n, complete_polish_space_metric (E n),
  haveI : ∀ n, second_countable_topology (E n) := λ n, polish_space.second_countable (E n),
  letI m : metric_space (Π n, E n) := pi_nat_nondiscrete.metric_space E,
  apply_instance,
end

/-- Without this instance, `polish_space (ℕ → ℕ)` is not found by typeclass inference. -/
instance polish_space.fun {F : Type*} [topological_space F] [polish_space F] :
  polish_space (ℕ → F) :=
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
