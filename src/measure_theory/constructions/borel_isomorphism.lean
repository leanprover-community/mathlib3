/-
Copyright (c) 2023 Felix Weilacher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Weilacher
-/
import measure_theory.constructions.polish
import topology.perfect

/-!
# The Borel Isomorphism Theorem

In this file we prove several versions of the Borel isomorphism theorem.

## Main Statements

* `borel_schroeder_bernstein` : If two Polish spaces admit Borel injections to eachother,
then they are Borel isomorphic.
* `borel_equiv_of_uncountable_of_uncountable` : Any two uncountable Polish spaces
are Borel isomorphic.
* `equiv.borel_equiv` : Any two Polish spaces of the same cardinality are Borel isomorphic.

## References

* [kechris1995] (Chapter 15)

## Tags

polish space, standard borel space

-/

variables {α β : Type*}

open topological_space set

/-Note: Perhaps this should be in topology/instances/discrete or topology/metric_space/polish.
It also seems likely there is a simpler proof. -/
@[priority 50]
instance polish_of_countable [h : countable α] [topological_space α] [discrete_topology α]
  : polish_space α :=
begin
  obtain ⟨f, hf⟩ := h.exists_injective_nat,
  have : closed_embedding f,
  { apply closed_embedding_of_continuous_injective_closed continuous_of_discrete_topology hf,
    exact λ t _, is_closed_discrete _, },
  exact this.polish_space,
end

/-Note: This is to avoid a loop in TC inference. When ported to Lean 4, this will not
be necessary, and `second_countable_of_polish` should probably
just be added as an instance soon after the definition of `polish_space`.-/
private lemma second_countable_of_polish
  [topological_space α] [h : polish_space α] : second_countable_topology α :=
h.second_countable

local attribute [-instance] polish_space_of_complete_second_countable
local attribute [instance] second_countable_of_polish

variables [topological_space α] [polish_space α] [topological_space β] [polish_space β]
variables [measurable_space α] [borel_space α] [measurable_space β] [borel_space β]

noncomputable theory

/-- If two Polish spaces admit Borel measurable injections to one another,
then they are Borel isomorphic.-/
def borel_schroeder_bernstein
  {f : α → β} {g : β → α}
  (fmeas : measurable f) (finj : function.injective f)
  (gmeas : measurable g) (ginj : function.injective g) :
  α ≃ᵐ β :=
(fmeas.measurable_embedding finj).schroeder_bernstein (gmeas.measurable_embedding ginj)

/-- Any uncountable Polish space is Borel isomorphic to the Cantor space `ℕ → bool`.-/
def borel_nat_bool_equiv_of_uncountable (h : ¬countable α) : (ℕ → bool) ≃ᵐ α :=
begin
  apply nonempty.some,
  obtain ⟨f, -, fcts, finj⟩ := is_closed_univ.exists_nat_bool_injection_of_uncountable
    (by rwa [← countable_coe_iff ,(equiv.set.univ _).countable_iff]),
  obtain ⟨g, gmeas, ginj⟩ := measurable_space.measurable_inj_cantor_of_countably_generated α,
  exact ⟨borel_schroeder_bernstein fcts.measurable finj gmeas ginj⟩,
end

/-- The **Borel Isomorphism Theorem**: Any two uncountable Polish spaces are Borel isomorphic.-/
def measurable_equiv_of_uncountable (hα : ¬ countable α) (hβ : ¬ countable β ) : α ≃ᵐ β :=
(measurable_equiv_nat_bool_of_uncountable hα).trans
  (measurable_equiv_nat_bool_of_uncountable hβ).symm

/-- The **Borel Isomorphism Theorem**: If two Polish spaces have the same cardinality,
they are Borel isomorphic.-/
def equiv.measurable_equiv (e : α ≃ β) : α ≃ᵐ β :=
begin
  by_cases h : countable α,
  { letI := h,
    letI := countable.of_equiv α e,
    use e; apply measurable_of_countable, },
  apply borel_equiv_of_uncountable_of_uncountable,
  { exact h },
  rwa e.countable_iff at h,
end
