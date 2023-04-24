/-
Copyright (c) 2023 Felix Weilacher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Weilacher
-/
import measure_theory.constructions.polish
import topology.perfect

/-!
# The Borel Isomorphism Theorem

In this file we prove the Borel isomorphism theorem.

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

lemma second_countable_of_polish
  [topological_space α] [h : polish_space α] : second_countable_topology α :=
h.second_countable

instance polish_of_countable [h : countable α] [topological_space α] [discrete_topology α]
  : polish_space α :=
begin
  rw countable_iff_exists_injective at h,
  cases h with f hf,
  have : closed_embedding f, {
    apply closed_embedding_of_continuous_injective_closed,
    { apply continuous_of_discrete_topology},
    { exact hf,},
    intros t ht,
    apply is_closed_discrete,
  },
  apply this.polish_space,
end

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
  obtain ⟨g, gmeas, ginj⟩ := measurable_space.measurable_inj_cantor_of_countable_generated α,
  exact ⟨borel_schroeder_bernstein fcts.measurable finj gmeas ginj⟩,
end

/-- The **Borel Isomorphism Theorem**: Any two uncountable Polish spaces are Borel isomorphic.-/
def borel_equiv_of_uncountable_of_uncountable (hα : ¬countable α) (hβ : ¬countable β ) : α ≃ᵐ β :=
(borel_nat_bool_equiv_of_uncountable hα).symm.trans (borel_nat_bool_equiv_of_uncountable hβ)

/-- The **Borel Isomorphism Theorem**: If two Polish spaces have the same cardinality,
they are Borel isomorphic.-/
def equiv.borel_equiv (e : α ≃ β) : α ≃ᵐ β :=
begin
  by_cases h : countable α,
  { letI := h,
    letI := countable.of_equiv α e,
    use e; apply measurable_of_countable, },
  apply borel_equiv_of_uncountable_of_uncountable,
  { exact h },
  rwa e.countable_iff at h,
end
