/-
Copyright (c) 2022 Anand Rao, Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anand Rao, Rémi Bottinelli
-/
import combinatorics.simple_graph.ends.defs
import category_theory.cofiltered_system

/-!
# Properties of the ends of graphs

This file is meant to contain results about the ends of (locally finite connected) graphs.

-/

variables {V : Type*} (G : simple_graph V)

namespace simple_graph

instance empty_ends [finite V] : is_empty G.end :=
⟨ begin
    rintro ⟨s, _⟩,
    casesI nonempty_fintype V,
    obtain ⟨v, h⟩ := (s $ opposite.op finset.univ).nonempty,
    exact set.disjoint_iff.mp (s _).disjoint_right
      ⟨by simp only [opposite.unop_op, finset.coe_univ], h⟩,
  end ⟩

/--
The `component_compl`s chosen by an end are all infinite.
-/
lemma end_component_compl_infinite (e : G.end) (K : (finset V)ᵒᵖ) : (e.val K).supp.infinite :=
begin
  apply (e.val K).infinite_iff_in_all_ranges.mpr (λ L h, _),
  change opposite.unop K ⊆ opposite.unop (opposite.op L) at h,
  exact ⟨e.val (opposite.op L), (e.prop (category_theory.op_hom_of_le h))⟩,
end

instance compononent_compl_functor_nonempty_of_infinite  [Vi : infinite V] (K : (finset V)ᵒᵖ) :
  nonempty (G.component_compl_functor.obj K) := G.component_compl_nonempty_of_infinite K.unop

instance component_compl_functor_finite [Glf : locally_finite G] [fact $ preconnected G]
  (K : (finset V)ᵒᵖ) : finite (G.component_compl_functor.obj K) := G.component_compl_finite K.unop

lemma component_compl_functor_is_mittag_leffler [locally_finite G] [fact G.preconnected] :
  G.component_compl_functor.is_mittag_leffler :=
by classical; exact category_theory.functor.is_mittag_leffler_of_exists_finite_range _
                (λ K, ⟨K, 𝟙 K, set.to_finite _⟩)

instance component_compl_functor_to_eventual_ranges_fintype
  [category_theory.is_cofiltered_or_empty (finset V)ᵒᵖ]
  {G : simple_graph V} [locally_finite G] [fact G.preconnected] (K : (finset V)ᵒᵖ) :
  finite (G.component_compl_functor.to_eventual_ranges.obj K) :=
category_theory.functor.to_eventual_ranges_finite _ _

instance component_compl_functor_to_eventual_ranges_nonempty_of_infinite
  [category_theory.is_cofiltered_or_empty (finset V)ᵒᵖ]
  (G : simple_graph V) [G.locally_finite] [fact G.preconnected]
  [infinite V] (K : (finset V)ᵒᵖ) :
  nonempty (G.component_compl_functor.to_eventual_ranges.obj K) :=
begin
  apply category_theory.functor.to_eventual_ranges_nonempty,
  apply component_compl_functor_is_mittag_leffler,
end

/--
A locally finite preconnected infinite graph has at least one end.
-/
lemma nonempty_ends_of_infinite [Glf : locally_finite G] [fact $ preconnected G] [Vi : infinite V] :
  G.end.nonempty :=
by classical; apply nonempty_sections_of_finite_inverse_system G.component_compl_functor

end simple_graph
