/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

-- TODO: rename this file

import graph_theory.basic
import measure_theory.probability_mass_function
import .to_mathlib

/-!
# Graphs with high chromatic number and girth
-/

open_locale classical
noncomputable theory

universe variables v v₁ v₂ v₃ u u₁ u₂ u₃

variables {V : Type u}

-- def graph.weighted_edge_count [fintype V] (G : graph V) (p : nnreal) (hp : p ≤ 1) :
--   nnreal :=
-- finset.prod finset.univ $ λ (xy : V × V),
-- if xy.1 ~[G] xy.2 then p else (1 - p)

@[ext]
lemma graph.ext (G₁ G₂ : graph V) (h : ∀ x y, (x ~[G₁] y) ↔ (x ~[G₂] y)) : G₁ = G₂ :=
begin
  repeat {cases G₁ with G₁, cases G₂ with G₂},
  have : G₁ = G₂, { ext, apply h },
  cases this, congr, ext, refl,
end

def graph_from_sets (E : set ({s : finset V // s.card = 1 ∨ s.card = 2})) : graph V :=
{ edge := assume x y, ∃ e ∈ E, ({x,y} : finset V) = e,
  symm :=
  begin
    rintro x y ⟨e, he, h⟩,
    refine ⟨e, he, _⟩,
    rw ← h,
    finish [finset.ext],
  end }
.

lemma graph_from_sets.aux {x y : V} : @finset.card V {x, y} = 1 ∨ @finset.card V {x, y} = 2 :=
begin
  classical,
  by_cases h : x = y,
  { simp only [h, finset.insert_singleton_self_eq', true_or, eq_self_iff_true,
      finset.singleton_eq_singleton, finset.card_singleton], },
  { right, rw finset.card_insert_of_not_mem, { refl },
    simp only [ne.symm h, not_false_iff, finset.mem_singleton, finset.singleton_eq_singleton], }
end

lemma graph_from_sets_edge_iff (E : set ({s : finset V // s.card = 1 ∨ s.card = 2})) (x y : V) :
  (x ~[graph_from_sets E] y) ↔
  ((⟨{x, y}, graph_from_sets.aux⟩ : {s : finset V // s.card = 1 ∨ s.card = 2}) ∈ E) :=
begin
  split,
  { rintro ⟨⟨s, hs⟩, hsE, h⟩, convert hsE },
  { intro h, exact ⟨_, h, rfl⟩ }
end

lemma graph_from_sets.aux' (s : finset V) (hs : s.card = 1 ∨ s.card = 2) :
  ∃ (x y : V), s = {x, y} :=
begin
  cases hs,
  { rcases finset.card_eq_one.mp hs with ⟨x, hx⟩,
    use [x, x], simp only [hx, finset.insert_singleton_self_eq', finset.singleton_eq_singleton] },
  { rw finset.card_eq_succ at hs,
    rcases hs with ⟨y, t, hy, hyt, ht⟩,
    rcases finset.card_eq_one.mp ht with ⟨x, hx⟩,
    use [x, y], finish, }
end

example (X : Type*) (a b c d : X) (h : ({a, b} : finset X) = {c, d}) :
  (a = c ∧ b = d) ∨ (a = d ∧ b = c) := sorry

lemma graph_from_sets_bijective : function.bijective (@graph_from_sets V) :=
begin
  split,
  { assume E₁ E₂ h,
    apply set.ext,
    rintro ⟨s, hs⟩,
    rcases graph_from_sets.aux' s hs with ⟨x, y, rfl⟩,
    erw ← graph_from_sets_edge_iff E₁ x y,
    erw ← graph_from_sets_edge_iff E₂ x y,
    rw h, },
  { assume G,
    let E : set {s : finset V // s.card = 1 ∨ s.card = 2} :=
      λ s, ∃ (x y : V), (x ~[G] y) ∧ s.1 = {x, y},
    use E,
    ext x y,
    rw graph_from_sets_edge_iff,
    split,
    { rintro ⟨a, b, hab, H⟩,
      suffices : (x = a ∧ y = b) ∨ (x = b ∧ y = a),
      { rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩,
        { exact hab },
        { exact G.symm hab } },
      rw classical.or_iff_not_imp_right,
      simp at H,
       },
    { intro e, use [x, y, e] }
  }
end

abbreviation random_graph (V : Type u) := pmf (graph V)

namespace random_graph

/-- The Erdős–Rényi model for random graphs. -/
def with_edge_prob (V : Type u) [fintype V] (p : nnreal) (hp : p ≤ 1) :
  random_graph V :=
pmf.map (graph_from_sets ∘ coe) $ pmf.binomial {s : finset V // s.card = 1 ∨ s.card = 2} p hp


end random_graph
