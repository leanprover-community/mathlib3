/-
Copyright (c) 2020 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton
-/

import ..todo
import topology.separation

/-!
A formal roadmap for the shrinking lemma for local finite countable covers.

It contains the statement of the lemma, and an informal sketch of the proof,
along with references.

Any contributor should feel welcome to contribute a formal proof. When this happens,
we should also consider preserving the current file as an exemplar of a formal roadmap.
-/

open set zorn

universes u v

structure shrinking_lemma_data (X : Type*) [topological_space X] :=
(base :  set (set X))
(open_base : ∀ s ∈ base, is_open s)
(shrink_base : ∀ (s ∈ base) t, is_open t → s ∪ t = univ →
  ∃ s' ∈ base, closure s' ⊆ s ∧ s' ∪ t = univ)

namespace shrinking_lemma_data

def of_normal (X : Type*) [topological_space X] [normal_space X] :
  shrinking_lemma_data X :=
{ base := {s | is_open s},
  open_base := λ s, id,
  shrink_base := λ s hs t ht hst,
    have disjoint sᶜ tᶜ, by rwa [set.disjoint_iff_inter_eq_empty, ← compl_union, compl_empty_iff],
    let ⟨s', t', h⟩ := normal_separation _ _ (is_closed_compl_iff.2 hs) (is_closed_compl_iff.2 ht) this }
  
variables {X : Type*} [topological_space X] (B : shrinking_lemma_data X)

structure partial_refinement {ι : Type*} (

/-- A point-finite open cover of a closed subset of a normal space can be "shrunk" to a new open
cover so that the closure of each new open set is contained in the corresponding original open
set. -/
lemma shrinking_lemma {X : Type u} [topological_space X] [normal_space X]
  {s : set X} (hs : is_closed s) {α : Type v} (u : α → set X) (uo : ∀ a, is_open (u a))
  (uf : ∀ x, finite {a | x ∈ u a}) (su : s ⊆ Union u) :
  ∃ v : α → set X, s ⊆ Union v ∧ ∀ a, is_open (v a) ∧ closure (v a) ⊆ u a :=
begin
  classical,
  set T := Σ t : set α, {v : α → set X // s ⊆ Union v ∧ (∀ a, is_open (v a)) ∧
    (∀ a ∈ t, closure (v a) ⊆ u a) ∧ (∀ a ∉ t, v a = u a)},
  set r : T → T → Prop := λ tv tv', tv.1 ⊆ tv'.1 ∧ ∀ a ∈ tv.1, tv.2.1 a = tv'.2.1 a,
  haveI : is_refl T r := ⟨λ tv, ⟨subset.refl _, λ a ha, rfl⟩⟩,
  have eq_of_chain : ∀ {c} (hc : chain r c) {tv tv' : T} (h : tv ∈ c) (h' : tv' ∈ c)
    {a} (ha : a ∈ tv.1) (ha' : a ∈ tv'.1), tv.2.1 a = tv'.2.1 a,
  { intros c hc tv tv' h h' a ha ha',
    rcases hc.total_of_refl h h' with (h|h'),
    exacts [h.2 _ ha, (h'.2 _ ha').symm] },
  have r_chain : ∀ c, chain r c → ∃ ub, ∀ a ∈ c, r a ub,
  { intros c hc,
    set I : set α := ⋃ tv ∈ c, sigma.fst tv,
    set v : α → set X := λ a, if h : a ∈ I  then (mem_bUnion_iff.1 h).some.2.1 a else u a,
    have v_of_mem : ∀ (tv : T) (htv : tv ∈ c) (a ∈ tv.1), v a = tv.2.1 a,
    { intros tv htv a ha,
      have : a ∈ I, from mem_bUnion htv ha,
      simp only [v], rw [dif_pos this],
      exact eq_of_chain hc (mem_bUnion_iff.1 this).some_spec.fst htv
        (mem_bUnion_iff.1 this).some_spec.snd ha },
    have v_of_not_mem : ∀ a ∉ I, v a = u a, from λ a ha, dif_neg ha,
    have mem_cases : ∀ a, (∃ (tv : T) (htv : tv ∈ c), a ∈ tv.1) ∨ a ∉ I,
    { refine λ a, (em (a ∈ I)).imp _ id, simp only [I, mem_Union], exact id },
    refine ⟨⟨I, ⟨v, _, _, _, _⟩⟩, _⟩,
    { sorry },
    { intro a,  },
    { intros a ha,
      simp only [v], rw dif_pos ha,
      exact (mem_bUnion_iff.1 ha).some.2.2.2.2.1 _ (mem_bUnion_iff.1 ha).some_spec.snd },
    { intros a ha, simp only [v], rw dif_neg ha },
    { intros tv htv,
      have hsub : tv.fst ⊆ I, from subset_bUnion_of_mem htv,
      refine ⟨hsub, λ a ha, _⟩,
      simp only [v], rw [dif_pos],
       } }
end

/-
Apply Zorn's lemma to
 T = Σ (i : set α), {v : α → set X // s ⊆ Union v ∧ (∀ a, is_open (v a)) ∧
                                      (∀ a ∈ i, closure (v a) ⊆ u a) ∧ (∀ a ∉ i, v a = u a)}
with the ordering
 ⟨i, v, _⟩ ≤ ⟨i', v', _⟩ ↔ i ⊆ i' ∧ ∀ a ∈ i, v a = v' a
The hypothesis that `X` is normal implies that a maximal element must have `i = univ`.
Point-finiteness of `u` (hypothesis `uf`) implies that
the least upper bound of a chain in `T` again yields a covering of `s`.

Compare proofs in
* https://ncatlab.org/nlab/show/shrinking+lemma#ShrinkingLemmaForLocallyFiniteCountableCovers
* Bourbaki, General Topology, Chapter IX, §4.3
* Dugundji, Topology, Chapter VII, Theorem 6.1
-/
--434611
