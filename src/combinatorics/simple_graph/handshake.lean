/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kyle Miller.
-/
import combinatorics.simple_graph.basic
import algebra.big_operators.basic
import data.nat.parity
import data.zmod.basic
import tactic.omega
/-!
# Degree-sum formula and handshaking lemma

The degree-sum formula is that the sum of the degrees of a finite
graph is equal to twice the number of edges.  The handshaking lemma is
a corollary, which is that the number of odd-degree vertices is even.

## Main definitions

- A `dart` is a directed edge, consisting of a vertex and an edge incident to it.
- `simple_graph.sum_degrees_eq_twice_card_edges` is the degree-sum formula.
- `simple_graph.card_odd_degree_vertices_is_even` is the handshaking lemma.
- `simple_graph.card_odd_degree_vertices_ne_is_odd` is that the number of odd-degree
  vertices different from a given odd-degree vertex is odd.
- `simple_graph.exists_ne_odd_degree_if_exists_odd` is that the existence of an
  odd-degree vertex implies the existence of another one.

## Implementation notes

We give a combinatorial proof by using the fact that the map from
darts to vertices has fibers whose cardinalities are the degrees and
that the map from darts to edges is 2-to-1.

## Tags

simple graphs, sums, degree-sum formula, handshaking lemma
-/
open finset

open_locale big_operators

namespace simple_graph
universes u
variables {V : Type u} (G : simple_graph V)

/-- A `dart` is a directed edge, consisting of a vertex and an edge incident to it -/
@[ext, derive decidable_eq]
structure dart :=
(vert : V)
(edge : sym2 V)
(edge_mem : edge ∈ G.edge_set)
(vert_mem : vert ∈ edge)

/-- There is an equivalence between darts and pairs of a vertex and an incident edge. -/
def dart_equiv_sigma : G.dart ≃ Σ v, G.incidence_set v :=
{ to_fun := λ d, ⟨d.vert, d.edge, d.edge_mem, d.vert_mem⟩,
  inv_fun := λ s, ⟨s.fst, s.snd, s.snd.property.1, s.snd.property.2⟩,
  left_inv := λ d, by { ext, simp only, simp only [subtype.coe_mk], },
  right_inv := λ s, by { ext, simp only, simp only [subtype.coe_eta], } }

instance dart.fintype [fintype V] [decidable_eq V] [decidable_rel G.adj] : fintype (dart G) :=
fintype.of_equiv _ G.dart_equiv_sigma.symm

instance dart.inhabited [inhabited V] [inhabited (G.incidence_set (default _))] :
  inhabited G.dart := ⟨G.dart_equiv_sigma.symm ⟨default _, default _⟩⟩

variables {G}

/-- Reverses the orientation of a dart. -/
def dart.rev [decidable_eq V] (d : G.dart) : G.dart :=
{ vert := sym2.mem.other' d.vert_mem,
  edge := d.edge,
  edge_mem := d.edge_mem,
  vert_mem := sym2.mem_other_mem' d.vert_mem }

@[simp] lemma dart.rev_edge_eq [decidable_eq V] (d : G.dart) : d.rev.edge = d.edge := rfl

@[simp] lemma dart.rev_rev_eq [decidable_eq V] (d : G.dart) : d.rev.rev = d :=
begin
  apply dart.ext,
  apply sym2.other_invol',
  simp only [dart.rev_edge_eq],
end

@[simp] lemma dart_rev_involutive [decidable_eq V] : function.involutive (dart.rev : G.dart → G.dart) :=
dart.rev_rev_eq

lemma dart.neq_rev [decidable_eq V] (d : G.dart) : d ≠ d.rev :=
begin
  intro h, rw dart.ext_iff at h,
  dsimp [dart.vert, dart.rev] at h,
  apply G.edge_other_ne d.edge_mem d.vert_mem,
  convert h.1.symm, rw sym2.other_eq_other',
end

lemma dart_edge_eq_iff [decidable_eq V] (d₁ d₂ : G.dart) :
  d₁.edge = d₂.edge ↔ d₁ = d₂ ∨ d₁ = d₂.rev :=
begin
  have h₁ : d₁.edge = ⟦(d₁.vert, d₁.rev.vert)⟧ := (sym2.mem_other_spec' d₁.vert_mem).symm,
  have h₂ : d₂.edge = ⟦(d₂.vert, d₂.rev.vert)⟧ := (sym2.mem_other_spec' d₂.vert_mem).symm,
  split,
  { rw [dart.ext_iff, dart.ext_iff, dart.rev_edge_eq],
    intro h, simp only [h, and_true, eq_self_iff_true],
    rw [h₁, h₂, sym2.eq_iff] at h,
    cases h,
    { exact or.inl h.1 },
    { exact or.inr h.1 }, },
  { intro h, cases h; subst d₁, refl, },
end

variables (G)

/-- For a given vertex `v`, the injective map from the incidence set at `v` to the darts there. --/
def dart_from_incidence_set (v : V) : G.incidence_set v → G.dart :=
λ ee, ⟨v, ee, ee.property.1, ee.property.2⟩

lemma dart_from_incidence_set_inj (v : V) : function.injective (G.dart_from_incidence_set v) :=
by { intros e₁ e₂, dsimp only [dart_from_incidence_set, dart_equiv_sigma],
     simp only [true_and, equiv.coe_fn_symm_mk, eq_self_iff_true], exact subtype.ext,  }

section degree_sum
variables [fintype V] [decidable_eq V] [decidable_rel G.adj]

lemma dart_vert_fiber_card_eq_degree (v : V) :
  (univ.filter (λ d : G.dart, d.vert = v)).card = G.degree v :=
begin
  have hh := card_image_of_injective univ (G.dart_from_incidence_set_inj v),
  rw [finset.card_univ, card_incidence_set_eq_degree] at hh,
  convert hh,
  ext d,
  simp only [mem_image, true_and, mem_filter, set_coe.exists, mem_univ, exists_prop_of_true],
  split,
  { rintro rfl, use [d.edge, ⟨d.edge_mem, d.vert_mem⟩],
    apply dart.ext; simp [dart_from_incidence_set, dart.vert, dart.edge], },
  { rintro ⟨e, he, rfl⟩, simp [dart_from_incidence_set, dart.vert] },
end

lemma dart_card_eq_sum_degrees : fintype.card G.dart = ∑ v, G.degree v :=
begin
  convert_to (univ : finset G.dart).card = _,
  rw @card_eq_sum_card_fiberwise _ _ (by assumption) dart.vert _ univ (λ d h, mem_univ _),
  simp [G.dart_vert_fiber_card_eq_degree],
end

lemma dart_edge_fiber (d : G.dart) :
  (univ.filter (λ (d' : G.dart), d'.edge = d.edge)) = {d, d.rev} :=
begin
  ext d',
  simp only [true_and, mem_filter, mem_insert, mem_univ, mem_singleton],
  exact dart_edge_eq_iff d' d,
end

lemma dart_edge_fiber_card (e : sym2 V) (h : e ∈ G.edge_set) :
  (univ.filter (λ (d : G.dart), d.edge = e)).card = 2 :=
begin
  refine quotient.ind (λ p h, _) e h, cases p with v w,
  let d : G.dart := ⟨v, ⟦(v, w)⟧, h, sym2.mk_has_mem _ _⟩,
  convert_to _ = finset.card {d, d.rev},
  { rw [card_insert_of_not_mem, card_singleton], simp [d.neq_rev], },
  congr, apply G.dart_edge_fiber d,
end

lemma dart_card_eq_twice_card_edges : fintype.card G.dart = 2 * G.edge_finset.card :=
begin
  convert_to (univ : finset G.dart).card = _,
  rw @card_eq_sum_card_fiberwise _ _ _ dart.edge _ G.edge_finset
    (λ d h, by { rw mem_edge_finset, apply dart.edge_mem }),
  rw @sum_congr _ _ G.edge_finset G.edge_finset
    (λ e, (univ.filter (λ (x : G.dart), dart.edge x = e)).card) (λ e, 2) _ rfl,
  simp [mul_comm],
  intros e h, rw mem_edge_finset at h,
  exact G.dart_edge_fiber_card e h,
end

/-- The degree-sum formula.  This is also known as the handshaking lemma, which might
more specifically refer to `simple_graph.card_odd_degree_vertices_is_even`. -/
theorem sum_degrees_eq_twice_card_edges : ∑ v, G.degree v = 2 * G.edge_finset.card :=
G.dart_card_eq_sum_degrees.symm.trans G.dart_card_eq_twice_card_edges

end degree_sum


section TODO_move

lemma zmod_eq_zero_iff_even (n : ℕ) : (n : zmod 2) = 0 ↔ even n :=
(char_p.cast_eq_zero_iff (zmod 2) 2 n).trans even_iff_two_dvd.symm

lemma zmod_eq_one_iff_odd (n : ℕ) : (n : zmod 2) = 1 ↔ odd n :=
begin
  change (n : zmod 2) = ((1 : ℕ) : zmod 2) ↔ _,
  rw [zmod.eq_iff_modeq_nat, nat.odd_iff],
  trivial,
end

lemma zmod_neq_zero_iff_odd (n : ℕ) : (n : zmod 2) ≠ 0 ↔ odd n :=
by split; { contrapose, simp [zmod_eq_zero_iff_even], }

end TODO_move

/-- The handshaking lemma.  See also `simple_graph.sum_degrees_eq_twice_card_edges`. -/
theorem card_odd_degree_vertices_is_even [fintype V] :
  even (univ.filter (λ v, odd (G.degree v))).card :=
begin
  classical,
  have h := congr_arg ((λ n, ↑n) : ℕ → zmod 2) G.sum_degrees_eq_twice_card_edges,
  simp only [zmod.cast_self, zero_mul, nat.cast_mul] at h,
  rw sum_nat_cast at h,
  rw ←sum_filter_ne_zero at h,
  rw @sum_congr _ (zmod 2) _ _ (λ v, (G.degree v : zmod 2)) (λ v, (1 : zmod 2)) _ rfl at h,
  simp only [filter_congr_decidable, mul_one, nsmul_eq_mul, sum_const, ne.def] at h,
  rw ←zmod_eq_zero_iff_even,
  convert h,
  ext v, rw ←zmod_neq_zero_iff_odd, split, intro h, convert h, intro h, convert h,
  intros v, simp only [true_and, mem_filter, mem_univ, ne.def],
  rw [zmod_eq_zero_iff_even, zmod_eq_one_iff_odd, nat.odd_iff_not_even, imp_self], trivial,
end

lemma card_odd_degree_vertices_ne_is_odd [fintype V] [decidable_eq V]
  (v : V) (h : odd (G.degree v)) :
  odd (univ.filter (λ w, w ≠ v ∧ odd (G.degree w))).card :=
begin
  rcases G.card_odd_degree_vertices_is_even with ⟨k, hg⟩,
  have hk : 0 < k,
  { have hh : (filter (λ (v : V), odd (G.degree v)) univ).nonempty,
    { use v, simp only [true_and, mem_filter, mem_univ], use h, },
    rw ←card_pos at hh, rw hg at hh, clear hg, linarith, },
  have hc : (λ (w : V), w ≠ v ∧ odd (G.degree w)) = (λ (w : V), odd (G.degree w) ∧ w ≠ v),
  { ext w, rw and_comm, },
  simp only [hc, filter_congr_decidable],
  rw [←filter_filter, filter_ne'],
  rw card_erase_of_mem,
  use k - 1, rw nat.pred_eq_succ_iff, rw hg, clear hc hg, rw nat.mul_sub_left_distrib, omega,
  simp only [true_and, mem_filter, mem_univ],
  exact h,
end

lemma exists_ne_odd_degree_if_exists_odd [fintype V]
  (v : V) (h : odd (G.degree v)) :
  ∃ (w : V), w ≠ v ∧ odd (G.degree w) :=
begin
  haveI : decidable_eq V := by { classical, apply_instance },
  rcases G.card_odd_degree_vertices_ne_is_odd v h with ⟨k, hg⟩,
  have hg' : (filter (λ (w : V), w ≠ v ∧ odd (G.degree w)) univ).card > 0,
  { rw hg, apply nat.succ_pos, },
  rcases card_pos.mp hg' with ⟨w, hw⟩,
  simp only [true_and, mem_filter, mem_univ, ne.def] at hw,
  exact ⟨w, hw⟩,
end

end simple_graph
