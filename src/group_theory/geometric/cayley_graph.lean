/-
Copyright (c) 2022 Georgi Kocharyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgi Kocharyan
-/
import combinatorics.simple_graph.metric
import group_theory.geometric.marked_group
import data.finset.basic

/-!
# Cayley graphs
-/

namespace geometric_group_theory
variables {G S : Type*} [group G] (m : marking G S)

def cayley : simple_graph G := simple_graph.from_rel $ λ g h, ∃ s : S, g * m (free_group.of s) = h

theorem cayley.adj_iff : ∀ g h : G, (cayley m).adj g h ↔ g ≠ h ∧ ∃ (s : S) (sgn : bool), g * m (free_group.of_gen s sgn) = h :=
begin
  intros g h,
  rw [cayley, simple_graph.from_rel_adj],
  simp, intro, split,
  { intro hyp, cases hyp,
    { rcases hyp with ⟨s, hs⟩,
      use s, right, exact hs, },
    { rcases hyp with ⟨s, hs⟩,
      use s, left, rw [← hs], group, }
   },
  {
    rintro ⟨s, hs⟩, cases hs,
    { right, use s, rw [← hs], group, },
    { left, use s, exact hs, }
  }
end

def cayley.move (g : G) (moves : list (S × bool)) : (cayley m).walk g (g * m (free_group.mk moves)) :=
begin
  revert g,
  induction moves,
  { intro g, rw [← free_group.one_eq_mk], simp,},
  { intro g,
    cases moves_hd,
    rw [free_group.cons_mk, free_group.of_gen],
    refine simple_graph.walk.cons _ _,
    { exact g * m (free_group.of_gen moves_hd_fst moves_hd_snd) },
    { rw [cayley.adj_iff], split,
      { sorry },
      {use moves_hd_fst, use moves_hd_snd, } },
    { have : g * m (free_group.mk [(moves_hd_fst, moves_hd_snd)] * free_group.mk moves_tl) = (g * m (free_group.mk [(moves_hd_fst, moves_hd_snd)])) * m (free_group.mk moves_tl),
      { sorry },
      rw [this], apply moves_ih, } }
end

lemma cayley_preconnected [decidable_eq S] : (cayley m).preconnected :=
begin
  intros x y,
  let z := x⁻¹ * y,
  rcases (marking.to_fun_surjective m z) with ⟨z_, h_img : m z_ = z⟩,
  let w_ := z_.to_word,
  have h := cayley.move m x w_,
  have : x * z = y := by group,
  rw [free_group.to_word.mk, h_img, this] at h,
  apply nonempty.intro, exact h,
end

lemma cayley_connected [nonempty G] [decidable_eq S] : (cayley m).connected := ⟨cayley_preconnected _⟩

def cayley_locally_finite (Sfin : finite S) : (cayley m).locally_finite := sorry

def mul_isom (g : G) : (cayley m) ≃g (cayley m) :=
begin
  fsplit,
  { refine ⟨(λ x, g * x),(λx, g ⁻¹ * x),_,_⟩,
    { dsimp only [function.left_inverse],
      funext x, simp },
    { dsimp only [function.right_inverse,function.left_inverse],
      funext x, simp },},
  rintro a b,
  simp only [cayley.adj_iff, equiv.coe_fn_mk, ne.def, mul_right_inj, bool.exists_bool,
             free_group.of_gen_false_inv, free_group.of_gen_to_of, map_inv, and.congr_right_iff],
  rintro,
  apply exists_congr,
  rintro,
  apply or_congr; rw mul_assoc;
  apply function.injective.eq_iff;
  apply function.bijective.injective;
  apply group.mul_left_bijective,
end

-- Don't know of a good name
lemma infinite_well_spaced [infinite G] [decidable_eq G] (K : finset G) :
  ∃ g : G, disjoint (finset.image (mul_isom m g) K) K :=
begin
  let KKm := finset.bUnion K (λ x, finset.image (λ y, x * y ⁻¹) K),
  obtain ⟨g,gKKm⟩ := infinite.exists_not_mem_finset KKm,
  use g,
  rintro _ h,
  simp only [finset.inf_eq_inter, finset.mem_inter, finset.mem_image, exists_prop] at h,
  obtain ⟨⟨k,kK,rfl⟩,gkK⟩ := h,
  suffices : (g * k) * k⁻¹ ∈ KKm, {
    rw [mul_assoc,mul_right_inv,mul_one] at this,
    exact gKKm this,},
  rw finset.mem_bUnion,
  use [g*k,gkK],
  simp only [finset.mem_image, exists_prop],
  use [k,kK],
end

variables (g : G)

lemma dist_cayley (g h : G) : ((cayley m).dist g h : ℝ) = dist (to_marked g : marked m) h := sorry

end geometric_group_theory
