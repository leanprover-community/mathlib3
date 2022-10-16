/-
Copyright (c) 2022 Georgi Kocharyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgi Kocharyan
-/
import combinatorics.simple_graph.metric
import data.finset.basic
import .marked_group

/-!
# Cayley graphs
-/

namespace geometric_group_theory
variables {G S : Type*} [group G] (m : marking G S)

/-- The Cayley graph of a marked group. -/
@[simps] def cayley : simple_graph G :=
{ adj := λ a b, a ≠ b ∧ ∃ s : S × bool, a * m (free_group.mk [s]) = b,
  symm := λ a b, begin
    rintro ⟨h, s, rfl⟩,
    refine ⟨h.symm, s.map id bnot, _⟩,
    obtain ⟨_, _| _⟩ := s; sorry,
  end,
  loopless := λ a h, h.1 rfl }

def cayley.move (g : G) (moves : list (S × bool)) : (cayley m).walk g (g * m (free_group.mk moves)) :=
begin
  induction moves generalizing g,
  { simp [←free_group.one_eq_mk] },
  rw free_group.mk_cons,
  refine simple_graph.walk.cons _ _,
  { exact g * m (free_group.mk [moves_hd]) },
  { rw [cayley_adj],
    refine ⟨_, moves_hd, rfl⟩,
    sorry },
  { have : g * m (free_group.mk [moves_hd] * free_group.mk moves_tl) =
      (g * m (free_group.mk [moves_hd])) * m (free_group.mk moves_tl),
    { sorry },
    rw [this],
    apply moves_ih }
end

lemma cayley_preconnected : (cayley m).preconnected :=
begin
  classical,
  intros x y,
  let z := x⁻¹ * y,
  rcases (marking.to_fun_surjective m z) with ⟨z_, h_img : m z_ = z⟩,
  let w_ := z_.to_word,
  have h := cayley.move m x w_,
  have : x * z = y := by group,
  rw [free_group.to_word.mk, h_img, this] at h,
  apply nonempty.intro, exact h,
end

lemma cayley_connected [nonempty G] : (cayley m).connected := ⟨cayley_preconnected _⟩

def gens_as_els : set G := set.range (λ s : S, m (free_group.of s))
def gens_as_els.finite [fintype S] : (gens_as_els m).finite :=
by apply set.finite_range

lemma cayley_neighbor_set_sub (g : G) :
  (cayley m).neighbor_set g ⊆ (set.image (λ (x : G), g * x) (gens_as_els m))
                              ∪ (set.image (λ (x : G), g * x ⁻¹) (gens_as_els m)) :=
begin
  rintro h hn,
  simp only [cayley_adj, simple_graph.mem_neighbor_set, ne.def, bool.exists_bool,
             free_group.of_gen_false_inv,free_group.of_gen_to_of, map_inv] at hn,
  rcases hn with ⟨ne,⟨s,rfl|rfl⟩⟩,
  { right,
    unfold gens_as_els,
    simp only [set.mem_image, set.mem_range, exists_exists_eq_and, exists_apply_eq_apply]},
  { left,
    unfold gens_as_els,
    simp only [set.image_mul_left, set.mem_preimage, inv_mul_cancel_left, set.mem_range,
               exists_apply_eq_apply]}
end

noncomputable def cayley_locally_finite [fintype S] : (cayley m).locally_finite :=
begin
  rintro g,
  --rw cayley_neighbor_set_eq,
  apply set.finite.fintype,
  apply set.finite.subset _ (cayley_neighbor_set_sub m g),
  apply set.finite.union;
  apply set.finite.image;
  apply gens_as_els.finite,
end

def mul_isom (g : G) : (cayley m) ≃g (cayley m) :=
begin
  fsplit,
  { refine ⟨(λ x, g * x),(λx, g ⁻¹ * x),_,_⟩,
    { dsimp only [function.left_inverse],
      funext x, simp },
    { dsimp only [function.right_inverse,function.left_inverse],
      funext x, simp },},
  rintro a b,
  simp only [cayley_adj, equiv.coe_fn_mk, ne.def, mul_right_inj, bool.exists_bool,
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
