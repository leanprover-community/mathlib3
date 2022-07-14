/-
Copyright (c) 2022 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ritwick Bhargava, Melissa Wei, Allen Knutson
-/

import tactic
import group_theory.perm.sign
import data.list.intervals
import group_theory.perm.support
import algebra.order.with_zero
import data.list.infix

/-!
# Length of a permutation and Tits' theorem

This file defines `equiv.perm.length`, which is the number of inversions of a permutation of fin n,
and associated lemmas about the length.

It also contains a definition of a reduced word for a permutation, which is an expression of that
permutation as a product of adjacent transpositions with minimal length.

The relation `equiv.perm.braid_equiv` states that one word can be transformed into another
via the braid relations.

* `equiv.perm.Tits'_theorem`: if two reduced words represent the same permutation,
one can be transformed into the other via the braid relations.
-/


open equiv fintype finset function

open_locale big_operators

variable {n:ℕ}

@[derive decidable_pred]
def in_order (π : perm (fin n)) : ( Σ (b : fin n), fin n) → Prop := λ x, π x.1 ≤ π x.2

/-- The finset of all inversions of a permutation, i.e. the set of all (a,b) with b < a and
π a ≤ π b  -/
def inversions (π : equiv.perm (fin n)) := finset.filter (in_order π) (perm.fin_pairs_lt n)

/-- The length of a permutation is the cardinality of the set of inversions  -/
def length  (π : equiv.perm (fin n)) := finset.card (inversions π)

lemma length_zero_iff_id  {π : equiv.perm (fin n)} : length π = 0 ↔ π = 1:=
begin
  rw [length, finset.card_eq_zero],
  split,
  begin
    rw [inversions, <-equiv.perm.support_eq_empty_iff],
    contrapose,
    intro h',
    apply (finset.ne_empty_of_mem),
    let sup_min :(fin n) := finset.min' (π.support) (finset.nonempty_iff_ne_empty.mpr h'),
    have k1: sup_min ∈ π.support:= (perm.support π).min'_mem (nonempty_iff_ne_empty.mpr h'),
    have k2: π⁻¹(sup_min)∈ π.support:=
      by { apply perm.apply_mem_support.mp, rw [perm.apply_inv_self], exact k1},
    have k3: π⁻¹(sup_min)≠ sup_min :=
      by {apply perm.mem_support.mp, rw perm.support_inv, exact k1,},
    show (⟨π⁻¹(sup_min),sup_min⟩ : (Σ (c : fin n), fin n))
      ∈ filter (in_order π) (perm.fin_pairs_lt n),
    rw mem_filter,
    split,
    apply perm.mem_fin_pairs_lt.mpr,
    simp only,
    exact (ne.symm k3).le_iff_lt.mp (finset.min'_le π.support _ k2),
    rw [in_order, perm.apply_inv_self],
    exact finset.min'_le π.support _  (perm.apply_mem_support.mpr (k1)),
  end,
  begin
    rw inversions,
    unfold in_order,
    rintro h,
    rw h,
    simp only [perm.coe_one, id.def],
    apply filter_false_of_mem,
    intro x,
    rw perm.mem_fin_pairs_lt,
    exact not_le.mpr,
  end,
end

/-- The map where an adjacent transposition acts on both elements of a pair  -/
def swap_apply (i : fin n) (h1 : (↑i + 1) < n) :
  (Σ (b : fin n), fin n) → (Σ (b : fin n), fin n) :=
  λ x, ⟨swap i (⟨i+1, h1⟩: fin n) x.1, swap i  (⟨i+1, h1⟩: fin n) x.2⟩

/--describes the image of all inversions of a permutation under the function swap_apply -/
lemma inv_mul_swap_descent_aux  (π : equiv.perm (fin n)) (i : fin n) (h1 : (↑i + 1) < n)
  (h2 : π i> π  (⟨i + 1, h1⟩ : fin n)) :
  set.maps_to (@swap_apply n i h1)
  (λ (x : Σ (b : fin n), fin n), x ∈ (finset.erase (inversions π) ⟨ (⟨i+1, h1⟩ : fin n), i⟩).val)
  (λ (x : Σ (b : fin n), fin n), x ∈ (inversions (π * swap i  (⟨i+1, h1⟩ : fin n))).val) :=
begin
  unfold inversions in_order swap_apply,
  refine set.maps_to'.mpr _,
  simp only [<-finset.filter_erase, set.subset_def, filter_val, multiset.mem_filter,
    set.mem_image, sigma.exists, perm.coe_mul, comp_app, forall_exists_index, and_imp,
    sigma.forall, heq_iff_eq, <-finset.mem_def, finset.mem_erase],
  intros a_1 b x x_1,
  simp only [set.mem_def, set.mem_def, perm.mem_fin_pairs_lt, perm.mem_fin_pairs_lt,
   heq_iff_eq, not_and, and_imp],
  intros g1 g2 g3 g4 g5,
  rw [<-g4, <-g5],
  simp only [swap_apply_self],
  split,
  simp only [equiv.swap_apply_def, equiv.perm.mul_apply, fin.ext_iff, fin.coe_add, fin.coe_mk],
  apply fin.coe_fin_lt.mp,
  have k1:=  fin.coe_fin_lt.mpr g2,
  have myh:= nat.mod_eq_of_lt h1,
  simp only [fin.coe_mk, ne.def, heq_iff_eq, not_and, fin.ext_iff,fin.coe_add,myh] at g1,
  split_ifs; try{linarith}; try{simp  [fin.coe_add,fin.coe_mk, myh], linarith};
     try{exfalso, cc},
  begin
    rw h at k1,
    refine (ne.le_iff_lt (ne.symm h_2)).mp _,
    exact nat.add_one_le_iff.mpr k1,
  end,
  begin
    rw h_3 at k1,
    refine (ne.le_iff_lt (h)).mp _,
    exact nat.lt_add_one_iff.mp k1,
  end,
  exact g3,
end

--inverse of inv_mul_swap_descent_aux
lemma inv_mul_swap_descent_aux'  (π : equiv.perm (fin n)) (i : fin n) (h1 : (↑i + 1) < n)
  (h2 : π i > π (⟨i+1, h1⟩ : fin n)) :
  set.maps_to (@swap_apply n i h1)
  (λ (x : Σ (b : fin n), fin n), x ∈ (inversions (π * swap i  (⟨i+1, h1⟩: fin n))).val)
  (λ (x : Σ (b : fin n), fin n), x ∈ (finset.erase (inversions π) ⟨ (⟨i+1, h1⟩: fin n), i⟩).val) :=
begin
  unfold inversions in_order swap_apply,
  refine set.maps_to'.mpr _,
  simp only [<-finset.filter_erase, set.subset_def, filter_val, multiset.mem_filter,
    set.mem_image, sigma.exists, perm.coe_mul, comp_app, forall_exists_index, and_imp,
    sigma.forall, heq_iff_eq,<-finset.mem_def,finset.mem_erase],
  intros a_1 b x x_1,
  simp only [set.mem_def, set.mem_def, perm.mem_fin_pairs_lt, perm.mem_fin_pairs_lt,
    ne.def, heq_iff_eq, not_and, and_imp],
  intros g1 g2 g3 g4,
  simp only [<-g3,<-g4],
  split,
  split,
  intro eq,
  have myeq:= congr_arg ⇑(swap i (⟨i+1, h1⟩: fin n)) eq,
  simp only [swap_apply_self, swap_apply_right] at myeq,
  by_contra hyp,
  have myeq':= congr_arg ⇑(swap i (⟨i+1, h1⟩: fin n)) hyp,
  simp only [swap_apply_self, swap_apply_left] at myeq',
  rw [myeq,myeq'] at g1,
  have g':=  fin.coe_fin_lt.mpr g1,
  linarith,
  have k1:=  fin.coe_fin_lt.mpr g1,
  have k2:=  fin.coe_fin_lt.mpr h2,
  have k3:=  fin.coe_fin_le.mpr g2,
  simp only [equiv.swap_apply_def, equiv.perm.mul_apply, fin.ext_iff, fin.coe_add,fin.coe_mk],
  apply fin.coe_fin_lt.mp,
  have myh:= nat.mod_eq_of_lt h1,
  have myh': ↑(⟨i+1, h1⟩: fin n)=↑i+1 :=
  begin
  simp only [ fin.coe_add, fin.coe_mk],
  end,
  split_ifs; try{linarith}; try{simp only [fin.val_add,myh], linarith}; try{exfalso, cc},
  exfalso,
  simp only [<-fin.ext_iff] at h,
  rw [<-myh', <-fin.ext_iff] at h_2,
  rw [h,h_2] at k3,
  simp only [swap_apply_right, fin.val_eq_coe, swap_apply_left, fin.coe_fin_le, fin.coe_fin_le] at k3,
  have k4:= fin.coe_fin_le.mpr k3,
  linarith only [k4, k2],
  rw h at k1,
  simp only [myh'],
  refine lt_of_le_of_ne _ (ne.symm h_2),
  have k':= nat.succ_le_iff.mpr k1,
  exact k',
  rw h_3 at k1,
  refine lt_of_le_of_ne _ (h),
  exact nat.lt_succ_iff.mp k1,
  exact g2,
end

--For some reason I have to factor this out to use it below
lemma helper_lem {i: fin n} (h1: (i.val + 1) < n) (z:(fin n)) :
(equiv.swap i (⟨i+1, h1⟩: fin n)) ((equiv.swap i (⟨i+1, h1⟩: fin n)) z) = z:=
begin
  rw [equiv.swap_apply_self],
end

/--bijection between inversions of π ∘ (i i+1) and inversions of π minus (i,i+1),
where π i > π (i+1)-/
def inv_mul_swap_descent (π : equiv.perm (fin n)) (i : fin n) (h1 : (↑i + 1) < n)
  (h2 : π i> π (⟨i+1, h1⟩: fin n)) :
  (finset.erase (inversions π) ⟨⟨i+1, h1⟩, i⟩) ≃ inversions (π * swap i ⟨i+1, h1⟩) :=
{ to_fun :=
    begin refine set.maps_to.restrict (swap_apply i h1)
      {x : Σ (b : fin n), fin n |
      x ∈  (finset.erase (inversions π) ⟨(⟨i+1, h1⟩: fin n), i⟩)}
      {x : Σ (b : fin n), fin n| x ∈ (inversions (π * swap i (⟨i+1, h1⟩: fin n)))}
      (inv_mul_swap_descent_aux π i h1 h2)
    end,
  inv_fun :=
    begin refine set.maps_to.restrict (swap_apply i h1)
    {x : Σ (b : fin n), fin n| x ∈ (inversions (π * swap i (⟨i+1, h1⟩: fin n)))}
    {x : Σ (b : fin n), fin n |
     x ∈  (finset.erase (inversions π) ⟨(⟨i+1, h1⟩: fin n), i⟩)}
    (inv_mul_swap_descent_aux' π i h1 h2)
     end,
  left_inv :=
  begin
    refine left_inverse_iff_comp.mpr _,
    unfold set.maps_to.restrict,
    refine funext _,
    simp only [comp_app, id.def],
    unfold subtype.map swap_apply,
    dsimp,
    simp only [(helper_lem h1 _)],
    intro x,
    refine set_coe.ext_iff.mp _,
    dsimp,
    refine sigma.ext _ _,
    dsimp,
    simp only [(helper_lem h1 _)],
    dsimp,
    exact heq.rfl,
  end,
  right_inv :=
  begin
    refine left_inverse_iff_comp.mpr _,
    unfold set.maps_to.restrict,
    refine funext _,
    simp only [comp_app, id.def],
    unfold subtype.map,
    unfold swap_apply,
    dsimp,
    simp only  [(helper_lem h1 _)],
    intro x,
    refine set_coe.ext_iff.mp _,
    dsimp,
    refine sigma.ext _ _,
    dsimp,
    simp only  [(helper_lem h1 _)],
    dsimp,
    exact heq.rfl,
  end,
}



/--The length of a permutation with a descent at i decreases by one when multiplied by the
  permutation swapping i and i+1-/
lemma length_mul_swap_descent {π : equiv.perm (fin n)} {i: fin n} (h1: (i.val + 1) < n) (h2: π i> π (⟨i+1, h1⟩: fin n)):
 length(π * (equiv.swap i (⟨i+1, h1⟩: fin n)))= length(π)-1 :=
begin
  unfold length,
  have myh := fintype.card_congr (inv_mul_swap_descent π i h1 h2),
  simp only [fintype.card_coe] at myh,
  rw<- myh,
  apply finset.card_erase_of_mem,
  unfold inversions in_order perm.fin_pairs_lt,
  simp only [mem_filter, mem_sigma, mem_univ, mem_attach_fin, mem_range, true_and],
  split,
  simp only [<-fin.val_eq_coe, fin.val_add, nat.mod_eq_of_lt h1],
  exact lt_add_one i.val,
  exact le_of_lt h2,
end

/--The length of a permutation with an ascent at i increases by one when multiplied by the
  permutation swapping i and i+1-/
lemma length_mul_swap_ascent  {π : equiv.perm (fin n)} {i: fin n} (h1: (i.val + 1) < n) (h2: π i< π (⟨i+1, h1⟩: fin n)):
 length(π * (equiv.swap i (⟨i+1, h1⟩: fin n)))= length(π)+1 :=
begin
have h3: (π * (equiv.swap i (⟨i+1, h1⟩: fin n))) i> (π * (equiv.swap i (⟨i+1, h1⟩: fin n))) (⟨i+1, h1⟩: fin n) :=
  begin
    simp only [perm.coe_mul, comp_app, swap_apply_left, swap_apply_right, gt_iff_lt],
    exact h2,
  end,
  have h4 := length_mul_swap_descent h1 h3,
  simp only [mul_swap_mul_self] at h4,
  have h5:length (π * swap i ⟨↑i + 1, h1⟩)≠ 0:=
  begin
    unfold length,
    apply (iff.not (finset.card_eq_zero)).mpr,
    apply (finset.ne_empty_of_mem),
    show ( ⟨⟨i+1, h1⟩,i⟩ :( Σ (c : fin n), fin n))∈ inversions (π * swap i ⟨↑i + 1, h1⟩),
    unfold inversions in_order perm.fin_pairs_lt,
    simp only [perm.coe_mul, comp_app, mem_filter, mem_sigma, mem_univ, fin.coe_mk, mem_attach_fin, self_mem_range_succ,
    swap_apply_right, swap_apply_left, true_and],
    exact (le_of_lt h2),
  end,
  have h6:= (add_left_inj 1).mpr h4,
  have h7 : length (π * swap i ⟨↑i + 1, h1⟩) - 1 + 1 =length (π * swap i ⟨↑i + 1, h1⟩) := nat.sub_add_cancel (nat.one_le_iff_ne_zero.mpr h5),
  rw h7 at h6,
  exact eq.symm (h6),
end


lemma perm_neq (π : equiv.perm (fin n))(i: fin n) (h1: (i.val + 1) < n) :π i≠  π (⟨i+1, h1⟩: fin n):=
  begin
    by_contra,
    have h':= (equiv.injective π) h,
    rw fin.eq_iff_veq at h',
    simp only [fin.val_eq_coe, self_eq_add_right, nat.one_ne_zero] at h',
    exact h',
  end

lemma length_mul_swap {π : equiv.perm (fin n)} {i: fin n} (h1: (i.val + 1) < n) :
 length(π * (equiv.swap i (⟨i+1, h1⟩: fin n)))= if π i> π (⟨i+1, h1⟩: fin n) then length(π)-1 else length(π)+1 :=
begin
  split_ifs,
  exact (length_mul_swap_descent h1 h),
  simp only [not_lt] at h,
  have h4:= lt_of_le_of_ne h (perm_neq π i h1),
  exact (length_mul_swap_ascent h1 h4),
end

lemma length_inc_or_dec {π : equiv.perm (fin n)} {i: fin n} (h1: (i.val + 1) < n) :
 length(π * (equiv.swap i (⟨i+1, h1⟩: fin n)))= length(π)-1 ∨ length(π * (equiv.swap i (⟨i+1, h1⟩: fin n)))= length(π)+1 :=
begin
  by_cases h2: π i> π (⟨i+1, h1⟩: fin n),
  exact or.inl (length_mul_swap_descent h1 h2),
  simp only [not_lt] at h2,
  have h4:= lt_of_le_of_ne h2 (perm_neq π i h1),
  exact or.inr (length_mul_swap_ascent h1 h4),
end


/--function that acts on pairs by switching the order and applying the permutation-/
def switch_apply (π : equiv.perm (fin n)) : (Σ (b : fin n), fin n) →
   (Σ (b : fin n), fin n) := λ x, ⟨π x.2, π x.1⟩

lemma maps_correct (π: equiv.perm (fin n)): set.maps_to (switch_apply π) (λ (x : Σ (b : fin n), fin n), x ∈ (inversions π).val)
  (λ (x : Σ (b : fin n), fin n), x ∈ (inversions π⁻¹).val) :=
begin
    unfold switch_apply inversions in_order,
    refine set.maps_to'.mpr _,
    simp only [<-finset.filter_erase, set.subset_def, filter_val, multiset.mem_filter,
      set.mem_image, sigma.exists, perm.coe_mul, comp_app, forall_exists_index, and_imp,
      sigma.forall, heq_iff_eq,<-finset.mem_def,finset.mem_erase],
    intros a b x x_1,
    simp only [set.mem_def, set.mem_def, perm.mem_fin_pairs_lt,
       perm.mem_fin_pairs_lt, ne.def, heq_iff_eq, not_and, and_imp],
    intros h1 h2 h3 h4,
    rw [<-h3, <-h4],
    simp only [perm.inv_apply_self],
    split,
    exact lt_of_le_of_ne h2
    (by by_contra h; exact ((ne_of_lt h1) (eq.symm ((equiv.injective π) h)))),
    exact le_of_lt h1,
end

--bijection between inversions of π  and inversions of π⁻¹
def inv_bij (π : equiv.perm (fin n)):
 (inversions π) ≃ inversions (π⁻¹):=
{ to_fun :=
    begin refine set.maps_to.restrict (switch_apply π)
      {x : Σ (b : fin n), fin n |
      x ∈ (inversions π)}
      {x : Σ (b : fin n), fin n| x ∈ inversions (π⁻¹)}
      (maps_correct π)
    end,
  inv_fun :=
    begin refine set.maps_to.restrict  (switch_apply π⁻¹)
      {x : Σ (b : fin n), fin n| x ∈ inversions (π⁻¹)}
      {x : Σ (b : fin n), fin n |
      x ∈ (inversions π)}
      (maps_correct π⁻¹)
     end,
  left_inv :=
  begin
    refine left_inverse_iff_comp.mpr _,
    unfold set.maps_to.restrict,
    refine funext _,
    simp only [comp_app, id.def],
    unfold subtype.map switch_apply,
    dsimp,
    intro x,
    refine subtype.ext _,
    simp only [perm.inv_apply_self, subtype.coe_mk],
    refine sigma.ext_iff.mpr _,
    simp only [perm.inv_apply_self, eq_self_iff_true, heq_iff_eq, and_self],
  end,
  right_inv :=
  begin
    refine right_inverse_iff_comp.mpr _,
    unfold set.maps_to.restrict,
    refine funext _,
    simp only [comp_app, id.def],
    unfold subtype.map switch_apply,
    dsimp,
    intro x,
    refine subtype.ext _,
    simp only [subtype.coe_mk],
    refine sigma.ext_iff.mpr _,
    simp only [perm.apply_inv_self, eq_self_iff_true, heq_iff_eq, and_self],
  end,
}

--length of a permutation under multiplying by an adjacent transposition
lemma length_of_inv (π : equiv.perm (fin n)):
 length π = length (π⁻¹) :=
begin
  unfold length,
  have myh := fintype.card_congr (inv_bij π),
  simp only [fintype.card_coe] at myh,
  exact myh,
end

lemma length_mul_swap_left {π : equiv.perm (fin n)} {i: fin n} (h1: (i.val + 1) < n) :
  length((swap i (⟨i+1, h1⟩: fin n)) * π)= if π⁻¹ i > π⁻¹ (⟨i+1, h1⟩: fin n) then length π - 1 else
  length π +1 :=
begin
  have h:= @length_mul_swap _ π⁻¹ _ h1,
  rw length_of_inv (π⁻¹ * swap i ⟨↑i + 1, h1⟩) at h,
  rw length_of_inv (π⁻¹) at h,
  simp only [mul_inv_rev, swap_inv, inv_inv] at h,
  exact h,
end

lemma neq_1_imp_supp_max_lemmas {π : perm (fin n)} (h' : ¬ π = 1):
  let supp_max := π.support.max'
  (finset.nonempty_of_ne_empty ((not_iff_not.mpr (equiv.perm.support_eq_empty_iff) ).mpr h')) in
  supp_max ∈ π.support ∧ π⁻¹(supp_max)∈ π.support ∧  π⁻¹(supp_max) ≠ supp_max ∧
  π⁻¹ supp_max < supp_max :=
begin
     rw <-equiv.perm.support_eq_empty_iff at h',
     intro supp_max,
    have k1: supp_max ∈ π.support:= (perm.support π).max'_mem (nonempty_iff_ne_empty.mpr h'),
    have k2: π⁻¹(supp_max)∈ π.support:= by { apply perm.apply_mem_support.mp, rw [perm.apply_inv_self], exact k1},
    have k3: π⁻¹(supp_max)≠ supp_max := by {apply perm.mem_support.mp, rw perm.support_inv, exact k1,},
    have k4: π⁻¹ supp_max < supp_max:=  (k3).le_iff_lt.mp (finset.le_max' _ _ k2),
    exact ⟨k1,k2,k3,k4⟩,
end

def inv_supp_max_plus_one_lt  {π : perm (fin n)} (h' : ¬π = 1) :
  let supp_max  := π.support.max' (finset.nonempty_of_ne_empty
  ((not_iff_not.mpr (equiv.perm.support_eq_empty_iff) ).mpr h')) in
  ↑(π⁻¹ supp_max) + 1 < n:=
begin
    intro supp_max,
    exact gt_of_gt_of_ge (fin.is_lt supp_max) (neq_1_imp_supp_max_lemmas h').2.2.2,
end

--The length of a permutation can be reduced by 1
lemma length_dec_one {π : perm (fin n)} (h' : ¬π = 1):
 let supp_max  := π.support.max' (finset.nonempty_of_ne_empty ((decidable.not_iff_not.mpr (equiv.perm.support_eq_empty_iff) ).mpr h')) in
 length (π * swap (π⁻¹ (supp_max)) (⟨π⁻¹ (supp_max) + 1, inv_supp_max_plus_one_lt h'⟩)) +1 = length π:=
begin
  intro supp_max,
  rcases (neq_1_imp_supp_max_lemmas h') with ⟨k1, k2, k3, k4⟩,
  have h2: π ( π⁻¹ supp_max)> π (⟨( π⁻¹ supp_max)+1, inv_supp_max_plus_one_lt h'⟩) :=
  begin
    simp,
    by_cases mem: (⟨( π⁻¹ supp_max)+1, _⟩ : fin n) ∈ π.support,
    have k6 := finset.le_max' _ _ (perm.apply_mem_support.mpr mem),
    suffices h': π (⟨( π⁻¹ supp_max)+1, _⟩) ≠ supp_max,
    exact (h').le_iff_lt.mp (k6),
    by_contra h',
    have h'': π⁻¹ (π (⟨( π⁻¹ supp_max)+1, _⟩)) = π⁻¹(supp_max) := congr_arg ⇑π⁻¹ h',
    simp at h'',
    rw fin.ext_iff at h'',
    simp at h'',
    exact h'',
    unfold perm.support at mem,
    have mem1 := mt (mem_filter.mpr) mem,
    simp only [mem_univ, true_and, not_not] at mem1,
    rw mem1,
    have mem':= congr_arg ⇑π⁻¹ mem1,
    simp only [perm.inv_apply_self] at mem',
    have k10:= fin.lt_iff_coe_lt_coe.mp k4,
    rw fin.lt_iff_coe_lt_coe,
    simp only [fin.coe_mk],
    simp only [fin.ne_iff_vne,fin.val_eq_coe] at k3,
    have k11 := nat.add_one_le_iff.mpr k10,
    refine (ne.le_iff_lt _).mp k4,
    rw <-fin.coe_mk (inv_supp_max_plus_one_lt h'),
    rw [<-fin.val_eq_coe],
    nth_rewrite_rhs 0 [<-fin.val_eq_coe],
    rw [<-fin.ne_iff_vne],
    apply (function.injective.ne_iff (equiv.injective  π⁻¹)).mp ,
    rw<- mem',
    simp only [fin.val_eq_coe,fin.ne_iff_vne],
    linarith,
  end,
  rw [length_mul_swap_descent (inv_supp_max_plus_one_lt h') h2],
  have length_pos: length(π) ≠ 0:=
  begin
    by_contra c,
    rw <-equiv.perm.support_eq_empty_iff at h',
    exact h'(equiv.perm.support_eq_empty_iff.mpr ((length_zero_iff_id).mp c)),
  end,
  exact nat.sub_add_cancel (nat.one_le_iff_ne_zero.mpr length_pos),
end


--The length of a permutation can be made to decrease by multiplying with a suitable transposition
lemma length_dec {π : perm (fin n)} (h' : ¬π = 1):
 let supp_max  := π.support.max' (finset.nonempty_of_ne_empty ((decidable.not_iff_not.mpr (equiv.perm.support_eq_empty_iff) ).mpr h')) in
 length (π * swap (π⁻¹ (supp_max)) (⟨π⁻¹ (supp_max) + 1, inv_supp_max_plus_one_lt h'⟩)) < length π:=
begin
  have h'' := @length_dec_one n π  h',
  have neq_1: length(π)≠ 0 :=
  begin
  by_contra,
  exact h' (length_zero_iff_id.mp h),
  end,
  omega,
end

/--defines a reduced word for a permutation by induction on the length-/
def reduced_word  : perm (fin n)→ list (perm (fin n))
| π :=
 if h': π =1 then (@list.nil (perm (fin n)))
 else
    let supp_max  := π.support.max' (finset.nonempty_of_ne_empty ((decidable.not_iff_not.mpr (equiv.perm.support_eq_empty_iff) ).mpr h')) in
    have length_less: length (π * swap (π⁻¹ (π.support.max' _)) (⟨π⁻¹ (supp_max) + 1, inv_supp_max_plus_one_lt h'⟩)) < length π := @length_dec n π h',
     list.concat (@reduced_word (π * swap (π⁻¹ supp_max)  (⟨π⁻¹ (supp_max) + 1, inv_supp_max_plus_one_lt h'⟩ :fin n))) (swap (π⁻¹ supp_max) (⟨π⁻¹ (supp_max) + 1, inv_supp_max_plus_one_lt h'⟩))
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf length⟩]}

/--defines a reduced word for a permutation where swap x (x+1) is represented by x-/
def reduced_word' (n:ℕ): perm (fin n)→ list (fin (n-1))
| π :=
 if h': π =1 then (@list.nil  (fin (n-1)) )
 else
    let supp_max  := π.support.max' (finset.nonempty_of_ne_empty ((decidable.not_iff_not.mpr (equiv.perm.support_eq_empty_iff) ).mpr h')) in
    have length_less: length (π * swap (π⁻¹ (π.support.max' _)) (⟨π⁻¹ (supp_max) + 1, inv_supp_max_plus_one_lt h'⟩)) < length π := @length_dec n π h',
     list.concat (reduced_word' (π * swap (π⁻¹ supp_max) (⟨π⁻¹ (supp_max) + 1, inv_supp_max_plus_one_lt h'⟩ :fin n))) ⟨↑(π⁻¹ supp_max), begin simp only [supp_max], have k := inv_supp_max_plus_one_lt h', simp at k, exact nat.lt_pred_iff.mpr k, end ⟩
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf length⟩]}


/--A reduced word of a permutation has product equal to the original permutation-/
lemma red_word_prod_eq   :∀ π, (@reduced_word n π).prod = π
|π:=
  if h':π =1 then
  begin
    rw reduced_word,
    split_ifs,
    simp only [list.prod_nil],
    exact eq.symm h'
  end
  else
  have length_less: length (π * swap (π⁻¹ (π.support.max' _)) (⟨π⁻¹ ((π.support.max' _)) + 1, inv_supp_max_plus_one_lt h'⟩ :fin n)) < length π := @length_dec n π h',
  begin
    rw reduced_word, split_ifs,
    simp only [list.concat_eq_append, list.prod_append, list.prod_cons, list.prod_nil, mul_one],
    suffices k: (reduced_word (π * swap (π⁻¹ (π.support.max' _)) (⟨π⁻¹ ((π.support.max' _)) + 1, inv_supp_max_plus_one_lt h'⟩ :fin n))).prod = (π * swap (π⁻¹ (π.support.max' _)) (⟨π⁻¹ ((π.support.max' _)) + 1, inv_supp_max_plus_one_lt h'⟩ :fin n)),
    rw k,
    simp only [mul_swap_mul_self],
    exact red_word_prod_eq  _,
  end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf length⟩]}

/--A reduced word of a permutation has length equal to the length of the permutation-/
lemma red_word_length   :∀ π, (@reduced_word' n π).length = length π
|π:=
  if h':π =1 then
  begin
    rw reduced_word',
    split_ifs,
    simp only [list.length],
    exact eq.symm (length_zero_iff_id.mpr h'),
  end
  else
  have length_less: length (π * swap (π⁻¹ (π.support.max' _)) (⟨π⁻¹ ((π.support.max' _)) + 1, inv_supp_max_plus_one_lt h'⟩ :fin n)) < length π := @length_dec n π h',
  begin
    rw reduced_word', split_ifs,
    simp only [list.concat_eq_append, list.length_append, list.length_singleton],
    suffices k: (reduced_word' n (π * swap (π⁻¹ (π.support.max' _)) (⟨π⁻¹ ((π.support.max' _)) + 1, inv_supp_max_plus_one_lt h'⟩ :fin n))).length = length (π * swap (π⁻¹ (π.support.max' _)) (⟨π⁻¹ ((π.support.max' _)) + 1, inv_supp_max_plus_one_lt h'⟩ :fin n)),
    rw k,
    have l:= @length_dec_one n π h',
    exact l,
    exact red_word_length  _,
  end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf length⟩]}

/-- The map that takes x to the permutation swapping x and (x+1)-/
def swap_map_fin (n:ℕ) (i:fin (n-1)) : perm (fin n) :=
  equiv.swap (⟨i.val, by have h' := i.2; omega⟩) (⟨i.val+1, by have h' := i.2; omega⟩)


/-- reduced_word and reduced_word' are compatible under swap_map-/
lemma swap_map_red_word : ∀π, list.map (swap_map_fin n) (@reduced_word' n π) = (@reduced_word n π)
|π:=
  if h':π =1 then
  begin
    unfold reduced_word',
    unfold reduced_word,
    split_ifs,
    simp only [list.map_nil],
  end
  else
  have length_less: length (π * swap (π⁻¹ (π.support.max' _)) (⟨π⁻¹ ((π.support.max' _)) + 1, inv_supp_max_plus_one_lt h'⟩ :fin n)) < length π := @length_dec n π h',
  begin
    unfold reduced_word',
    unfold reduced_word,
    split_ifs,
    simp only [list.map, list.concat_eq_append, list.map_append],
    unfold swap_map_fin,
    simp only [fin.coe_mk, fin.eta],
    have recurse:= swap_map_red_word (π * swap (π⁻¹ (π.support.max' _)) ⟨↑(π⁻¹ (π.support.max' _)) + 1, _⟩),
    rw recurse,
  end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf length⟩]}


--reduced_word is computable!
--#eval @reduced_word 10 (swap (⟨1 ,(cmp_eq_lt_iff 1 10).mp rfl⟩: (fin 10))  (⟨8,(cmp_eq_lt_iff 8 10).mp rfl⟩: (fin 10))  )


/--equivalence relation generated by all commutation and braid relations -/
inductive braid_equiv : list ℕ → list ℕ → Prop
  | nil : braid_equiv [] []
  | cons  : Π (x : ℕ) {l₁ l₂ : list ℕ}, braid_equiv l₁ l₂ → braid_equiv (x::l₁) (x::l₂)
  | append  : Π (x : ℕ) {l₁ l₂ : list ℕ}, braid_equiv l₁ l₂ → braid_equiv (l₁++ [x]) (l₂++ [x])
  | swap  : Π {x y : ℕ} (l : list ℕ), 1 < |(y:ℤ) -(x:ℤ)| →  braid_equiv (y::x::l) (x::y::l)
  | braid : Π (x : ℕ) (l : list ℕ), braid_equiv  (x::(x+1)::x::l) ((x+1)::x::(x+1)::l)
  | trans : Π {l₁ l₂ l₃ : list ℕ }, braid_equiv l₁ l₂ → braid_equiv l₂ l₃ → braid_equiv l₁ l₃
  | symm: Π {l₁ l₂ : list ℕ }, braid_equiv l₁ l₂ → braid_equiv l₂ l₁
  | refl: Π {l : list ℕ }, braid_equiv l l


def braid_equiv_fin   : list (fin n)→ list (fin n) → Prop :=
  λ l_1,λ l_2, braid_equiv (list.map coe l_1) (list.map coe l_2)

def swap_map (i:ℕ) : perm ℕ := equiv.swap i (i+1)

/-- The permutation corresponding to a list under swap_map-/
def perm_of_list : list ℕ→ equiv.perm ℕ :=  λ l_1, ((list.map (swap_map) l_1)).prod

def perm_of_list_fin (n:ℕ) : list (fin (n-1)) → perm(fin (n)) :=  λ l_1, ((list.map (@swap_map_fin n ) l_1)).prod

lemma swap_commutes {i:ℕ} {j:ℕ} ( h: |(i:ℤ)-(j:ℤ)| >1) :
  (equiv.swap i (i + 1)) * (equiv.swap j (j + 1)) = (equiv.swap j (j + 1))*(equiv.swap i (i + 1)) :=
begin
  have k: ∀(a:ℕ),∀(b:ℕ), |(a:ℤ)-(b:ℤ)| > 1 → (a ≠b ) ∧ (a ≠ b+1) :=
  begin
    intros a b h1,
    split,
    by_contra,
    have eqn': (a:ℤ) = b, from congr_arg coe h,
    rw eqn' at h1,
    simp only [gt_iff_lt, abs_zero, sub_self] at h1,
    linarith,
    by_contra,
    have eqn': (a:ℤ) = b+1, from congr_arg coe h,
    rw eqn' at h1,
    simp only [lt_self_iff_false, add_tsub_cancel_left, gt_iff_lt, abs_one] at h1,
    exact h1,
  end,
  have l1: i ≠ j, from (k i j h).1,
  have l2: i≠ j+1, from (k i j h).2,
  have l3: j≠ i+1, from (k j i (by rw [<- abs_neg, gt_iff_lt, neg_sub]; exact h)).2,
  apply equiv.ext,
  intro x,
  simp only [equiv.swap_apply_def, equiv.perm.mul_apply],
  split_ifs;
  omega nat,
end

lemma braid_on_swap (i:ℕ) :
  equiv.swap i (i + 1) * (equiv.swap (i + 1) (i + 2) * equiv.swap i (i + 1)) =
  (equiv.swap (i + 1) (i + 2)) * (equiv.swap i (i + 1)) * (equiv.swap (i + 1) (i + 2)) :=
begin
  apply fun_like.ext,
  intro x,
  simp only [equiv.swap_apply_def, equiv.perm.mul_apply],
  split_ifs;
  omega nat,
end

/-- Braid relations preserve the permutation corresponding to the list-/
lemma braid_equiv_prod_eq {w_1 w_2: list ℕ}  (h': braid_equiv w_1 w_2) :
  perm_of_list w_1 = perm_of_list w_2 :=
begin
  unfold perm_of_list,
  apply braid_equiv.rec_on h',
  simp only [eq_self_iff_true],
  simp only [list.map, list.prod_cons, mul_right_inj, imp_self, implies_true_iff, forall_const],
  simp only [list.map_append, list.prod_append, mul_left_inj, imp_self, implies_true_iff, forall_const],
  simp only [list.map, gt_iff_lt, list.prod_cons],
  intros a b l h,
  unfold swap_map,
  rw <-mul_assoc,
  rw <-mul_assoc,
  simp only [mul_left_inj],
  exact swap_commutes h,
  simp only [list.map, list.prod_cons],
  intros x l,
  unfold swap_map,
  simp only [←mul_assoc, mul_left_inj],
  have k: x+1 +1= x+2 := rfl,
  rw k,
  exact braid_on_swap _,
  intros a b c d e,
  exact eq.trans,
  intros l1 l2 h,
  exact eq.symm,
  exact congr_fun rfl,
end

/-- Braid relations respect the length of the list-/
lemma braid_equiv_length_eq {w_1 w_2: list (ℕ)}  (h':@braid_equiv w_1 w_2) :
  w_1.length = w_2.length :=
begin
  apply braid_equiv.rec_on h',
  simp only [eq_self_iff_true],
  simp only [list.length, add_left_inj, imp_self, implies_true_iff, forall_const],
  simp only [list.length_append, add_left_inj, imp_self, implies_true_iff, forall_const],
  simp only [list.length, eq_self_iff_true, implies_true_iff, forall_const],
  simp only [list.length, eq_self_iff_true, forall_const],
  intros a b c d e,
  exact eq.trans,
  intros l1 l2 h,
  exact eq.symm,
  exact congr_fun rfl,
end

/-- Braid relations respect the minimum of the list-/
lemma braid_equiv_min {w_1 w_2: list (ℕ)}  (h':@braid_equiv w_1 w_2) : w_1.minimum = w_2.minimum :=
begin
  apply braid_equiv.rec_on h',
  simp only [eq_self_iff_true],
  simp only [list.minimum_cons],
  tauto,
  simp only [list.minimum_concat],
  tauto,
  simp [list.minimum_cons],
  simp [<-min_assoc],
  intros x y,
  rw min_comm ↑x ↑y,
  exact congr_fun₂ rfl,
  simp [list.minimum_cons, min_eq_right, min_le_iff, with_top.coe_le_coe, le_add_iff_nonneg_right, zero_le', true_or, le_refl, <-min_assoc],
  intros a b c d e,
  exact eq.trans,
  intros l1 l2 h,
  exact eq.symm,
  exact congr_fun rfl,
end

lemma braid_equiv_infix (s t :list ℕ) {l1 l2:list ℕ} : braid_equiv l1 l2 → braid_equiv (s ++ l1 ++ t) (s ++ l2 ++ t) :=
begin
  apply s.rec_on,
  simp only [list.nil_append],
  apply list.reverse_rec_on t,
  simp only [list.append_nil, imp_self],
  intros l a h,
  rw [<-list.append_assoc, <-list.append_assoc],
  intro h2,
  have h3:= h h2,
  exact braid_equiv.append a h3,
  intros hd tl h,
  intro h2,
  have h3:= h h2,
  exact braid_equiv.cons hd h3,
end

lemma Ico_braid_commutes {m k l:ℕ} : (l>m+k ∨ l+1<m) → braid_equiv (list.Ico m (m+k) ++ [l] ) ([l]++ list.Ico m (m+k)) :=
begin
  apply k.rec_on,
  simp only [add_zero, gt_iff_lt, list.Ico.self_empty, list.nil_append],
  intro h,
  exact braid_equiv.refl,
  intros n h,
  simp only [<-nat.add_one, <- add_assoc],
  intro g,
  rw list.Ico.succ_top,
  have abs_gt_one: | (l:ℤ) - ↑(m+n)| > 1 :=
  begin
  cases g with g1 g2,
  have gt_one: 1< (l:ℤ) - ↑(m+n) :=
  begin
    refine gt_iff_lt.mp _,
    apply lt_sub_iff_add_lt.mpr,
    refine gt.lt _,
    apply int.coe_nat_lt.mpr ,
    linarith,
    exact covariant_swap_add_lt_of_covariant_add_lt ℤ,
  end,
  refine lt_abs.mpr _,
  refine or.inl _,
  revert gt_one,
  exact @gt.lt _ _ (↑l - ↑(m + n)) 1,
  refine lt_abs.mpr _,
  refine or.inr _,
  simp only [int.coe_nat_add, neg_sub],
  rw add_sub_right_comm,
  linarith,
  end,
  have swap:=   (braid_equiv.swap [] abs_gt_one),
  simp only [list.append_assoc, list.singleton_append],
  have swap' := @braid_equiv_infix (list.Ico m (m+n)) [] _ _ swap,
  simp only [list.append_nil] at swap',
  apply braid_equiv.trans  (braid_equiv.symm swap') _,
  rw [<-list.singleton_append, <-list.append_assoc],
  exact @braid_equiv_infix [] [m+n] _ _ (h $ or.imp_left nat.lt_of_succ_lt g),
  exact le_self_add,
end

lemma Ico_braid_commutes' {m k i:ℕ} {h: k≠ 0} : (i+1<k) → braid_equiv (list.Ico m (m+k) ++ [m+i] ) ((m+i+1):: list.Ico m (m+k)) :=
begin
  revert h,
  apply k.rec_on,
  simp only [ne.def, eq_self_iff_true, not_true, is_empty.forall_iff],
  simp only [<-nat.add_one,<-add_assoc, nat.add_succ_sub_one, add_zero],
  intros n h h',
    by_cases h'' :n=0,
  rw h'',
  simp only [nat.lt_one_iff, nat.succ_ne_zero, is_empty.forall_iff],
  intro g,
  by_cases h''': i=n-1,
  rw h''',
  rw list.Ico.succ_top,
  have k: n-1 +1 =n:= by revert h''; omega,
  rw <-k,
  rw <- add_assoc,
  rw list.Ico.succ_top,
  simp only [ nat.add_succ_sub_one, add_zero],
  rw add_assoc,
  rw k,
  have braid':= @braid_equiv_infix (list.Ico m (m + (n - 1))) [] _ _ (braid_equiv.braid (m+(n-1)) []),
  simp only [list.append_nil] at braid',
  rw [add_assoc,k] at braid',
  simp only [list.append_assoc, list.singleton_append, list.cons_append],
  apply braid_equiv.trans braid' _,
  have comm_past :=  @braid_equiv_infix [] [m+ (n-1),m+n] _ _ (@Ico_braid_commutes m (n-1) (m+n) _),
  simp only [list.nil_append, list.append_assoc, list.cons_append] at comm_past,
  exact comm_past,
  refine or.inl _,
  linarith,
  exact le_self_add,
  exact le_self_add,
  rw list.Ico.succ_top,
  have lt: i<n-1:=
  begin
    omega,
  end,
  have gt_1 :1<(m+n)-(m+i):= by omega,
  have abs_gt_one: 1 < |((m+n):ℤ) - (m+i) |:=
  begin
  refine lt_abs.mpr (or.inl (int.lt_to_nat.mp _)),
  simp only [add_sub_add_left_eq_sub, int.lt_to_nat, int.coe_nat_succ, int.coe_nat_zero, zero_add],
  refine lt_tsub_comm.mp (int.lt_to_nat.mp _),
  simp only [int.pred_to_nat, int.to_nat_coe_nat],
  exact lt,
  end,
  have swap:= @braid_equiv_infix (list.Ico m (m + n)) [] _ _ (braid_equiv.swap [] abs_gt_one),
  simp only [list.append_nil] at swap,
  simp only [list.append_assoc, list.singleton_append],
  apply braid_equiv.trans  swap _,
  have lt_n : i+1<n :=by omega,
  have g:=  @braid_equiv_infix [] [m+n] _ _ (h lt_n),
  simp only [list.nil_append, list.append_assoc, list.cons_append] at g,
  exact g,
  exact h'',
  exact le_self_add,
end

/--The decomposition required in the proof of Tits' theorem,
  list.Ico a b := [a,a+1,...,b-1] is the segment that is bubbled to the right using the relations
  till l_2=[]-/
lemma decomp {l :list ℕ} {m:ℕ} (h: ↑m = list.minimum l):  ∃ k:ℕ, ∃ l_1 :list ℕ, ∃ l_2:list ℕ, l= l_1 ++ (list.Ico m (m+k)) ++ l_2 ∧ list.minimum l_1 > m ∧ ¬ list.is_prefix [m+k] l_2 ∧ k≠ 0 :=
begin
  revert h,
  apply l.rec_on,
  intros h,
  use 0,
  intros hd tl h' h2,
  rw list.minimum_cons at h2,
  by_cases tl.minimum<hd,
  rw min_eq_right_iff.mpr (le_of_lt h) at h2,
  rcases h' h2 with ⟨k, l_1, l_2, h_1, h_2, h_3⟩,
  use k,
  use [hd :: l_1, l_2],
  simp only [h_1, list.minimum_cons, gt_iff_lt, lt_min_iff],
  nth_rewrite 0 h2,
  tauto,
  simp only [not_lt] at h,
  rw min_eq_left_iff.mpr h at h2,
  let possible_interval:fin ((hd::tl).length+1) →Prop := λ k, list.is_prefix (list.Ico m (m+↑k)) (hd::tl),
  let interval_candidates :=  {x: fin ((hd::tl).length+1) // possible_interval(x)},
  have is_fin := subtype.fintype possible_interval,
  have nonempty: nonempty interval_candidates :=
  begin
    simp only [nonempty_subtype],
    dsimp,
    refine exists_comm.mp _,
    use hd::tl,
    use 0,
    simp only [fin.coe_zero, add_zero, list.Ico.self_empty, list.nil_append, eq_self_iff_true, and_self],
  end,
  let f: interval_candidates → ℕ := λx,↑↑x,
  have max:= @fintype.exists_max _ _ nonempty _ _ f,
  cases max with max g,
  use f(max),
  have g': possible_interval(max) := subtype.prop max,
  simp [possible_interval, list.is_prefix] at g',
  cases g' with t g',
  simp,
  use list.nil,
  use t,
  split,
  simp only [list.nil_append],
  exact (eq.symm g'),
  split,
  simp only [list.minimum_nil],
  exact with_top.coe_lt_top _,
  split,
  by_contra,
  unfold list.is_prefix at h,
  cases h with t_1 h,
  rw <-h at g',
  rw <-list.append_assoc at g',
  rw <-list.Ico.succ_top at g',
  have g'':=congr_arg list.length g',
  simp only [list.length_append, list.Ico.length] at g'',
  ring_nf at g'',
  simp only [add_tsub_cancel_left] at g'',
  have g'':=  nat.lt_succ_of_le (nat.le.intro g''),
  rw <-nat.add_one at g'',
  have mem: possible_interval(⟨↑↑max +1,g''⟩):=
  begin
  simp only [possible_interval],
  unfold list.is_prefix,
  use t_1,
  exact g',
  end,
  have g:= g(⟨⟨↑↑max + 1, g''⟩,mem⟩),
  simp [f, fin.le_iff_coe_le_coe] at g,
  exact g,
  exact le_self_add,
  have lt_one: 1<(hd :: tl).length+1:= by rw list.length_cons; linarith,
  have mem: possible_interval ⟨1,lt_one⟩:=
  begin
  dsimp [possible_interval],
  unfold list.is_prefix,
  use tl,
  simp only [list.Ico.succ_singleton, list.singleton_append, eq_self_iff_true, and_true],
  exact with_top.coe_eq_coe.mp h2,
  end,
  have g'':= g (⟨⟨1,lt_one⟩, mem⟩),
  dsimp [f] at g'',
  simp only at g'',
  dsimp [f],
  linarith,
end

def is_reduced_word : list ℕ → Prop := λ w, ∀ v : list ℕ, braid_equiv w v →
  (¬ ∃ a : ℕ, ∃ k : ℕ, k > 1 ∧  list.is_infix (list.repeat a k) v)


lemma coe_lt  {l:list (fin n)}: ∀m∈ ((list.map coe l):list ℕ), m<n :=
begin
  intro m,
  simp only [list.mem_map, forall_exists_index, and_imp],
  intros x h h1,
  rw <-h1,
  exact fin.is_lt x,
end

lemma lt_to_fin (n:ℕ) {l:list ℕ} : (∀m∈ l, m < n )→ ∃! (l': list (fin n)), l = list.map coe l':=
begin
  revert n,
  apply l.rec_on,
  simp only [list.not_mem_nil, forall_const],
  intro n,
  use list.nil,
  simp only [list.map_nil, eq_self_iff_true, true_and],
  intros y h,
  have h' :=  congr_arg list.length h,
  simp only [list.length, list.length_map] at h',
  exact list.length_eq_zero.mp h'.symm,
  simp only [list.mem_cons_iff],
  intros hd tl ind_hyp n hyp,
  specialize ind_hyp n,
  cases (ind_hyp (λ m,λ h, hyp m (or.inr h))) with l' ind_hyp',
  have hd_lt_n: hd<n:=
  begin
    have h''':= hyp (hd),
    rw [eq_self_iff_true, true_or, forall_true_left] at h''',
    exact h''',
  end,
  have k: hd :: tl = list.map coe (⟨hd, hd_lt_n⟩ :: l' : list (fin n)),
  simp only [list.map, fin.coe_mk, eq_self_iff_true, true_and],
  exact ind_hyp'.1,
  apply exists_unique.intro (⟨hd,hd_lt_n⟩::l' : list (fin n)),
  exact k,
  rw k,
  intro y,
  intro eq,
  exact (list.map_injective_iff.mpr (fin.coe_injective)) eq.symm,
end


lemma coe_embedding : injective (λ π : perm (fin n), perm.of_subtype π ) :=
begin
  unfold perm.of_subtype,
  simp only,
  unfold injective perm.of_subtype,
  simp only [monoid_hom.coe_mk, and_imp],
  intros a1 a2 h1 _,
  apply perm.ext,
  intro x,
  have h1':= congr_fun h1 x,
  simp only [fin.eta, dite_eq_ite] at h1',
  split_ifs at h1',
  exact fin.ext h1',
  exact absurd x.2 h,
end

lemma coe_commutes  {l:list (fin n)}: perm_of_list (list.map coe l)= perm.of_subtype (perm_of_list_fin (n+1) l) :=
begin
  unfold perm_of_list perm_of_list_fin perm.of_subtype,
  apply l.rec_on,
  simp only [list.map_nil, list.prod_nil, map_one],
  simp only [list.map, list.map_map, list.prod_cons, map_mul],
  intros hd tl ind_hyp,
  rw ind_hyp,
  simp only [mul_left_inj],
  unfold swap_map swap_map_fin perm.of_subtype,
  have k1:= swap_map_fin._proof_1 (n+1) hd,
  have k2:= swap_map_fin._proof_2 (n+1) hd,
  simp only [fin.val_eq_coe] at k1,
  simp only [fin.val_eq_coe] at k2,
  simp only [fin.val_eq_coe, swap_inv, monoid_hom.coe_mk],
  apply perm.ext,
  intro x,
  simp only [swap_apply_def, coe_fn_mk, swap_inv, subtype.mk_eq_mk, monoid_hom.coe_mk],
  split_ifs; try {rw subtype.coe_mk <|> cc},
end

lemma lt_braid_equiv_lt {l1 l2:list ℕ } (n m :ℕ): braid_equiv l1 l2 →  ((n∈ l1→ n<m) ↔ (n∈ l2→ n<m)):=
begin
  intro h,
  apply braid_equiv.rec_on h,
  any_goals {tauto},
  simp only [list.mem_cons_iff, forall_eq_or_imp, and_imp],
  tauto,
  simp only [list.mem_append, list.mem_singleton],
  tauto,
  simp only [list.mem_cons_iff],
  tauto,
  simp only [list.mem_cons_iff],
  tauto,
end

lemma infix_mem  {l:list (fin n)} {a k :ℕ} (h:k>0): list.repeat a k <:+: (list.map coe l) → a < n:=
begin
  intro h1,
  apply @coe_lt n l a,
  unfold list.is_infix at h1,
  cases h1 with s h2,
  cases h2 with t h3,
  rw <-h3,
  simp only [list.append_assoc, list.mem_append],
  apply or.inr,
  apply or.inl,
  have eq: k-1 +1 =k := by omega,
  rw <-eq,
  rw list.repeat_succ,
  simp only [list.mem_cons_iff, eq_self_iff_true, true_or],
end

lemma infix_coe_imp_infix {l:list (fin n)} {a k :ℕ} (h:k>0): list.repeat a k <:+: (list.map coe l) →
  list.repeat (⟨a, by exact infix_mem h ᾰ ⟩: fin n) k <:+: l :=
begin
  unfold list.is_infix,
  intro h1,
  cases h1 with s h1,
  cases h1 with t h1,
  have lt_l:= @coe_lt n l,
  have lt_s:∀ (m : ℕ), m ∈ s  → m < n := λ m, λ mem_s,
     lt_l m (by rw [<-h1, list.append_assoc, list.mem_append]; exact or.inl mem_s),
  have lt_t:∀ (m : ℕ), m ∈ t  → m < n := λ m, λ mem_t,
     lt_l m (by rw [<-h1, list.append_assoc, list.mem_append, list.mem_append]; exact or.inr (or.inr mem_t)),
  have exists_s' := exists_of_exists_unique (lt_to_fin n lt_s),
  have exists_t' := exists_of_exists_unique (lt_to_fin n lt_t),
  cases exists_s' with s' s'_eq,
  cases exists_t' with t' t'_eq,
  use s',
  use t',
  rw [s'_eq,t'_eq] at h1,
  suffices: injective (list.map coe :list (fin n)→ list ℕ),
  apply this,
  simp only [list.map_append, list.map_repeat, fin.coe_mk],
  exact h1,
  apply list.map_injective_iff.mpr,
  unfold injective,
  exact (@fin.ext n),
end

lemma repeat_prod  {a:fin n}{k:ℕ}:swap_map_fin (n+1) a ^ k = (list.map (swap_map_fin (n+1)) (ite (even k) list.nil [a])).prod :=
begin
  unfold swap_map_fin,
  apply k.rec_on,
  simp only [pow_zero, even_zero, if_true,list.map_nil, list.prod_nil],
  intros m h,
  rw <-nat.add_one,
  rw pow_add,
  rw h,
  simp only [pow_one, ite_mul, one_mul, swap_mul_self],
  split_ifs;try{simp}; try {unfold swap_map_fin, simp},
  exact nat.even_add_one.mp(h_2) h_1,
  exact h_2 (nat.even_add_one.mpr(h_1)),
end

lemma braid_equiv_prod_eq_fin  (w_1 w_2: list (fin n))  (h':braid_equiv_fin w_1 w_2) : perm_of_list_fin (n+1) w_1 = perm_of_list_fin (n+1) w_2 :=
begin
  unfold braid_equiv_fin at h',
  have h'':= braid_equiv_prod_eq h',
  simp only [coe_commutes] at h'',
  exact coe_embedding h'',
end

lemma braid_equiv_length_eq_fin  {w_1 w_2: list (fin n)}  (h':@braid_equiv_fin n w_1 w_2) : w_1.length = w_2.length :=
begin
  unfold braid_equiv_fin at h',
  have h'':= braid_equiv_length_eq h',
  simp only [list.length_map] at h'',
  exact h'',
end

lemma word_length_lt_eq_length'  :∀π, ∀w:list (fin n), perm_of_list_fin (n+1)  w =π → w.length ≥ length (π) :=
begin
  intros π w,
  revert π,
  unfold perm_of_list_fin,
  apply w.rec_on,
  simp only [list.length, list.map_nil, list.prod_nil, ge_iff_le, le_zero_iff, forall_eq'],
  exact (length_zero_iff_id).mpr (by refl),
  intros hd tl ind_hyp π,
  simp only [list.map, list.length, list.prod_cons, ge_iff_le],
  unfold swap_map_fin,
  intro hyp,
  have h := @length_mul_swap_left (n+1) (list.map (swap_map_fin (n+1)) tl).prod ⟨hd.val,swap_map_fin._proof_1 (n+1) hd ⟩ (swap_map_fin._proof_2 (n+1) hd),
  simp only [fin.val_eq_coe, fin.coe_mk, gt_iff_lt] at h,
  simp only [fin.val_eq_coe] at hyp,
  rw hyp at h,
  specialize ind_hyp (list.map (swap_map_fin (n+1)) tl).prod rfl,
  split_ifs at h;omega,
end

lemma word_length_reduced'  : ∀w:list (fin n), w.length = length(perm_of_list_fin (n+1) w) →  is_reduced_word (list.map coe w) :=
begin
  intros w h,
  unfold is_reduced_word,
  intros v h,
  by_contra,
  rcases h with ⟨a, k, h1 ,h2⟩,
  have lt:= @coe_lt n w,
  have lt_v:= exists_of_exists_unique (lt_to_fin n (λ m:ℕ, ((lt_braid_equiv_lt m n h).mp (lt m)))),
  cases lt_v with l' lt_v,
  rw lt_v at h2,
  have h3:= infix_coe_imp_infix (pos_of_gt h1) h2,
  unfold list.is_infix at h3,
  cases h3 with s h3,
  cases h3 with t h3,
  let repl := if odd k then [(⟨a, _⟩: fin n)] else [],
  have repl_v_prod: perm_of_list_fin (n+1) (s ++ repl ++ t) = perm_of_list_fin (n+1) l' :=
  begin
    rw <-h3,
    unfold perm_of_list_fin,
    dsimp [repl],
    simp only [nat.odd_iff_not_even, ite_not, list.map_append,
      list.prod_append, list.map_repeat, list.prod_repeat, mul_right_inj, mul_left_inj],
    exact eq.symm repeat_prod,
  end,
  have length_less: (s ++ repl ++ t).length < l'.length :=
  begin
    rw <-h3,
    simp only [list.length_append, list.length_repeat,
      add_lt_add_iff_left, add_lt_add_iff_right],
    dsimp [repl],
    simp only [list.length_repeat, nat.odd_iff_not_even, ite_not],
    split_ifs; simp; linarith,
    recover,
  end,
  rw lt_v at h,
  have same_perm:= braid_equiv_prod_eq_fin w l' h,
  have same_length:= braid_equiv_length_eq_fin h,
  rw <-same_perm at repl_v_prod,
  rw <-same_length at length_less,
  have length_ge:= word_length_lt_eq_length' (perm_of_list_fin (n+1) w) (s ++ repl ++ t) (repl_v_prod),
  linarith,
end

lemma red_word_braid {l_1 l_2:list ℕ}: is_reduced_word l_1 -> braid_equiv l_1 l_2 -> is_reduced_word l_2 :=
begin
  unfold is_reduced_word,
  intros h1 h2,
  intros v h3,
  by_contra,
  have h' := h1 v (braid_equiv.trans h2 h3),
  exact h' h,
end

lemma move_decomp_right {l l_1 l_2:list ℕ} {m k:ℕ} (h: ↑m = list.minimum l) (h'': l= l_1 ++ (list.Ico m (m+k)) ++ l_2 ∧ list.minimum l_1 > m) (h':is_reduced_word l) (h''':k≠ 0) : ∃k':ℕ, ∃l':list ℕ, braid_equiv l (l' ++ list.Ico m (m+k')) ∧ list.minimum l' > m ∧ k'≠ 0:=
begin
  revert h'' h',
  revert h,
  revert m k l_1 l,
  apply l_2.rec_on,
  simp only [ne.def, list.append_nil, gt_iff_lt, and_imp],
  intros m k l_1 l h5 h1 h2 h3 h4,
  use [k, l_1],
  rw h2,
  split,
  exact braid_equiv.refl,
  split,
  exact h3,
  exact h5,
  intros hd tl ind_hyp m k l_1 l h' h hyp red,
  cases hyp with hyp1 hyp2,
  have eq': hd::tl=[hd]++tl:=rfl,
  rw eq' at hyp1,
  rw <-list.append_assoc at hyp1,
  have ge_min : m≤hd:=
  begin
    apply with_top.coe_le_coe.mp,
    rw h,
    suffices mem: hd∈ l, by exact list.le_minimum_of_mem' mem,
    rw hyp1,
    refine list.mem_append.mpr _,
    refine or.inl _,
    refine list.mem_append.mpr _,
    refine or.inr _,
    simp only [list.mem_singleton],
  end,
  by_cases h''': hd>m+k,
  have com:= braid_equiv_infix l_1 tl (Ico_braid_commutes (or.inl h''')),
  rw [<-list.append_assoc] at com,
  rw hyp1,
  have same_set : ∀ a:ℕ, a ∈ (l_1 ++ hd :: list.Ico m (m + k) ++ tl) ↔ a∈ l :=
  begin
    intro a,
    rw hyp1,
    simp only [list.append_assoc, list.cons_append, list.mem_append, list.mem_cons_iff, list.Ico.mem, list.singleton_append],
    tauto,
  end,
  have min: ↑m =(l_1 ++ hd :: list.Ico m (m + k) ++ tl).minimum :=
  begin
    apply eq.symm,
    apply list.minimum_eq_coe_iff.mpr,
    split,
    have mem' := list.minimum_mem (eq.symm h),
    exact (same_set m).mpr mem',
    intro a,
    intro memb,
    exact ((list.minimum_le_of_mem ((same_set a).mp memb)) (eq.symm h)),
  end,
  have nec_hyp:l_1 ++ hd :: list.Ico m (m + k) ++ tl = l_1 ++ [hd] ++ list.Ico m (m + k) ++ tl ∧ (l_1 ++ [hd]).minimum > ↑m :=
  begin
    split,
    simp only [list.append_assoc, list.singleton_append],
    rw list.minimum_concat,
    refine lt_min hyp2 _,
    apply with_top.coe_lt_coe.mpr,
    revert h''',
    omega manual,
  end,
  specialize ind_hyp h' min nec_hyp (red_word_braid red (by rw [<-hyp1] at com; by exact com)),
  cases ind_hyp with k' ind_hyp,
  cases ind_hyp with l' ind_hyp,
  use [k', l'],
  split,
  exact braid_equiv.trans com (ind_hyp.1),
  exact ind_hyp.2,
  by_cases eq': hd=m+k,
  have hyp1': l =l_1 ++ list.Ico m (m + k + 1) ++ tl :=
  begin
  have eqq: l_1 ++ list.Ico m (m + k) ++ [m + k] = l_1 ++ (list.Ico m (m + k) ++ [m + k]):= by rw list.append_assoc,
  rw [hyp1, eq',eqq, <-list.Ico.succ_top],
  simp only [le_add_iff_nonneg_right, zero_le'],
  end,
  rw add_assoc at hyp1',
  specialize ind_hyp (ne_comm.mp (ne_of_lt (@nat.succ_pos k))) h (and.intro hyp1' hyp2) red,
  cases ind_hyp with k' ind_hyp,
  cases ind_hyp with l' ind_hyp,
  use [k',l'],
  exact ind_hyp,
  simp only [not_lt] at h''',
  have lt_mk := nat.lt_of_le_and_ne h''' eq',
  have ex: m+(hd-m)=hd:= by revert ge_min; omega manual,
  have lt_k: hd-m<k := by omega,
  have neq_k_minus_one : (hd-m) +1≠ k :=
  begin
    by_contra eq'',
    have hd_eq : hd=k+m-1:=by omega,
    rw hd_eq at hyp1,
    have neq: m+k≠ 0 := by omega,
    have ad_min_one:(k+m -1) +1=m+k := by omega,
    rw [<-ad_min_one, list.Ico.succ_top, <-list.append_assoc] at hyp1,
    have exists_repeat: (∃ a: ℕ, ∃ k:ℕ, k>1 ∧  list.is_infix (list.repeat a k) l):=
    begin
      use [k+m-1,2],
      split,
      exact lt_add_one 1,
      rw hyp1,
      unfold list.is_infix,
      use [l_1 ++ list.Ico m (k + m - 1), tl],
      simp only [list.repeat, list.append_assoc, list.singleton_append],
    end,
    unfold is_reduced_word at red,
    specialize red l,
    exact (red braid_equiv.refl) exists_repeat,
    linarith,
  end,
  have lt_plus_one_k:(hd-m)+1<k := by omega,
  have com := @braid_equiv_infix l_1 tl _ _ (@Ico_braid_commutes' m _ _ _ lt_plus_one_k),
  rw ex at com,
  rw [<-list.append_assoc, <-hyp1] at com,
  have min' :↑m = (l_1 ++ (hd + 1) :: list.Ico m (m + k) ++ tl).minimum :=
  begin
    apply eq.symm,
    apply list.minimum_eq_coe_iff.mpr,
    split,
    simp only [list.append_assoc, list.cons_append, list.mem_append, list.mem_cons_iff, list.Ico.mem, le_refl, lt_add_iff_pos_right,
    true_and],
    refine or.inr _,
    refine or.inr _,
    refine or.inl _,
    omega,
    intro a,
    simp only [list.append_assoc, list.cons_append, list.mem_append, list.mem_cons_iff, list.Ico.mem],
    have h'''': a=hd+1 →m≤a := by omega,
    rw <-or.assoc,
    intro ors,
    have ors:= or.imp_left or.comm.mp ors,
    rw or.assoc at ors,
    cases ors with hd' ors,
    rw hd',
    linarith,
    have a_in_l: a∈ l :=
    begin
      rw hyp1,
      simp only [list.append_assoc, list.singleton_append, list.mem_append, list.Ico.mem, list.mem_cons_iff],
      revert ors,
      tauto,
    end,
    exact ((list.minimum_le_of_mem a_in_l) (eq.symm h)),
  end,
  have nec_hyp: l_1 ++ (hd + 1) :: list.Ico m (m + k) ++ tl = l_1 ++ [hd + 1] ++ list.Ico m (m + k) ++ tl ∧
  (l_1 ++ [hd + 1]).minimum > ↑m :=
  begin
    split,
    simp only [list.append_assoc, list.singleton_append],
    rw list.minimum_concat,
    refine lt_min hyp2 _,
    apply with_top.coe_lt_coe.mpr,
    omega,
  end,
  specialize ind_hyp h' min' nec_hyp (red_word_braid red com),
  rcases ind_hyp with ⟨k', l', ind_hyp⟩,
  use [k',l'],
  split,
  exact braid_equiv.trans com ind_hyp.1,
  exact ind_hyp.2,
  linarith,
end


lemma list_bounded (w:list ℕ) : ∃M :ℕ, ∀ x:ℕ, x∈ w → x < M :=
begin
  apply w.rec_on,
  use 1,
  simp only [list.not_mem_nil, is_empty.forall_iff, forall_const],
  intros hd tl ind_hyp,
  cases ind_hyp with M' ind_hyp,
  use max (hd+1) M',
  intro x,
  simp only [list.mem_cons_iff, lt_max_iff],
  specialize ind_hyp x,
  refine or.imp _ ind_hyp,
  omega,
end

/--Th length of the permutation corresponding to the list -/
def perm_of_list_length : list ℕ → ℕ
| [] := 0
| (hd :: tl) :=
  if (perm_of_list tl)⁻¹ hd > (perm_of_list tl)⁻¹ (hd+1) then  perm_of_list_length tl - 1
  else  perm_of_list_length tl + 1

lemma perm_of_list_length_coe  {n:ℕ} {l: list (fin n)}: length (perm_of_list_fin (n+1) l) = perm_of_list_length (list.map coe l) :=
begin
  apply l.rec_on,
  simp only [list.map_nil],
  unfold perm_of_list_fin perm_of_list_length,
  simp only [list.map_nil, list.prod_nil],
  exact (length_zero_iff_id).mpr (by refl),
  simp only [list.map],
  unfold perm_of_list_fin perm_of_list_length,
  simp only [list.map, list.prod_cons],
  unfold swap_map_fin,
  simp only [fin.val_eq_coe],
  intros hd tl ind_hyp,
  have rev_unfold: (list.map (swap_map_fin (n+1)) tl).prod = perm_of_list_fin (n+1) tl := by unfold perm_of_list_fin,
  rw rev_unfold,
  rw <-ind_hyp,
  have k := @length_mul_swap_left (n+1) (perm_of_list_fin (n+1) tl) ⟨hd.val,swap_map_fin._proof_1 (n+1) hd ⟩ (swap_map_fin._proof_2 (n+1) hd),
  simp only [fin.val_eq_coe, fin.coe_mk, gt_iff_lt] at k,
  have eq_cond:(perm_of_list (list.map coe tl))⁻¹ ↑hd > (perm_of_list (list.map coe tl))⁻¹ (↑hd + 1) = (((list.map (swap_map_fin (n+1)) tl).prod)⁻¹ ⟨↑hd + 1, _⟩ < ((list.map (swap_map_fin (n+1)) tl).prod)⁻¹ ⟨↑hd, _⟩ ):=
  begin
    simp only [list.map_map, gt_iff_lt, eq_iff_iff],
    simp only [coe_commutes],
    simp only [<-map_inv],
    rw [perm.of_subtype_apply_of_mem, perm.of_subtype_apply_of_mem],
    simp only [fin.lt_iff_coe_lt_coe],
    unfold perm_of_list_fin,
    recover,
    rw <-fin.val_eq_coe; exact swap_map_fin._proof_1 (n+1) hd,
    rw <-fin.val_eq_coe; exact swap_map_fin._proof_2 (n+1) hd,
  end,
  simp only [eq_cond],
  unfold perm_of_list_fin at k,
  exact k,
end

lemma perm_eq_imp_length_eq {w_1 w_2 :list ℕ}: (perm_of_list w_1 = perm_of_list w_2) → perm_of_list_length w_1 = perm_of_list_length w_2:=
begin
  have bounded_w_1 := list_bounded w_1,
  have bounded_w_2 := list_bounded w_2,
  cases bounded_w_1 with M_1 bounded_w_1,
  cases bounded_w_2 with M_2 bounded_w_2,
  let M := max M_1 M_2,
  have lt_coe_1 := exists_of_exists_unique
    (@lt_to_fin M w_1 (λ m mem, lt_of_lt_of_le (bounded_w_1 m mem) (le_sup_left))),
  have lt_coe_2 := exists_of_exists_unique
    (@lt_to_fin M w_2 (λ m mem, lt_of_lt_of_le (bounded_w_2 m mem) (le_sup_right))),
  cases lt_coe_1 with l_1 lt_coe_1,
  cases lt_coe_2 with l_2 lt_coe_2,
  rw [lt_coe_1,lt_coe_2, <- perm_of_list_length_coe,<- perm_of_list_length_coe, coe_commutes, coe_commutes],
  intro h,
  have h':= coe_embedding h,
  rw h',
end

lemma word_length_lt_eq_length  : ∀w:list ℕ, w.length ≥ perm_of_list_length w :=
begin
  intro w,
  apply w.rec_on,
  unfold perm_of_list_length,
  simp only [list.length, ge_iff_le, le_zero_iff],
  unfold perm_of_list_length,
  simp only [list.length, ge_iff_le],
  intros hd tl ind_hyp,
  split_ifs; omega,
end

lemma word_length_reduced  : ∀w:list ℕ, w.length = perm_of_list_length w →  is_reduced_word w :=
begin
  intros w,
  have bounded_w := list_bounded w,
  cases bounded_w with M bounded_w,
  have lt_coe := exists_of_exists_unique (@lt_to_fin M w  (bounded_w)),
  cases lt_coe with l lt_coe,
  rw lt_coe,
  intro h,
  apply word_length_reduced',
  refine eq.trans _ (eq.symm (@perm_of_list_length_coe M _)),
  refine eq.trans _ h,
  simp only [list.length_map],
end


lemma braid_equiv_eq_length {w_1 w_2 : list ℕ} : braid_equiv w_1 w_2 →
  perm_of_list_length w_1 = perm_of_list_length w_2 :=
begin
  intro h,
  have same_prod := braid_equiv_prod_eq h,
  exact perm_eq_imp_length_eq same_prod,
end

--#eval repr (@perm_of_list_fin 10 ( reduced_word' 10 (swap (⟨1 ,(cmp_eq_lt_iff 1 10).mp rfl⟩: (fin 10))  (⟨8,(cmp_eq_lt_iff 8 10).mp rfl⟩: (fin 10)) ) ))

lemma end_interval_length_fixed {l: list ℕ} {m k:ℕ} (h: list.minimum l > m ) :
  perm_of_list (l ++ list.Ico m (m+k)) (m+k) = m  :=
begin
  revert h m l,
  unfold perm_of_list swap_map,
  apply k.rec_on,
  simp only [gt_iff_lt, nat.nat_zero_eq_zero, add_zero, list.Ico.self_empty, list.append_nil],
  intros l,
  apply l.rec_on,
  simp only [list.map_nil, list.prod_nil, perm.coe_one, id.def, eq_self_iff_true, implies_true_iff],
  simp only [list.map, list.prod_cons, perm.coe_mul, comp_app],
  intros hd tl ind_hyp m hyp,
  rw list.minimum_cons at hyp,
  rw ind_hyp (lt_min_iff.mp hyp).2,
  unfold swap_map,
  have lt_hd:= (with_top.coe_lt_coe.mp (lt_min_iff.mp hyp).1),
  apply equiv.swap_apply_of_ne_of_ne,
  exact ne_of_lt lt_hd,
  exact ne_of_lt (lt_trans lt_hd (lt_add_one hd)),
  intros n ind_hyp l m hyp,
  rw [<-nat.add_one,<-add_assoc],
  simp [list.Ico.succ_top],
  unfold swap_map,
  simp only [swap_apply_right],
  simp only [gt_iff_lt, list.map_append, list.prod_append, perm.coe_mul, comp_app] at ind_hyp,
  exact ind_hyp hyp,
end

lemma lt_fixed {l:list ℕ} {m :ℕ} (h: list.minimum l > m ) : perm_of_list l m = m :=
begin
  unfold perm_of_list,
  revert h m,
  apply list.reverse_rec_on l,
  simp only [list.map_nil, list.prod_nil, perm.coe_one, id.def, eq_self_iff_true, implies_true_iff],
  intros hd tl ind_hyp m,
  simp only [list.map, gt_iff_lt, list.map_append, list.prod_append,
    list.prod_cons, list.prod_nil, mul_one, perm.coe_mul, comp_app],
  simp [list.minimum_concat],
  intros h1 h2,
  unfold swap_map,
  rw equiv.swap_apply_of_ne_of_ne (ne_of_lt h2) (ne_of_lt (lt_trans h2 (lt_add_one tl))),
  apply ind_hyp,
  exact h1,
end

lemma Ico_min {m k:ℕ} : k ≠ 0 → (list.Ico m (m+k)).minimum = ↑m :=
begin
  revert m,
  apply k.rec_on,
  intro m,
  simp only [ne.def, eq_self_iff_true, not_true, is_empty.forall_iff],
  intros n h,
  simp only [<-nat.add_one,<-add_assoc],
  simp only [list.Ico.succ_top, le_add_iff_nonneg_right, zero_le', nat.succ_ne_zero, if_false],
  simp [list.minimum_concat],
  intro m,
  by_cases h': n=0,
  rw h',
  simp only [add_zero, list.Ico.self_empty, list.minimum_nil, min_eq_right, le_top],
  rw h,
  simp only [min_eq_left, with_top.coe_le_coe, le_add_iff_nonneg_right, zero_le'],
  exact h',
end

lemma minimum_fixed {l: list ℕ} {m k:ℕ} (h1: (l ++ list.Ico m (m+k)).minimum =↑m )
  (h2: list.minimum l > m ) : (∀x<m, perm_of_list (l ++ list.Ico m (m+k)) x= x ) ∧
  (perm_of_list (l ++ list.Ico m (m+k))) m ≠ m :=
begin
  split,
  intros x h,
  apply lt_fixed,
  rw h1,
  exact with_top.coe_lt_coe.mpr h,
  revert h1 h2 m k,
  unfold perm_of_list swap_map,
  apply list.rec_on l,
  simp only [list.nil_append, list.minimum_nil, gt_iff_lt, ne.def],
  intros m k,
  revert m,
  apply k.rec_on,
  simp only [add_zero, list.Ico.self_empty, list.minimum_nil, with_top.top_ne_nat, is_empty.forall_iff, forall_const],
  intros n h m,
  simp only [<-nat.add_one,<-add_assoc],
  simp only [list.Ico.succ_top, list.map, le_add_iff_nonneg_right, zero_le', list.map_append,
    list.prod_append, list.prod_cons, list.prod_nil, mul_one, perm.coe_mul, comp_app],
  simp only [list.minimum_concat],
  intros h1 h2,
  by_cases h': n=0,
  rw h',
  unfold swap_map,
  simp only [add_zero, list.Ico.self_empty, list.map_nil, list.prod_nil, swap_apply_left,
    perm.coe_one, id.def, nat.succ_ne_self, not_false_iff],
  unfold swap_map,
  have lt_plus_n: m<m+n := by omega,
  rw equiv.swap_apply_of_ne_of_ne (ne_of_lt lt_plus_n)
    (ne_of_lt (lt_trans lt_plus_n (lt_add_one (m + n)))),
  apply h,
  exact Ico_min h',
  exact h2,
  intros hd tl,
  simp only [list.map, gt_iff_lt, list.map_append, list.prod_append,
    perm.coe_mul, comp_app, ne.def, list.cons_append, list.prod_cons],
  simp only [list.minimum_cons, lt_min_iff, with_top.coe_lt_coe, and_imp],
  intros ind_hyp m k hyp1 hyp2 hyp3,
  by_contra,
  have h'':= congr_arg (swap_map hd) h,
  unfold swap_map at h'',
  rw [equiv.swap_apply_of_ne_of_ne (ne_of_lt hyp2) (ne_of_lt (lt_trans hyp2 (lt_add_one (hd))))]
    at h'',
  simp only [swap_apply_self] at h'',
  refine ind_hyp _ _ h'',
  rw <-hyp1,
  apply eq.symm,
  by_contra,
  have k':= (((iff.not min_eq_right_iff).mp) (h)),
  simp only [not_le] at k',
  have k'':= min_eq_left_of_lt k',
  rw k'' at hyp1,
  exact (ne_of_lt hyp2) (with_top.coe_eq_coe.mp (eq.symm hyp1)),
  exact hyp3,
end

lemma eq_prod_unique {l l' : list ℕ} {m k m' k' : ℕ} (h1 : (l ++ list.Ico m (m+k)).minimum = ↑m)
  (h2 : list.minimum l > m ) (h1' : (l' ++ list.Ico m' (m'+k')).minimum = ↑m')
  (h2': list.minimum l' > m') : perm_of_list (l ++ list.Ico m (m + k)) =
  perm_of_list (l' ++ list.Ico m' (m' + k')) → k = k' ∧ m = m' :=
begin
  intro h,
  have min_eq:= minimum_fixed h1 h2,
  have min_eq':= minimum_fixed h1' h2',
  rw <-h at min_eq',
  have order:= lt_trichotomy m m',
  cases order,
  have eq1:= min_eq'.1 m order,
  have eq2:= min_eq.2,
  exfalso,
  exact eq2 eq1,
  cases (or.symm order),
  have eq1:= min_eq.1 m' h_1,
  have eq2:= min_eq'.2,
  exfalso,
  exact eq2 eq1,
  have k_eq:= @end_interval_length_fixed _ _ k h2,
  have k_eq':= @end_interval_length_fixed _ _ k' h2',
  rw <-h at k_eq',
  rw <- h_1 at k_eq',
  have keq_1:= congr_arg ⇑( (perm_of_list (l ++ list.Ico m (m + k))))⁻¹ k_eq,
  have keq_2:= congr_arg ⇑( (perm_of_list (l ++ list.Ico m (m + k))))⁻¹ k_eq',
  simp only [perm.inv_apply_self] at keq_1,
  simp only [perm.inv_apply_self] at keq_2,
  rw <-keq_1 at keq_2,
  simp only [add_right_inj] at keq_2,
  exact and.intro (eq.symm keq_2) h_1,
end


lemma move_stuff_right {w:list ℕ } (h1 : w ≠ []) (h2 : perm_of_list_length w = w.length) :
  ∃ (m : ℕ) (k' : ℕ) (l : list ℕ), ↑m = list.minimum w ∧
  braid_equiv w (l ++ list.Ico m (m + k')) ∧ l.minimum > ↑m ∧ l.length < w.length:=
begin
    let min := list.minimum w,
    have nontrivial : min ≠ none :=  (not_iff_not_of_iff list.minimum_eq_none).mpr h1,
    have ex: ∃m:ℕ, ↑m = min  := can_lift.prf min nontrivial,
    cases ex with m ex,
    have dec:= decomp ex,
    rcases dec with ⟨k, s, t, dec1, dec2, dec3⟩,
    have right_most := move_decomp_right ex (and.intro dec1 dec2)
      (word_length_reduced w (eq.symm h2)) dec3.2,
    rcases right_most with ⟨k', l', right_most⟩,
    have pos := nat.pos_of_ne_zero right_most.2.2,
    use [m, k', l'],
    rw (braid_equiv_length_eq (right_most.1)),
    simp only [list.length_append, list.Ico.length, add_tsub_cancel_left, lt_add_iff_pos_right],
    tauto,
end

lemma red_imp_infix_red_fin (s t :list (fin n)) {l:list (fin n)} :
 (s++ l ++t).length = length (perm_of_list_fin (n+1) (s++ l ++t)) →
 l.length = length (perm_of_list_fin (n+1) l):=
begin
  intro h,
  suffices: l.length ≤ length (perm_of_list_fin (n+1) l),
  have ge:= word_length_lt_eq_length' (perm_of_list_fin (n+1) l) l (rfl),
  exact ge_antisymm ge this,
  revert l h t,
  apply s.rec_on,
  simp only [list.nil_append, list.length_append],
  intro t,
  apply list.reverse_rec_on t,
  simp only [list.length, add_zero, list.append_nil],
  intro l,
  exact eq.le,
  unfold perm_of_list_fin,
  simp only [list.map, list.map_append, list.prod_append, list.length_append, list.length_singleton, list.prod_cons, list.prod_nil,
  mul_one],
  intros l a ind_hyp hd hyp,
  unfold swap_map_fin at hyp,
  rw <-mul_assoc at hyp,
    have h := @length_inc_or_dec (n+1) ((list.map (swap_map_fin (n+1)) hd).prod * (list.map (swap_map_fin (n+1)) l).prod) ⟨a.val,swap_map_fin._proof_1 (n+1) a ⟩ (swap_map_fin._proof_2 (n+1) a),
    cases h with h h,
    simp only [fin.val_eq_coe, fin.coe_mk] at h,
    simp only [fin.val_eq_coe] at hyp,
    rw h at hyp,
    simp only [<-list.prod_append, <-list.map_append, <-list.map] at hyp,
    have ge:= word_length_lt_eq_length' (perm_of_list_fin (n+1) (hd ++ l)) (hd ++ l) (rfl),
    unfold perm_of_list_fin at ge,
    simp only [list.length_append, list.map_append, list.prod_append, ge_iff_le] at ge,
    simp only [list.map_append, list.prod_append] at hyp,
    omega,
    simp only [fin.val_eq_coe] at hyp,
    simp only [fin.val_eq_coe, fin.coe_mk] at h,
    rw <-hyp at h,
    have h': hd.length + l.length = length ((list.map (swap_map_fin (n+1)) hd).prod * (list.map (swap_map_fin (n+1)) l).prod) := by omega,
    exact ind_hyp h',
  intros hd tl ind_hyp t l,
  rw [<-list.singleton_append],
  simp only [list.length, list.singleton_append, list.cons_append],
  unfold perm_of_list_fin,
  simp only [list.map, list.nil_append, list.map_append, list.prod_cons],
  unfold swap_map_fin,
  intro h,
  have h' := @length_mul_swap_left (n+1) (list.map (swap_map_fin (n+1)) tl ++ list.map (swap_map_fin (n+1)) l ++ list.map (swap_map_fin (n+1)) t).prod ⟨hd.val,swap_map_fin._proof_1 (n+1) hd ⟩ (swap_map_fin._proof_2 (n+1) hd),
  split_ifs at h',
  have ge:= word_length_lt_eq_length'  (perm_of_list_fin (n+1) (tl++l++t)) (tl ++ l ++t) (rfl),
  unfold perm_of_list_fin at ge,
  simp only [fin.val_eq_coe, fin.coe_mk] at h',
  simp only [fin.val_eq_coe] at h,
  rw h' at h,
  simp only [list.append_assoc, list.length_append, list.prod_append] at h,
  simp only [list.append_assoc, list.length_append, list.map_append, list.prod_append, ge_iff_le] at ge,
  omega,
  simp only [fin.val_eq_coe, fin.coe_mk] at h',
  simp only [fin.val_eq_coe, fin.coe_mk] at h,
  rw h' at h,
  have eqq:(tl ++ l ++ t).length = length (perm_of_list_fin (n+1) (tl ++ l ++ t)) :=
  begin
    unfold perm_of_list_fin,
    simp only [list.map_append],
    omega,
  end,
  have k:= ind_hyp t eqq,
  unfold perm_of_list_fin at k,
  exact k,
end

lemma red_imp_infix_red (s t :list ℕ) {l:list ℕ} :
  (s++ l ++t).length = perm_of_list_length (s++ l ++t) → l.length = perm_of_list_length l:=
begin
  have bounded := list_bounded (s++ l ++t),
  cases bounded with M bounded,
  have exists_big := lt_to_fin M bounded,
  simp only [list.append_assoc, list.mem_append] at bounded,
  have lt_s:∀ (m : ℕ), m ∈ s  → m < M := λ m, λ mem_s, bounded m (by tauto),
  have lt_l:∀ (m : ℕ), m ∈ l  → m < M := λ m, λ mem_l, bounded m (by tauto),
  have lt_t:∀ (m : ℕ), m ∈ t  → m < M := λ m, λ mem_l, bounded m (by tauto),
  cases exists_of_exists_unique(lt_to_fin M lt_s) with s' es,
  cases exists_of_exists_unique (lt_to_fin M lt_l) with l' el,
  cases exists_of_exists_unique (lt_to_fin M lt_t) with t' et,
  intro h,
  simp only [el],
  rw <- (@perm_of_list_length_coe M l'),
  simp only [list.length_map],
  apply (@red_imp_infix_red_fin M s' t'),
  rw  (@perm_of_list_length_coe M _),
  rw [<-list.length_map coe],
  simp only [ list.map_append, list.length_map],
  rw [<- es, <-el, <- et],
  exact h,
end


theorem Tits'_theorem  : ∀w_1, perm_of_list_length w_1 = w_1.length →
  ∀w_2:list ℕ,  perm_of_list w_1 = perm_of_list w_2
  → perm_of_list_length w_2 = w_2.length → braid_equiv w_1 w_2
|w_1:=
  if h':w_1 = [] then
  begin
    rw h',
    intros h w_2 h2 h3,
    have h4:= perm_eq_imp_length_eq h2,
    unfold perm_of_list_length at h4,
    rw h3 at h4,
    rw list.length_eq_zero.mp (eq.symm h4),
    exact braid_equiv.nil,
  end
  else
  begin
    intros h1 w_2 h2 h3,
    have k:= (not_iff_not_of_iff list.length_eq_zero).mpr h',
    have braided_w_1:= move_stuff_right h' h1,
    have h':= perm_eq_imp_length_eq h2,
    rw h' at h1,
    rw h3 at h1,
    rw <-h1 at k,
    rw <-h3 at h1,
    rw <-h' at h1,
    have k':= (not_iff_not_of_iff list.length_eq_zero).mp k,
    have braided_w_2:= move_stuff_right k' h3,
    rcases braided_w_1 with ⟨m1, k1, l1, braided_w_1⟩,
    rcases braided_w_2 with ⟨m2, k2, l2, braided_w_2⟩,
    have same_prod: perm_of_list (l1 ++ list.Ico m1 (m1 + k1)) = perm_of_list (l2 ++ list.Ico m2 (m2 + k2)) :=
    begin
      have eq1:= braid_equiv_prod_eq (braided_w_1.2).1,
      have eq2:= braid_equiv_prod_eq (braided_w_2.2).1,
      refine eq.trans (eq.symm eq1) _,
      refine eq.trans _ eq2,
      exact h2,
    end,
    have same_numbers : k1 = k2 ∧ m1 = m2 :=
    begin
      refine eq_prod_unique _ ((braided_w_1.2).2).1 _ ((braided_w_2.2).2).1 same_prod,
      rw braided_w_1.1,
      rw braid_equiv_min (braided_w_1.2).1,
      rw braided_w_2.1,
      rw braid_equiv_min (braided_w_2.2).1,
    end,
    rw [<-same_numbers.1, <-same_numbers.2] at braided_w_2,
    suffices: braid_equiv l1 l2,
    have this':= braid_equiv_infix [] (list.Ico m1 (m1 + k1)) this,
    simp only [list.nil_append] at this',
    refine braid_equiv.trans (braided_w_1.2).1 _,
    refine braid_equiv.trans this' _,
    refine braid_equiv.trans _ (braid_equiv.symm (braided_w_2.2).1),
    exact braid_equiv.refl,
    have lth_eq_1: perm_of_list_length l1 = l1.length :=
    begin
      refine eq.symm (red_imp_infix_red [] (list.Ico m1 (m1 + k1)) _),
      simp only [list.nil_append],
      refine eq.trans _ (braid_equiv_eq_length  (braided_w_1.2).1),
      rw h1,
      exact eq.symm (braid_equiv_length_eq (braided_w_1.2).1),
    end,
    have prod_eq :perm_of_list l1 = perm_of_list l2:=
    begin
    rw [<-same_numbers.1, <-same_numbers.2] at same_prod,
    unfold perm_of_list,
    unfold perm_of_list at same_prod,
    simp only [list.map_append, list.prod_append, mul_left_inj] at same_prod,
    exact same_prod,
    end,
    have lth_eq_2 : perm_of_list_length l2 = l2.length :=
    begin
    refine eq.symm (red_imp_infix_red [] (list.Ico m1 (m1 + k1)) _),
    simp only [list.nil_append],
    refine eq.trans _ (braid_equiv_eq_length  (braided_w_2.2).1),
    rw h3,
    exact eq.symm (braid_equiv_length_eq (braided_w_2.2).1),
    end,
    exact have l1.length<w_1.length:= ((braided_w_1.2).2).2,
    Tits'_theorem l1 lth_eq_1 l2 prod_eq lth_eq_2,
  end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf list.length⟩]}

lemma Tits'_fin : ∀π : perm (fin(n+1)), ∀l_1 :list (fin n), ∀ l_2:list (fin n),
  perm_of_list_fin (n+1) (l_1) = π → perm_of_list_fin (n+1) (l_2) = π →
    list.length l_1= length (π) → list.length l_2 = length(π) → braid_equiv_fin l_1 l_2 :=
begin
  intros π l1 l2 h1 h2 h3 h4,
  unfold braid_equiv_fin,
  apply Tits'_theorem,
  refine eq.trans (eq.symm perm_of_list_length_coe) _,
  rw h1,
  simp only [list.length_map],
  exact h3.symm,
  simp only [coe_commutes],
  exact congr_arg perm.of_subtype (eq.trans h1 h2.symm),
  refine eq.trans (eq.symm perm_of_list_length_coe) _,
  rw h2,
  simp only [list.length_map],
  exact h4.symm,
end
