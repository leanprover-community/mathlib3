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

/--describes the image of the inversions of a permutation under the map swap_apply -/
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
  simp only
    [swap_apply_right, fin.val_eq_coe, swap_apply_left, fin.coe_fin_le, fin.coe_fin_le] at k3,
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
lemma length_mul_swap_descent {π : equiv.perm (fin n)} {i: fin n} (h1: (i.val + 1) < n)
  (h2: π i> π (⟨i+1, h1⟩: fin n)) :
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
lemma length_mul_swap_ascent  {π : equiv.perm (fin n)} {i: fin n} (h1: (i.val + 1) < n)
  (h2: π i< π (⟨i+1, h1⟩: fin n)) :
 length(π * (equiv.swap i (⟨i+1, h1⟩: fin n)))= length(π)+1 :=
begin
  have h3: (π * (equiv.swap i (⟨i+1, h1⟩: fin n))) i> (π * (equiv.swap i (⟨i+1, h1⟩: fin n)))
    (⟨i+1, h1⟩: fin n) :=
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
    simp only [perm.coe_mul, comp_app, mem_filter, mem_sigma, mem_univ, fin.coe_mk, mem_attach_fin,
      self_mem_range_succ, swap_apply_right, swap_apply_left, true_and],
    exact (le_of_lt h2),
  end,
  have h6:= (add_left_inj 1).mpr h4,
  have h7 : length (π * swap i ⟨↑i + 1, h1⟩) - 1 + 1 =length (π * swap i ⟨↑i + 1, h1⟩) :=
    nat.sub_add_cancel (nat.one_le_iff_ne_zero.mpr h5),
  rw h7 at h6,
  exact eq.symm (h6),
end


lemma perm_neq (π : equiv.perm (fin n)) (i: fin n) (h1: (i.val + 1) < n) :
  π i ≠  π (⟨i+1, h1⟩: fin n) :=
  begin
    by_contra,
    have h':= (equiv.injective π) h,
    rw fin.eq_iff_veq at h',
    simp only [fin.val_eq_coe, self_eq_add_right, nat.one_ne_zero] at h',
    exact h',
  end

lemma length_mul_swap {π : equiv.perm (fin n)} {i: fin n} (h1: (i.val + 1) < n) :
 length(π * (equiv.swap i (⟨i+1, h1⟩: fin n))) =
  if π i> π (⟨i+1, h1⟩: fin n) then length π-1 else length π +1 :=
begin
  split_ifs,
  exact (length_mul_swap_descent h1 h),
  simp only [not_lt] at h,
  have h4:= lt_of_le_of_ne h (perm_neq π i h1),
  exact (length_mul_swap_ascent h1 h4),
end



/--function that acts on pairs by switching the order and applying the permutation-/
def switch_apply (π : equiv.perm (fin n)) : (Σ (b : fin n), fin n) →
   (Σ (b : fin n), fin n) := λ x, ⟨π x.2, π x.1⟩

lemma maps_correct (π: equiv.perm (fin n)) : set.maps_to (switch_apply π)
  (λ (x : Σ (b : fin n), fin n), x ∈ (inversions π).val)
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
lemma length_of_inv (π : equiv.perm (fin n)) : length π = length (π⁻¹) :=
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
    have k2: π⁻¹(supp_max)∈ π.support :=
      by { apply perm.apply_mem_support.mp, rw [perm.apply_inv_self], exact k1},
    have k3: π⁻¹(supp_max)≠ supp_max  :=
      by {apply perm.mem_support.mp, rw perm.support_inv, exact k1,},
    have k4: π⁻¹ supp_max < supp_max  :=  (k3).le_iff_lt.mp (finset.le_max' _ _ k2),
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
 let supp_max  := π.support.max' (finset.nonempty_of_ne_empty
            ((decidable.not_iff_not.mpr (equiv.perm.support_eq_empty_iff) ).mpr h')) in
 length (π * swap (π⁻¹ (supp_max)) (⟨π⁻¹ (supp_max) + 1, inv_supp_max_plus_one_lt h'⟩)) + 1
  = length π :=
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
 let supp_max  := π.support.max' (finset.nonempty_of_ne_empty
          ((decidable.not_iff_not.mpr (equiv.perm.support_eq_empty_iff) ).mpr h')) in
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
    let supp_max  := π.support.max' (finset.nonempty_of_ne_empty
            ((decidable.not_iff_not.mpr (equiv.perm.support_eq_empty_iff) ).mpr h')) in
    have length_less: length (π * swap (π⁻¹ (π.support.max' _))
      (⟨π⁻¹ (supp_max) + 1, inv_supp_max_plus_one_lt h'⟩)) < length π := @length_dec n π h',
     list.concat (@reduced_word (π * swap (π⁻¹ supp_max)
        (⟨π⁻¹ (supp_max) + 1, inv_supp_max_plus_one_lt h'⟩ :fin n)))
      (swap (π⁻¹ supp_max) (⟨π⁻¹ (supp_max) + 1, inv_supp_max_plus_one_lt h'⟩))
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf length⟩]}

/--A reduced word of a permutation has product equal to the original permutation-/
lemma red_word_prod_eq   : ∀ π, (@reduced_word n π).prod = π
|π:=
  if h':π =1 then
  begin
    rw reduced_word,
    split_ifs,
    simp only [list.prod_nil],
    exact eq.symm h'
  end
  else
  have length_less: length (π * swap (π⁻¹ (π.support.max' _))
    (⟨π⁻¹ ((π.support.max' _)) + 1, inv_supp_max_plus_one_lt h'⟩ :fin n)) < length π :=
      @length_dec n π h',
  begin
    rw reduced_word, split_ifs,
    simp only [list.concat_eq_append, list.prod_append, list.prod_cons, list.prod_nil, mul_one],
    suffices k: (reduced_word (π * swap (π⁻¹ (π.support.max' _))
      (⟨π⁻¹ ((π.support.max' _)) + 1, inv_supp_max_plus_one_lt h'⟩ :fin n))).prod =
      (π * swap (π⁻¹ (π.support.max' _)) (⟨π⁻¹ ((π.support.max' _)) + 1,
        inv_supp_max_plus_one_lt h'⟩ :fin n)),
    rw k,
    simp only [mul_swap_mul_self],
    exact red_word_prod_eq  _,
  end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf length⟩]}

/--A reduced word of a permutation has length equal to the length of the permutation-/
lemma red_word_length   :∀ π, (@reduced_word n π).length = length π
|π:=
  if h':π =1 then
  begin
    rw reduced_word,
    split_ifs,
    simp only [list.length],
    exact eq.symm (length_zero_iff_id.mpr h'),
  end
  else
  have length_less: length (π * swap (π⁻¹ (π.support.max' _))
  (⟨π⁻¹ ((π.support.max' _)) + 1, inv_supp_max_plus_one_lt h'⟩ :fin n)) < length π  :=
      length_dec h',
  begin
    rw reduced_word, split_ifs,
    simp only [list.concat_eq_append, list.length_append, list.length_singleton],
    suffices k: (reduced_word (π * swap (π⁻¹ (π.support.max' _)) (⟨π⁻¹ ((π.support.max' _)) + 1,
      inv_supp_max_plus_one_lt h'⟩ :fin n))).length = length (π * swap (π⁻¹ (π.support.max' _))
     (⟨π⁻¹ ((π.support.max' _)) + 1, inv_supp_max_plus_one_lt h'⟩ :fin n)),
    rw k,
    exact length_dec_one _,
    exact red_word_length  _,
  end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf length⟩]}
