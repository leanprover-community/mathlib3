/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes
-/
import data.matrix.basic
import group_theory.perm.sign

import data.polynomial

universes u v w
open equiv equiv.perm finset function

namespace matrix

variables {n : Type u} [fintype n] [decidable_eq n] {R : Type v} [comm_ring R]

local notation `ε` σ:max := ((sign σ : ℤ ) : R)

definition det (M : matrix n n R) : R :=
univ.sum (λ (σ : perm n), ε σ * univ.prod (λ i, M (σ i) i))

@[simp] lemma det_diagonal {d : n → R} : det (diagonal d) = univ.prod d :=
begin
  refine (finset.sum_eq_single 1 _ _).trans _,
  { intros σ h1 h2,
    cases not_forall.1 (mt (equiv.ext _ _) h2) with x h3,
    convert ring.mul_zero _,
    apply finset.prod_eq_zero,
    { change x ∈ _, simp },
    exact if_neg h3 },
  { simp },
  { simp }
end

@[simp] lemma det_zero (h : nonempty n) : det (0 : matrix n n R) = 0 :=
by rw [← diagonal_zero, det_diagonal, finset.prod_const, ← fintype.card,
  zero_pow (fintype.card_pos_iff.2 h)]

@[simp] lemma det_one : det (1 : matrix n n R) = 1 :=
by rw [← diagonal_one]; simp [-diagonal_one]

lemma det_mul_aux {M N : matrix n n R} {p : n → n} (H : ¬bijective p) :
  univ.sum (λ σ : perm n, (ε σ) * (univ.prod (λ x, M (σ x) (p x) * N (p x) x))) = 0 :=
begin
  obtain ⟨i, j, hpij, hij⟩ : ∃ i j, p i = p j ∧ i ≠ j,
  { rw [← fintype.injective_iff_bijective, injective] at H,
    push_neg at H,
    exact H },
  exact sum_involution
    (λ σ _, σ * swap i j)
    (λ σ _,
      have ∀ a, p (swap i j a) = p a := λ a, by simp only [swap_apply_def]; split_ifs; cc,
      have univ.prod (λ x, M (σ x) (p x)) = univ.prod (λ x, M ((σ * swap i j) x) (p x)),
        from prod_bij (λ a _, swap i j a) (λ _ _, mem_univ _) (by simp [this])
          (λ _ _ _ _ h, (swap i j).injective h)
          (λ b _, ⟨swap i j b, mem_univ _, by simp⟩),
      by simp [sign_mul, this, sign_swap hij, prod_mul_distrib])
    (λ σ _ _ h, hij (σ.injective $ by conv {to_lhs, rw ← h}; simp))
    (λ _ _, mem_univ _)
    (λ _ _, equiv.ext _ _ $ by simp)
end

@[simp] lemma det_mul (M N : matrix n n R) : det (M * N) = det M * det N :=
calc det (M * N) = univ.sum (λ σ : perm n, (univ.pi (λ a, univ)).sum
    (λ (p : Π (a : n), a ∈ univ → n), ε σ *
    univ.attach.prod (λ i, M (σ i.1) (p i.1 (mem_univ _)) * N (p i.1 (mem_univ _)) i.1))) :
  by simp only [det, mul_val', prod_sum, mul_sum]
... = univ.sum (λ σ : perm n, univ.sum
    (λ p : n → n, ε σ * univ.prod (λ i, M (σ i) (p i) * N (p i) i))) :
  sum_congr rfl (λ σ _, sum_bij
    (λ f h i, f i (mem_univ _)) (λ _ _, mem_univ _)
    (by simp) (by simp [funext_iff]) (λ b _, ⟨λ i hi, b i, by simp⟩))
... = univ.sum (λ p : n → n, univ.sum
    (λ σ : perm n, ε σ * univ.prod (λ i, M (σ i) (p i) * N (p i) i))) :
  finset.sum_comm
... = ((@univ (n → n) _).filter bijective).sum (λ p : n → n, univ.sum
    (λ σ : perm n, ε σ * univ.prod (λ i, M (σ i) (p i) * N (p i) i))) :
  eq.symm $ sum_subset (filter_subset _)
    (λ f _ hbij, det_mul_aux $ by simpa using hbij)
... = (@univ (perm n) _).sum (λ τ, univ.sum
    (λ σ : perm n, ε σ * univ.prod (λ i, M (σ i) (τ i) * N (τ i) i))) :
  sum_bij (λ p h, equiv.of_bijective (mem_filter.1 h).2) (λ _ _, mem_univ _)
    (λ _ _, rfl) (λ _ _ _ _ h, by injection h)
    (λ b _, ⟨b, mem_filter.2 ⟨mem_univ _, b.bijective⟩, eq_of_to_fun_eq rfl⟩)
... = univ.sum (λ σ : perm n, univ.sum (λ τ : perm n,
    (univ.prod (λ i, N (σ i) i) * ε τ) * univ.prod (λ j, M (τ j) (σ j)))) :
  by simp [mul_sum, det, mul_comm, mul_left_comm, prod_mul_distrib, mul_assoc]
... = univ.sum (λ σ : perm n, univ.sum (λ τ : perm n,
    (univ.prod (λ i, N (σ i) i) * (ε σ * ε τ)) *
    univ.prod (λ i, M (τ i) i))) :
  sum_congr rfl (λ σ _, sum_bij (λ τ _, τ * σ⁻¹) (λ _ _, mem_univ _)
    (λ τ _,
      have univ.prod (λ j, M (τ j) (σ j)) = univ.prod (λ j, M ((τ * σ⁻¹) j) j),
        by rw prod_univ_perm σ⁻¹; simp [mul_apply],
      have h : ε σ * ε (τ * σ⁻¹) = ε τ :=
        calc ε σ * ε (τ * σ⁻¹) = ε ((τ * σ⁻¹) * σ) :
          by rw [mul_comm, sign_mul (τ * σ⁻¹)]; simp [sign_mul]
        ... = ε τ : by simp,
      by rw h; simp [this, mul_comm, mul_assoc, mul_left_comm])
    (λ _ _ _ _, (mul_right_inj _).1) (λ τ _, ⟨τ * σ, by simp⟩))
... = det M * det N : by simp [det, mul_assoc, mul_sum, mul_comm, mul_left_comm]

instance : is_monoid_hom (det : matrix n n R → R) :=
{ map_one := det_one,
  map_mul := det_mul }

@[simp] lemma det_neg_one : det (-1 : matrix n n R) = (-1) ^ fintype.card n :=
by { rw [←diagonal_one, diagonal_neg, det_diagonal, finset.prod_const], refl }

@[simp] lemma det_neg (M : matrix n n R) : det (-M) = (-1) ^ fintype.card n * det M :=
by rw [neg_eq_neg_one_mul, det_mul, det_neg_one]

--TODO: move
lemma is_semiring_hom.map_nat_cast (a : ℕ) {S : Type w} [comm_ring S] (f : R → S) [hf : is_semiring_hom f] :
  f a = a :=
begin
induction a with _ hn,
{ rw_mod_cast [hf.map_zero] },
{ rw [nat.succ_eq_add_one, nat.cast_add, hf.map_add], rw_mod_cast [hf.map_one, hn], refl }
end

lemma det_map_hom {S : Type w} [comm_ring S] (f : R → S) [is_ring_hom f] (M : matrix n n R) :
  f (det M) = det (λ i j, f (M i j)) :=
begin
  unfold det,
  rw [←finset.sum_hom f],
  congr,
  ext,
  rw [is_ring_hom.map_mul f, ←finset.prod_hom f],
  congr,
  induction (sign x : ℤ) with _ n,
  { exact is_semiring_hom.map_nat_cast _ f },
  { rw [int.neg_succ_of_nat_eq, int.cast_neg, is_ring_hom.map_neg f],
    norm_cast,
    rw [is_semiring_hom.map_nat_cast _ f, int.cast_neg, int.cast_coe_nat] }
end

variables {m : Type u} [fintype m] [decidable_eq m]
variables {l o : Type w} [fintype l] [decidable_eq l] [fintype o] [decidable_eq o]

def submatrix (A : matrix m n R) (row : l → m) (col : o → n) : matrix l o R :=
  λ i j, A (row i) (col j)

def swap_subtype (i j : n) : {k // k ≠ i} → {k // k ≠ j} := subtype.map (swap i j)
  (λ a hi, by { by_cases hj : a ≠ j, rwa [swap_apply_of_ne_of_ne hi hj],
    rw [ne.def, not_not] at hj, symmetry, rw[hj] at hi, rwa [hj, swap_apply_right] })

def minor2 (i j : n) (M : matrix n n R) : R :=
det $ submatrix M (subtype.val ∘ swap_subtype i j) (subtype.val : {k : n // k ≠ i} → n)

lemma laplace_expansion_aux (M : matrix n n R) (i j : n) :
  univ.sum (λ σ : { σ : perm n // σ.to_fun i = j }, ε σ.val * univ.prod (λ l, M (σ l) l)) =
  M j i * minor2 i j M :=
calc univ.sum (λ σ : { σ : perm n // σ.to_fun i = j }, ε σ.val * univ.prod (λ l, M (σ l) l)) =
      M j i * univ.sum (λ σ : { σ : perm n // σ.to_fun i = j }, ε σ.val *
        (erase univ i).prod (λ l, M (σ l) l)) :
  begin rw [mul_sum], conv_rhs { congr, funext, skip, funext, rw [mul_comm, mul_assoc, mul_comm _ (M j i)],
    rw [show M j i = M (x i) i, begin unfold_coes, sorry end],
    rw [←@prod_insert _ _ _ _ (λ l, M (x l) l) _ _ (not_mem_erase i _)],
    rw [insert_erase (mem_univ _)] } end
... = M j i * univ.sum (λ σ : { σ : perm n // σ.to_fun i = j }, ε σ.val *
        (erase univ i).prod (λ l, M (equiv.swap i j $ equiv.swap i j $ σ l) l)) :
  begin congr, funext, apply congr_arg, congr, funext, rw [swap_swap_apply] end
... = M j i * univ.sum (λ τ : perm { k // k ≠ i }, ε τ * univ.prod (λ l, M (swap i j $ τ l) l)) :
  begin
    apply congr_arg,
    refine sum_bij (λ σ _, subtype_congr (equiv.trans σ.1 (swap i j))
        (λ l, begin rw [equiv.trans_apply, not_iff_not], unfold_coes,
          exact ⟨λ h, by {rw [h, σ.2], exact swap_apply_right i j }, sorry⟩ end))
      (λ _ _, mem_univ _) _
      (λ σ₁ σ₂ _ _ h, by { rw [subtype.ext], ext l, by_cases hl : l = i,
        { unfold_coes, rw [hl, σ₁.2, σ₂.2] },
        { let h1 := congr_arg equiv.to_fun h,
          have h2 := congr_fun h1 ⟨l, hl⟩,
          have h3 := congr_arg (equiv.swap i j ∘ subtype.val) h2,
          change equiv.swap i j (equiv.swap i j (σ₁.val l)) = equiv.swap i j (equiv.swap i j (σ₂.val l)) at h3,
          rwa [swap_swap_apply, swap_swap_apply] at h3 } } )
      (λ τ hτ, sorry ), --make this nicer,
    intros σ _,
    rw [show sign (subtype_congr (equiv.trans (σ.val) (swap i j)) _) = sign σ.val, from sorry],
    apply congr_arg,
    refine prod_bij (λ l hl, ⟨l, (mem_erase.mp hl).1⟩) (λ _ _, mem_univ _) (λ _ _, rfl) _ _,
    { assume l1 l2 _ _ h, sorry },
    { assume l _, exact ⟨l, mem_erase.mpr ⟨l.2, mem_univ _⟩, eq.symm (subtype.eta _ _)⟩ }
  end
... = M j i * minor2 i j M : rfl

lemma laplace_expansion (M : matrix n n R) (i : n) : det M = univ.sum (λ j, M j i * minor2 i j M) :=
begin
  conv_rhs { congr, skip, funext, rw ←laplace_expansion_aux },
  rw ←@sum_sigma _ _ _ (λ j, {σ : perm n // σ.to_fun i = j}) _ _
    (λ σ, ε (σ.2.val) * univ.prod (λ l, M (σ.2 l) l)),
  refine sum_bij (λ σ _, sigma.mk (σ i) ⟨σ, rfl⟩) (by simp [mem_sigma, mem_univ, and_self])
    (λ _ _, rfl) _ _,
  { intros _ _ _ _ h,
    have h2, from (sigma.mk.inj h).1,
    have h3, from type_eq_of_heq (sigma.mk.inj h).2,
    have h4, from (sigma.mk.inj h).2,
    sorry
    --rw [@heq_iff_eq (perm (fin k)) (λ σ : perm (fin k), σ i = a₁ i)] at h3,
    --rw [@heq_iff_eq _ (@subtype.mk (perm (fin k)) (λ (σ : perm (fin k)), σ i = a₁ i) a₁ _) (@subtype.mk (perm (fin k)) (λ (σ : perm (fin k)), σ i = a₂ i) a₂ _), subtype.mk_eq_mk] at h2,
  },
  { intros f h, existsi [f.snd.val, finset.mem_univ _],
    refine sigma.eq (eq.symm $ f.snd.property) (subtype.eq _),
    simp only [], congr, dsimp, unfold_coes, simp [f.snd.property], simp only [eq_rec_heq] }
end

open polynomial
lemma test1 (i : n) (M : matrix n n R) :
  submatrix (diagonal (λ _:n, (X : polynomial R)) - (λ k l, C (M k l))) (subtype.val ∘ swap_subtype i i) (subtype.val : {k : n // k ≠ i} → n) =
  (diagonal (λ _, X)) - (λ k l, C (M (swap i i k) l)) :=
begin
funext k l,
unfold submatrix swap_subtype,
simp [subtype.map],
dsimp,
rw [swap_self],
simp only [refl_apply, diagonal, subtype.ext],
congr
end


/-noncomputable def bij : n ≃ fin (fintype.card n) :=
  classical.some $ trunc.exists_rep $ fintype.equiv_fin n

noncomputable def matrix_to_fin_matrix (M : matrix n m R) :
  matrix (fin $ fintype.card n) (fin $ fintype.card m) R :=
λ i j, M (bij.inv_fun i) (bij.inv_fun j)-/

variable {k : ℕ}
open fin

def det_minor (i j : fin (k+1)) (M : matrix (fin (k+1)) (fin (k+1)) R) : R :=
  det (submatrix M (succ_above i) (succ_above j))

/-def rotate (p : fin (k+1)) : perm (fin (k+1)) :=
{ to_fun := λ i, if h : i.1 < k then succ_above p ⟨i.1, h⟩ else i,
  inv_fun := λ i, if h : i ≠ p then (pred_above p i h).cast_succ else p,
  left_inv := λ i,begin dsimp, by_cases h : i.1 < k,
    { rw [dif_pos h, dif_pos (succ_above_ne p _), pred_above_succ_above], exact cast_succ_cast_lt i h },
    { rw [dif_neg h], split_ifs, { symmetry, assumption },   }
     end,
  right_inv := sorry
}-/

/-def rotate : perm (fin (k+1)) :=
{ to_fun := λ i, if h : i.1 < k then fin.succ ⟨i.1, h⟩ else ⟨0, nat.zero_lt_succ k⟩,
  inv_fun := λ i, if i.1 ≠ 0 then ⟨nat.pred i.1, lt_of_le_of_lt (nat.pred_le _) i.2⟩ else last k,
  left_inv := λ i, begin dsimp, by_cases hi : i.1 < k,
    { rw [dif_pos hi], split_ifs with h h, { rw [succ_val] at h, contradiction }, { rw [eq_iff_veq], refl } },
    { rw [dif_neg hi], split_ifs with h h,
      { rw [eq_iff_veq, last_val], exact le_antisymm (le_of_not_lt hi) (nat.le_of_lt_succ i.2) },
      { contradiction } } end,
  right_inv := λ i, begin dsimp, by_cases hi : i.1 ≠ 0,
    { rw [if_pos hi], split_ifs with h h,
      { rw [eq_iff_veq, succ_val], exact nat.succ_pred_eq_of_pos (nat.pos_of_ne_zero hi) },
      { exfalso, dsimp at h,
        exact h (lt_of_lt_of_le (nat.pred_lt_pred hi i.2) (nat.pred_succ k ▸ le_refl k)) } },
    { rw [if_neg hi], split_ifs with h h,
      { rw [last_val] at h, exfalso, exact lt_irrefl _ h },
      { rw [eq_iff_veq], symmetry, rwa [ne.def, not_not] at hi } } end }-/

/-lemma fin_add_injective (i : fin k) : injective (fin.add i) := sorry

lemma fin_add_bijective (i : fin k) : bijective (fin.add i) :=
fintype.injective_iff_bijective.mp $ fin_add_injective i-/

def rotate (p : fin k) : perm (fin k) :=
{ to_fun := fin.add p,
  inv_fun := sorry,
  left_inv := sorry,
  right_inv := sorry }

lemma is_cycle_rotate (p : fin k) : is_cycle (rotate p) := sorry

/-def shift (k n : ℕ) (σ : perm (fin k)) : perm (fin (k + n)) :=
{ to_fun := λ i, if h : n ≤ i.val then add_nat n (σ (sub_nat n i h)) else i,
  inv_fun := λ i, if h : n ≤ i.val then add_nat n (σ.inv_fun (sub_nat n i h)) else i,
  left_inv := λ i, begin dsimp, split_ifs with h h,
    { rw [dif_pos h], }
   end,
  right_inv := sorry

}

def f (k n : ℕ) : monoid_hom (perm (fin k)) (perm (fin (k + n))) :=
{ to_fun := λ σ i, if n ≤ i.val then add_nat n (σ (sub_nat n i h)) else i,
  map_one' := sorry,
  map_mul' := sorry
}-/

def rotate_above (p : fin (k+1)) : perm (fin (k+1)) :=
{ to_fun := λ i, if h : i.1 < k then p.succ_above ⟨i.1, h⟩ else p,
  inv_fun := sorry, --λ i, if h : i ≠ p then p.pred_above i h else i,
  left_inv := sorry,
  right_inv := sorry }

lemma rotate_above_ne (p : fin (k+1)) (i : fin k) : rotate_above p i ≠ p :=
sorry

lemma is_cycle_rotate_above (p : fin (k+1)) : is_cycle (rotate_above p) := sorry

lemma sign_rotate_above (p : fin (k+1)) : sign (rotate_above p) = (-1)^(k+1-p) := sorry

def res {σ : perm (fin (k+1))} (h : σ (last k) = (last k)) : perm (fin k) :=
{ to_fun := λ l, ⟨σ l, lt_of_le_of_ne sorry begin assume h, end⟩,
  inv_fun := sorry,
  left_inv := sorry,
  right_inv := sorry
}

lemma laplace_expansion_aux (hk : k > 0) (M : matrix (fin (k+1)) (fin (k+1)) R) (i j : fin (k+1)) :
  univ.sum (λ σ : { σ : perm (fin (k+1)) // σ.to_fun i = j }, ε σ.val * univ.prod (λ l, M (σ l) l)) =
  M j i * (-1)^(i.1 + j.1) * det_minor j i M :=
calc univ.sum (λ σ : { σ : perm (fin (k+1)) // σ.to_fun i = j }, ε σ.val * univ.prod (λ l, M (σ l) l)) =
      M j i * univ.sum (λ σ : { σ : perm (fin (k+1)) // σ.to_fun i = j }, ε σ.val *
        (erase univ i).prod (λ l, M (σ l) l)) :
  begin rw [mul_sum], conv_rhs { congr, funext, skip, funext, rw [mul_comm, mul_assoc, mul_comm _ (M j i)],
    rw [show M j i = M (x i) i, begin unfold_coes, sorry end],
    rw [←@prod_insert _ _ _ _ (λ l : fin (k+1), M (x l) l) _ _ (not_mem_erase i _)],
    rw [insert_erase (mem_univ _)] } end
... = M j i * univ.sum (λ σ : { σ : perm (fin (k+1)) // σ.to_fun i = j }, ε σ.val *
        univ.prod (λ l : fin k, M (σ $ rotate_above i l) (rotate_above i l))) :
  begin congr, funext, apply congr_arg, symmetry,
    refine prod_bij (λ l _, rotate_above i l)
      (λ l _, by { rw [mem_erase], exact ⟨rotate_above_ne _ _, mem_univ _⟩ }) (λ _ _, rfl)
      (λ _ _ _ _ h, sorry)
      (λ l hl, ⟨fin.cast_le sorry ((rotate_above i).inv_fun l), mem_univ _, sorry⟩)end--⟨i.pred_above l (mem_erase.mp hl).1, mem_univ _, eq.symm $ succ_above_descend i l _⟩) end
... = M j i * univ.sum (λ σ : { σ : perm (fin (k+1)) // σ.to_fun i = j }, ε σ.val *
        univ.prod (λ l : fin k, M (rotate_above j $ (rotate_above j).inv_fun $ σ $ rotate_above i l) (rotate_above i l))) :
  by { congr, funext, congr, funext, unfold_coes, rw [(rotate_above j).right_inv] }
... = M j i * univ.sum (λ τ : perm (fin k), (-1)^(i.1 + j.1) * (ε τ *
        univ.prod (λ l : fin k, M (succ_above j $ τ l) (succ_above i l)))) :
  begin
    apply congr_arg,
    refine sum_bij (λ σ _, sorry) (λ _ _, mem_univ _) _
      (λ σ₁ σ₂ _ _, by { rw [subtype.ext], exact shift_inv_inj hk i j _ _ σ₁.2 σ₂.2 })
      (λ τ hτ, begin rw [←image_shift_inv hk i j, mem_image] at hτ,
       cases hτ with σ h, cases h with hσ h2, existsi [σ, hσ], symmetry, exact h2 end), --make this nicer,
    intros σ _,
    rw [←mul_assoc],
    congr,
    sorry --the proof of the signs
  end
... = M j i * (-1)^(i.1 + j.1) * det_minor j i M : by { rw [←mul_sum, mul_assoc], refl }














lemma succ_above_injective2 (p : fin (k+1)) : injective (succ_above p) :=
λ i j hij, by { let h := congr_arg (λ l, if h : l ≠ p then p.pred_above l h else i) hij,
  dsimp at h,
  rwa [dif_pos (succ_above_ne p i), dif_pos (succ_above_ne p j),
    pred_above_succ_above, pred_above_succ_above] at h }

lemma succ_above_injective (p : fin (k+1)) : ∀ (i j : fin k),
   succ_above p i = succ_above p j → i = j := succ_above_injective2 p

def pred_above' (p : fin (k+1)) (hk : k > 0) (i : fin (k+1)) : fin k :=
if h : i ≠ p then p.pred_above i h else ⟨0, hk⟩

lemma succ_above_descend' (hk : k > 0) :
  ∀ (p i : fin (k+1)) (h : i ≠ p), p.succ_above (pred_above' p hk i) = i := sorry

lemma pred_above_succ_above' (hk : k > 0) (p : fin (k+1)) (i : fin k) (h : p.succ_above i ≠ p) :
  pred_above' p hk (p.succ_above i) = i := sorry

def shift_inv (hk : k > 0) (i : fin (k+1)) (σ : perm (fin (k+1))) : perm (fin k) :=
{ to_fun := (pred_above' (σ i) hk) ∘ σ ∘ i.succ_above,
  inv_fun := (pred_above' i hk) ∘ σ.inv_fun ∘ (σ i).succ_above,
  left_inv := λ l, begin dsimp, unfold_coes,
    rw [succ_above_descend', σ.left_inv, pred_above_succ_above' hk _ _ (succ_above_ne _ _)],
    assume h, exact (succ_above_ne _ _) (σ.injective h) end,
  right_inv := λ l, begin dsimp, unfold_coes,
    rw [succ_above_descend', σ.right_inv, pred_above_succ_above' hk _ _ (succ_above_ne _ _)],
    assume h, exact (succ_above_ne _ _) (inv_eq_iff_eq.mp h) end }

lemma image_shift_inv (hk : k > 0) (i j : fin (k+1)) :
  image (shift_inv hk i ∘ subtype.val) (@finset.univ {σ : perm (fin (k+1)) // σ.to_fun i = j} _) = univ := sorry

lemma shift_inv_inj (hk : k > 0) (i j : fin (k+1)) (σ₁ σ₂ : perm (fin (k+1)))
  (h₁ : σ₁ i = j) (h₂ : σ₂ i = j) : shift_inv hk i σ₁ = shift_inv hk i σ₂ → σ₁ = σ₂ :=
sorry

lemma shift_inv_prop (hk : k > 0) (i j : fin (k+1)) (σ : perm (fin (k+1))) (h : σ i = j) :
  σ ∘ (succ_above i) = (succ_above j) ∘ (shift_inv hk i σ) :=
sorry

lemma laplace_expansion_aux (hk : k > 0) (M : matrix (fin (k+1)) (fin (k+1)) R) (i j : fin (k+1)) :
  univ.sum (λ σ : { σ : perm (fin (k+1)) // σ.to_fun i = j }, ε σ.val * univ.prod (λ l, M (σ l) l)) =
  M j i * (-1)^(i.1 + j.1) * det_minor j i M :=
calc univ.sum (λ σ : { σ : perm (fin (k+1)) // σ.to_fun i = j }, ε σ.val * univ.prod (λ l, M (σ l) l)) =
      M j i * univ.sum (λ σ : { σ : perm (fin (k+1)) // σ.to_fun i = j }, ε σ.val *
        (erase univ i).prod (λ l, M (σ l) l)) :
  begin rw [mul_sum], conv_rhs { congr, funext, skip, funext, rw [mul_comm, mul_assoc, mul_comm _ (M j i)],
    rw [show M j i = M (x i) i, begin unfold_coes, sorry end],
    rw [←@prod_insert _ _ _ _ (λ l : fin (k+1), M (x l) l) _ _ (not_mem_erase i _)],
    rw [insert_erase (mem_univ _)] } end
... = M j i * univ.sum (λ σ : { σ : perm (fin (k+1)) // σ.to_fun i = j }, ε σ.val *
        univ.prod (λ l : fin k, M (σ $ succ_above i l) (succ_above i l))) :
  begin congr, funext, apply congr_arg, symmetry,
    refine prod_bij (λ l _, succ_above i l)
      (λ l _, by { rw [mem_erase], exact ⟨succ_above_ne _ _, mem_univ _⟩ }) (λ _ _, rfl)
      (λ _ _ _ _, succ_above_injective i _ _)
      (λ l hl, ⟨i.pred_above l (mem_erase.mp hl).1, mem_univ _, eq.symm $ succ_above_descend i l _⟩) end
... = M j i * univ.sum (λ σ : { σ : perm (fin (k+1)) // σ.to_fun i = j }, ε σ.val *
        univ.prod (λ l : fin k, M (succ_above j $ shift_inv hk i σ l) (succ_above i l))) :
  by { congr, funext, congr, funext, congr, exact congr_fun (shift_inv_prop hk i j σ.1 σ.2) l }
... = M j i * univ.sum (λ τ : perm (fin k), (-1)^(i.1 + j.1) * (ε τ *
        univ.prod (λ l : fin k, M (succ_above j $ τ l) (succ_above i l)))) :
  begin
    apply congr_arg,
    refine sum_bij (λ σ _, shift_inv hk i σ) (λ _ _, mem_univ _) _
      (λ σ₁ σ₂ _ _, by { rw [subtype.ext], exact shift_inv_inj hk i j _ _ σ₁.2 σ₂.2 })
      (λ τ hτ, begin rw [←image_shift_inv hk i j, mem_image] at hτ,
       cases hτ with σ h, cases h with hσ h2, existsi [σ, hσ], symmetry, exact h2 end), --make this nicer,
    intros σ _,
    rw [←mul_assoc],
    congr,
    sorry --the proof of the signs
  end
... = M j i * (-1)^(i.1 + j.1) * det_minor j i M : by { rw [←mul_sum, mul_assoc], refl }

lemma laplace_expansion (hk : k > 0) (M : matrix (fin (k+1)) (fin (k+1)) R) (i : fin (k+1)) :
  det M = univ.sum (λ j : fin (k+1), M j i * (-1)^(i.1 + j.1) * det_minor j i M) :=
begin
  conv_rhs { congr, skip, funext, rw ←laplace_expansion_aux hk },
  rw ←@sum_sigma _ _ _ (λ j, {σ : perm (fin (k+1)) // σ.to_fun i = j}) _ _
    (λ σ, ε (σ.2.val) * univ.prod (λ (l : fin (k+1)), M (σ.2 l) l)),
  refine sum_bij (λ σ _, sigma.mk (σ i) ⟨σ, rfl⟩) (by simp [mem_sigma, mem_univ, and_self])
    (λ _ _, rfl) _ _,
  { intros _ _ _ _ h,
    have h2, from (sigma.mk.inj h).1,
    have h3, from type_eq_of_heq (sigma.mk.inj h).2,
    have h4, from (sigma.mk.inj h).2,
    sorry
    --rw [@heq_iff_eq (perm (fin k)) (λ σ : perm (fin k), σ i = a₁ i)] at h3,
    --rw [@heq_iff_eq _ (@subtype.mk (perm (fin k)) (λ (σ : perm (fin k)), σ i = a₁ i) a₁ _) (@subtype.mk (perm (fin k)) (λ (σ : perm (fin k)), σ i = a₂ i) a₂ _), subtype.mk_eq_mk] at h2,
  },
  { intros f h, existsi [f.snd.val, finset.mem_univ _],
    refine sigma.eq (eq.symm $ f.snd.property) (subtype.eq _),
    simp only [], congr, dsimp, unfold_coes, simp [f.snd.property], simp only [eq_rec_heq] }
end

/-
/-lemma image_shift_inv (i j : fin (k+1)) :
  image (shift_inv i j ∘ subtype.val) (@finset.univ {σ : perm (fin (k+1)) // σ.to_fun i = j} _) = univ := sorry

lemma shift_inv_inj (i j : fin (k+1)) (σ₁ σ₂ : perm (fin (k+1))) :
  shift_inv i j σ₁ = shift_inv i j σ₂ → σ₁ = σ₂ := sorry

lemma shift_inv_prop (i j : fin (k+1)) (σ : perm (fin (k+1))) :
  σ ∘ (succ_above i) = (succ_above j) ∘ (shift_inv i j σ) :=
sorry-/

lemma laplace_expansion_aux (M : matrix (fin (k+1)) (fin (k+1)) R) (i j : fin (k+1)) :
  univ.sum (λ σ : { σ : perm (fin (k+1)) // σ.to_fun i = j }, ε σ.val * univ.prod (λ l, M (σ l) l)) =
  M j i * (-1)^(i.1 + j.1) * det_minor j i M :=
calc univ.sum (λ σ : { σ : perm (fin (k+1)) // σ.to_fun i = j }, ε σ.val * univ.prod (λ l, M (σ l) l)) =
      M j i * univ.sum (λ σ : { σ : perm (fin (k+1)) // σ.to_fun i = j }, ε σ.val *
        (erase univ i).prod (λ l, M (σ l) l)) :
  begin rw [mul_sum], conv_rhs { congr, funext, skip, funext, rw [mul_comm, mul_assoc, mul_comm _ (M j i)],
    rw [show M j i = M (x i) i, begin unfold_coes, sorry end],
    rw [←@prod_insert _ _ _ _ (λ l : fin (k+1), M (x l) l) _ _ (not_mem_erase i _)],
    rw [insert_erase (mem_univ _)] } end
... = M j i * univ.sum (λ σ : { σ : perm (fin (k+1)) // σ.to_fun i = j }, ε σ.val *
        univ.prod (λ l : fin k, M (σ $ succ_above i l) (succ_above i l))) :
  begin congr, funext, apply congr_arg, symmetry,
    refine prod_bij (λ l _, succ_above i l)
      (λ l _, by { rw [mem_erase], exact ⟨succ_above_ne _ _, mem_univ _⟩ }) (λ _ _, rfl)
      (λ _ _ _ _, succ_above_injective i _ _)
      (λ l hl, ⟨i.pred_above l (mem_erase.mp hl).1, mem_univ _, eq.symm $ succ_above_descend i l _⟩) end
... = M j i * univ.sum (λ σ : { σ : perm (fin (k+1)) // σ.to_fun i = j }, ε σ.val *
        univ.prod (λ l : fin k, M (succ_above j $ shift_inv i j σ l) (succ_above i l))) :
  by { congr, funext, congr, funext, congr, exact congr_fun (shift_inv_prop i j σ) l }
... = M j i * univ.sum (λ τ : perm (fin k), (-1)^(i.1 + j.1) * (ε τ *
        univ.prod (λ l : fin k, M (succ_above j $ τ l) (succ_above i l)))) :
  begin
    apply congr_arg,
    refine sum_bij (λ σ _, shift_inv i j σ) (λ _ _, mem_univ _) _
      (λ _ _ _ _, by { rw [subtype.ext], exact shift_inv_inj i j _ _ })
      (λ τ hτ, begin rw [←image_shift_inv i j, mem_image] at hτ,
       cases hτ with σ h, cases h with hσ h2, existsi [σ, hσ], symmetry, exact h2 end), --make this nicer,
    intros σ _,
    rw [←mul_assoc],
    congr,
    sorry --the proof of the signs
  end
... = M j i * (-1)^(i.1 + j.1) * det_minor j i M : by { rw [←mul_sum, mul_assoc], refl }

lemma laplace_expansion (M : matrix (fin (k+1)) (fin (k+1)) R) (i : fin (k+1)) :
  det M = univ.sum (λ j : fin (k+1), M j i * (-1)^(i.1 + j.1) * det_minor j i M) :=
begin
  conv_rhs { congr, skip, funext, rw ←laplace_expansion_aux },
  rw ←@sum_sigma _ _ _ (λ j, {σ : perm (fin (k+1)) // σ.to_fun i = j}) _ _
    (λ σ, ε (σ.2.val) * univ.prod (λ (l : fin (k+1)), M (σ.2 l) l)),
  refine sum_bij (λ σ _, sigma.mk (σ i) ⟨σ, rfl⟩) (by simp [mem_sigma, mem_univ, and_self])
    (λ _ _, rfl) _ _,
  { intros _ _ _ _ h,
    have h2, from (sigma.mk.inj h).1,
    have h3, from type_eq_of_heq (sigma.mk.inj h).2,
    have h4, from (sigma.mk.inj h).2,
    sorry
    --rw [@heq_iff_eq (perm (fin k)) (λ σ : perm (fin k), σ i = a₁ i)] at h3,
    --rw [@heq_iff_eq _ (@subtype.mk (perm (fin k)) (λ (σ : perm (fin k)), σ i = a₁ i) a₁ _) (@subtype.mk (perm (fin k)) (λ (σ : perm (fin k)), σ i = a₂ i) a₂ _), subtype.mk_eq_mk] at h2,
  },
  { intros f h, existsi [f.snd.val, finset.mem_univ _],
    refine sigma.eq (eq.symm $ f.snd.property) (subtype.eq _),
    simp only [], congr, dsimp, unfold_coes, simp [f.snd.property], simp only [eq_rec_heq] }
end
-/

end matrix
