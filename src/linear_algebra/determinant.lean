/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes
-/
import data.matrix.basic
import group_theory.perm.sign
import algebra.char_p

universes u v
open equiv equiv.perm finset function

namespace equiv.perm
variables {n : ℕ} {R : Type u} [comm_ring R]

/-- A useful lemma if you want to rewrite `fin.pred_above`. -/
def fin.pred_above_congr {i i' j j' : fin n.succ} (h : j ≠ i) (hi : i = i') (hj : j = j') :
  fin.pred_above i j h = fin.pred_above i' j' (λ p, h (trans hj (trans p (symm hi)))) := by {congr; finish}

/-- Extend the function `f` by setting `f i = j` and moving the other values out of the way. -/
def fin.insert (i j : fin n.succ) (f : fin n → fin n) (k : fin n.succ) : fin n.succ :=
if h : k = i then j else fin.succ_above j (f (fin.pred_above i k h))

lemma fin.insert_eq {i j : fin n.succ} {f : fin n → fin n} {k : fin n.succ} : k = i ↔ fin.insert i j f k = j
:= begin
  apply iff.intro; intro hi,
  { simp [hi, fin.insert] },
  { by_contradiction hk,
    rw [fin.insert, dif_neg hk] at hi,
    exact fin.succ_above_ne _ _ hi
  }
end

lemma fin.insert_self {i j : fin n.succ} {f : fin n → fin n} : fin.insert i j f i = j
:= fin.insert_eq.mp rfl

lemma fin.insert_ne {i j : fin n.succ} {f : fin n → fin n} {k : fin n.succ} (h : k ≠ i) :
  fin.insert i j f k = fin.succ_above j (f (fin.pred_above i k h)) := dif_neg h

lemma fin.insert_succ_above {i j : fin n.succ} {f : fin n → fin n} {k : fin n} :
  fin.insert i j f (fin.succ_above i k) = fin.succ_above j (f k) :=
by rw [fin.insert_ne (fin.succ_above_ne _ _), fin.pred_above_succ_above]

def fin.delete (i : fin n.succ) (f : fin n.succ → fin n.succ) (h : ∀ k, f k = f i → k = i) (k : fin n) : fin n :=
fin.pred_above (f i) (f (fin.succ_above i k)) (λ p, fin.succ_above_ne _ _ (h _ p))

lemma fin.delete_insert (i j : fin n.succ) (f : fin n → fin n) (k : fin n) :
  fin.delete i (fin.insert i j f) (λ k p, fin.insert_eq.mpr (trans p fin.insert_self)) k = f k
:= calc
fin.delete i (fin.insert i j f) _ k
    = fin.pred_above (fin.insert i j f i) (fin.insert i j f (fin.succ_above i k)) _ : rfl
... = fin.pred_above j (fin.insert i j f (fin.succ_above i k)) _ : fin.pred_above_congr _ fin.insert_self rfl
... = fin.pred_above j (fin.succ_above j (f (fin.pred_above i (fin.succ_above i k) (fin.succ_above_ne _ _)))) _
  : fin.pred_above_congr _ rfl (fin.insert_ne _)
... = f (fin.pred_above i (fin.succ_above i k) (fin.succ_above_ne _ _)) : fin.pred_above_succ_above _ _ _
... = f k : by rw [fin.pred_above_succ_above]

lemma fin.left_inverse_insert (i j : fin n.succ) {f g : fin n → fin n} :
  function.left_inverse g f → function.left_inverse (fin.insert j i g) (fin.insert i j f) := begin
intros linv k,
by_cases k = i,
{ rw [h, fin.insert_self, fin.insert_self] },
have h' : fin.succ_above j (f (fin.pred_above i k h)) ≠ j := fin.succ_above_ne _ _,
rw [fin.insert_ne h, fin.insert_ne h', fin.pred_above_succ_above, linv, fin.succ_above_descend]
end

lemma fin.left_inverse_delete (i : fin n.succ) {f g : fin n.succ → fin n.succ}
  (hf : ∀ k, f k = f i → k = i) (hg : ∀ k, g k = g (f i) → k = f i) :
  function.left_inverse g f → function.left_inverse (fin.delete (f i) g hg) (fin.delete i f hf) := begin
intros linv k, calc
  fin.delete (f i) g hg (fin.delete i f hf k)
      = fin.pred_above (g (f i)) (g (fin.succ_above (f i) (fin.delete i f hf k))) _ : rfl
  ... = fin.pred_above i (g (f (fin.succ_above i _)) ) _
    : fin.pred_above_congr _ (linv i) (by {congr, apply fin.succ_above_descend})
  ... = fin.pred_above i (fin.succ_above i _) _
    : fin.pred_above_congr _ (refl i) (linv _)
  ... = k : fin.pred_above_succ_above _ _ _
end

lemma fin.right_inverse_delete (i : fin n.succ) {f g : fin n.succ → fin n.succ}
  (hf : ∀ k, f k = f i → k = i) (hg : ∀ k, g k = g (f i) → k = f i) :
  function.left_inverse g f → function.right_inverse g f →
  function.right_inverse (fin.delete (f i) g hg) (fin.delete i f hf) := begin
intros linv rinv k, calc -- TODO: cleanup!
  fin.delete i f hf (fin.delete (f i) g hg k) 
      = fin.pred_above (f i) (f (fin.succ_above i (fin.delete (f i) g hg k))) _ : rfl
  ... = fin.pred_above (f i) (f (fin.succ_above i (fin.pred_above (g (f i)) (g (fin.succ_above (f i) k)) _))) _
    : fin.pred_above_congr _ rfl (by {congr})
  ... = fin.pred_above (f i) (f (fin.succ_above i (fin.pred_above i (g (fin.succ_above (f i) k)) _))) _
    : fin.pred_above_congr _ rfl (by {congr' 2, apply fin.pred_above_congr, apply linv, refl})
  ... = fin.pred_above (f i) (f (g (fin.succ_above _ _))) _
    : fin.pred_above_congr _ rfl (by {congr, apply fin.succ_above_descend})
  ... = fin.pred_above (f i) (fin.succ_above (f i) _) _
    : fin.pred_above_congr _ rfl (rinv _)
  ... = k : fin.pred_above_succ_above _ _ (fin.succ_above_ne _ _)
end

def insert (i j : fin n.succ) (σ : equiv.perm (fin n)) : equiv.perm (fin n.succ) :=
⟨ fin.insert i j σ.to_fun
, fin.insert j i σ.inv_fun
, fin.left_inverse_insert i j σ.3
, fin.left_inverse_insert j i σ.4⟩

def delete (i : fin n.succ) (σ : equiv.perm (fin n.succ)) : equiv.perm (fin n) :=
⟨ fin.delete i σ.to_fun (λ k p, function.injective_of_left_inverse σ.3 p)
, fin.delete (σ i) σ.inv_fun (λ k p, function.injective_of_left_inverse σ.4 p)
, fin.left_inverse_delete i _ _ σ.3
, fin.right_inverse_delete i _ _ σ.3 σ.4⟩


lemma insert_to_fun {i j : fin n.succ} {σ : equiv.perm (fin n)} :
  (insert i j σ).to_fun = fin.insert i j (σ.to_fun) := rfl

lemma insert_self {i j : fin n.succ} {σ : equiv.perm (fin n)} : (insert i j σ).to_fun i = j :=
by rw [insert_to_fun, fin.insert_self]
lemma insert_eq {i j k : fin n.succ} {σ : equiv.perm (fin n)} : k = i ↔ (insert i j σ).to_fun k = j :=
fin.insert_eq

lemma insert_succ_above (i j : fin n.succ) (σ : equiv.perm (fin n)) (k : fin n) :
  (insert i j σ).to_fun (fin.succ_above i k) = fin.succ_above j (σ.to_fun k) := fin.insert_succ_above

lemma insert_inj (i j : fin n.succ) : function.injective (insert i j)
:= begin
  intros σ τ hins,
  ext k,
  calc σ.to_fun k
      = fin.pred_above j (fin.succ_above j (σ.to_fun k)) _ : symm (fin.pred_above_succ_above _ _ (fin.succ_above_ne _ _))
  ... = fin.pred_above j ((insert i j σ).to_fun (fin.succ_above i k)) (fin.succ_above_ne _ _ ∘ insert_eq.mpr)
    : by {congr, rw [insert_succ_above]}
  ... = fin.pred_above j ((insert i j τ).to_fun (fin.succ_above i k)) (fin.succ_above_ne _ _ ∘ insert_eq.mpr)
    : by {congr, assumption}
  ... = fin.pred_above j (fin.succ_above j (τ.to_fun k)) _ : fin.pred_above_congr _ rfl (insert_succ_above i j τ k)
  ... = τ.to_fun k : fin.pred_above_succ_above _ _ (fin.succ_above_ne _ _)
end

lemma insert_surj (i : fin n.succ) (σ : equiv.perm (fin n.succ)) : ∃ τ, σ = insert i (σ i) τ :=
⟨delete i σ, begin
  ext k,
  apply symm,
  by_cases k = i,
  { calc (insert i (σ.to_fun i) (delete i σ)).to_fun k
        = σ.to_fun i : dif_pos h
    ... = σ.to_fun k : by rw h },
  calc (insert i (σ.to_fun i) (delete i σ)).to_fun k
      = fin.succ_above (σ.to_fun i) (fin.pred_above (σ.to_fun i) (σ.to_fun (fin.succ_above i (fin.pred_above i k _))) _) : dif_neg h
  ... = σ.to_fun k : by rw [fin.succ_above_descend (σ.to_fun i), fin.succ_above_descend i]
end⟩
end equiv.perm

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

/-- Transposing a matrix preserves the determinant. -/
@[simp] lemma det_transpose (M : matrix n n R) : M.transpose.det = M.det :=
begin
apply sum_bij (λ σ _, σ⁻¹),
{ intros σ _, apply mem_univ },
{ intros σ _,
  rw [sign_inv],
  congr' 1,
  apply prod_bij (λ i _, σ i),
  { intros i _, apply mem_univ },
  { intros i _, simp },
  { intros i j _ _ h, simp at h, assumption },
  { intros i _, use σ⁻¹ i, finish }
},
{ intros σ σ' _ _ h, simp at h, assumption },
{ intros σ _, use σ⁻¹, finish }
end

/-- Permuting the columns changes the sign of the determinant. -/
lemma det_permute (M : matrix n n R) (σ : perm n) : matrix.det (λ i, M (σ i)) = σ.sign * M.det :=
begin
unfold det,
rw mul_sum,
apply sum_bij (λ τ _, σ * τ),
{ intros τ _, apply mem_univ },
{ intros τ _,
  show
    ↑(sign τ) * finset.prod univ (λ i, M (σ.to_fun (τ.to_fun i)) i)
    = ↑(sign σ) * (↑(sign (σ * τ)) * finset.prod univ (λ i, M (σ.to_fun (τ.to_fun i)) i)),
  rw ←mul_assoc,
  congr,
  calc ε τ
       = ↑(sign σ * sign σ * sign τ) :
    by {conv_lhs {rw [←one_mul (sign τ), ←int.units_pow_two (sign σ)]}, norm_num}
  ... = ε σ * ε (σ * τ) :
    by simp only [mul_assoc, int.cast_mul, sign_mul, coe_coe, units.coe_mul] },
{ intros τ τ' _ _, exact (mul_left_inj σ).mp },
{ intros τ _, use σ⁻¹ * τ, use (mem_univ _), exact (mul_inv_cancel_left _ _).symm }
end

/-- The determinant is zero if the matrix contains a repeated column.

The proof shows `M.det = -M.det` and concludes `M.det = 0`,
so it doesn't work in characteristic `2`.
-/
lemma det_zero_of_column_eq_of_char_ne_two (char_ne_2 : ∀ (a : R), a = -a → a = 0)
(M : matrix n n R) (i j : n) (i_ne_j : i ≠ j) (hij : M i = M j) : M.det = 0 :=
begin
suffices : M.det = - M.det, { apply char_ne_2, assumption },
have : (λ a, M (swap i j a)) = M,
{ ext a b,
  by_cases hi : a = i, { rw [hi, swap_apply_left, hij] },
  by_cases hj : a = j, { rw [hj, swap_apply_right, hij] },
  rw [swap_apply_of_ne_of_ne hi hj]
},
calc M.det = (-1 : units ℤ) * M.det : by rw [←sign_swap i_ne_j, ←det_permute M, this]
       ... = -det M : by norm_num
end

/-- 
  Helper function for `det_zero_of_column_eq_of_has_lt`:
  sends two permutations that differ by a `swap i j` to the same value.
-/
def identify_swaps [has_lt n] [decidable_rel ((<) : n → n → Prop)] (i j : n) (σ : perm n) : perm n :=
if σ⁻¹ i > σ⁻¹ j then swap i j * σ else σ

lemma identify_swaps_iff_aux [has_lt n] [decidable_rel ((<) : n → n → Prop)] {i j : n} {σ τ : perm n}
  (h : identify_swaps i j τ = identify_swaps i j σ) : τ = σ ∨ τ = swap i j * σ :=
begin
  unfold identify_swaps at h,
  by_cases hσ : σ⁻¹ i > σ⁻¹ j;
  try {rw [if_pos hσ] at h}; try {rw [if_neg hσ] at h};
  by_cases hτ : τ⁻¹ i > τ⁻¹ j;
  try {rw [if_pos hτ] at h}; try {rw [if_neg hτ] at h},
  { finish },
  { finish },
  { apply or.inr, rw [←h, swap_mul_self_mul] },
  { finish }
end

lemma mul_swap_ne [has_lt n] [decidable_rel ((<) : n → n → Prop)] {i j : n} {σ : perm n}
  (i_ne_j : i ≠ j) : swap i j * σ ≠ σ := sorry

lemma identify_swaps_iff [decidable_linear_order n] {i j : n} (σ τ : perm n)
  (i_ne_j : i ≠ j) : (identify_swaps i j τ = identify_swaps i j σ) ↔ (τ = σ ∨ τ = swap i j * σ) :=
begin
  split,
  { apply identify_swaps_iff_aux },
  { intros h, cases h; rw [h],
    unfold identify_swaps,
    have σswap_i : (σ⁻¹ * swap i j) i = σ⁻¹ j := by simp,
    have σswap_j : (σ⁻¹ * swap i j) j = σ⁻¹ i := by simp,
    rw [mul_inv_rev, swap_inv, σswap_i, σswap_j],
    by_cases σ⁻¹ i > σ⁻¹ j,
    { have : ¬(σ⁻¹ j > σ⁻¹ i) := assume i_lt_j, lt_asymm h i_lt_j, 
      rw [if_pos h, if_neg this] },
    { have : σ⁻¹ i ≠ σ⁻¹ j := assume eq, i_ne_j (injective_of_left_inverse σ.4 eq),
      have : σ⁻¹ j > σ⁻¹ i := lt_of_le_of_ne (le_of_not_lt h) this,
      rw [if_neg h, if_pos this, swap_mul_self_mul] },
  },
end

/--
  A version of `det_zero_of_column_eq_of_char_ne_two`
  which replaces the assumption on the ring `α` with one on the index set `n`.
-/
lemma det_zero_of_column_eq_of_lin [decidable_linear_order n]
  (M : matrix n n R) (i j : n) (i_ne_j : i ≠ j) (hij : M i = M j) : M.det = 0 :=
begin
have swap_invariant : ∀ k l, M (swap i j k) l = M k l,
{ intros k l,
  rw [swap_apply_def],
  by_cases k = i, { rw [if_pos h, h, ←hij] },
  rw [if_neg h],
  by_cases k = j, { rw [if_pos h, h, hij] },
  rw [if_neg h] },

suffices : sum (univ.image (identify_swaps i j))
             (λ (σ : perm n),
                ε σ * univ.prod (λ (k : n), M (σ.to_fun k) k) +
                ε (swap i j * σ) * univ.prod (λ (k : n), M ((swap i j * σ).to_fun k) k)) =
           sum univ (λ (σ : perm n), ε σ * univ.prod (λ (k : n), M (σ.to_fun k) k)),
{ calc det M
    = sum (univ.image (identify_swaps i j)) (λ (σ : perm n),
      ε σ * univ.prod (λ (k : n), M (σ.to_fun k) k) +
      ε (swap i j * σ) * univ.prod (λ (k : n), M ((swap i j * σ).to_fun k) k)) : symm this
... = sum (univ.image (identify_swaps i j)) (λ (σ : perm n),
      ε σ * univ.prod (λ (k : n), M (σ.to_fun k) k) +
      ε (swap i j * σ) * univ.prod (λ (k : n), M (swap i j (σ.to_fun k)) k)) : rfl
... = sum (univ.image (identify_swaps i j)) (λ (σ : perm n),
      ε σ * univ.prod (λ (k : n), M (σ.to_fun k) k) +
      -1 * ε σ * univ.prod (λ (k : n), M (σ.to_fun k) k)) :
  by { congr, ext σ, congr,
    { simp [sign_mul, if_neg i_ne_j] },
    ext k, apply swap_invariant }
... = sum (univ.image (identify_swaps i j)) (λ (σ : perm n), 0) : by { congr, ext σ, ring }
... = 0 : sum_const_zero },

apply sum_image',
intros σ _,
rw [@filter_congr _ (λ τ, identify_swaps i j τ = identify_swaps i j σ) _ _ _ _
  (λ τ _, identify_swaps_iff σ τ i_ne_j)],
simp only [filter_or, filter_eq', if_pos (mem_univ _), insert_empty_eq_singleton,
    sum_union (disjoint_singleton.mpr (λ h, mul_swap_ne i_ne_j (mem_singleton.mp h))),
    sum_singleton],

by_cases σ⁻¹ i > σ⁻¹ j,
{ rw [identify_swaps, if_pos h, swap_mul_self_mul], ring },
{ rw [identify_swaps, if_neg h] }
end

end matrix
