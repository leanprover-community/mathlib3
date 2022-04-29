import tactic.linarith
import tactic.omega
import tactic.fin_cases
import algebra.group.cohomology.lemmas
import group_theory.quotient_group
import linear_algebra.finsupp
import algebra.homology.homotopy_category
import category_theory.abelian.projective
import algebra.category.Group.abelian

universes v u
variables (G : Type u) [monoid G] (M : Type v) [add_comm_group M] [distrib_mul_action G M] (n : ℕ)

variables {G M n}

def F (j : ℕ) (g : fin (n + 1) → G) (k : fin n) : G :=
if (k : ℕ) < j then g (fin.cast_lt k (lt_trans k.2 $ lt_add_one _)) else
if (k : ℕ) = j then g (fin.cast_lt k (lt_trans k.2 $ lt_add_one _)) * g (fin.add_nat 1 k)
else g (fin.add_nat 1 k)

lemma F_lt_apply (j : ℕ) (g : fin (n + 1) → G) (k : fin n) (h : (k : ℕ) < j) :
  F j g k = g (fin.cast_lt k (lt_trans k.2 $ lt_add_one _)) := if_pos h

lemma F_eq_apply (j : ℕ) (g : fin (n + 1) → G) (k : fin n) (h : (k : ℕ) = j) :
  F j g k = g (fin.cast_lt k (lt_trans k.2 $ lt_add_one _)) * g (fin.add_nat 1 k) :=
begin
  have : ¬(k : ℕ) < j, by linarith,
  unfold F,
  rw [if_neg this, if_pos h],
end

lemma F_neg_apply (j : ℕ) (g : fin (n + 1) → G) (k : fin n)
  (h : ¬(k : ℕ) < j) (h' : ¬(k : ℕ) = j) :
  F j g k = g (fin.add_nat 1 k) :=
begin
  unfold F,
  rw [if_neg h, if_neg h'],
end

theorem degenerate {j : ℕ} {k : ℕ} (h : j ≤ k) (g : fin (n + 2) → G) :
  F j (F (k + 1) g) = F k (F j g) :=
begin
  ext,
  by_cases hjl : (x : ℕ) < j,
  { repeat {rw F_lt_apply},
    all_goals {show (x : ℕ) < _, by omega}},
  { by_cases hje : (x : ℕ) = j,
    { rw [F_eq_apply _ _ _ hje, F_lt_apply],
      work_on_goal 1 {show (x : ℕ) < _, by omega},
      by_cases (j = k),
      { iterate 3 {rw F_eq_apply},
        all_goals {simp only [*, fin.coe_cast_lt, fin.coe_add_nat] at *},
        rw [F_neg_apply, mul_assoc],
        { refl },
        all_goals {dsimp, omega}},
      { rw [F_lt_apply, F_lt_apply, F_eq_apply _ _ (x.cast_lt _) hje],
        { refl },
        all_goals {try {dsimp}, omega}}},
    { rw F_neg_apply _ _ _ hjl hje,
      by_cases hkl : (x : ℕ) < k,
    { rw [F_lt_apply, F_lt_apply _ _ _ hkl, F_neg_apply _ _ (x.cast_lt _) hjl hje],
      { refl },
      { dsimp, omega }},
    { by_cases hke : (x : ℕ) = k,
      { rw [F_eq_apply, F_eq_apply _ _ _ hke, F_neg_apply _ _ (x.cast_lt _) hjl hje,
            F_neg_apply],
        { refl },
        all_goals {dsimp, omega}},
      { repeat {rw F_neg_apply},
        any_goals {assumption},
        all_goals {dsimp, omega}}}}}
end.

theorem neg_one_power (n : ℕ) (m : M) : ((-1:ℤ)^n  + (-1:ℤ)^(n+1)) • m = 0 :=
by simp [pow_succ]

theorem neg_degenerate (j : ℕ) (k : ℕ) (g : fin (n + 2) → G)
  (h : j ≤ k) (v : (fin n → G) → M) :
  (-1 : ℤ) ^ (j + k + 1) • (v (F j (F (k + 1) g)))
    + (-1 : ℤ) ^ (j + k) • (v (F k (F j g))) = 0 :=
begin
  rw [degenerate h, ←add_smul, add_comm, neg_one_power],
end

open finset

def F_comp (g : fin (n + 2) → G) (v : (fin n → G) → M) : ℕ × ℕ → M :=
λ j, (-1 : ℤ) ^ (j.1 + j.2) • v (F j.2 (F j.1 g))

theorem F_comp_degenerate {j : ℕ} {k : ℕ} (h : j ≤ k) (g : fin (n + 2) → G)
  (v : (fin n → G) → M) :
  F_comp g v (k + 1, j) + F_comp g v (j, k) = 0 :=
begin
  have := neg_degenerate j k g h v,
  rwa [add_assoc j, add_comm j] at this,
end

lemma not_le_of_invo_pos {j : ℕ × ℕ}
  (h : j.1 ≤ j.2) :
  ¬(invo j).1 ≤ (invo j).2 :=
begin
  rw invo_pos h,
  exact not_le.2 (nat.lt_succ_of_le h),
end

lemma le_of_invo_neg {j : ℕ × ℕ} (h : ¬j.1 ≤ j.2) :
  (invo j).1 ≤ (invo j).2 :=
begin
  rw invo_neg h,
  exact nat.pred_le_pred (not_le.1 h),
end

theorem double_sum_zero1 (n : ℕ) (g : fin (n + 3) → G) (v : (fin (n + 1) → G) → M) :
(range (n + 3)).sum (λ i, (range (n + 2)).sum (λ j, (F_comp g v (i, j)))) = 0 :=
begin
  rw ←sum_product,
  refine sum_involution (λ jk h, invo jk) _ _ _ _,
  { intros j hj,
    by_cases h : j.1 ≤ j.2,
    { rw add_comm,
      convert F_comp_degenerate h g v,
      { exact invo_pos h },
      { rw prod.mk.eta }},
    { convert F_comp_degenerate (le_of_invo_neg h) g v,
      { rw invo_neg h,
        exact prod.ext (nat.sub_add_cancel (by linarith)).symm rfl },
      { rw prod.mk.eta }}},
  { intros j hj _ h,
    by_cases H : j.1 ≤ j.2,
    { refine not_le_of_invo_pos H (by rwa h) },
    { have h2 := le_of_invo_neg H,
      refine H (by rwa ←h) }},
  { intros j hj,
    rw [mem_product, mem_range, mem_range] at hj ⊢,
    by_cases h : j.1 ≤ j.2,
    { rw invo_pos h,
      split,
      all_goals { linarith }},
    { rw [invo_neg h],
      dsimp,
      sorry
      }},
  { intros j hj,
    exact invo_invo j }
end

def d_to_fun (φ: (fin n → G) → M): (fin (n + 1) → G) → M :=
λ g, g 0 • φ (λ i, g (fin.add_nat 1 i))
  + (range (n + 1)).sum (λ j, (-1 : ℤ) ^ (j + 1) • φ (F j g))

lemma cochain_zero_eq (φ : (fin 0 → G) → M) (x y : fin 0 → G) :
  φ x = φ y :=
congr_arg _ $ subsingleton.elim _ _

lemma fin.cast_lt_zero {m : ℕ} :
  fin.cast_lt (0 : fin (n + 1)) (show 0 < m + 1, from m.succ_pos) = 0 := rfl

lemma F_succ_zero {m : ℕ} (g : fin (n + 2) → G) :
  F (m + 1) g 0 = g 0 := F_lt_apply _ _ _ m.succ_pos

lemma F_zero_succ {i : fin n} (g : fin (n + 2) → G) :
  F 0 g (fin.add_nat 1 i) = g (fin.add_nat 1 (fin.add_nat 1 i)) :=
F_neg_apply 0 g (fin.add_nat 1 i) (by linarith) (nat.succ_ne_zero i)

lemma F_shift {j : ℕ} (g : fin (n + 2) → G) (k : fin n) :
  F j (λ i, g (fin.add_nat 1 i)) k = F (j + 1) g (fin.add_nat 1 k) :=
begin
  by_cases h : (k : ℕ) < j,
  { rw [F_lt_apply _ _ _ h, F_lt_apply _ _ (fin.add_nat 1 k)
      (show (k : ℕ) + 1 < j + 1, by linarith)],
    refl },
  { by_cases h' : (k : ℕ) = j,
    { rw [F_eq_apply _ _ _ h', F_eq_apply _ _ (fin.add_nat 1 k) ((add_left_inj 1).2 h')],
      refl },
    { rw [F_neg_apply _ _ _ h h', F_neg_apply],
      { show ¬(k : ℕ) + 1 < _, by linarith },
      { show ¬(k : ℕ) + 1 = _, by omega }}}
end

theorem d_to_fun_square_zero (φ : (fin n → G) → M) :
  d_to_fun (d_to_fun φ) = 0 :=
begin
  unfold d_to_fun,
  funext,
  dsimp,
  simp only [smul_add],
  cases n with n,
  { rw [sum_range_succ, sum_range_succ, sum_range_zero],
    norm_num,
    rw [F_eq_apply 0 _ 0, F_lt_apply 1 _ 0],
    { simp only [mul_smul, cochain_zero_eq φ _ (default (fin 0 → G)), ←sub_eq_neg_add, ←sub_eq_add_neg],
      erw fin.cast_lt_zero,
      abel },
    { dec_trivial },
    { refl }},
  { rw [sum_add_distrib, sum_range_succ' _ (n + 2), F_eq_apply 0 _ 0],
  simp only [F_succ_zero, mul_smul, F_zero_succ, one_zsmul, pow_one, zero_add, neg_smul],
  erw [fin.cast_lt_zero, ←sub_eq_add_neg],
  abel,
  simp only [distrib_mul_action.smul_zsmul, ←F_shift],
  sorry, sorry

  /-erw [←smul_sum, ←smul_add, ←sum_add_distrib, @sum_eq_zero _ _ _ _ (range (n + 2)),
    smul_zero, add_zero],
  { simp only [smul_sum, ←mul_smul, ←pow_add],
    have : ∀ i j : ℕ, (-1 : ℤ) ^ (i + 1 + (j + 1)) = (-1 : ℤ) ^ (i + j) := λ i j, by
    { simp only [pow_add, pow_one],
      norm_num },
    simp only [this],
    exact double_sum_zero1 n g φ },
  { intros x hx,
    rw [←add_smul, add_comm, neg_one_power] },
  { refl }-/
  },
end

/-
example (G : Type*) [group G] (M : Type*) [add_comm_group M] [G_module G M]
(φ : cochain 1 G M) (hφ : d_to_fun φ = (λ i, 0)) (g h : G) : φ (λ _, g * h) = φ (λ _, g) + g • φ (λ _, h) :=
begin
  unfold d_to_fun at hφ,
  let glist : fin 2 → G := λ i, if i.val = 0 then g else if i.val = 1 then h else 1,
  have h2 : (λ (gi : fin (1 + 1) → G),
       gi ⟨0, _⟩ • φ (λ (i : fin 1), gi ⟨i.val + 1, _⟩) +
         finset.sum (finset.range (1 + 1)) (λ (j : ℕ), (-1: ℤ) ^ (j + 1) • φ (F j gi))) glist = 0,
    rw hφ,
  dsimp at h2,
  change g • φ (λ (i : fin 1), glist ⟨i.val + 1, _⟩) +
      finset.sum (finset.range (1 + 1)) (λ (j : ℕ), (-1 : ℤ) ^ (j + 1) • φ (F j glist)) =
    0 at h2,
  rw finset.sum_range_succ at h2,
  rw finset.sum_range_succ at h2,
  rw finset.sum_range_zero at h2,
  have H : (-1 : ℤ) ^ (1 + 1) = 1,
    norm_num,
  rw H at h2,
  rw one_smul at h2,
  rw ←add_assoc at h2,
  rw add_zero at h2,
  clear H,
  have H : (-1 : ℤ) ^ (0 + 1) = -1,
    norm_num,
  rw H at h2,
  rw neg_one_smul at h2,
  clear H,
  rw add_neg_eq_zero at h2,
  rw eq_comm at h2,
  rw add_comm at h2,
  convert h2,
  {
    ext,
    cases x with x hx,
    cases (nat.sub_eq_zero_of_le hx),
    refl,
  },
  { ext,
    cases x with x hx,
    cases (nat.sub_eq_zero_of_le hx),
    refl,
  },
  { ext,
    cases x with x hx,
    cases (nat.sub_eq_zero_of_le hx),
    refl,
  }
end-/

variables (G M n)

def cochain.d : ((fin n → G) → M) →+ ((fin (n + 1) → G) → M) :=
{ to_fun := d_to_fun,
  map_zero' := funext $ λ x, by simp only [d_to_fun, add_zero, pi.zero_apply,
    sum_const_zero, smul_zero],
  map_add' := λ x y, funext $ λ g, by simp only [d_to_fun, smul_add, sum_add_distrib,
    pi.add_apply]; abel }

variables {G M}

lemma cochain.d_zero_apply (x : (fin 0 → G) → M) (g : fin 1 → G) :
  cochain.d G M 0 x g = g 0 • x (default _) - x (default _) :=
begin
  dsimp [cochain.d, d_to_fun],
  simp only [pow_one, one_zsmul, sum_singleton, neg_smul],
  rw [unique.eq_default (λ i, g (fin.add_nat 1 i)), unique.eq_default (F 0 g), sub_eq_add_neg],
end

lemma cochain.d_one_apply (x : (fin 1 → G) → M) (g : fin 2 → G) :
  cochain.d G M 1 x g = g 0 • x (λ i, g 1) - x (λ i, g 0 * g 1) + x (λ i, g 0) :=
begin
  dsimp [cochain.d, d_to_fun],
  rw [finset.range_succ', finset.sum_insert],
  simp only [pow_one, image_singleton, one_zsmul,
    sum_singleton, nat.neg_one_sq, neg_smul, range_one],
  rw [←add_assoc, sub_eq_add_neg],
  congr,
  { ext y,
    rw subsingleton.elim y 0,
    refl },
  { ext y,
    rw [F_eq_apply 0 _ y (by rw subsingleton.elim y 0; refl), subsingleton.elim y 0],
    refl },
  { ext y,
    rw [subsingleton.elim y 0, F_succ_zero] },
  { simp }
end

lemma cochain.d_one_apply' (x : (fin 1 → G) → M) (g h : G) :
  cochain.d G M 1 x (fin.cons g (λ i, h)) = g • x (λ i, h) - x (λ i, g * h) + x (λ i, g) :=
begin
  convert cochain.d_one_apply x (fin.cons g (λ i, h)),
end

variables (G M)

theorem cochain.d_square_zero : (cochain.d G M (n + 1)).comp (cochain.d G M n) = 0 :=
by ext1; exact d_to_fun_square_zero _

def cochain_cx : cochain_complex Ab ℕ :=
cochain_complex.of (λ n, AddCommGroup.of $ (fin n → G) → M) (λ n, cochain.d G M n)
  (cochain.d_square_zero G M)
