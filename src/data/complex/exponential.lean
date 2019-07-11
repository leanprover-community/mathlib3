/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir
-/
import algebra.archimedean
import data.nat.choose data.complex.basic
import tactic.linarith

local attribute [instance, priority 0] classical.prop_decidable
local notation `abs'` := _root_.abs
open is_absolute_value

section
open real is_absolute_value finset

lemma forall_ge_le_of_forall_le_succ {α : Type*} [preorder α] (f : ℕ → α) {m : ℕ}
  (h : ∀ n ≥ m, f n.succ ≤ f n) : ∀ {l}, ∀ k ≥ m, k ≤ l → f l ≤ f k :=
begin
  assume l k hkm hkl,
  generalize hp : l - k = p,
  have : l = k + p := add_comm p k ▸ (nat.sub_eq_iff_eq_add hkl).1 hp,
  subst this,
  clear hkl hp,
  induction p with p ih,
  { simp },
  { exact le_trans (h _ (le_trans hkm (nat.le_add_right _ _))) ih }
end

variables {α : Type*} {β : Type*} [ring β]
  [discrete_linear_ordered_field α] [archimedean α] {abv : β → α} [is_absolute_value abv]

lemma is_cau_of_decreasing_bounded (f : ℕ → α) {a : α} {m : ℕ} (ham : ∀ n ≥ m, abs (f n) ≤ a)
  (hnm : ∀ n ≥ m, f n.succ ≤ f n) : is_cau_seq abs f :=
λ ε ε0,
let ⟨k, hk⟩ := archimedean.arch a ε0 in
have h : ∃ l, ∀ n ≥ m, a - add_monoid.smul l ε < f n :=
  ⟨k + k + 1, λ n hnm, lt_of_lt_of_le
    (show a - add_monoid.smul (k + (k + 1)) ε < -abs (f n),
      from lt_neg.1 $ lt_of_le_of_lt (ham n hnm) (begin
        rw [neg_sub, lt_sub_iff_add_lt, add_monoid.add_smul],
        exact add_lt_add_of_le_of_lt hk (lt_of_le_of_lt hk
          (lt_add_of_pos_left _ ε0)),
      end))
    (neg_le.2 $ (abs_neg (f n)) ▸ le_abs_self _)⟩,
let l := nat.find h in
have hl : ∀ (n : ℕ), n ≥ m → f n > a - add_monoid.smul l ε := nat.find_spec h,
have hl0 : l ≠ 0 := λ hl0, not_lt_of_ge (ham m (le_refl _))
  (lt_of_lt_of_le (by have := hl m (le_refl m); simpa [hl0] using this) (le_abs_self (f m))),
begin
  cases classical.not_forall.1
    (nat.find_min h (nat.pred_lt hl0)) with i hi,
  rw [not_imp, not_lt] at hi,
  existsi i,
  assume j hj,
  have hfij : f j ≤ f i := forall_ge_le_of_forall_le_succ f hnm _ hi.1 hj,
  rw [abs_of_nonpos (sub_nonpos.2 hfij), neg_sub, sub_lt_iff_lt_add'],
  exact calc f i ≤ a - add_monoid.smul (nat.pred l) ε : hi.2
    ... = a - add_monoid.smul l ε + ε :
      by conv {to_rhs, rw [← nat.succ_pred_eq_of_pos (nat.pos_of_ne_zero hl0), succ_smul',
        sub_add, add_sub_cancel] }
    ... < f j + ε : add_lt_add_right (hl j (le_trans hi.1 hj)) _
end

lemma is_cau_of_mono_bounded (f : ℕ → α) {a : α} {m : ℕ} (ham : ∀ n ≥ m, abs (f n) ≤ a)
  (hnm : ∀ n ≥ m, f n ≤ f n.succ) : is_cau_seq abs f :=
begin
  refine @eq.rec_on (ℕ → α) _ (is_cau_seq abs) _ _
    (-⟨_, @is_cau_of_decreasing_bounded _ _ _ (λ n, -f n) a m (by simpa) (by simpa)⟩ : cau_seq α abs).2,
  ext,
  exact neg_neg _
end

lemma is_cau_series_of_abv_le_cau  {f : ℕ → β} {g : ℕ → α}  (n : ℕ) : (∀ m, n ≤ m → abv (f m) ≤ g m) →
  is_cau_seq abs (λ n, (range n).sum g) → is_cau_seq abv (λ n, (range n).sum f) :=
begin
  assume hm hg ε ε0,
  cases hg (ε / 2) (div_pos ε0 (by norm_num)) with i hi,
  existsi max n i,
  assume j ji,
  have hi₁ := hi j (le_trans (le_max_right n i) ji),
  have hi₂ := hi (max n i) (le_max_right n i),
  have sub_le := abs_sub_le ((range j).sum g) ((range i).sum g) ((range (max n i)).sum g),
  have := add_lt_add hi₁ hi₂,
  rw [abs_sub ((range (max n i)).sum g), add_halves ε] at this,
  refine lt_of_le_of_lt (le_trans (le_trans _ (le_abs_self _)) sub_le) this,
  generalize hk : j - max n i = k,
  clear this hi₂ hi₁ hi ε0 ε hg sub_le,
  rw nat.sub_eq_iff_eq_add ji at hk,
  rw hk,
  clear hk ji j,
  induction k with k' hi,
  { simp [abv_zero abv] },
  { dsimp at *,
    rw [nat.succ_add, sum_range_succ, sum_range_succ, add_assoc, add_assoc],
    refine le_trans (abv_add _ _ _) _,
    exact add_le_add (hm _ (le_add_of_nonneg_of_le (nat.zero_le _) (le_max_left _ _))) hi },
end

lemma is_cau_series_of_abv_cau {f : ℕ → β} : is_cau_seq abs (λ m, (range m).sum (λ n, abv (f n))) →
  is_cau_seq abv (λ m, (range m).sum f) :=
is_cau_series_of_abv_le_cau 0 (λ n h, le_refl _)

lemma is_cau_geo_series {β : Type*} [field β] {abv : β → α} [is_absolute_value abv]
   (x : β) (hx1 : abv x < 1) : is_cau_seq abv (λ n, (range n).sum (λ m, x ^ m)) :=
have hx1' : abv x ≠ 1 := λ h, by simpa [h, lt_irrefl] using hx1,
is_cau_series_of_abv_cau
begin
  simp only [abv_pow abv, geom_sum hx1'] {eta := ff},
  conv in (_ / _) { rw [← neg_div_neg_eq, neg_sub, neg_sub] },
  refine @is_cau_of_mono_bounded _ _ _ _ ((1 : α) / (1 - abv x)) 0 _ _,
  { assume n hn,
    rw abs_of_nonneg,
    refine div_le_div_of_le_of_pos (sub_le_self _ (abv_pow abv x n ▸ abv_nonneg _ _))
      (sub_pos.2 hx1),
    refine div_nonneg (sub_nonneg.2 _) (sub_pos.2 hx1),
    clear hn,
    induction n with n ih,
    { simp },
    { rw [_root_.pow_succ, ← one_mul (1 : α)],
      refine mul_le_mul (le_of_lt hx1) ih (abv_pow abv x n ▸ abv_nonneg _ _) (by norm_num) } },
  { assume n hn,
    refine div_le_div_of_le_of_pos (sub_le_sub_left _ _) (sub_pos.2 hx1),
    rw [← one_mul (_ ^ n), _root_.pow_succ],
    exact mul_le_mul_of_nonneg_right (le_of_lt hx1) (pow_nonneg (abv_nonneg _ _) _) }
end

lemma is_cau_geo_series_const (a : α) {x : α} (hx1 : abs x < 1) : is_cau_seq abs (λ m, (range m).sum (λ n, a * x ^ n)) :=
have is_cau_seq abs (λ m, a * (range m).sum (λ n, x ^ n)) := (cau_seq.const abs a * ⟨_, is_cau_geo_series x hx1⟩).2,
  by simpa only [mul_sum]

lemma series_ratio_test {f : ℕ → β} (n : ℕ) (r : α)
  (hr0 : 0 ≤ r) (hr1 : r < 1) (h : ∀ m, n ≤ m → abv (f m.succ) ≤ r * abv (f m)) :
  is_cau_seq abv (λ m, (range m).sum f) :=
have har1 : abs r < 1, by rwa abs_of_nonneg hr0,
begin
  refine is_cau_series_of_abv_le_cau n.succ _ (is_cau_geo_series_const (abv (f n.succ) * r⁻¹ ^ n.succ) har1),
  assume m hmn,
  cases classical.em (r = 0) with r_zero r_ne_zero,
  { have m_pos := lt_of_lt_of_le (nat.succ_pos n) hmn,
    have := h m.pred (nat.le_of_succ_le_succ (by rwa [nat.succ_pred_eq_of_pos m_pos])),
    simpa [r_zero, nat.succ_pred_eq_of_pos m_pos, pow_succ] },
  generalize hk : m - n.succ = k,
  have r_pos : 0 < r := lt_of_le_of_ne hr0 (ne.symm r_ne_zero),
  replace hk : m = k + n.succ := (nat.sub_eq_iff_eq_add hmn).1 hk,
  induction k with k ih generalizing m n,
  { rw [hk, zero_add, mul_right_comm, ← pow_inv _ _ r_ne_zero, ← div_eq_mul_inv, mul_div_cancel],
    exact (ne_of_lt (pow_pos r_pos _)).symm },
  { have kn : k + n.succ ≥ n.succ, by rw ← zero_add n.succ; exact add_le_add (zero_le _) (by simp),
    rw [hk, nat.succ_add, pow_succ' r, ← mul_assoc],
    exact le_trans (by rw mul_comm; exact h _ (nat.le_of_succ_le kn))
      (mul_le_mul_of_nonneg_right (ih (k + n.succ) n h kn rfl) hr0) }
end

lemma sum_range_diag_flip {α : Type*} [add_comm_monoid α] (n : ℕ) (f : ℕ → ℕ → α) :
  (range n).sum (λ m, (range (m + 1)).sum (λ k, f k (m - k))) =
  (range n).sum (λ m, (range (n - m)).sum (f m)) :=
have h₁ : ((range n).sigma (range ∘ nat.succ)).sum
    (λ (a : Σ m, ℕ), f (a.2) (a.1 - a.2)) =
    (range n).sum (λ m, (range (m + 1)).sum
    (λ k, f k (m - k))) := sum_sigma,
have h₂ : ((range n).sigma (λ m, range (n - m))).sum (λ a : Σ (m : ℕ), ℕ, f (a.1) (a.2)) =
    (range n).sum (λ m, sum (range (n - m)) (f m)) := sum_sigma,
h₁ ▸ h₂ ▸ sum_bij
(λ a _, ⟨a.2, a.1 - a.2⟩)
(λ a ha, have h₁ : a.1 < n := mem_range.1 (mem_sigma.1 ha).1,
  have h₂ : a.2 < nat.succ a.1 := mem_range.1 (mem_sigma.1 ha).2,
    mem_sigma.2 ⟨mem_range.2 (lt_of_lt_of_le h₂ h₁),
    mem_range.2 ((nat.sub_lt_sub_right_iff (nat.le_of_lt_succ h₂)).2 h₁)⟩)
(λ _ _, rfl)
(λ ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ha hb h,
  have ha : a₁ < n ∧ a₂ ≤ a₁ :=
      ⟨mem_range.1 (mem_sigma.1 ha).1, nat.le_of_lt_succ (mem_range.1 (mem_sigma.1 ha).2)⟩,
  have hb : b₁ < n ∧ b₂ ≤ b₁ :=
      ⟨mem_range.1 (mem_sigma.1 hb).1, nat.le_of_lt_succ (mem_range.1 (mem_sigma.1 hb).2)⟩,
  have h : a₂ = b₂ ∧ _ := sigma.mk.inj h,
  have h' : a₁ = b₁ - b₂ + a₂ := (nat.sub_eq_iff_eq_add ha.2).1 (eq_of_heq h.2),
  sigma.mk.inj_iff.2
    ⟨nat.sub_add_cancel hb.2 ▸ h'.symm ▸ h.1 ▸ rfl,
      (heq_of_eq h.1)⟩)
(λ ⟨a₁, a₂⟩ ha,
  have ha : a₁ < n ∧ a₂ < n - a₁ :=
      ⟨mem_range.1 (mem_sigma.1 ha).1, (mem_range.1 (mem_sigma.1 ha).2)⟩,
  ⟨⟨a₂ + a₁, a₁⟩, ⟨mem_sigma.2 ⟨mem_range.2 (nat.lt_sub_right_iff_add_lt.1 ha.2),
    mem_range.2 (nat.lt_succ_of_le (nat.le_add_left _ _))⟩,
  sigma.mk.inj_iff.2 ⟨rfl, heq_of_eq (nat.add_sub_cancel _ _).symm⟩⟩⟩)

lemma abv_sum_le_sum_abv {γ : Type*} (f : γ → β) (s : finset γ) :
  abv (s.sum f) ≤ s.sum (abv ∘ f) :=
by haveI := classical.dec_eq γ; exact
finset.induction_on s (by simp [abv_zero abv])
  (λ a s has ih, by rw [sum_insert has, sum_insert has];
    exact le_trans (abv_add abv _ _) (add_le_add_left ih _))

lemma sum_range_sub_sum_range {α : Type*} [add_comm_group α] {f : ℕ → α}
  {n m : ℕ} (hnm : n ≤ m) : (range m).sum f - (range n).sum f =
  ((range m).filter (λ k, n ≤ k)).sum f :=
begin
  rw [← sum_sdiff (@filter_subset _ (λ k, n ≤ k) _ (range m)),
    sub_eq_iff_eq_add, ← eq_sub_iff_add_eq, add_sub_cancel'],
  refine finset.sum_congr
    (finset.ext.2 $ λ a, ⟨λ h, by simp at *; finish,
    λ h, have ham : a < m := lt_of_lt_of_le (mem_range.1 h) hnm,
      by simp * at *⟩)
    (λ _ _, rfl),
end

lemma cauchy_product {a b : ℕ → β}
  (ha : is_cau_seq abs (λ m, (range m).sum (λ n, abv (a n))))
  (hb : is_cau_seq abv (λ m, (range m).sum b)) (ε : α) (ε0 : 0 < ε) :
  ∃ i : ℕ, ∀ j ≥ i, abv ((range j).sum a * (range j).sum b -
  (range j).sum (λ n, (range (n + 1)).sum (λ m, a m * b (n - m)))) < ε :=
let ⟨Q, hQ⟩ := cau_seq.bounded ⟨_, hb⟩ in
let ⟨P, hP⟩ := cau_seq.bounded ⟨_, ha⟩ in
have hP0 : 0 < P, from lt_of_le_of_lt (abs_nonneg _) (hP 0),
have hPε0 : 0 < ε / (2 * P),
  from div_pos ε0 (mul_pos (show (2 : α) > 0, from by norm_num) hP0),
let ⟨N, hN⟩ := cau_seq.cauchy₂ ⟨_, hb⟩ hPε0 in
have hQε0 : 0 < ε / (4 * Q),
  from div_pos ε0 (mul_pos (show (0 : α) < 4, by norm_num) (lt_of_le_of_lt (abv_nonneg _ _) (hQ 0))),
let ⟨M, hM⟩ := cau_seq.cauchy₂ ⟨_, ha⟩ hQε0 in
⟨2 * (max N M + 1), λ K hK,
have h₁ : sum (range K) (λ m, (range (m + 1)).sum (λ k, a k * b (m - k))) =
    sum (range K) (λ m, sum (range (K - m)) (λ n, a m * b n)),
  by simpa using sum_range_diag_flip K (λ m n, a m * b n),
have h₂ : (λ i, (range (K - i)).sum (λ k, a i * b k)) = (λ i, a i * (range (K - i)).sum b),
  by simp [finset.mul_sum],
have h₃ : (range K).sum (λ i, a i * (range (K - i)).sum b) =
    (range K).sum (λ i, a i * ((range (K - i)).sum b - (range K).sum b))
    + (range K).sum (λ i, a i * (range K).sum b),
  by rw ← sum_add_distrib; simp [(mul_add _ _ _).symm],
have two_mul_two : (4 : α) = 2 * 2, by norm_num,
have hQ0 : Q ≠ 0, from λ h, by simpa [h, lt_irrefl] using hQε0,
have h2Q0 : 2 * Q ≠ 0, from mul_ne_zero two_ne_zero hQ0,
have hε : ε / (2 * P) * P + ε / (4 * Q) * (2 * Q) = ε,
  by rw [← div_div_eq_div_mul, div_mul_cancel _ (ne.symm (ne_of_lt hP0)),
    two_mul_two, mul_assoc, ← div_div_eq_div_mul, div_mul_cancel _ h2Q0, add_halves],
have hNMK : max N M + 1 < K,
  from lt_of_lt_of_le (by rw two_mul; exact lt_add_of_pos_left _ (nat.succ_pos _)) hK,
have hKN : N < K,
  from calc N ≤ max N M : le_max_left _ _
  ... < max N M + 1 : nat.lt_succ_self _
  ... < K : hNMK,
have hsumlesum : (range (max N M + 1)).sum (λ i, abv (a i) *
    abv ((range (K - i)).sum b - (range K).sum b)) ≤ (range (max N M + 1)).sum
    (λ i, abv (a i) * (ε / (2 * P))),
  from sum_le_sum (λ m hmJ, mul_le_mul_of_nonneg_left
    (le_of_lt (hN (K - m) K
      (nat.le_sub_left_of_add_le (le_trans
        (by rw two_mul; exact add_le_add (le_of_lt (mem_range.1 hmJ))
          (le_trans (le_max_left _ _) (le_of_lt (lt_add_one _)))) hK))
      (le_of_lt hKN))) (abv_nonneg abv _)),
have hsumltP : sum (range (max N M + 1)) (λ n, abv (a n)) < P :=
  calc sum (range (max N M + 1)) (λ n, abv (a n))
      = abs (sum (range (max N M + 1)) (λ n, abv (a n))) :
  eq.symm (abs_of_nonneg (zero_le_sum (λ x h, abv_nonneg abv (a x))))
  ... < P : hP (max N M + 1),
begin
  rw [h₁, h₂, h₃, sum_mul, ← sub_sub, sub_right_comm, sub_self, zero_sub, abv_neg abv],
  refine lt_of_le_of_lt (abv_sum_le_sum_abv _ _) _,
  suffices : (range (max N M + 1)).sum (λ (i : ℕ), abv (a i) * abv ((range (K - i)).sum b - (range K).sum b)) +
    ((range K).sum (λ (i : ℕ), abv (a i) * abv ((range (K - i)).sum b - (range K).sum b)) -(range (max N M + 1)).sum
     (λ (i : ℕ), abv (a i) * abv ((range (K - i)).sum b - (range K).sum b))) < ε / (2 * P) * P + ε / (4 * Q) * (2 * Q),
  { rw hε at this, simpa [abv_mul abv] },
  refine add_lt_add (lt_of_le_of_lt hsumlesum
    (by rw [← sum_mul, mul_comm]; exact (mul_lt_mul_left hPε0).mpr hsumltP)) _,
  rw sum_range_sub_sum_range (le_of_lt hNMK),
  exact calc sum ((range K).filter (λ k, max N M + 1 ≤ k))
      (λ i, abv (a i) * abv (sum (range (K - i)) b - sum (range K) b))
      ≤ sum ((range K).filter (λ k, max N M + 1 ≤ k)) (λ i, abv (a i) * (2 * Q)) :
    sum_le_sum (λ n hn, begin
      refine mul_le_mul_of_nonneg_left _ (abv_nonneg _ _),
      rw sub_eq_add_neg,
      refine le_trans (abv_add _ _ _) _,
      rw [two_mul, abv_neg abv],
      exact add_le_add (le_of_lt (hQ _)) (le_of_lt (hQ _)),
    end)
    ... < ε / (4 * Q) * (2 * Q) :
      by rw [← sum_mul, ← sum_range_sub_sum_range (le_of_lt hNMK)];
      refine (mul_lt_mul_right $ by rw two_mul;
        exact add_pos (lt_of_le_of_lt (abv_nonneg _ _) (hQ 0))
          (lt_of_le_of_lt (abv_nonneg _ _) (hQ 0))).2
        (lt_of_le_of_lt (le_abs_self _)
          (hM _ _ (le_trans (nat.le_succ_of_le (le_max_right _ _)) (le_of_lt hNMK))
            (nat.le_succ_of_le (le_max_right _ _))))
end⟩

end

open finset

open cau_seq

namespace complex

lemma is_cau_abs_exp (z : ℂ) : is_cau_seq _root_.abs
  (λ n, (range n).sum (λ m, abs (z ^ m / nat.fact m))) :=
let ⟨n, hn⟩ := exists_nat_gt (abs z) in
have hn0 : (0 : ℝ) < n, from lt_of_le_of_lt (abs_nonneg _) hn,
series_ratio_test n (complex.abs z / n) (div_nonneg_of_nonneg_of_pos (complex.abs_nonneg _) hn0)
  (by rwa [div_lt_iff hn0, one_mul])
  (λ m hm,
    by rw [abs_abs, abs_abs, nat.fact_succ, pow_succ,
      mul_comm m.succ, nat.cast_mul, ← div_div_eq_div_mul, mul_div_assoc,
      mul_div_right_comm, abs_mul, abs_div, abs_cast_nat];
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_le_left (abs_nonneg _) (nat.cast_pos.2 (nat.succ_pos _)) hn0
        (nat.cast_le.2 (le_trans hm (nat.le_succ _)))) (abs_nonneg _))

noncomputable theory

lemma is_cau_exp (z : ℂ) : is_cau_seq abs (λ n, (range n).sum (λ m, z ^ m / nat.fact m)) :=
  is_cau_series_of_abv_cau (is_cau_abs_exp z)

def exp' (z : ℂ) : cau_seq ℂ complex.abs := ⟨λ n, (range n).sum (λ m, z ^ m / nat.fact m), is_cau_exp z⟩

def exp (z : ℂ) : ℂ := lim (exp' z)

def sin (z : ℂ) : ℂ := ((exp (-z * I) - exp (z * I)) * I) / 2

def cos (z : ℂ) : ℂ := (exp (z * I) + exp (-z * I)) / 2

def tan (z : ℂ) : ℂ := sin z / cos z

def sinh (z : ℂ) : ℂ := (exp z - exp (-z)) / 2

def cosh (z : ℂ) : ℂ := (exp z + exp (-z)) / 2

def tanh (z : ℂ) : ℂ := sinh z / cosh z

end complex

namespace real

open complex

def exp (x : ℝ) : ℝ := (exp x).re

def sin (x : ℝ) : ℝ := (sin x).re

def cos (x : ℝ) : ℝ := (cos x).re

def tan (x : ℝ) : ℝ := (tan x).re

def sinh (x : ℝ) : ℝ := (sinh x).re

def cosh (x : ℝ) : ℝ := (cosh x).re

def tanh (x : ℝ) : ℝ := (tanh x).re

end real

namespace complex

variables (x y : ℂ)

@[simp] lemma exp_zero : exp 0 = 1 :=
lim_eq_of_equiv_const $
  λ ε ε0, ⟨1, λ j hj, begin
  convert ε0,
  cases j,
  { exact absurd hj (not_le_of_gt zero_lt_one) },
  { dsimp [exp'],
    induction j with j ih,
    { dsimp [exp']; simp },
    { rw ← ih dec_trivial,
      simp only [sum_range_succ, pow_succ],
      simp } }
end⟩

lemma exp_add : exp (x + y) = exp x * exp y :=
show lim (⟨_, is_cau_exp (x + y)⟩ : cau_seq ℂ abs) =
  lim (show cau_seq ℂ abs, from ⟨_, is_cau_exp x⟩)
  * lim (show cau_seq ℂ abs, from ⟨_, is_cau_exp y⟩),
from
have hj : ∀ j : ℕ, (range j).sum
    (λ m, (x + y) ^ m / m.fact) = (range j).sum
    (λ i, (range (i + 1)).sum (λ k, x ^ k / k.fact *
    (y ^ (i - k) / (i - k).fact))),
  from assume j,
    finset.sum_congr rfl (λ m hm, begin
      rw [add_pow, div_eq_mul_inv, sum_mul],
      refine finset.sum_congr rfl (λ i hi, _),
      have h₁ : (nat.choose m i : ℂ) ≠ 0 := nat.cast_ne_zero.2
        (nat.pos_iff_ne_zero.1 (nat.choose_pos (nat.le_of_lt_succ (mem_range.1 hi)))),
      have h₂ := nat.choose_mul_fact_mul_fact (nat.le_of_lt_succ $ finset.mem_range.1 hi),
      rw [← h₂, nat.cast_mul, nat.cast_mul, mul_inv', mul_inv'],
      simp only [mul_left_comm (nat.choose m i : ℂ), mul_assoc, mul_left_comm (nat.choose m i : ℂ)⁻¹,
        mul_comm (nat.choose m i : ℂ)],
      rw inv_mul_cancel h₁,
      simp [div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm]
    end),
by rw lim_mul_lim;
  exact eq.symm (lim_eq_lim_of_equiv (by dsimp; simp only [hj];
    exact cauchy_product (is_cau_abs_exp x) (is_cau_exp y)))

attribute [irreducible] complex.exp

lemma exp_nat_mul (x : ℂ) : ∀ n : ℕ, exp(n*x) = (exp x)^n
| 0 := by rw [nat.cast_zero, zero_mul, exp_zero, pow_zero]
| (nat.succ n) := by rw [pow_succ', nat.cast_add_one, add_mul, exp_add, ←exp_nat_mul, one_mul]

lemma exp_ne_zero : exp x ≠ 0 :=
λ h, @zero_ne_one ℂ _ $
  by rw [← exp_zero, ← add_neg_self x, exp_add, h]; simp

lemma exp_neg : exp (-x) = (exp x)⁻¹ :=
by rw [← domain.mul_left_inj (exp_ne_zero x), ← exp_add];
  simp [mul_inv_cancel (exp_ne_zero x)]

lemma exp_sub : exp (x - y) = exp x / exp y :=
by simp [exp_add, exp_neg, div_eq_mul_inv]

@[simp] lemma exp_conj : exp (conj x) = conj (exp x) :=
begin
  dsimp [exp],
  rw [← lim_conj],
  refine congr_arg lim (cau_seq.ext (λ _, _)),
  dsimp [exp', function.comp, cau_seq_conj],
  rw ← sum_hom conj,
  refine sum_congr rfl (λ n hn, _),
  rw [conj_div, conj_pow, ← of_real_nat_cast, conj_of_real]
end

@[simp] lemma of_real_exp_of_real_re (x : ℝ) : ((exp x).re : ℂ) = exp x :=
eq_conj_iff_re.1 $ by rw [← exp_conj, conj_of_real]

@[simp] lemma of_real_exp (x : ℝ) : (real.exp x : ℂ) = exp x :=
of_real_exp_of_real_re _

@[simp] lemma exp_of_real_im (x : ℝ) : (exp x).im = 0 :=
by rw [← of_real_exp_of_real_re, of_real_im]

lemma exp_of_real_re (x : ℝ) : (exp x).re = real.exp x := rfl

lemma two_sinh : 2 * sinh x = exp x - exp (-x) :=
mul_div_cancel' _ two_ne_zero'

lemma two_cosh : 2 * cosh x = exp x + exp (-x) :=
mul_div_cancel' _ two_ne_zero'

@[simp] lemma sinh_zero : sinh 0 = 0 := by simp [sinh]

@[simp] lemma sinh_neg : sinh (-x) = -sinh x :=
by simp [sinh, exp_neg, (neg_div _ _).symm, add_mul]

private lemma sinh_add_aux {a b c d : ℂ} :
  (a - b) * (c + d) + (a + b) * (c - d) = 2 * (a * c - b * d) := by ring

lemma sinh_add : sinh (x + y) = sinh x * cosh y + cosh x * sinh y :=
begin
  rw [← domain.mul_left_inj (@two_ne_zero' ℂ _ _ _), two_sinh,
      exp_add, neg_add, exp_add, eq_comm,
      mul_add, ← mul_assoc, two_sinh, mul_left_comm, two_sinh,
      ← domain.mul_left_inj (@two_ne_zero' ℂ _ _ _), mul_add,
      mul_left_comm, two_cosh, ← mul_assoc, two_cosh],
  exact sinh_add_aux
end

@[simp] lemma cosh_zero : cosh 0 = 1 := by simp [cosh]

@[simp] lemma cosh_neg : cosh (-x) = cosh x :=
by simp [cosh, exp_neg]

private lemma cosh_add_aux {a b c d : ℂ} :
  (a + b) * (c + d) + (a - b) * (c - d) = 2 * (a * c + b * d) := by ring

lemma cosh_add : cosh (x + y) = cosh x * cosh y + sinh x * sinh y :=
begin
  rw [← domain.mul_left_inj (@two_ne_zero' ℂ _ _ _), two_cosh,
      exp_add, neg_add, exp_add, eq_comm,
      mul_add, ← mul_assoc, two_cosh, ← mul_assoc, two_sinh,
      ← domain.mul_left_inj (@two_ne_zero' ℂ _ _ _), mul_add,
      mul_left_comm, two_cosh, mul_left_comm, two_sinh],
  exact cosh_add_aux
end

lemma sinh_sub : sinh (x - y) = sinh x * cosh y - cosh x * sinh y :=
by simp [sinh_add, sinh_neg, cosh_neg]

lemma cosh_sub : cosh (x - y) = cosh x * cosh y - sinh x * sinh y :=
by simp [cosh_add, sinh_neg, cosh_neg]

lemma sinh_conj : sinh (conj x) = conj (sinh x) :=
by rw [sinh, ← conj_neg, exp_conj, exp_conj, ← conj_sub, sinh, conj_div, conj_two]

@[simp] lemma of_real_sinh_of_real_re (x : ℝ) : ((sinh x).re : ℂ) = sinh x :=
eq_conj_iff_re.1 $ by rw [← sinh_conj, conj_of_real]

@[simp] lemma of_real_sinh (x : ℝ) : (real.sinh x : ℂ) = sinh x :=
of_real_sinh_of_real_re _

@[simp] lemma sinh_of_real_im (x : ℝ) : (sinh x).im = 0 :=
by rw [← of_real_sinh_of_real_re, of_real_im]

lemma sinh_of_real_re (x : ℝ) : (sinh x).re = real.sinh x := rfl

lemma cosh_conj : cosh (conj x) = conj (cosh x) :=
by rw [cosh, ← conj_neg, exp_conj, exp_conj, ← conj_add, cosh, conj_div, conj_two]

@[simp] lemma of_real_cosh_of_real_re (x : ℝ) : ((cosh x).re : ℂ) = cosh x :=
eq_conj_iff_re.1 $ by rw [← cosh_conj, conj_of_real]

@[simp] lemma of_real_cosh (x : ℝ) : (real.cosh x : ℂ) = cosh x :=
of_real_cosh_of_real_re _

@[simp] lemma cosh_of_real_im (x : ℝ) : (cosh x).im = 0 :=
by rw [← of_real_cosh_of_real_re, of_real_im]

lemma cosh_of_real_re (x : ℝ) : (cosh x).re = real.cosh x := rfl

lemma tanh_eq_sinh_div_cosh : tanh x = sinh x / cosh x := rfl

@[simp] lemma tanh_zero : tanh 0 = 0 := by simp [tanh]

@[simp] lemma tanh_neg : tanh (-x) = -tanh x := by simp [tanh, neg_div]

lemma tanh_conj : tanh (conj x) = conj (tanh x) :=
by rw [tanh, sinh_conj, cosh_conj, ← conj_div, tanh]

@[simp] lemma of_real_tanh_of_real_re (x : ℝ) : ((tanh x).re : ℂ) = tanh x :=
eq_conj_iff_re.1 $ by rw [← tanh_conj, conj_of_real]

@[simp] lemma of_real_tanh (x : ℝ) : (real.tanh x : ℂ) = tanh x :=
of_real_tanh_of_real_re _

@[simp] lemma tanh_of_real_im (x : ℝ) : (tanh x).im = 0 :=
by rw [← of_real_tanh_of_real_re, of_real_im]

lemma tanh_of_real_re (x : ℝ) : (tanh x).re = real.tanh x := rfl

lemma cosh_add_sinh : cosh x + sinh x = exp x :=
by rw [← domain.mul_left_inj (@two_ne_zero' ℂ _ _ _), mul_add,
       two_cosh, two_sinh, add_add_sub_cancel, two_mul]

lemma sinh_add_cosh : sinh x + cosh x = exp x :=
by rw [add_comm, cosh_add_sinh]

lemma cosh_sub_sinh : cosh x - sinh x = exp (-x) :=
by rw [← domain.mul_left_inj (@two_ne_zero' ℂ _ _ _), mul_sub,
       two_cosh, two_sinh, add_sub_sub_cancel, two_mul]

lemma cosh_sq_sub_sinh_sq : cosh x ^ 2 - sinh x ^ 2 = 1 :=
by rw [sq_sub_sq, cosh_add_sinh, cosh_sub_sinh, ← exp_add, add_neg_self, exp_zero]

@[simp] lemma sin_zero : sin 0 = 0 := by simp [sin]

@[simp] lemma sin_neg : sin (-x) = -sin x :=
by simp [sin, exp_neg, (neg_div _ _).symm, add_mul]

lemma two_sin : 2 * sin x = (exp (-x * I) - exp (x * I)) * I :=
mul_div_cancel' _ two_ne_zero'

lemma two_cos : 2 * cos x = exp (x * I) + exp (-x * I) :=
mul_div_cancel' _ two_ne_zero'

lemma sinh_mul_I : sinh (x * I) = sin x * I :=
by rw [← domain.mul_left_inj (@two_ne_zero' ℂ _ _ _), two_sinh,
       ← mul_assoc, two_sin, mul_assoc, I_mul_I, mul_neg_one,
       neg_sub, neg_mul_eq_neg_mul]

lemma cosh_mul_I : cosh (x * I) = cos x :=
by rw [← domain.mul_left_inj (@two_ne_zero' ℂ _ _ _), two_cosh,
       two_cos, neg_mul_eq_neg_mul]

lemma sin_add : sin (x + y) = sin x * cos y + cos x * sin y :=
by rw [← domain.mul_right_inj I_ne_zero, ← sinh_mul_I,
       add_mul, add_mul, mul_right_comm, ← sinh_mul_I,
       mul_assoc, ← sinh_mul_I, ← cosh_mul_I, ← cosh_mul_I, sinh_add]

@[simp] lemma cos_zero : cos 0 = 1 := by simp [cos]

@[simp] lemma cos_neg : cos (-x) = cos x :=
by simp [cos, exp_neg]

private lemma cos_add_aux {a b c d : ℂ} :
  (a + b) * (c + d) - (b - a) * (d - c) * (-1) =
  2 * (a * c + b * d) := by ring

lemma cos_add : cos (x + y) = cos x * cos y - sin x * sin y :=
by rw [← cosh_mul_I, add_mul, cosh_add, cosh_mul_I, cosh_mul_I,
       sinh_mul_I, sinh_mul_I, mul_mul_mul_comm, I_mul_I,
       mul_neg_one, sub_eq_add_neg]

lemma sin_sub : sin (x - y) = sin x * cos y - cos x * sin y :=
by simp [sin_add, sin_neg, cos_neg]

lemma cos_sub : cos (x - y) = cos x * cos y + sin x * sin y :=
by simp [cos_add, sin_neg, cos_neg]

lemma sin_conj : sin (conj x) = conj (sin x) :=
by rw [← domain.mul_right_inj I_ne_zero, ← sinh_mul_I,
       ← conj_neg_I, ← conj_mul, ← conj_mul, sinh_conj,
       mul_neg_eq_neg_mul_symm, sinh_neg, sinh_mul_I, mul_neg_eq_neg_mul_symm]

@[simp] lemma of_real_sin_of_real_re (x : ℝ) : ((sin x).re : ℂ) = sin x :=
eq_conj_iff_re.1 $ by rw [← sin_conj, conj_of_real]

@[simp] lemma of_real_sin (x : ℝ) : (real.sin x : ℂ) = sin x :=
of_real_sin_of_real_re _

@[simp] lemma sin_of_real_im (x : ℝ) : (sin x).im = 0 :=
by rw [← of_real_sin_of_real_re, of_real_im]

lemma sin_of_real_re (x : ℝ) : (sin x).re = real.sin x := rfl

lemma cos_conj : cos (conj x) = conj (cos x) :=
by rw [← cosh_mul_I, ← conj_neg_I, ← conj_mul, ← cosh_mul_I,
       cosh_conj, mul_neg_eq_neg_mul_symm, cosh_neg]

@[simp] lemma of_real_cos_of_real_re (x : ℝ) : ((cos x).re : ℂ) = cos x :=
eq_conj_iff_re.1 $ by rw [← cos_conj, conj_of_real]

@[simp] lemma of_real_cos (x : ℝ) : (real.cos x : ℂ) = cos x :=
of_real_cos_of_real_re _

@[simp] lemma cos_of_real_im (x : ℝ) : (cos x).im = 0 :=
by rw [← of_real_cos_of_real_re, of_real_im]

lemma cos_of_real_re (x : ℝ) : (cos x).re = real.cos x := rfl

@[simp] lemma tan_zero : tan 0 = 0 := by simp [tan]

lemma tan_eq_sin_div_cos : tan x = sin x / cos x := rfl

@[simp] lemma tan_neg : tan (-x) = -tan x := by simp [tan, neg_div]

lemma tan_conj : tan (conj x) = conj (tan x) :=
by rw [tan, sin_conj, cos_conj, ← conj_div, tan]

@[simp] lemma of_real_tan_of_real_re (x : ℝ) : ((tan x).re : ℂ) = tan x :=
eq_conj_iff_re.1 $ by rw [← tan_conj, conj_of_real]

@[simp] lemma of_real_tan (x : ℝ) : (real.tan x : ℂ) = tan x :=
of_real_tan_of_real_re _

@[simp] lemma tan_of_real_im (x : ℝ) : (tan x).im = 0 :=
by rw [← of_real_tan_of_real_re, of_real_im]

lemma tan_of_real_re (x : ℝ) : (tan x).re = real.tan x := rfl

lemma cos_add_sin_I : cos x + sin x * I = exp (x * I) :=
by rw [← cosh_add_sinh, sinh_mul_I, cosh_mul_I]

lemma cos_sub_sin_I : cos x - sin x * I = exp (-x * I) :=
by rw [← neg_mul_eq_neg_mul, ← cosh_sub_sinh, sinh_mul_I, cosh_mul_I]

lemma sin_sq_add_cos_sq : sin x ^ 2 + cos x ^ 2 = 1 :=
eq.trans
  (by rw [cosh_mul_I, sinh_mul_I, mul_pow, I_sq, mul_neg_one, sub_neg_eq_add, add_comm])
  (cosh_sq_sub_sinh_sq (x * I))

lemma cos_two_mul' : cos (2 * x) = cos x ^ 2 - sin x ^ 2 :=
by rw [two_mul, cos_add, ← pow_two, ← pow_two]

lemma cos_two_mul : cos (2 * x) = 2 * cos x ^ 2 - 1 :=
by rw [cos_two_mul', eq_sub_iff_add_eq.2 (sin_sq_add_cos_sq x),
       ← sub_add, sub_add_eq_add_sub, two_mul]

lemma sin_two_mul : sin (2 * x) = 2 * sin x * cos x :=
by rw [two_mul, sin_add, two_mul, add_mul, mul_comm]

lemma cos_square : cos x ^ 2 = 1 / 2 + cos (2 * x) / 2 :=
by simp [cos_two_mul, div_add_div_same, mul_div_cancel_left, two_ne_zero', -one_div_eq_inv]

lemma sin_square : sin x ^ 2 = 1 - cos x ^ 2 :=
by { rw [←sin_sq_add_cos_sq x], simp }

lemma exp_mul_I : exp (x * I) = cos x + sin x * I :=
(cos_add_sin_I _).symm

lemma exp_add_mul_I : exp (x + y * I) = exp x * (cos y + sin y * I) :=
by rw [exp_add, exp_mul_I]

lemma exp_eq_exp_re_mul_sin_add_cos : exp x = exp x.re * (cos x.im + sin x.im * I) :=
by rw [← exp_add_mul_I, re_add_im]

theorem cos_add_sin_mul_I_pow (n : ℕ) (z : ℂ) : (cos z + sin z * I) ^ n = cos (↑n * z) + sin (↑n * z) * I :=
begin
  rw [← exp_mul_I, ← exp_mul_I],
  induction n with n ih,
  { rw [pow_zero, nat.cast_zero, zero_mul, zero_mul, exp_zero] },
  { rw [pow_succ', ih, nat.cast_succ, add_mul, add_mul, one_mul, exp_add] }
end

end complex

namespace real

open complex

variables (x y : ℝ)

@[simp] lemma exp_zero : exp 0 = 1 :=
by simp [real.exp]

lemma exp_add : exp (x + y) = exp x * exp y :=
by simp [exp_add, exp]

lemma exp_nat_mul (x : ℝ) : ∀ n : ℕ, exp(n*x) = (exp x)^n
| 0 := by rw [nat.cast_zero, zero_mul, exp_zero, pow_zero]
| (nat.succ n) := by rw [pow_succ', nat.cast_add_one, add_mul, exp_add, ←exp_nat_mul, one_mul]

lemma exp_ne_zero : exp x ≠ 0 :=
λ h, exp_ne_zero x $ by rw [exp, ← of_real_inj] at h; simp * at *

lemma exp_neg : exp (-x) = (exp x)⁻¹ :=
by rw [← of_real_inj, exp, of_real_exp_of_real_re, of_real_neg, exp_neg,
  of_real_inv, of_real_exp]

lemma exp_sub : exp (x - y) = exp x / exp y :=
by simp [exp_add, exp_neg, div_eq_mul_inv]

@[simp] lemma sin_zero : sin 0 = 0 := by simp [sin]

@[simp] lemma sin_neg : sin (-x) = -sin x :=
by simp [sin, exp_neg, (neg_div _ _).symm, add_mul]

lemma sin_add : sin (x + y) = sin x * cos y + cos x * sin y :=
by rw [← of_real_inj]; simp [sin, sin_add]

@[simp] lemma cos_zero : cos 0 = 1 := by simp [cos]

@[simp] lemma cos_neg : cos (-x) = cos x :=
by simp [cos, exp_neg]

lemma cos_add : cos (x + y) = cos x * cos y - sin x * sin y :=
by rw ← of_real_inj; simp [cos, cos_add]

lemma sin_sub : sin (x - y) = sin x * cos y - cos x * sin y :=
by simp [sin_add, sin_neg, cos_neg]

lemma cos_sub : cos (x - y) = cos x * cos y + sin x * sin y :=
by simp [cos_add, sin_neg, cos_neg]

lemma tan_eq_sin_div_cos : tan x = sin x / cos x :=
if h : complex.cos x = 0 then by simp [sin, cos, tan, *, complex.tan, div_eq_mul_inv] at *
else
  by rw [sin, cos, tan, complex.tan, ← of_real_inj, div_eq_mul_inv, mul_re];
  simp [norm_sq, (div_div_eq_div_mul _ _ _).symm, div_self h]; refl

@[simp] lemma tan_zero : tan 0 = 0 := by simp [tan]

@[simp] lemma tan_neg : tan (-x) = -tan x := by simp [tan, neg_div]

lemma sin_sq_add_cos_sq : sin x ^ 2 + cos x ^ 2 = 1 :=
of_real_inj.1 $ by simpa using sin_sq_add_cos_sq x

lemma sin_sq_le_one : sin x ^ 2 ≤ 1 :=
by rw ← sin_sq_add_cos_sq x; exact le_add_of_nonneg_right' (pow_two_nonneg _)

lemma cos_sq_le_one : cos x ^ 2 ≤ 1 :=
by rw ← sin_sq_add_cos_sq x; exact le_add_of_nonneg_left' (pow_two_nonneg _)

lemma abs_sin_le_one : abs' (sin x) ≤ 1 :=
(mul_self_le_mul_self_iff (_root_.abs_nonneg (sin x)) (by exact zero_le_one)).2 $
by rw [← _root_.abs_mul, abs_mul_self, mul_one, ← pow_two];
   apply sin_sq_le_one

lemma abs_cos_le_one : abs' (cos x) ≤ 1 :=
(mul_self_le_mul_self_iff (_root_.abs_nonneg (cos x)) (by exact zero_le_one)).2 $
by rw [← _root_.abs_mul, abs_mul_self, mul_one, ← pow_two];
   apply cos_sq_le_one

lemma sin_le_one : sin x ≤ 1 :=
(abs_le.1 (abs_sin_le_one _)).2

lemma cos_le_one : cos x ≤ 1 :=
(abs_le.1 (abs_cos_le_one _)).2

lemma neg_one_le_sin : -1 ≤ sin x :=
(abs_le.1 (abs_sin_le_one _)).1

lemma neg_one_le_cos : -1 ≤ cos x :=
(abs_le.1 (abs_cos_le_one _)).1

lemma cos_two_mul : cos (2 * x) = 2 * cos x ^ 2 - 1 :=
by rw ← of_real_inj; simp [cos_two_mul]

lemma sin_two_mul : sin (2 * x) = 2 * sin x * cos x :=
by rw ← of_real_inj; simp [sin_two_mul]

lemma cos_square : cos x ^ 2 = 1 / 2 + cos (2 * x) / 2 :=
of_real_inj.1 $ by simpa using cos_square x

lemma sin_square : sin x ^ 2 = 1 - cos x ^ 2 :=
eq_sub_iff_add_eq.2 $ sin_sq_add_cos_sq _

@[simp] lemma sinh_zero : sinh 0 = 0 := by simp [sinh]

@[simp] lemma sinh_neg : sinh (-x) = -sinh x :=
by simp [sinh, exp_neg, (neg_div _ _).symm, add_mul]

lemma sinh_add : sinh (x + y) = sinh x * cosh y + cosh x * sinh y :=
by rw ← of_real_inj; simp [sinh_add]

@[simp] lemma cosh_zero : cosh 0 = 1 := by simp [cosh]

@[simp] lemma cosh_neg : cosh (-x) = cosh x :=
by simp [cosh, exp_neg]

lemma cosh_add : cosh (x + y) = cosh x * cosh y + sinh x * sinh y :=
by rw ← of_real_inj; simp [cosh, cosh_add]

lemma sinh_sub : sinh (x - y) = sinh x * cosh y - cosh x * sinh y :=
by simp [sinh_add, sinh_neg, cosh_neg]

lemma cosh_sub : cosh (x - y) = cosh x * cosh y - sinh x * sinh y :=
by simp [cosh_add, sinh_neg, cosh_neg]

lemma tanh_eq_sinh_div_cosh : tanh x = sinh x / cosh x :=
of_real_inj.1 $ by simp [tanh_eq_sinh_div_cosh]

@[simp] lemma tanh_zero : tanh 0 = 0 := by simp [tanh]

@[simp] lemma tanh_neg : tanh (-x) = -tanh x := by simp [tanh, neg_div]

open is_absolute_value

/- TODO make this private and prove ∀ x -/
lemma add_one_le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) : x + 1 ≤ exp x :=
calc x + 1 ≤ lim (⟨(λ n : ℕ, ((exp' x) n).re), is_cau_seq_re (exp' x)⟩ : cau_seq ℝ abs') :
  le_lim (cau_seq.le_of_exists ⟨2,
    λ j hj, show x + (1 : ℝ) ≤ ((range j).sum (λ m, (x ^ m / m.fact : ℂ))).re,
      from have h₁ : (((λ m : ℕ, (x ^ m / m.fact : ℂ)) ∘ nat.succ) 0).re = x, by simp,
      have h₂ : ((x : ℂ) ^ 0 / nat.fact 0).re = 1, by simp,
      begin
        rw [← nat.sub_add_cancel hj, sum_range_succ', sum_range_succ',
          add_re, add_re, h₁, h₂, add_assoc,
          ← @sum_hom _ _ _ _ _ _ _ complex.re
            (is_add_group_hom.to_is_add_monoid_hom _)],
        refine le_add_of_nonneg_of_le (zero_le_sum (λ m hm, _)) (le_refl _), dsimp [-nat.fact_succ],
        rw [← of_real_pow, ← of_real_nat_cast, ← of_real_div, of_real_re],
        exact div_nonneg (pow_nonneg hx _) (nat.cast_pos.2 (nat.fact_pos _)),
      end⟩)
... = exp x : by rw [exp, complex.exp, ← cau_seq_re, lim_re]

lemma one_le_exp {x : ℝ} (hx : 0 ≤ x) : 1 ≤ exp x :=
by linarith [add_one_le_exp_of_nonneg hx]

lemma exp_pos (x : ℝ) : 0 < exp x :=
(le_total 0 x).elim (lt_of_lt_of_le zero_lt_one ∘ one_le_exp)
  (λ h, by rw [← neg_neg x, real.exp_neg];
    exact inv_pos (lt_of_lt_of_le zero_lt_one (one_le_exp (neg_nonneg.2 h))))

@[simp] lemma abs_exp (x : ℝ) : abs' (exp x) = exp x :=
abs_of_pos (exp_pos _)

lemma exp_strict_mono : strict_mono exp :=
λ x y h, by rw [← sub_add_cancel y x, real.exp_add];
  exact (lt_mul_iff_one_lt_left (exp_pos _)).2
    (lt_of_lt_of_le (by linarith) (add_one_le_exp_of_nonneg (by linarith)))

lemma exp_lt_exp {x y : ℝ} : exp x < exp y ↔ x < y := exp_strict_mono.lt_iff_lt

lemma exp_le_exp {x y : ℝ} : exp x ≤ exp y ↔ x ≤ y := exp_strict_mono.le_iff_le

lemma exp_injective : function.injective exp := exp_strict_mono.injective

@[simp] lemma exp_eq_one_iff : exp x = 1 ↔ x = 0 :=
by rw [← exp_zero, exp_injective.eq_iff]

end real

namespace complex

lemma sum_div_fact_le {α : Type*} [discrete_linear_ordered_field α] (n j : ℕ) (hn : 0 < n) :
  (sum (filter (λ k, n ≤ k) (range j)) (λ m : ℕ, (1 / m.fact : α))) ≤ n.succ * (n.fact * n)⁻¹ :=
calc (filter (λ k, n ≤ k) (range j)).sum (λ m : ℕ, (1 / m.fact : α))
    = (range (j - n)).sum (λ m, 1 / (m + n).fact) :
  sum_bij (λ m _, m - n)
    (λ m hm, mem_range.2 $ (nat.sub_lt_sub_right_iff (by simp at hm; tauto)).2
      (by simp at hm; tauto))
    (λ m hm, by rw nat.sub_add_cancel; simp at *; tauto)
    (λ a₁ a₂ ha₁ ha₂ h,
      by rwa [nat.sub_eq_iff_eq_add, ← nat.sub_add_comm, eq_comm, nat.sub_eq_iff_eq_add, add_right_inj, eq_comm] at h;
        simp at *; tauto)
    (λ b hb, ⟨b + n, mem_filter.2 ⟨mem_range.2 $ nat.add_lt_of_lt_sub_right (mem_range.1 hb), nat.le_add_left _ _⟩,
      by rw nat.add_sub_cancel⟩)
... ≤ (range (j - n)).sum (λ m, (nat.fact n * n.succ ^ m)⁻¹) :
  begin
    refine  sum_le_sum (assume m n, _),
    rw [one_div_eq_inv, inv_le_inv],
    { rw [← nat.cast_pow, ← nat.cast_mul, nat.cast_le, add_comm],
      exact nat.fact_mul_pow_le_fact },
    { exact nat.cast_pos.2 (nat.fact_pos _) },
    { exact mul_pos (nat.cast_pos.2 (nat.fact_pos _)) (pow_pos (nat.cast_pos.2 (nat.succ_pos _)) _) },
  end
... = (nat.fact n)⁻¹ * (range (j - n)).sum (λ m, n.succ⁻¹ ^ m) :
  by simp [mul_inv', mul_sum.symm, sum_mul.symm, -nat.fact_succ, mul_comm, inv_pow']
... = (n.succ - n.succ * n.succ⁻¹ ^ (j - n)) / (n.fact * n) :
  have h₁ : (n.succ : α) ≠ 1, from @nat.cast_one α _ _ ▸ mt nat.cast_inj.1
        (mt nat.succ_inj (nat.pos_iff_ne_zero.1 hn)),
  have h₂ : (n.succ : α) ≠ 0, from nat.cast_ne_zero.2 (nat.succ_ne_zero _),
  have h₃ : (n.fact * n : α) ≠ 0, from mul_ne_zero (nat.cast_ne_zero.2 (nat.pos_iff_ne_zero.1 (nat.fact_pos _)))
    (nat.cast_ne_zero.2 (nat.pos_iff_ne_zero.1 hn)),
  have h₄ : (n.succ - 1 : α) = n, by simp,
  by rw [geom_sum_inv h₁ h₂, eq_div_iff_mul_eq _ _ h₃, mul_comm _ (n.fact * n : α),
      ← mul_assoc (n.fact⁻¹ : α), ← mul_inv', h₄, ← mul_assoc (n.fact * n : α),
      mul_comm (n : α) n.fact, mul_inv_cancel h₃];
    simp [mul_add, add_mul, mul_assoc, mul_comm]
... ≤ n.succ / (n.fact * n) :
  begin
    refine (div_le_div_right (mul_pos _ _)).2 _,
    exact nat.cast_pos.2 (nat.fact_pos _),
    exact nat.cast_pos.2 hn,
    exact sub_le_self _ (mul_nonneg (nat.cast_nonneg _) (pow_nonneg (inv_nonneg.2 (nat.cast_nonneg _)) _))
  end

lemma exp_bound {x : ℂ} (hx : abs x ≤ 1) {n : ℕ} (hn : 0 < n) :
  abs (exp x - (range n).sum (λ m, x ^ m / m.fact)) ≤ abs x ^ n * (n.succ * (n.fact * n)⁻¹) :=
begin
  rw [← lim_const ((range n).sum _), exp, sub_eq_add_neg, ← lim_neg, lim_add, ← lim_abs],
  refine lim_le (cau_seq.le_of_exists ⟨n, λ j hj, _⟩),
  show abs ((range j).sum (λ m, x ^ m / m.fact) - (range n).sum (λ m, x ^ m / m.fact))
    ≤ abs x ^ n * (n.succ * (n.fact * n)⁻¹),
  rw sum_range_sub_sum_range hj,
  exact calc abs (((range j).filter (λ k, n ≤ k)).sum (λ m : ℕ, (x ^ m / m.fact : ℂ)))
      = abs (((range j).filter (λ k, n ≤ k)).sum (λ m : ℕ, (x ^ n * (x ^ (m - n) / m.fact) : ℂ))) :
    congr_arg abs (sum_congr rfl (λ m hm, by rw [← mul_div_assoc, ← pow_add, nat.add_sub_cancel']; simp at hm; tauto))
  ... ≤ sum (filter (λ k, n ≤ k) (range j)) (λ m, abs (x ^ n * (_ / m.fact))) : abv_sum_le_sum_abv _ _
  ... ≤ sum (filter (λ k, n ≤ k) (range j)) (λ m, abs x ^ n * (1 / m.fact)) :
    begin
      refine sum_le_sum (λ m hm, _),
      rw [abs_mul, abv_pow abs, abs_div, abs_cast_nat],
      refine mul_le_mul_of_nonneg_left ((div_le_div_right _).2 _) _,
      exact nat.cast_pos.2 (nat.fact_pos _),
      rw abv_pow abs,
      exact (pow_le_one _ (abs_nonneg _) hx),
      exact pow_nonneg (abs_nonneg _) _
    end
  ... = abs x ^ n * (((range j).filter (λ k, n ≤ k)).sum (λ m : ℕ, (1 / m.fact : ℝ))) :
    by simp [abs_mul, abv_pow abs, abs_div, mul_sum.symm]
  ... ≤ abs x ^ n * (n.succ * (n.fact * n)⁻¹) :
    mul_le_mul_of_nonneg_left (sum_div_fact_le _ _ hn) (pow_nonneg (abs_nonneg _) _)
end

lemma abs_exp_sub_one_le {x : ℂ} (hx : abs x ≤ 1) :
  abs (exp x - 1) ≤ 2 * abs x :=
calc abs (exp x - 1) = abs (exp x - (range 1).sum (λ m, x ^ m / m.fact)) :
  by simp [sum_range_succ]
... ≤ abs x ^ 1 * ((nat.succ 1) * (nat.fact 1 * (1 : ℕ))⁻¹) :
  exp_bound hx dec_trivial
... = 2 * abs x : by simp [two_mul, mul_two, mul_add, mul_comm]

end complex

namespace real

open complex finset

lemma cos_bound {x : ℝ} (hx : abs' x ≤ 1) : abs' (cos x - (1 - x ^ 2 / 2)) ≤ abs' x ^ 4 * (5 / 96) :=
calc abs' (cos x - (1 - x ^ 2 / 2)) = abs (complex.cos x - (1 - x ^ 2 / 2)) :
  by rw ← abs_of_real; simp [of_real_bit0, of_real_one, of_real_inv]
... = abs ((complex.exp (x * I) + complex.exp (-x * I) - (2 - x ^ 2)) / 2) :
  by simp [complex.cos, sub_div, add_div, neg_div, div_self (@two_ne_zero' ℂ _ _ _)]
... = abs (((complex.exp (x * I) - (range 4).sum (λ m, (x * I) ^ m / m.fact)) +
    ((complex.exp (-x * I) - (range 4).sum (λ m, (-x * I) ^ m / m.fact)))) / 2) :
  congr_arg abs (congr_arg (λ x : ℂ, x / 2) begin
    simp only [sum_range_succ],
    simp [pow_succ],
    apply complex.ext; simp [div_eq_mul_inv, norm_sq]; ring
  end)
... ≤ abs ((complex.exp (x * I) - (range 4).sum (λ m, (x * I) ^ m / m.fact)) / 2) +
    abs ((complex.exp (-x * I) - (range 4).sum (λ m, (-x * I) ^ m / m.fact)) / 2) :
  by rw add_div; exact abs_add _ _
... = (abs ((complex.exp (x * I) - (range 4).sum (λ m, (x * I) ^ m / m.fact))) / 2 +
    abs ((complex.exp (-x * I) - (range 4).sum (λ m, (-x * I) ^ m / m.fact))) / 2) :
  by simp [complex.abs_div]
... ≤ ((complex.abs (x * I) ^ 4 * (nat.succ 4 * (nat.fact 4 * (4 : ℕ))⁻¹)) / 2 +
    (complex.abs (-x * I) ^ 4 * (nat.succ 4 * (nat.fact 4 * (4 : ℕ))⁻¹)) / 2)  :
  add_le_add ((div_le_div_right (by norm_num)).2 (exp_bound (by simpa) dec_trivial))
             ((div_le_div_right (by norm_num)).2 (exp_bound (by simpa) dec_trivial))
... ≤ abs' x ^ 4 * (5 / 96) : by norm_num; simp [mul_assoc, mul_comm, mul_left_comm, mul_div_assoc]

lemma sin_bound {x : ℝ} (hx : abs' x ≤ 1) : abs' (sin x - (x - x ^ 3 / 6)) ≤ abs' x ^ 4 * (5 / 96) :=
calc abs' (sin x - (x - x ^ 3 / 6)) = abs (complex.sin x - (x - x ^ 3 / 6)) :
  by rw ← abs_of_real; simp [of_real_bit0, of_real_one, of_real_inv]
... = abs (((complex.exp (-x * I) - complex.exp (x * I)) * I - (2 * x - x ^ 3 / 3)) / 2) :
  by simp [complex.sin, sub_div, add_div, neg_div, mul_div_cancel_left _ (@two_ne_zero' ℂ _ _ _),
    div_div_eq_div_mul, show (3 : ℂ) * 2 = 6, by norm_num]
... = abs ((((complex.exp (-x * I) - (range 4).sum (λ m, (-x * I) ^ m / m.fact)) -
    (complex.exp (x * I) - (range 4).sum (λ m, (x * I) ^ m / m.fact))) * I) / 2) :
  congr_arg abs (congr_arg (λ x : ℂ, x / 2) begin
    simp only [sum_range_succ],
    simp [pow_succ],
    apply complex.ext; simp [div_eq_mul_inv, norm_sq]; ring
  end)
... ≤ abs ((complex.exp (-x * I) - (range 4).sum (λ m, (-x * I) ^ m / m.fact)) * I / 2) +
    abs (-((complex.exp (x * I) - (range 4).sum (λ m, (x * I) ^ m / m.fact)) * I) / 2) :
  by rw [sub_mul, sub_eq_add_neg, add_div]; exact abs_add _ _
... = (abs ((complex.exp (x * I) - (range 4).sum (λ m, (x * I) ^ m / m.fact))) / 2 +
    abs ((complex.exp (-x * I) - (range 4).sum (λ m, (-x * I) ^ m / m.fact))) / 2) :
  by simp [complex.abs_div, complex.abs_mul]
... ≤ ((complex.abs (x * I) ^ 4 * (nat.succ 4 * (nat.fact 4 * (4 : ℕ))⁻¹)) / 2 +
    (complex.abs (-x * I) ^ 4 * (nat.succ 4 * (nat.fact 4 * (4 : ℕ))⁻¹)) / 2) :
  add_le_add ((div_le_div_right (by norm_num)).2 (exp_bound (by simpa) dec_trivial))
             ((div_le_div_right (by norm_num)).2 (exp_bound (by simpa) dec_trivial))
... ≤ abs' x ^ 4 * (5 / 96) : by norm_num; simp [mul_assoc, mul_comm, mul_left_comm, mul_div_assoc]

lemma cos_pos_of_le_one {x : ℝ} (hx : abs' x ≤ 1) : 0 < cos x :=
calc 0 < (1 - x ^ 2 / 2) - abs' x ^ 4 * (5 / 96) :
  sub_pos.2 $ lt_sub_iff_add_lt.2
    (calc abs' x ^ 4 * (5 / 96) + x ^ 2 / 2
          ≤ 1 * (5 / 96) + 1 / 2 :
        add_le_add
          (mul_le_mul_of_nonneg_right (pow_le_one _ (abs_nonneg _) hx) (by norm_num))
          ((div_le_div_right (by norm_num)).2 (by rw [pow_two, ← abs_mul_self, _root_.abs_mul];
            exact mul_le_one hx (abs_nonneg _) hx))
      ... < 1 : by norm_num)
... ≤ cos x : sub_le.1 (abs_sub_le_iff.1 (cos_bound hx)).2

lemma sin_pos_of_pos_of_le_one {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1) : 0 < sin x :=
calc 0 < x - x ^ 3 / 6 - abs' x ^ 4 * (5 / 96) :
  sub_pos.2 $ lt_sub_iff_add_lt.2
    (calc abs' x ^ 4 * (5 / 96) + x ^ 3 / 6
        ≤ x * (5 / 96) + x / 6 :
      add_le_add
        (mul_le_mul_of_nonneg_right
          (calc abs' x ^ 4 ≤ abs' x ^ 1 : pow_le_pow_of_le_one (abs_nonneg _)
                (by rwa _root_.abs_of_nonneg (le_of_lt hx0))
                dec_trivial
            ... = x : by simp [_root_.abs_of_nonneg (le_of_lt (hx0))]) (by norm_num))
        ((div_le_div_right (by norm_num)).2
          (calc x ^ 3 ≤ x ^ 1 : pow_le_pow_of_le_one (le_of_lt hx0) hx dec_trivial
            ... = x : pow_one _))
    ... < x : by linarith)
... ≤ sin x : sub_le.1 (abs_sub_le_iff.1 (sin_bound
    (by rwa [_root_.abs_of_nonneg (le_of_lt hx0)]))).2

lemma sin_pos_of_pos_of_le_two {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 2) : 0 < sin x :=
have x / 2 ≤ 1, from div_le_of_le_mul (by norm_num) (by simpa),
calc 0 < 2 * sin (x / 2) * cos (x / 2) :
  mul_pos (mul_pos (by norm_num) (sin_pos_of_pos_of_le_one (half_pos hx0) this))
    (cos_pos_of_le_one (by rwa [_root_.abs_of_nonneg (le_of_lt (half_pos hx0))]))
... = sin x : by rw [← sin_two_mul, two_mul, add_halves]

lemma cos_one_le : cos 1 ≤ 2 / 3 :=
calc cos 1 ≤ abs' (1 : ℝ) ^ 4 * (5 / 96) + (1 - 1 ^ 2 / 2) :
  sub_le_iff_le_add.1 (abs_sub_le_iff.1 (cos_bound (by simp))).1
... ≤ 2 / 3 : by norm_num

lemma cos_one_pos : 0 < cos 1 := cos_pos_of_le_one (by simp)

lemma cos_two_neg : cos 2 < 0 :=
calc cos 2 = cos (2 * 1) : congr_arg cos (mul_one _).symm
... = _ : real.cos_two_mul 1
... ≤ 2 * (2 / 3) ^ 2 - 1 :
  sub_le_sub_right (mul_le_mul_of_nonneg_left
    (by rw [pow_two, pow_two]; exact
      mul_self_le_mul_self (le_of_lt cos_one_pos)
        cos_one_le)
    (by norm_num)) _
... < 0 : by norm_num

end real

namespace complex

lemma abs_cos_add_sin_mul_I (x : ℝ) : abs (cos x + sin x * I) = 1 :=
have _ := real.sin_sq_add_cos_sq x,
by simp [abs, norm_sq, pow_two, *, sin_of_real_re, cos_of_real_re, mul_re] at *

lemma abs_exp_eq_iff_re_eq {x y : ℂ} : abs (exp x) = abs (exp y) ↔ x.re = y.re :=
by rw [exp_eq_exp_re_mul_sin_add_cos, exp_eq_exp_re_mul_sin_add_cos y,
    abs_mul, abs_mul, abs_cos_add_sin_mul_I, abs_cos_add_sin_mul_I,
    ← of_real_exp, ← of_real_exp, abs_of_nonneg (le_of_lt (real.exp_pos _)),
    abs_of_nonneg (le_of_lt (real.exp_pos _)), mul_one, mul_one];
  exact ⟨λ h, real.exp_injective h, congr_arg _⟩

@[simp] lemma abs_exp_of_real (x : ℝ) : abs (exp x) = real.exp x :=
by rw [← of_real_exp]; exact abs_of_nonneg (le_of_lt (real.exp_pos _))

end complex
