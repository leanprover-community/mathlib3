import data.complex.basic algebra.archimedean data.nat.binomial algebra.field_power
#exit
section
open real nat is_absolute_value finset
noncomputable theory
local attribute [instance, priority 0] classical.prop_decidable

lemma pow_lt_pow_of_gt_one {α : Type*} [linear_ordered_semiring α] {x : α} {n m : ℕ}
  (h1x : 1 < x) (hnm : n < m) : x ^ n < x ^ m :=
begin
  rw [← nat.sub_add_cancel hnm, _root_.pow_add, _root_.pow_succ, ← mul_assoc],
  refine (lt_mul_iff_one_lt_left (pow_pos (lt_trans zero_lt_one h1x) _)).2 _,
  rw ← one_mul (1 : α),
  exact mul_lt_mul' (one_le_pow_of_one_le (le_of_lt h1x) _) h1x zero_le_one
    (pow_pos (lt_trans zero_lt_one h1x) _)
end

lemma pow_lt_pow_of_lt_one_of_pos {α : Type*} [discrete_linear_ordered_field α] {x : α} {n m : ℕ}
  (hx1 : x < 1) (h0x : 0 < x) (hnm : n < m) : x ^ m < x ^ n :=
(inv_lt_inv (pow_pos h0x _) (pow_pos h0x _)).1
  (by rw [pow_inv _ _ (ne.symm (ne_of_lt h0x)), pow_inv _ _ (ne.symm (ne_of_lt h0x))];
    exact pow_lt_pow_of_gt_one (one_lt_inv h0x hx1) hnm)

open finset

lemma geo_series_eq {α : Type*} [field α] {x : α} : ∀ (n : ℕ) (hx1 : x ≠ 1),
  (range n).sum (λ m, x ^ m) = (1 - x ^ n) / (1 - x)
| 0     hx1 := by simp
| (n+1) hx1 := have 1 - x ≠ 0 := mt sub_eq_zero_iff_eq.1 hx1.symm,
by rw [sum_range_succ, ← mul_div_cancel (x ^ n) this, geo_series_eq n hx1, ← add_div, _root_.pow_succ];
    simp [mul_add, add_mul, mul_comm]

lemma forall_ge_le_of_forall_le_succ {α : Type*} [preorder α] (f : ℕ → α) {m : ℕ}
  (h : ∀ n ≥ m, f (succ n) ≤ f n) : ∀ {l}, ∀ k ≥ m, k ≤ l → f l ≤ f k :=
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
  (hnm : ∀ n ≥ m, f (succ n) ≤ f n) : is_cau_seq abs f :=
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
    (nat.find_min h (pred_lt hl0)) with i hi,
  rw [not_imp, not_lt] at hi,
  existsi i,
  assume j hj,
  have hfij : f j ≤ f i := forall_ge_le_of_forall_le_succ f hnm _ hi.1 hj,
  rw [abs_of_nonpos (sub_nonpos.2 hfij), neg_sub, sub_lt_iff_lt_add'],
  exact calc f i ≤ a - add_monoid.smul (pred l) ε : hi.2
    ... = a - add_monoid.smul l ε + ε :
      by conv {to_rhs, rw [← succ_pred_eq_of_pos (nat.pos_of_ne_zero hl0), succ_smul',
        sub_add, add_sub_cancel] }
    ... < f j + ε : add_lt_add_right (hl j (le_trans hi.1 hj)) _
end

lemma is_cau_of_mono_bounded (f : ℕ → α) {a : α} {m : ℕ} (ham : ∀ n ≥ m, abs (f n) ≤ a)
  (hnm : ∀ n ≥ m, f n ≤ f (succ n)) : is_cau_seq abs f :=
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
    rw [succ_add, sum_range_succ, sum_range_succ, add_assoc, add_assoc],
    refine le_trans (abv_add _ _ _) _,
    exact add_le_add (hm _ (le_add_of_nonneg_of_le (nat.zero_le _) (le_max_left _ _))) hi },
end

lemma pow_abv {α β : Type*} [discrete_linear_ordered_field α] [domain β] (abv : β → α) [is_absolute_value abv]
  (a : β) (n : ℕ) : abv (a ^ n) = abv a ^ n :=
by induction n; simp [abv_mul abv, _root_.pow_succ, abv_one abv, *]

lemma series_cau_of_abv_cau {f : ℕ → β} : is_cau_seq abs (λ m, (range m).sum (λ n, abv (f n))) →
  is_cau_seq abv (λ m, (range m).sum f) :=
is_cau_series_of_abv_le_cau 0 (λ n h, le_refl _)

lemma geo_series_cau {β : Type*} [field β] {abv : β → α} [is_absolute_value abv]
   (x : β) (hx1 : abv x < 1) : is_cau_seq abv (λ n, (range n).sum (λ m, x ^ m)) :=
have hx1' : abv x ≠ 1 := λ h, by simpa [h, lt_irrefl] using hx1,
series_cau_of_abv_cau
begin
  simp only [pow_abv abv, geo_series_eq _ hx1'] {eta := ff},
  refine @is_cau_of_mono_bounded _ _ _ _ ((1 : α) / (1 - abv x)) 0 _ _,
  { assume n hn,
    rw abs_of_nonneg ,
    refine div_le_div_of_le_of_pos (sub_le_self _ (pow_abv abv x n ▸ abv_nonneg _ _))
      (sub_pos.2 hx1),
    refine div_nonneg (sub_nonneg.2 _) (sub_pos.2 hx1),
    clear hn,
    induction n with n ih,
    { simp },
    { rw [_root_.pow_succ, ← one_mul (1 : α)],
      refine mul_le_mul (le_of_lt hx1) ih (pow_abv abv x n ▸ abv_nonneg _ _) (by norm_num) } },
  { assume n hn,
    refine div_le_div_of_le_of_pos (sub_le_sub_left _ _) (sub_pos.2 hx1),
    rw [← one_mul (_ ^ n), _root_.pow_succ],
    exact mul_le_mul_of_nonneg_right (le_of_lt hx1) (pow_nonneg (abv_nonneg _ _) _) }
end

lemma geo_series_const_cau (a : α) {x : α} (hx1 : abs x < 1) : is_cau_seq abs (λ m, (range m).sum (λ n, a * x ^ n)) :=
have is_cau_seq abs (λ m, a * (range m).sum (λ n, x ^ n)) := (cau_seq.const abs a * ⟨_, geo_series_cau x hx1⟩).2,
  by simpa only [mul_sum]

-- The form of ratio test with  0 ≤ r < 1, and abv (f (succ m)) ≤ r * abv (f m) handled zero terms of series the best
lemma series_ratio_test {f : ℕ → β} (n : ℕ) {r : α} (hr0 : 0 ≤ r) (hr1 : r < 1) (h : ∀ m, n ≤ m → abv (f (succ m)) ≤ r * abv (f m)) :
  is_cau_seq abv (λ m, (range m).sum f) :=
have har1 : abs r < 1, by rwa abs_of_nonneg hr0,
begin
  refine is_cau_series_of_abv_le_cau (succ n) (λ m hmn, _) (geo_series_const_cau (abv (f (succ n)) * r⁻¹ ^ (succ n)) har1),


  have := forall_ge_le_of_forall_le_succ,
end

lemma sum_range_diag_flip {α : Type*} [add_comm_monoid α] (n : ℕ) (f : ℕ → ℕ → α) :
  (range n).sum (λ m, (range (m + 1)).sum (λ k, f k (m - k))) =
  (range n).sum (λ m, (range (n - m)).sum (f m)) :=
have h₁ : ((range n).sigma (range ∘ succ)).sum
    (λ (a : Σ m, ℕ), f (a.2) (a.1 - a.2)) =
    (range n).sum (λ m, (range (m + 1)).sum
    (λ k, f k (m - k))) := sum_sigma,
have h₂ : ((range n).sigma (λ m, range (n - m))).sum (λ a : Σ (m : ℕ), ℕ, f (a.1) (a.2)) =
    (range n).sum (λ m, sum (range (n - m)) (f m)) := sum_sigma,
h₁ ▸ h₂ ▸ sum_bij
(λ a _, ⟨a.2, a.1 - a.2⟩)
(λ a ha, have h₁ : a.1 < n := mem_range.1 (mem_sigma.1 ha).1,
  have h₂ : a.2 < succ a.1 := mem_range.1 (mem_sigma.1 ha).2,
    mem_sigma.2 ⟨mem_range.2 (lt_of_lt_of_le h₂ h₁),
    mem_range.2 ((nat.sub_lt_sub_right_iff (le_of_lt_succ h₂)).2 h₁)⟩)
(λ _ _, rfl)
(λ ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ha hb h,
  have ha : a₁ < n ∧ a₂ ≤ a₁ :=
      ⟨mem_range.1 (mem_sigma.1 ha).1, le_of_lt_succ (mem_range.1 (mem_sigma.1 ha).2)⟩,
  have hb : b₁ < n ∧ b₂ ≤ b₁ :=
      ⟨mem_range.1 (mem_sigma.1 hb).1, le_of_lt_succ (mem_range.1 (mem_sigma.1 hb).2)⟩,
  have h : a₂ = b₂ ∧ _ := sigma.mk.inj h,
  have h' : a₁ = b₁ - b₂ + a₂ := (nat.sub_eq_iff_eq_add ha.2).1 (eq_of_heq h.2),
  sigma.mk.inj_iff.2
    ⟨nat.sub_add_cancel hb.2 ▸ h'.symm ▸ h.1 ▸ rfl,
      (heq_of_eq h.1)⟩)
(λ ⟨a₁, a₂⟩ ha,
  have ha : a₁ < n ∧ a₂ < n - a₁ :=
      ⟨mem_range.1 (mem_sigma.1 ha).1, (mem_range.1 (mem_sigma.1 ha).2)⟩,
  ⟨⟨a₂ + a₁, a₁⟩, ⟨mem_sigma.2 ⟨mem_range.2 ((nat.lt_sub_right_iff_add_lt
      (le_of_lt ha.1)).1 ha.2),
    mem_range.2 (lt_succ_of_le (le_add_left _ _))⟩,
  sigma.mk.inj_iff.2 ⟨rfl, heq_of_eq (nat.add_sub_cancel _ _).symm⟩⟩⟩)

lemma abv_sum_le_sum_abv {α β γ : Type*} [discrete_linear_ordered_field α] [ring β]
  (abv : β → α) [is_absolute_value abv] (f : γ → β) (s : finset γ) : abv (s.sum f) ≤ s.sum (abv ∘ f) :=
finset.induction_on s (by simp [abv_zero abv]) $ λ a s has ih,
by rw [sum_insert has, sum_insert has];
  exact le_trans (abv_add abv _ _) (add_le_add_left ih _)

lemma sum_nonneg {α β : Type*} [ordered_comm_monoid α] {f : β → α} {s : finset β} :
  (∀ x ∈ s, 0 ≤ f x) → 0 ≤ s.sum f :=
finset.induction_on s (by simp) $ λ a s has ih h, begin
  rw [sum_insert has],
  exact add_nonneg' (h a (by simp)) (ih (λx hx, by simp *)),
end

lemma neg_sum {α β : Type*} [add_comm_group α] {f : β → α} {s : finset β} :
  -s.sum f = s.sum (λ x, -f x) :=
finset.induction_on s (by simp) (by simp {contextual := tt})

@[simp] lemma filter_true {α : Type*} (s : finset α) : s.filter (λ _, true) = s :=
finset.ext.2 $ by simp

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

lemma series_cauchy_prod {α β : Type*} [discrete_linear_ordered_field α] [ring β] {a b : ℕ → β}
  {abv : β → α} [is_absolute_value abv] : is_cau_seq abs (λ m, (range m).sum (λ n, abv (a n))) → is_cau_seq abv (λ m, (range m).sum b) →
  ∀ ε : α, 0 < ε → ∃ i : ℕ, ∀ j ≥ i, abv ((range j).sum a * (range j).sum b - (range j).sum (λ n,
  (range (n + 1)).sum (λ m, a m * b (n - m))) ) < ε :=
begin
-- slightly adapted version of theorem 9.4.7 from "The Real Numbers and Real Analysis", Ethan D. Bloch
  assume ha hb ε ε0,
  cases cau_seq.bounded ⟨_, hb⟩ with Q hQ,simp at hQ,
  cases cau_seq.bounded ⟨_, ha⟩ with P hP,simp at hP,
  have P0 : 0 < P,exact lt_of_le_of_lt (abs_nonneg _) (hP 0),
  have Pε0 := div_pos ε0 (mul_pos (show (2 : α) > 0, from by norm_num) P0),
  cases cau_seq.cauchy₂ ⟨_, hb⟩ Pε0 with N hN,simp at hN,
  have Qε0 := div_pos ε0 (mul_pos (show (4 : α) > 0, from by norm_num) (lt_of_le_of_lt (abv_nonneg _ _) (hQ 0))),
  cases cau_seq.cauchy₂ ⟨_, ha⟩ Qε0 with M hM,simp at hM,
  existsi 2 * (max N M + 1),
  assume K hK,
  have := sum_range_diag_flip K (λ m n, a m * b n),
  dsimp at this,
  rw this,
  have : (λ (i : ℕ), (range (K - i)).sum (λ (k : ℕ), a i * b k)) = (λ (i : ℕ), a i * (range (K - i)).sum b),
    by simp [finset.mul_sum],
  rw this,clear this,
  have : (range K).sum (λ (i : ℕ), a i * (range (K - i)).sum b) =
    (range K).sum (λ (i : ℕ), a i * ((range (K - i)).sum b - (range K).sum b))
    + (range K).sum (λ i, a i * (range K).sum b),
    {rw ←sum_add_distrib,simp[(mul_add _ _ _).symm]},
  rw this, clear this,
  rw sum_mul, simp,
  rw abv_neg abv,
  refine lt_of_le_of_lt (abv_sum_le_sum_abv _ _ _) _,
  simp [abv_mul abv],
  suffices : (range (max N M + 1)).sum (λ (i : ℕ), abv (a i) * abv ((range (K - i)).sum b - (range K).sum b)) +
    ((range K).sum (λ (i : ℕ), abv (a i) * abv ((range (K - i)).sum b - (range K).sum b)) -(range (max N M + 1)).sum
     (λ (i : ℕ),
    abv (a i) * abv ((range (K - i)).sum b - (range K).sum b))) < ε / (2 * P) * P + ε / (4 * Q) * (2 * Q),
  { simp [(div_div_eq_div_mul _ _ _).symm] at this,
    rwa[div_mul_cancel _ (ne_of_lt P0).symm,(by norm_num : (4 : α) = 2 * 2),←div_div_eq_div_mul,mul_comm (2 : α),←_root_.mul_assoc,
    div_mul_cancel _ (ne_of_lt (lt_of_le_of_lt (abv_nonneg _ _) (hQ 0))).symm,div_mul_cancel,add_halves] at this,
    norm_num},
  refine add_lt_add _ _,
  {have : (range (max N M + 1)).sum (λ (i : ℕ), abv (a i) *
    abv ((range (K - i)).sum b - (range K).sum b)) ≤ (range (max N M + 1)).sum
  (λ (i : ℕ), abv (a i) * (ε / (2 * P))) := by
    {refine sum_le_sum _,assume m mJ,refine mul_le_mul_of_nonneg_left _ _,
      {refine le_of_lt (hN (K - m) K _ _),{
      refine nat.le_sub_left_of_add_le (le_trans _ hK),
      rw[succ_mul,_root_.one_mul],
      exact add_le_add (le_of_lt (mem_range.1 mJ)) (le_trans (le_max_left _ _) (le_of_lt (lt_add_one _)))},
      {refine le_trans _ hK,rw ←_root_.one_mul N,
      refine mul_le_mul (by norm_num) (by rw _root_.one_mul;exact le_trans (le_max_left _ _)
      (le_of_lt (lt_add_one _))) (zero_le _) (zero_le _)}},
      exact abv_nonneg abv _},
  refine lt_of_le_of_lt this _,
  rw [← sum_mul, mul_comm],
  specialize hP (max N M + 1),rwa abs_of_nonneg at hP,
  exact (mul_lt_mul_left Pε0).mpr hP,
  exact sum_nonneg (λ x h, abv_nonneg abv _)},
  {have hNMK : max N M + 1 < K := by
    {refine lt_of_lt_of_le _ hK,
    rw [succ_mul,_root_.one_mul,←add_zero (max N M + 1)],
    refine add_lt_add_of_le_of_lt (le_refl _) _,rw add_zero,
    refine add_pos_of_nonneg_of_pos (zero_le _) (by norm_num)},
  rw sum_range_sub_sum_range (le_of_lt hNMK),
  exact calc sum (filter (λ (k : ℕ), max N M + 1 ≤ k) (range K))
      (λ (i : ℕ), abv (a i) * abv (sum (range (K - i)) b - sum (range K) b))
      ≤ sum (filter (λ (k : ℕ), max N M + 1 ≤ k) (range K)) (λ i, abv (a i) * (2 * Q)) :
    sum_le_sum (begin
      assume n hn,
      refine mul_le_mul_of_nonneg_left _ (abv_nonneg _ _),
      rw sub_eq_add_neg,
      refine le_trans (abv_add _ _ _) _,
      rw [two_mul, abv_neg abv],
      refine add_le_add (le_of_lt (hQ _)) (le_of_lt (hQ _)),
    end)
    ... < _ : begin
      rw [← sum_mul, ← sum_range_sub_sum_range (le_of_lt hNMK)],
      refine (mul_lt_mul_right _).2 _,
      rw two_mul,
      refine add_pos (lt_of_le_of_lt (abv_nonneg _ _) (hQ 0))
        (lt_of_le_of_lt (abv_nonneg _ _) (hQ 0)),
      refine lt_of_le_of_lt (le_abs_self _) _,
      refine hM _ _ (le_trans (le_succ_of_le (le_max_right _ _)) (le_of_lt hNMK))
        (le_succ_of_le (le_max_right _ _))
     end }
end

end

open nat finset

lemma complex.exp_series_abs_cau (z : ℂ) : is_cau_seq abs (λ n, (range n).sum (λ m, complex.abs (z ^ m / fact m))) := begin
  cases exists_nat_gt (complex.abs z) with n hn,
  have n_pos : (0 : ℝ) < n := lt_of_le_of_lt (complex.abs_nonneg _) hn,
  refine series_ratio_test n (complex.abs z / n) _ _ _,exact div_nonneg_of_nonneg_of_pos (complex.abs_nonneg _) n_pos,rwa [div_lt_iff n_pos,one_mul],
  assume m mn,rw [abs_of_nonneg (complex.abs_nonneg _),abs_of_nonneg (complex.abs_nonneg _)],
  unfold fact,simp only [_root_.pow_succ, complex.abs_div,complex.abs_mul,div_eq_mul_inv,mul_inv',
    nat.cast_mul,complex.abs_inv],
  have : complex.abs z * complex.abs (z ^ m) * ((complex.abs ↑(fact m))⁻¹ * (complex.abs ↑(succ m))⁻¹) = complex.abs z *
    complex.abs (z ^ m) * (complex.abs ↑(fact m))⁻¹ * (complex.abs ↑(succ m))⁻¹,ring,rw this,
  have : complex.abs z * (↑n)⁻¹ * (complex.abs (z ^ m) * (complex.abs ↑(fact m))⁻¹) = complex.abs z * complex.abs (z ^ m) * (complex.abs ↑(fact m))⁻¹ * (↑n)⁻¹,ring,
  rw this,
  rw[(by simp : (succ m : ℂ) = ((succ m : ℝ) : ℂ)),complex.abs_of_nonneg],
  refine mul_le_mul_of_nonneg_left _ _,
  rw [inv_le_inv,nat.cast_le],exact le_succ_of_le mn,
  rw [←nat.cast_zero,nat.cast_lt],exact succ_pos _,exact n_pos,rw[←complex.abs_inv,←complex.abs_mul,←complex.abs_mul],
  exact complex.abs_nonneg _,rw[←nat.cast_zero,nat.cast_le],exact zero_le _,
end

lemma complex.exp_series_cau (z : ℂ) : is_cau_seq complex.abs (λ n, (range n).sum (λ m, z ^ m / fact m)) :=
  series_cau_of_abv_cau (complex.exp_series_abs_cau z)

def exp' (z : ℂ) : cau_seq ℂ complex.abs := ⟨_, complex.exp_series_cau z⟩

open complex

def exp (z : ℂ) : ℂ := complex.lim (exp' z)

def sin (z : ℂ) : ℂ := (exp (I * z) - exp (-I * z)) / (2 * I)

def cos (z : ℂ) : ℂ := (exp (I * z) + exp (-I * z)) / 2

def tan (z : ℂ) : ℂ := sin z / cos z

def sinh (z : ℂ) : ℂ := (exp z - exp (-z)) / 2

def cosh (z : ℂ) : ℂ := (exp z + exp (-z)) / 2

def tanh (z : ℂ) : ℂ := sinh z / cosh z

@[simp] lemma exp_zero : exp 0 = 1 := begin
  unfold exp exp',
  refine lim_eq_of_equiv_const _,
  assume ε ε0,
  existsi 1,
  assume j hj,
  dsimp [exp'],
  suffices : complex.abs (sum (range j) (λ (m : ℕ), 0 ^ m / ↑(fact m)) + -1) = 0,
    rwa this,
  cases j,
  { exact absurd hj (by norm_num) },
  { induction j,
    { simpa },
    { rw ← j_ih dec_trivial,
      simp only [sum_range_succ, _root_.pow_succ],
      simp } }
end

lemma exp_add (x y : ℂ) : exp (x + y) = exp x * exp y :=
show complex.lim (⟨_, complex.exp_series_cau (x + y)⟩ : cau_seq ℂ abs) =
  complex.lim (show cau_seq ℂ abs, from ⟨_, complex.exp_series_cau x⟩)
  * complex.lim (show cau_seq ℂ abs, from ⟨_, complex.exp_series_cau y⟩),
begin
 have hxa := complex.exp_series_abs_cau x,
 have hx := complex.exp_series_cau x,
 have hy := complex.exp_series_cau y,
 have hxy := complex.exp_series_cau (x + y),
   rw complex.lim_mul_lim,
 have hj : ∀ j : ℕ, (range j).sum (λ (m : ℕ),
    (x + y) ^ m / ↑(fact m)) = (range j).sum
    (λ i, (range (i + 1)).sum (λ k, x ^ k / fact k *
    (y ^ (i - k) / fact (i - k)))),
    { assume j,
      refine finset.sum_congr rfl (λ m hm, _),
      rw [add_pow, div_eq_mul_inv, sum_mul],
      refine finset.sum_congr rfl (λ i hi, _),
      have := choose_mul_fact_mul_fact (le_of_lt_succ $ finset.mem_range.1 hi),
      rw [← this, nat.cast_mul, nat.cast_mul, mul_inv', mul_inv'],
      simp only [mul_left_comm (choose m i : ℂ), mul_assoc, mul_left_comm (choose m i : ℂ)⁻¹,
        mul_comm (choose m i : ℂ)],
      have : (choose m i : ℂ) ≠ 0 := nat.cast_ne_zero.2 (λ h,
        by have := choose_pos (le_of_lt_succ (mem_range.1 hi)); simpa [h, lt_irrefl] using this),
      rw inv_mul_cancel this,
      simp [div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm] },
  have hf := funext hj, have hxy1 := hxy, rw hf at hxy1,
  have := series_cauchy_prod hxa hy,
  refine eq.symm (lim_eq_lim_of_equiv _),
  assume ε ε0,
  dsimp,
  simp only [hj],
  exact this ε ε0,
end
