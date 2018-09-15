import data.complex.basic algebra.archimedean data.nat.binomial algebra.field_power tactic.linarith

section
open real is_absolute_value finset

local attribute [instance, priority 0] classical.prop_decidable

lemma geo_series_eq {α : Type*} [field α] {x : α} : ∀ (n : ℕ) (hx1 : x ≠ 1),
  (range n).sum (λ m, x ^ m) = (1 - x ^ n) / (1 - x)
| 0     hx1 := by simp
| (n+1) hx1 := have 1 - x ≠ 0 := mt sub_eq_zero_iff_eq.1 hx1.symm,
by rw [sum_range_succ, ← mul_div_cancel (x ^ n) this, geo_series_eq n hx1, ← add_div, _root_.pow_succ];
    simp [mul_add, add_mul, mul_comm]

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
  simp only [abv_pow abv, geo_series_eq _ hx1'] {eta := ff},
  refine @is_cau_of_mono_bounded _ _ _ _ ((1 : α) / (1 - abv x)) 0 _ _,
  { assume n hn,
    rw abs_of_nonneg ,
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
  ⟨⟨a₂ + a₁, a₁⟩, ⟨mem_sigma.2 ⟨mem_range.2 ((nat.lt_sub_right_iff_add_lt
      (le_of_lt ha.1)).1 ha.2),
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
  eq.symm (abs_of_nonneg (sum_nonneg (λ x h, abv_nonneg abv (a x))))
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

def exp' (z : ℂ) : cau_seq ℂ complex.abs := ⟨_, is_cau_exp z⟩

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
      have h₁ : (choose m i : ℂ) ≠ 0 := nat.cast_ne_zero.2 (λ h,
        by simpa [h, lt_irrefl] using choose_pos (nat.le_of_lt_succ (mem_range.1 hi))),
      have h₂ := choose_mul_fact_mul_fact (nat.le_of_lt_succ $ finset.mem_range.1 hi),
      rw [← h₂, nat.cast_mul, nat.cast_mul, mul_inv', mul_inv'],
      simp only [mul_left_comm (choose m i : ℂ), mul_assoc, mul_left_comm (choose m i : ℂ)⁻¹,
        mul_comm (choose m i : ℂ)],
      rw inv_mul_cancel h₁,
      simp [div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm]
    end),
by rw lim_mul_lim;
  exact eq.symm (lim_eq_lim_of_equiv (by dsimp; simp only [hj];
    exact cauchy_product (is_cau_abs_exp x) (is_cau_exp y)))

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
  refine congr_arg lim _,
  dsimp [exp', function.comp],
  funext,
  rw ← sum_hom conj conj_zero conj_add,
  refine sum_congr rfl (λ n hn, _),
  rw [conj_div, conj_pow, ← of_real_nat_cast, conj_of_real]
end

@[simp] lemma exp_of_real_im (x : ℝ) : (exp x).im = 0 :=
begin
  rw [← domain.mul_left_inj (@two_ne_zero ℝ _), two_mul],
  conv in (exp x) { rw [← conj_of_real x, exp_conj] },
  simp
end

@[simp] lemma of_real_exp_of_real_re (x : ℝ) : ((exp x).re : ℂ) = exp x :=
complex.ext (by simp) (by simp)

@[simp] lemma of_real_exp (x : ℝ) : (real.exp x : ℂ) = exp x :=
complex.ext (by simp [real.exp]) (by simp [real.exp])

@[simp] lemma sin_zero : sin 0 = 0 := by simp [sin]

@[simp] lemma sin_neg : sin (-x) = -sin x :=
by simp [sin, exp_neg, (neg_div _ _).symm, add_mul]

lemma sin_add : sin (x + y) = sin x * cos y + cos x * sin y :=
begin
  rw [← domain.mul_left_inj (@two_ne_zero' ℂ _ _ _),
      ← domain.mul_left_inj (@two_ne_zero' ℂ _ _ _)],
  simp only [mul_add, add_mul, exp_add, div_mul_div, div_add_div_same,
    mul_assoc, (div_div_eq_div_mul _ _ _).symm,
    mul_div_cancel' _ (@two_ne_zero' ℂ _ _ _), sin, cos],
  simp [mul_add, add_mul, exp_add],
  ring
end

@[simp] lemma cos_zero : cos 0 = 1 := by simp [cos]

@[simp] lemma cos_neg : cos (-x) = cos x :=
by simp [cos, exp_neg]

lemma cos_add : cos (x + y) = cos x * cos y - sin x * sin y :=
begin
  rw [← domain.mul_left_inj (@two_ne_zero' ℂ _ _ _),
      ← domain.mul_left_inj (@two_ne_zero' ℂ _ _ _)],
  simp only [mul_add, add_mul, mul_sub, sub_mul, exp_add, div_mul_div,
    div_add_div_same, mul_assoc, (div_div_eq_div_mul _ _ _).symm,
    mul_div_cancel' _ (@two_ne_zero' ℂ _ _ _), sin, cos],
  apply complex.ext; simp [mul_add, add_mul, exp_add]; ring
end

lemma sin_sub : sin (x - y) = sin x * cos y - cos x * sin y :=
by simp [sin_add, sin_neg, cos_neg]

lemma cos_sub : cos (x - y) = cos x * cos y + sin x * sin y :=
by simp [cos_add, sin_neg, cos_neg]

lemma sin_conj : sin (conj x) = conj (sin x) :=
begin
  rw [sin, ← conj_neg_I, ← conj_mul, ← conj_neg, ← conj_mul,
    exp_conj, exp_conj, ← conj_sub, sin, conj_div, conj_two,
    ← domain.mul_left_inj (@two_ne_zero' ℂ _ _ _),
    mul_div_cancel' _ (@two_ne_zero' ℂ _ _ _),
    mul_div_cancel' _ (@two_ne_zero' ℂ _ _ _)],
  apply complex.ext; simp [sin, neg_add],
end

@[simp] lemma sin_of_real_im (x : ℝ) : (sin x).im = 0 :=
begin
  rw [← domain.mul_left_inj (@two_ne_zero ℝ _), two_mul],
  conv in (sin x) { rw [← conj_of_real x, sin_conj] },
  simp
end

@[simp] lemma of_real_sin_of_real_re (x : ℝ) : ((sin x).re : ℂ) = sin x :=
by apply complex.ext; simp

@[simp] lemma of_real_sin (x : ℝ) : (real.sin x : ℂ) = sin x :=
by simp [real.sin]

lemma cos_conj : cos (conj x) = conj (cos x) :=
begin
  rw [cos, ← conj_neg_I, ← conj_mul, ← conj_neg, ← conj_mul,
    exp_conj, exp_conj, cos, conj_div, conj_two,
    ← domain.mul_left_inj (@two_ne_zero' ℂ _ _ _),
    mul_div_cancel' _ (@two_ne_zero' ℂ _ _ _),
    mul_div_cancel' _ (@two_ne_zero' ℂ _ _ _)],
  apply complex.ext; simp
end

@[simp] lemma cos_of_real_im (x : ℝ) : (cos x).im = 0 :=
begin
  rw [← domain.mul_left_inj (@two_ne_zero ℝ _), two_mul],
  conv in (cos x) { rw [← conj_of_real x, cos_conj] },
  simp
end

@[simp] lemma of_real_cos_of_real_re (x : ℝ) : ((cos x).re : ℂ) = cos x :=
by apply complex.ext; simp

@[simp] lemma of_real_cos (x : ℝ) : (real.cos x : ℂ) = cos x :=
by simp [real.cos]

@[simp] lemma tan_zero : tan 0 = 0 := by simp [tan]

@[simp] lemma tan_neg : tan (-x) = -tan x := by simp [tan, neg_div]

lemma tan_conj : tan (conj x) = conj (tan x) :=
by rw [tan, sin_conj, cos_conj, ← conj_div, tan]

@[simp] lemma tan_of_real_im (x : ℝ) : (tan x).im = 0 :=
begin
  rw [← domain.mul_left_inj (@two_ne_zero ℝ _), two_mul],
  conv in (tan x) { rw [← conj_of_real x, tan_conj] },
  simp
end

@[simp] lemma of_real_tan_of_real_re (x : ℝ) : ((tan x).re : ℂ) = tan x :=
by apply complex.ext; simp

@[simp] lemma of_real_tan (x : ℝ) : (real.tan x : ℂ) = tan x :=
by simp [real.tan]

@[simp] lemma sinh_zero : sinh 0 = 0 := by simp [sinh]

@[simp] lemma sinh_neg : sinh (-x) = -sinh x :=
by simp [sinh, exp_neg, (neg_div _ _).symm, add_mul]

lemma sinh_add : sinh (x + y) = sinh x * cosh y + cosh x * sinh y :=
begin
  rw [← domain.mul_left_inj (@two_ne_zero' ℂ _ _ _),
      ← domain.mul_left_inj (@two_ne_zero' ℂ _ _ _)],
  simp only [mul_add, add_mul, exp_add, div_mul_div, div_add_div_same,
    mul_assoc, (div_div_eq_div_mul _ _ _).symm,
    mul_div_cancel' _ (@two_ne_zero' ℂ _ _ _), sinh, cosh],
  simp [mul_add, add_mul, exp_add],
  ring
end

@[simp] lemma cosh_zero : cosh 0 = 1 := by simp [cosh]

@[simp] lemma cosh_neg : cosh (-x) = cosh x :=
by simp [cosh, exp_neg]

lemma cosh_add : cosh (x + y) = cosh x * cosh y + sinh x * sinh y :=
begin
  rw [← domain.mul_left_inj (@two_ne_zero' ℂ _ _ _),
      ← domain.mul_left_inj (@two_ne_zero' ℂ _ _ _)],
  simp only [mul_add, add_mul, mul_sub, sub_mul, exp_add, div_mul_div,
    div_add_div_same, mul_assoc, (div_div_eq_div_mul _ _ _).symm,
    mul_div_cancel' _ (@two_ne_zero' ℂ _ _ _), sinh, cosh],
  apply complex.ext; simp [mul_add, add_mul, exp_add]; ring
end

lemma sinh_sub : sinh (x - y) = sinh x * cosh y - cosh x * sinh y :=
by simp [sinh_add, sinh_neg, cosh_neg]

lemma cosh_sub : cosh (x - y) = cosh x * cosh y - sinh x * sinh y :=
by simp [cosh_add, sinh_neg, cosh_neg]

lemma sinh_conj : sinh (conj x) = conj (sinh x) :=
by rw [sinh, ← conj_neg, exp_conj, exp_conj, ← conj_sub, sinh, conj_div, conj_two]

@[simp] lemma sinh_of_real_im (x : ℝ) : (sinh x).im = 0 :=
begin
  rw [← domain.mul_left_inj (@two_ne_zero ℝ _), two_mul],
  conv in (sinh x) { rw [← conj_of_real x, sinh_conj] },
  simp
end

@[simp] lemma of_real_sinh_of_real_re (x : ℝ) : ((sinh x).re : ℂ) = sinh x :=
by apply complex.ext; simp

@[simp] lemma of_real_sinh (x : ℝ) : (real.sinh x : ℂ) = sinh x :=
by simp [real.sinh]

lemma cosh_conj : cosh (conj x) = conj (cosh x) :=
by rw [cosh, ← conj_neg, exp_conj, exp_conj, ← conj_add, cosh, conj_div, conj_two]

@[simp] lemma cosh_of_real_im (x : ℝ) : (cosh x).im = 0 :=
begin
  rw [← domain.mul_left_inj (@two_ne_zero ℝ _), two_mul],
  conv in (cosh x) { rw [← conj_of_real x, cosh_conj] },
  simp
end

@[simp] lemma of_real_cosh_of_real_re (x : ℝ) : ((cosh x).re : ℂ) = cosh x :=
by apply complex.ext; simp

@[simp] lemma of_real_cosh (x : ℝ) : (real.cosh x : ℂ) = cosh x :=
by simp [real.cosh]

@[simp] lemma tanh_zero : tanh 0 = 0 := by simp [tanh]

@[simp] lemma tanh_neg : tanh (-x) = -tanh x := by simp [tanh, neg_div]

lemma tanh_conj : tanh (conj x) = conj (tanh x) :=
by rw [tanh, sinh_conj, cosh_conj, ← conj_div, tanh]

@[simp] lemma tanh_of_real_im (x : ℝ) : (tanh x).im = 0 :=
begin
  rw [← domain.mul_left_inj (@two_ne_zero ℝ _), two_mul],
  conv in (tanh x) { rw [← conj_of_real x, tanh_conj] },
  simp
end

@[simp] lemma of_real_tanh_of_real_re (x : ℝ) : ((tanh x).re : ℂ) = tanh x :=
by apply complex.ext; simp

@[simp] lemma of_real_tanh (x : ℝ) : (real.tanh x : ℂ) = tanh x :=
by simp [real.tanh]

end complex

namespace real

open complex

variables (x y : ℝ)

@[simp] lemma exp_zero : exp 0 = 1 :=
by rw [real.exp, of_real_zero]; simp

lemma exp_add : exp (x + y) = exp x * exp y :=
by simp [exp_add, real.exp]

lemma exp_ne_zero : exp x ≠ 0 :=
λ h, exp_ne_zero x $ by rw [real.exp, ← of_real_inj, of_real_zero] at h; simp * at *

lemma exp_neg : exp (-x) = (exp x)⁻¹ :=
by rw [← of_real_inj, real.exp, of_real_exp_of_real_re, of_real_neg, exp_neg,
  of_real_inv, of_real_exp]

lemma exp_sub : exp (x - y) = exp x / exp y :=
by simp [exp_add, exp_neg, div_eq_mul_inv]

@[simp] lemma sin_zero : sin 0 = 0 := by simp [sin, of_real_zero]

@[simp] lemma sin_neg : sin (-x) = -sin x :=
by simp [sin, exp_neg, (neg_div _ _).symm, add_mul]

lemma sin_add : sin (x + y) = sin x * cos y + cos x * sin y :=
by rw [← of_real_inj]; simp [sin, sin_add]

@[simp] lemma cos_zero : cos 0 = 1 := by simp [cos, of_real_zero]

@[simp] lemma cos_neg : cos (-x) = cos x :=
by simp [cos, exp_neg]

lemma cos_add : cos (x + y) = cos x * cos y - sin x * sin y :=
by rw ← of_real_inj; simp [cos, cos_add]

lemma sin_sub : sin (x - y) = sin x * cos y - cos x * sin y :=
by simp [sin_add, sin_neg, cos_neg]

lemma cos_sub : cos (x - y) = cos x * cos y + sin x * sin y :=
by simp [cos_add, sin_neg, cos_neg]

@[simp] lemma tan_zero : tan 0 = 0 := by simp [tan, of_real_zero]

@[simp] lemma tan_neg : tan (-x) = -tan x := by simp [tan, neg_div]

@[simp] lemma sinh_zero : sinh 0 = 0 := by simp [sinh, of_real_zero]

@[simp] lemma sinh_neg : sinh (-x) = -sinh x :=
by simp [sinh, exp_neg, (neg_div _ _).symm, add_mul]

lemma sinh_add : sinh (x + y) = sinh x * cosh y + cosh x * sinh y :=
by rw ← of_real_inj; simp [sinh, sinh_add]

@[simp] lemma cosh_zero : cosh 0 = 1 := by simp [cosh, of_real_zero]

@[simp] lemma cosh_neg : cosh (-x) = cosh x :=
by simp [cosh, exp_neg]

lemma cosh_add : cosh (x + y) = cosh x * cosh y + sinh x * sinh y :=
by rw ← of_real_inj; simp [cosh, cosh_add]

lemma sinh_sub : sinh (x - y) = sinh x * cosh y - cosh x * sinh y :=
by simp [sinh_add, sinh_neg, cosh_neg]

lemma cosh_sub : cosh (x - y) = cosh x * cosh y - sinh x * sinh y :=
by simp [cosh_add, sinh_neg, cosh_neg]

@[simp] lemma tanh_zero : tanh 0 = 0 := by simp [tanh, of_real_zero]

@[simp] lemma tanh_neg : tanh (-x) = -tanh x := by simp [tanh, neg_div]

end real
