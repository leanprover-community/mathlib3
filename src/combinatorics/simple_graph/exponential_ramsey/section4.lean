import combinatorics.simple_graph.exponential_ramsey.basic

lemma convex_on.mul {f g : ℝ → ℝ} {s : set ℝ} (hf : convex_on ℝ s f) (hg : convex_on ℝ s g)
  (hf' : monotone_on f s) (hg' : monotone_on g s)
  (hf'' : ∀ x ∈ s, 0 ≤ f x) (hg'' : ∀ x ∈ s, 0 ≤ g x) : convex_on ℝ s (λ x, f x * g x) :=
begin
  refine linear_order.convex_on_of_lt hf.1 _,
  intros x hx y hy hxy a b ha hb hab,
  replace hg := hg.2 hx hy ha.le hb.le hab,
  refine (mul_le_mul (hf.2 hx hy ha.le hb.le hab) hg (hg'' _ (hf.1 hx hy ha.le hb.le hab))
    (add_nonneg (smul_nonneg ha.le (hf'' _ hx)) (smul_nonneg hb.le (hf'' _ hy)))).trans _,
  have : b = 1 - a, { rwa eq_sub_iff_add_eq' },
  subst this,
  simp only [smul_eq_mul],
  suffices : 0 ≤ a * (1 - a) * (g y - g x) * (f y - f x),
  { nlinarith only [this] },
  exact mul_nonneg (mul_nonneg (by positivity) (sub_nonneg_of_le (hg' hx hy hxy.le)))
    (sub_nonneg_of_le (hf' hx hy hxy.le)),
end

lemma monotone_on.mul {s : set ℝ} {f g : ℝ → ℝ} (hf : monotone_on f s) (hg : monotone_on g s)
  (hf' : ∀ x ∈ s, 0 ≤ f x) (hg' : ∀ x ∈ s, 0 ≤ g x) :
  monotone_on (λ x, f x * g x) s :=
λ x hx y hy hxy, mul_le_mul (hf hx hy hxy) (hg hx hy hxy) (hg' _ hx) (hf' _ hy)

lemma convex_on_sub_const {s : set ℝ} {c : ℝ} (hs : convex ℝ s) : convex_on ℝ s (λ x, x - c) :=
(convex_on_id hs).sub (concave_on_const _ hs)

lemma convex.union {s t : set ℝ} (hs : convex ℝ s) (ht : convex ℝ t)
  (hst : ¬ disjoint s t) : convex ℝ (s ∪ t) :=
begin
  rw set.not_disjoint_iff at hst,
  obtain ⟨a, has, hat⟩ := hst,
  rw [convex_iff_ord_connected, set.ord_connected_iff_uIcc_subset],
  rintro x (hx | hx) y (hy | hy),
  { exact (hs.ord_connected.uIcc_subset hx hy).trans (set.subset_union_left _ _) },
  { exact set.uIcc_subset_uIcc_union_uIcc.trans (set.union_subset_union
      (hs.ord_connected.uIcc_subset hx has) (ht.ord_connected.uIcc_subset hat hy)) },
  { rw set.union_comm,
    exact set.uIcc_subset_uIcc_union_uIcc.trans (set.union_subset_union
      (ht.ord_connected.uIcc_subset hx hat) (hs.ord_connected.uIcc_subset has hy)) },
  { exact (ht.ord_connected.uIcc_subset hx hy).trans (set.subset_union_right _ _) },
end

lemma convex_on_univ_max {k : ℝ} : convex_on ℝ set.univ (max k) :=
begin
  refine linear_order.convex_on_of_lt convex_univ _,
  rintro x - y - hxy a b ha hb hab,
  simp only [smul_eq_mul],
  refine max_le _ _,
  { refine (add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha.le)
      (mul_le_mul_of_nonneg_left (le_max_left _ _) hb.le)).trans_eq' _,
    rw [←add_mul, hab, one_mul] },
  { exact add_le_add (mul_le_mul_of_nonneg_left (le_max_right _ _) ha.le)
      (mul_le_mul_of_nonneg_left (le_max_right _ _) hb.le) },
end

lemma convex_on.congr {s : set ℝ} {f g : ℝ → ℝ} (hf : convex_on ℝ s f) (h : s.eq_on f g) :
  convex_on ℝ s g :=
begin
  refine ⟨hf.1, _⟩,
  intros x hx y hy a b ha hb hab,
  rw [←h (hf.1 hx hy ha hb hab), ←h hx, ←h hy],
  exact hf.2 hx hy ha hb hab,
end

def desc_factorial {α : Type*} [has_one α] [has_mul α] [has_sub α] [has_nat_cast α] (x : α) : ℕ → α
| 0 := 1
| (k + 1) := (x - k) * desc_factorial k

lemma desc_factorial_nonneg {x : ℝ} : ∀ {k : ℕ}, (k : ℝ) - 1 ≤ x → 0 ≤ desc_factorial x k
| 0 h := zero_le_one
| (k + 1) h := mul_nonneg (by rwa [nat.cast_add_one, add_sub_cancel, ←sub_nonneg] at h)
  (desc_factorial_nonneg (h.trans' (by simp)))

lemma desc_factorial_nat (n : ℕ) : ∀ (k : ℕ), desc_factorial n k = n.desc_factorial k
| 0 := rfl
| (k + 1) := congr_arg _ (desc_factorial_nat k)

lemma desc_factorial_cast_nat (n : ℕ) : ∀ (k : ℕ), desc_factorial (n : ℝ) k = n.desc_factorial k
| 0 := by rw [desc_factorial, nat.desc_factorial_zero, nat.cast_one]
| (k + 1) :=
  begin
    rw [desc_factorial, nat.desc_factorial_succ, desc_factorial_cast_nat, nat.cast_mul],
    cases lt_or_le n k,
    { rw [nat.desc_factorial_of_lt h, nat.cast_zero, mul_zero, mul_zero] },
    { rw nat.cast_sub h },
  end

lemma desc_factorial_monotone_on : ∀ k, monotone_on (λ x : ℝ, desc_factorial x k) (set.Ici (k - 1))
| 0 :=
  begin
    simp only [desc_factorial],
    exact monotone_on_const,
  end
| (k + 1) :=
  begin
    rw [nat.cast_add_one, add_sub_cancel],
    refine monotone_on.mul _ ((desc_factorial_monotone_on k).mono _) _ _,
    { intros x hx y hy hxy,
      simpa using hxy },
    { rw set.Ici_subset_Ici,
      simp },
    { rintro x hx,
      exact sub_nonneg_of_le hx },
    rintro x (hx : _ ≤ _),
    refine desc_factorial_nonneg (hx.trans' _),
    simp
  end

lemma desc_factorial_convex : ∀ k : ℕ, convex_on ℝ (set.Ici ((k : ℝ) - 1)) (λ x, desc_factorial x k)
| 0 := convex_on_const 1 (convex_Ici _)
| (k + 1) :=
  begin
    rw [nat.cast_add_one, add_sub_cancel],
    change convex_on _ _ (λ x : ℝ, (x - k) * desc_factorial x k),
    refine convex_on.mul _ _ _ _ _ _,
    { exact convex_on_sub_const (convex_Ici _) },
    { refine (desc_factorial_convex k).subset _ (convex_Ici _),
      rw set.Ici_subset_Ici,
      simp },
    { intros x hx y hy hxy,
      simpa using hxy },
    { refine (desc_factorial_monotone_on _).mono _,
      rw set.Ici_subset_Ici,
      simp },
    { rintro x hx,
      exact sub_nonneg_of_le hx },
    rintro x (hx : _ ≤ _),
    refine desc_factorial_nonneg (hx.trans' _),
    simp
  end


lemma my_convex {k : ℝ} {f : ℝ → ℝ} (hf : convex_on ℝ (set.Ici k) f)
  (hf' : monotone_on f (set.Ici k)) (hk : ∀ x < k, f x = f k) : convex_on ℝ set.univ f :=
begin
  have : f = f ∘ max k,
  { ext x,
    rw function.comp_apply,
    cases lt_or_le x k,
    { rw [max_eq_left h.le, hk _ h] },
    { rw max_eq_right h } },
  rw this,
  have : set.range (max k) = set.Ici k,
  { ext x,
    rw [set.mem_range, set.mem_Ici],
    split,
    { rintro ⟨x, rfl⟩,
      exact le_max_left _ _ },
    intro h,
    refine ⟨x, _⟩,
    rw max_eq_right h },
  refine convex_on.comp _ _ _,
  { rwa [set.image_univ, this] },
  { exact convex_on_univ_max },
  rwa [set.image_univ, this],
end

-- is equal to desc_factorial for all naturals x, and for all x ≥ k - 1
noncomputable def my_desc_factorial (x : ℝ) (k : ℕ) : ℝ :=
if x < k - 1 then 0 else desc_factorial x k

-- lemma desc_factorial_convex : ∀ k : ℕ, convex_on ℝ (set.Ici ((k : ℝ) - 1)) (λ x, desc_factorial x k)

lemma my_desc_factorial_eq_on {k : ℕ} :
  (set.Ici ((k : ℝ) - 1)).eq_on (λ x, my_desc_factorial x k) (λ x, desc_factorial x k) :=
begin
  intros x hx,
  dsimp,
  rw [my_desc_factorial, if_neg],
  rwa not_lt
end

lemma my_desc_factorial_eq_nat_desc_factorial {n k : ℕ} :
  my_desc_factorial n k = n.desc_factorial k :=
begin
  rw [my_desc_factorial, desc_factorial_cast_nat, ite_eq_right_iff, eq_comm, nat.cast_eq_zero,
    nat.desc_factorial_eq_zero_iff_lt],
  intro h,
  rw ←@nat.cast_lt ℝ,
  linarith
end

lemma my_desc_factorial_convex_on_Ici (k : ℕ) :
  convex_on ℝ (set.Ici ((k : ℝ) - 1)) (λ x, my_desc_factorial x k) :=
(desc_factorial_convex _).congr my_desc_factorial_eq_on.symm

lemma my_desc_factorial_convex {k : ℕ} (hk : k ≠ 0):
  convex_on ℝ set.univ (λ x, my_desc_factorial x k) :=
begin
  refine my_convex ((desc_factorial_convex _).congr my_desc_factorial_eq_on.symm)
    ((desc_factorial_monotone_on _).congr my_desc_factorial_eq_on.symm) _,
  intros x hx,
  rw [my_desc_factorial, if_pos hx, my_desc_factorial, if_neg (lt_irrefl _)],
  have h : (k : ℝ) - 1 = (k - 1 : ℕ),
  { rw [nat.cast_sub, nat.cast_one],
    rwa [nat.succ_le_iff, pos_iff_ne_zero] },
  rw [h, desc_factorial_cast_nat, eq_comm, nat.cast_eq_zero, nat.desc_factorial_eq_zero_iff_lt],
  exact nat.pred_lt hk,
end

noncomputable def my_generalized_binomial (x : ℝ) (k : ℕ) : ℝ :=
(k.factorial : ℝ)⁻¹ • my_desc_factorial x k

lemma my_generalized_binomial_nat (n k : ℕ) :
  my_generalized_binomial n k = n.choose k :=
begin
  rw [my_generalized_binomial, my_desc_factorial_eq_nat_desc_factorial, smul_eq_mul,
    nat.desc_factorial_eq_factorial_mul_choose, nat.cast_mul, inv_mul_cancel_left₀],
  positivity
end

lemma my_generalized_binomial_convex {k : ℕ} (hk : k ≠ 0) :
  convex_on ℝ set.univ (λ x, my_generalized_binomial x k) :=
(my_desc_factorial_convex hk).smul (by positivity)

open_locale big_operators

lemma my_thing {α : Type*} {s : finset α} (f : α → ℕ) (b : ℕ) (hb : b ≠ 0) :
  my_generalized_binomial ((∑ i in s, f i) / s.card) b ≤ (∑ i in s, (f i).choose b) / s.card :=
begin
  simp only [div_eq_inv_mul, finset.mul_sum],
  cases eq_or_ne s.card 0 with hs hs,
  { simp only [hs, nat.cast_zero, inv_zero, zero_mul, finset.sum_const_zero],
    rw [←nat.cast_zero, my_generalized_binomial_nat, nat.cast_le, nat.choose_eq_zero_of_lt],
    rwa pos_iff_ne_zero },
  simp only [←my_generalized_binomial_nat],
  have h₁ : ∑ i in s, (s.card : ℝ)⁻¹ = 1,
  { rw [finset.sum_const, nsmul_eq_mul, mul_inv_cancel],
    positivity },
  have h₂ : ∀ i ∈ s, (f i : ℝ) ∈ (set.univ : set ℝ),
  { intros i hi, simp },
  have h₃ : ∀ i ∈ s, (0 : ℝ) ≤ (s.card)⁻¹,
  { intros i hi,
    positivity },
  exact (my_generalized_binomial_convex hb).map_sum_le h₃ h₁ h₂,
end

open real

lemma b_le_sigma_mul_m {m b : ℕ} {σ : ℝ} (hb : (b : ℝ) ≤ σ * m / 2) (hσ : 0 < σ) :
  (b : ℝ) ≤ σ * m := hb.trans (half_le_self (by positivity))

lemma cast_b_le_cast_m {m b : ℕ} {σ : ℝ} (hb : (b : ℝ) ≤ σ * m / 2)
  (hσ₀ : 0 < σ) (hσ₁ : σ < 1) : (b : ℝ) ≤ m :=
(b_le_sigma_mul_m hb hσ₀).trans (mul_le_of_le_one_left (nat.cast_nonneg _) hσ₁.le)

lemma b_le_m {m b : ℕ} {σ : ℝ} (hb : (b : ℝ) ≤ σ * m / 2)
  (hσ₀ : 0 < σ) (hσ₁ : σ < 1) : b ≤ m :=
nat.cast_le.1 (cast_b_le_cast_m hb hσ₀ hσ₁)

lemma four_two_aux_aux {m b : ℕ} {σ : ℝ} (hb : (b : ℝ) ≤ σ * m / 2) (hσ : 0 < σ) :
  (my_generalized_binomial (σ * m) b) * (m.choose b)⁻¹ =
    desc_factorial (σ * m) b / desc_factorial m b :=
begin
  rw [my_generalized_binomial, smul_eq_mul, nat.choose_eq_desc_factorial_div_factorial,
    nat.cast_div, inv_div, ←div_eq_inv_mul, div_mul_div_cancel, ←desc_factorial_cast_nat],
  { congr' 1,
    refine my_desc_factorial_eq_on _,
    rw set.mem_Ici,
    have : (b : ℝ) - 1 ≤ b, { linarith },
    refine this.trans (hb.trans _),
    apply half_le_self _,
    positivity },
  { positivity },
  { exact nat.factorial_dvd_desc_factorial _ _ },
  { positivity },
end

lemma four_two_aux {m b : ℕ} {σ : ℝ} :
  desc_factorial (σ * m) b / desc_factorial m b = ∏ i in finset.range b, (σ * m - i) / (m - i) :=
begin
  induction b with b ih,
  { rw [desc_factorial, desc_factorial, finset.prod_range_zero, div_one] },
  rw [desc_factorial, desc_factorial, finset.prod_range_succ, ←ih, div_mul_div_comm, mul_comm,
    mul_comm (_ - _)],
end

lemma four_two_aux' {m b : ℕ} {σ : ℝ} (hb : (b : ℝ) ≤ σ * m / 2) (hσ₀ : 0 < σ) (hσ₁ : σ < 1) :
  ∏ i in finset.range b, (σ * m - i) / (m - i) =
    σ ^ b * ∏ i in finset.range b, (1 - ((1 - σ) * i) / (σ * (m - i))) :=
begin
  rw [finset.pow_eq_prod_const, ←finset.prod_mul_distrib],
  refine finset.prod_congr rfl _,
  intros i hi,
  rw [mul_one_sub, mul_div_assoc', mul_div_mul_left _ _ hσ₀.ne', sub_div'],
  { ring_nf },
  rw finset.mem_range at hi,
  have hb' : 0 < b := pos_of_gt hi,
  have : (i : ℝ) < b, { rwa nat.cast_lt },
  suffices : (i : ℝ) < m, { linarith only [this] },
  refine (this.trans_le hb).trans_le ((half_le_self (by positivity)).trans _),
  exact mul_le_of_le_one_left (nat.cast_nonneg _) hσ₁.le,
end.

lemma four_two_aux'' {m b i : ℕ} {σ : ℝ} (hb : (b : ℝ) ≤ σ * m / 2) (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
  (hi : i ∈ finset.range b) :
  (1 : ℝ) - i / (σ * m) ≤ 1 - ((1 - σ) * i) / (σ * (m - i)) :=
begin
  rw finset.mem_range at hi,
  have : (i : ℝ) < m,
  { rw nat.cast_lt,
    refine hi.trans_le (b_le_m hb hσ₀ hσ₁) },
  rw [sub_le_sub_iff_left, mul_comm σ, ←div_mul_div_comm, ←div_div, div_eq_mul_one_div (i / σ : ℝ),
    mul_comm],
  refine mul_le_mul_of_nonneg_left _ (by positivity),
  rw [div_le_div_iff, one_mul, one_sub_mul, sub_le_sub_iff_left],
  { refine (hb.trans (half_le_self (by positivity))).trans' (le_of_lt _),
    rwa nat.cast_lt },
  { rwa sub_pos },
  exact this.trans_le' (nat.cast_nonneg _),
end

lemma exp_thing {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1 / 2) :
  real.exp (-2 * x) ≤ 1 - x :=
begin
  let a := 2 * x,
  have ha : 0 ≤ a := mul_nonneg (by norm_num1) hx₀,
  have ha' : 0 ≤ 1 - a,
  { simp only [a],
    linarith only [hx₁] },
  have := convex_on_exp.2 (set.mem_univ (-1)) (set.mem_univ 0) ha ha' (by simp),
  simp only [smul_eq_mul, mul_neg, ←neg_mul, mul_one, mul_zero, add_zero, real.exp_zero, a] at this,
  refine this.trans _,
  rw [add_comm, sub_add, sub_le_sub_iff_left, ←mul_one_sub],
end

-- lemma four_two_right {m b : ℕ} {σ : ℝ} (hb : (b : ℝ) ≤ σ * m / 2) (hσ₀ : 0 < σ) (hσ₁ : σ < 1) :
--   my_generalized_binomial (σ * m) b ≤ σ ^ b * m.choose b :=
-- begin
--   rw [←div_le_iff, div_eq_mul_inv, four_two_aux_aux hb hσ₀, four_two_aux, four_two_aux' hb hσ₀ hσ₁],
--   { refine mul_le_of_le_one_right (by positivity) _,
--     refine finset.prod_le_one _ _,
--   }
-- end

-- Fact 4.2
lemma four_two_left {m b : ℕ} {σ : ℝ} (hb : (b : ℝ) ≤ σ * m / 2) (hσ₀ : 0 < σ) (hσ₁ : σ < 1) :
  σ ^ b * m.choose b * exp (- b ^ 2 / (σ * m)) ≤ my_generalized_binomial (σ * m) b :=
begin
  have : 0 < (m.choose b : ℝ),
  { rw nat.cast_pos,
    exact nat.choose_pos (b_le_m hb hσ₀ hσ₁) },
  rw [mul_right_comm, ←le_div_iff this, div_eq_mul_inv (my_generalized_binomial _ _),
    four_two_aux_aux hb hσ₀, four_two_aux, four_two_aux' hb hσ₀ hσ₁],
  refine mul_le_mul_of_nonneg_left _ (by positivity),

end
