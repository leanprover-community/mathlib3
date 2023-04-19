import combinatorics.simple_graph.exponential_ramsey.basic
import combinatorics.simple_graph.exponential_ramsey.constructive

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
  rw [add_comm, sub_add, sub_le_sub_iff_left, ←mul_one_sub, mul_right_comm],
  refine le_mul_of_one_le_left hx₀ _,
  rw [←div_le_iff', le_sub_comm, real.exp_neg, inv_le],
  { exact exp_one_gt_d9.le.trans' (by norm_num) },
  { exact exp_pos _ },
  { norm_num1 },
  { norm_num1 },
end

lemma four_two_aux''' {m b i : ℕ} {σ : ℝ} (hb : (b : ℝ) ≤ σ * m / 2) (hσ₀ : 0 < σ)
  (hi : i ∈ finset.range b) :
  real.exp ((- 2 / (σ * m)) * i) ≤ (1 : ℝ) - i / (σ * m) :=
begin
  rw [div_mul_comm, mul_comm],
  refine exp_thing (by positivity) _,
  refine div_le_of_nonneg_of_le_mul (by positivity) (by norm_num) _,
  rw [mul_comm, mul_one_div],
  refine hb.trans' _,
  rw nat.cast_le,
  rw finset.mem_range at hi,
  exact hi.le
end

lemma four_two_aux'''' {m b : ℕ} {σ : ℝ} (hb : (b : ℝ) ≤ σ * m / 2) (hσ₀ : 0 < σ) (hσ₁ : σ < 1) :
  real.exp ((- 2 / (σ * m)) * ∑ i in finset.range b, i) ≤
    ∏ i in finset.range b, (1 - ((1 - σ) * i) / (σ * (m - i))) :=
begin
  rw [finset.mul_sum, real.exp_sum],
  refine finset.prod_le_prod _ _,
  { intros i hi,
    positivity },
  intros i hi,
  exact (four_two_aux''' hb hσ₀ hi).trans (four_two_aux'' hb hσ₀ hσ₁ hi),
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
  refine mul_le_mul_of_nonneg_left ((four_two_aux'''' hb hσ₀ hσ₁).trans' _) (by positivity),
  rw [exp_le_exp, ←nat.cast_sum, finset.sum_range_id, ←nat.choose_two_right, div_mul_eq_mul_div],
  refine div_le_div_of_le (by positivity) _,
  rw [neg_mul, neg_le_neg_iff, ←le_div_iff'],
  swap, { norm_num1 },
  refine (nat.choose_le_pow 2 b).trans _,
  simp,
end

open filter finset real

namespace simple_graph
variables {V : Type*} [decidable_eq V] [fintype V] {χ : top_edge_labelling V (fin 2)} (μ : ℝ)

lemma four_one_part_one (l k : ℕ) (C : book_config χ)
  (hC : ramsey_number ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊] ≤ C.num_big_blues μ)
  (hR : ¬ (∃ m : finset V, χ.monochromatic_of m 0 ∧ k ≤ m.card)) :
  ∃ U : finset V, χ.monochromatic_of U 1 ∧ U.card = ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊ ∧
    U ⊆ C.X ∧ ∀ x ∈ U, μ * C.X.card ≤ (blue_neighbors χ x ∩ C.X).card :=
begin
  let W := (C.X.filter (λ x, μ * C.X.card ≤ (blue_neighbors χ x ∩ C.X).card)),
  have : ramsey_number ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊] ≤ W.card := hC,
  rw [←fintype.card_coe W, ramsey_number_le_iff, is_ramsey_valid_iff_eq] at this,
  obtain ⟨U, hU⟩ := this (χ.pullback (function.embedding.subtype _)),
  rw [fin.exists_fin_two, matrix.cons_val_zero, matrix.cons_val_one, matrix.head_cons] at hU,
  replace hU := hU.resolve_left _,
  { refine ⟨U.map (function.embedding.subtype _), hU.1.map, _, _⟩,
    { rw [card_map, hU.2] },
    simp only [finset.subset_iff, finset.mem_map, mem_filter, function.embedding.coe_subtype,
      forall_exists_index, exists_prop, finset.exists_coe, subtype.coe_mk, exists_and_distrib_right,
      exists_eq_right],
    split,
    { rintro x ⟨hx₁, hx₂⟩ hx,
      exact hx₁ },
    { rintro x ⟨hx₁, hx₂⟩ hx,
      exact hx₂ } },
  rintro ⟨hU', hU''⟩,
  refine hR ⟨U.map (function.embedding.subtype _), _, _⟩,
  { exact hU'.map },
  rw [card_map, hU''],
end

lemma interedges_card_eq_sum {V : Type*} [decidable_eq V] [fintype V] {G : simple_graph V}
  [decidable_rel G.adj] {A B : finset V} :
  (G.interedges A B).card = ∑ x in A, (G.neighbor_finset x ∩ B).card :=
begin
  have : ∀ e ∈ G.interedges A B, prod.fst e ∈ A,
  { rintro ⟨e₁, e₂⟩ h,
    rw [interedges, rel.mk_mem_interedges_iff] at h,
    exact h.1 },
  rw card_eq_sum_card_fiberwise this,
  refine sum_congr rfl _,
  intros x hx,
  rw [interedges, rel.interedges, filter_filter],
  simp only [and_comm],
  rw [←filter_filter, filter_product_left (λ i, i = x), finset.filter_eq', if_pos hx,
    singleton_product, filter_map, card_map, inter_comm, ←filter_mem_eq_inter],
  congr' 1,
  refine filter_congr _,
  simp only [function.embedding.coe_fn_mk, mem_neighbor_finset, iff_self, implies_true_iff],
end

lemma col_density_eq_sum {K : Type*} [decidable_eq K] {χ : top_edge_labelling V K} {k : K}
  {A B : finset V} :
  col_density χ k A B = (∑ x in A, (col_neighbor_finset χ k x ∩ B).card) / (A.card * B.card) :=
begin
  rw [col_density, edge_density_def, interedges_card_eq_sum],
  simp only [nat.cast_sum, rat.cast_div, rat.cast_sum, rat.cast_coe_nat, rat.cast_mul],
  refl,
end

lemma red_density_eq_sum {A B : finset V} :
  red_density χ A B = (∑ x in A, (red_neighbors χ x ∩ B).card) / (A.card * B.card) :=
col_density_eq_sum

lemma blue_density_eq_sum {A B : finset V} :
  blue_density χ A B = (∑ x in A, (blue_neighbors χ x ∩ B).card) / (A.card * B.card) :=
col_density_eq_sum

-- (10)
lemma four_one_part_two {l : ℕ} {C : book_config χ} {U : finset V}
  (hl : l ≠ 0)
  (hU : U.card = ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊)
  (hU' : U ⊆ C.X) (hU'' : ∀ x ∈ U, μ * C.X.card ≤ (blue_neighbors χ x ∩ C.X).card) :
  (μ * C.X.card - U.card) / (C.X.card - U.card) ≤ blue_density χ U (C.X \ U) :=
begin
  rw [blue_density_eq_sum, card_sdiff hU', ←nat.cast_sub (card_le_of_subset hU'), ←div_div],
  refine div_le_div_of_le (nat.cast_nonneg _) _,
  rw [le_div_iff],
  have : U.card • (μ * C.X.card - U.card) ≤ ∑ x in U, (blue_neighbors χ x ∩ (C.X \ U)).card,
  { rw ←finset.sum_const,
    refine sum_le_sum _,
    intros x hx,
    rw [inter_sdiff, sub_le_iff_le_add, ←nat.cast_add],
    refine (hU'' _ hx).trans _,
    rw nat.cast_le,
    exact card_le_card_sdiff_add_card },
  refine this.trans_eq' _,
  { rw [nsmul_eq_mul, mul_comm] },
  rw hU,
  positivity
end

-- (10)
lemma four_one_part_three {k l : ℕ} {C : book_config χ} {U : finset V}
  (hμ : 0 ≤ μ) (hk₆ : 6 ≤ k) (hl : 3 ≤ l)
  (hU : U.card = ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊) (hU' : U ⊆ C.X)
  (hX : ramsey_number ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊] ≤ C.X.card) :
  μ - 2 / k ≤ (μ * C.X.card - U.card) / (C.X.card - U.card) :=
begin
  set m : ℕ := ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊,
  have hm₃ : 3 ≤ m,
  { rw [nat.add_one_le_ceil_iff, nat.cast_two, div_eq_mul_inv, rpow_mul (nat.cast_nonneg _),
      ←rpow_lt_rpow_iff, ←rpow_mul, inv_mul_cancel, rpow_one],
    { norm_cast,
      rw ←nat.succ_le_iff,
      exact (pow_le_pow_of_le_left (by norm_num1) hl 2).trans_eq' (by norm_num1) },
    { norm_num1 },
    { exact rpow_nonneg_of_nonneg (nat.cast_nonneg _) _ },
    { norm_num1 },
    { exact rpow_nonneg_of_nonneg (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _) _ },
    { norm_num1 } },
  have hm₂ : 2 ≤ m := hm₃.trans' (by norm_num1),
  have hk₀ : 0 < (k : ℝ),
  { rw nat.cast_pos,
    exact (hk₆.trans_lt' (by norm_num1)) },
  have hk₃ : 3 ≤ k := hk₆.trans' (by norm_num1),
  have := (right_lt_ramsey_number hk₃ hm₂).trans_le hX,
  have : (0 : ℝ) < C.X.card - U.card,
  { rwa [hU, sub_pos, nat.cast_lt] },
  rw [sub_div' _ _ _ hk₀.ne', div_le_div_iff hk₀ this, sub_mul, sub_mul, mul_sub, mul_sub, hU,
    sub_sub, mul_right_comm, sub_le_sub_iff_left],
  suffices : (m : ℝ) * (k / 2 * (1 - μ) + 1) ≤ C.X.card,
  { linarith },
  have : (m : ℝ) * (k / 2 * (1 - μ) + 1) ≤ (m : ℝ) * (k / 2 + 1),
  { refine mul_le_mul_of_nonneg_left (add_le_add_right _ _) (nat.cast_nonneg _),
    refine mul_le_of_le_one_right (half_pos hk₀).le _,
    rwa sub_le_self_iff },
  refine this.trans _,
  rw ramsey_number_pair_swap at hX,
  replace hX := (mul_sub_two_le_ramsey_number hm₃).trans hX,
  rw ←@nat.cast_le ℝ at hX,
  refine hX.trans' _,
  rw [nat.cast_mul, nat.cast_sub, nat.cast_two],
  swap,
  { exact hk₃.trans' (by norm_num1) },
  refine mul_le_mul_of_nonneg_left _ (nat.cast_nonneg _),
  rw [←@nat.cast_le ℝ, nat.cast_bit0, nat.cast_bit1, nat.cast_one] at hk₆,
  linarith only [hk₆],
end

variables {k l : ℕ} {C : book_config χ} {U : finset V}

lemma ceil_le_two_mul {x : ℝ} (hx : 1 / 2 ≤ x) : (⌈x⌉₊ : ℝ) ≤ 2 * x :=
begin
  cases lt_or_le x 1,
  { have : ⌈x⌉₊ = 1,
    { rw nat.ceil_eq_iff,
      { rw [nat.sub_self, nat.cast_zero, nat.cast_one],
        split;
        linarith },
      norm_num },
    rw [this, nat.cast_one],
    linarith },
  refine (nat.ceil_lt_add_one _).le.trans _;
  linarith
end

open filter

lemma four_one_part_four (hμ : 0 < μ) :
  ∀ᶠ (l : ℕ) in at_top, ∀ (k : ℕ), l ≤ k →
    ∀ (σ : ℝ), μ - 2 / k ≤ σ →
    (⌈(l : ℝ) ^ (1 / 4 : ℝ)⌉₊ : ℝ) ≤ σ * ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊ / 2 :=
begin
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_coe_nat_at_top_at_top,
  have h3 : (0 : ℝ) < 2 / 3 - 1 / 4, { norm_num1 },
  have h4 : (0 : ℝ) < 1 / 4, { norm_num1 },
  filter_upwards
    [((tendsto_rpow_at_top h4).comp t).eventually_ge_at_top (1 / 2),
    ((tendsto_rpow_at_top h3).comp t).eventually_ge_at_top (4 * 2 / μ),
    t.eventually_ge_at_top (4 / μ),
    eventually_gt_at_top 0]
    with l hl hl'' hl' hl₀ k hlk σ hσ,
  have hk : 4 / μ ≤ k,
  { refine hl'.trans _, rwa nat.cast_le },
  have : μ / 2 ≤ σ,
  { refine hσ.trans' _,
    rw [le_sub_comm, sub_half],
    refine (div_le_div_of_le_left (by norm_num1) _ hk).trans _,
    { positivity },
    rw [div_div_eq_mul_div, bit0_eq_two_mul (2 : ℝ), mul_div_mul_left],
    norm_num1 },
  rw [mul_div_assoc],
  refine (mul_le_mul_of_nonneg_right this (by positivity)).trans' _,
  rw [div_mul_div_comm, ←bit0_eq_two_mul],
  refine (ceil_le_two_mul hl).trans _,
  rw [le_div_iff', ←mul_assoc, ←div_le_iff' hμ],
  rotate,
  { norm_num1 },
  refine (nat.le_ceil _).trans' _,
  rw [mul_div_assoc, mul_div_left_comm, ←le_div_iff', ←rpow_sub],
  { exact hl'' },
  { rwa nat.cast_pos },
  refine rpow_pos_of_pos _ _,
  rwa nat.cast_pos,
end

def common_blues (χ : top_edge_labelling V (fin 2)) (S : finset V) :
  finset V := univ.filter (λ i, ∀ j ∈ S, i ∈ blue_neighbors χ j)

lemma four_one_part_five (χ : top_edge_labelling V (fin 2)) {m b : ℕ} {X U : finset V}
  (hXU : U ⊆ X) (hU : U.card = m) :
  ∑ S in powerset_len b U, ((common_blues χ S ∩ (X \ U)).card : ℝ) =
    ∑ v in X \ U, (blue_neighbors χ v ∩ U).card.choose b :=
begin
  have : ∀ S, ((common_blues χ S ∩ (X \ U)).card : ℝ) =
    ∑ v in X \ U, if v ∈ common_blues χ S then 1 else 0,
  { intro S,
    rw [sum_boole, filter_mem_eq_inter, inter_comm] },
  simp_rw this,
  rw sum_comm,
  refine sum_congr rfl _,
  intros v hv,
  rw [sum_boole, ←card_powerset_len],
  congr' 2,
  ext S,
  simp only [mem_powerset_len, mem_filter, common_blues, mem_univ, true_and, subset_inter_iff],

end

#exit

-- lemma 4.1
-- (9)
lemma four_one (hμ₀ : 0 < μ) (hμ₁ : μ < 1) : ∀ᶠ (l : ℕ) in filter.at_top, ∀ k, l ≤ k →
  ∀ C : book_config χ,
  ramsey_number ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊] ≤ C.num_big_blues μ →
  ¬ (∃ m : finset V, χ.monochromatic_of m 0 ∧ k ≤ m.card) →
  ∃ s t : finset V,
    χ.monochromatic_of s 1 ∧
    χ.monochromatic_between s t 1 ∧
    (l : ℝ) ^ (1 / 4 : ℝ) ≤ s.card ∧
    μ ^ s.card * C.X.card / 2 ≤ t.card :=
begin
  -- have := eventually_ge_at_top 6,
  filter_upwards [eventually_ge_at_top 6,
    four_one_part_four μ hμ₀] with l hl hl' --
    k hlk C hC hR,
  obtain ⟨U, Ublue, Usize, UX, Uneigh⟩ := four_one_part_one μ l k C hC hR,
  set m := ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊,
  have hC' : ramsey_number ![k, m] ≤ C.X.card := hC.trans (card_le_of_subset (filter_subset _ _)),
  let σ := blue_density χ U (C.X \ U),
  have : μ - 2 / k ≤ σ,
  { exact (four_one_part_three μ hμ₀.le (hl.trans hlk) (hl.trans' (by norm_num1)) Usize UX
      hC').trans (four_one_part_two μ (hl.trans_lt' (by norm_num1)).ne' Usize UX Uneigh) },
  simp only [←nat.ceil_le],
  specialize hl' k hlk σ this,
  set b := ⌈(l : ℝ) ^ (1 / 4 : ℝ)⌉₊,

end

end simple_graph
