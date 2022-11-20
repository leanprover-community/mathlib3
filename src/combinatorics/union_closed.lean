import combinatorics.set_family.intersecting
import topology.unit_interval
import analysis.special_functions.log.base
import analysis.convex.jensen
import analysis.convex.specific_functions

variables {Ω α β : Type*} [decidable_eq α] [decidable_eq α] [decidable_eq β] {F : finset (finset α)}

def is_union_closed (F : finset (finset α)) := ∀ ⦃A⦄, A ∈ F → ∀ ⦃B⦄, B ∈ F → A ∪ B ∈ F

example {p q : Prop} (h : q → p) :
  p ↔ (¬ q → p) :=
(or_iff_right_of_imp h).symm.trans or_iff_not_imp_left

lemma is_union_closed_iff_pairwise :
  is_union_closed F ↔ (F : set (finset α)).pairwise (λ A B, A ∪ B ∈ F) :=
begin
  refine forall₄_congr (λ A hA B hB, ⟨λ h _, h, λ h, _⟩),
  rcases or_iff_not_imp_left.2 h with rfl | h';
  simpa,
end

open_locale big_operators
open finset
variables [fintype Ω] [fintype α] [fintype β]

@[ext]
structure findist (α : Type*) [fintype α] :=
(w : α → ℝ)
(nonneg : ∀ x, 0 ≤ w x)
(has_sum : ∑ x : α, w x = 1)

noncomputable def uniform_on (F : finset α) (hF : F.nonempty) : findist α :=
{ w := λ Y, if Y ∈ F then F.card⁻¹ else 0,
  nonneg := λ Y, by split_ifs; positivity,
  has_sum :=
  begin
    rw [finset.sum_ite_mem, finset.univ_inter, finset.sum_const, nsmul_eq_mul, mul_inv_cancel],
    simp [hF.ne_empty],
  end }

lemma uniform_on_w_ne_zero {F : finset α} (hF : F.nonempty) (x : α) :
  (uniform_on F hF).w x ≠ 0 ↔ x ∈ F :=
by simp [uniform_on, hF.ne_empty]

lemma uniform_on_w_eq_zero {F : finset α} (hF : F.nonempty) (x : α) :
  (uniform_on F hF).w x = 0 ↔ x ∉ F :=
by simp [←uniform_on_w_ne_zero hF x]

lemma the_thing {α : Type*} (Y : finset α) (X : finset α) (Z : finset α) [decidable_eq α] :
  X ⊆ Y ∧ Y \ X ⊆ Z ∧ Z ⊆ Y ↔ X ∪ Z = Y :=
begin
  split,
  { rintro ⟨h₁, h₂, h₃⟩,
    refine (union_subset h₁ h₃).antisymm _,
    rw ←union_sdiff_of_subset h₁,
    exact union_subset_union (refl _) h₂ },
  rintro rfl,
  refine ⟨subset_union_left _ _, _, subset_union_right _ _⟩,
  rw union_sdiff_left,
  apply sdiff_subset,
end

def union (A B : findist (finset α)) : findist (finset α) :=
{ w := λ Z, ∑ X, ∑ Y, A.w X * B.w Y * ite (X ∪ Y = Z) 1 0,
  nonneg := λ Z, sum_nonneg $ λ X hX, sum_nonneg $ λ Y hY,
    mul_nonneg (mul_nonneg (A.nonneg _) (B.nonneg _)) (by split_ifs; positivity),
  has_sum :=
  begin
    rw sum_comm,
    suffices : ∑ (X Y Z : finset α), A.w X * B.w Y * ite (X ∪ Y = Z) 1 0 = 1,
    { refine (sum_congr rfl (λ X hX, _)).trans this,
      exact sum_comm },
    simp only [mul_boole, sum_ite_eq, mem_univ, if_true, ←mul_sum, B.has_sum, mul_one, A.has_sum]
  end }

lemma union_eq_zero_iff {A B : findist (finset α)} (Z : finset α) :
  (union A B).w Z = 0 ↔ ∀ X Y, A.w X = 0 ∨ B.w Y = 0 ∨ X ∪ Y ≠ Z :=
begin
  simp only [union],
  rw [sum_eq_zero_iff_of_nonneg],
  simp only [mem_univ, forall_true_left],
  refine forall_congr (λ X, _),
  { rw [sum_eq_zero_iff_of_nonneg],
    { simpa only [mem_univ, forall_true_left, mul_eq_zero, ite_eq_right_iff, one_ne_zero,
        or_assoc] },
    intros i hi,
    refine mul_nonneg (mul_nonneg (A.nonneg _) (B.nonneg _)) _,
    split_ifs; norm_num1 },
  { intros i hi,
    refine sum_nonneg (λ i hi, _),
    refine mul_nonneg (mul_nonneg (A.nonneg _) (B.nonneg _)) _,
    split_ifs; norm_num1 },
end

lemma union_ne_zero_iff {A B : findist (finset α)} (Z : finset α) :
  (union A B).w Z ≠ 0 ↔ ∃ X Y, A.w X ≠ 0 ∧ B.w Y ≠ 0 ∧ X ∪ Y = Z :=
begin
  rw [ne.def, union_eq_zero_iff],
  simp only [not_forall, not_or_distrib, not_not],
end

def findist.apply (A : findist α) (f : α → β) :
  findist β :=
{ w := λ b, ∑ i in univ.filter (λ i, f i = b), A.w i,
  nonneg := λ _, sum_nonneg (λ i _, A.nonneg _),
  has_sum := by rw [sum_fiberwise, A.has_sum] }

def findist.prod (A : findist α) (B : findist β) : findist (α × β) :=
{ w := λ x, A.w x.1 * B.w x.2,
  nonneg := λ x, mul_nonneg (A.nonneg _) (B.nonneg _),
  has_sum :=
  begin
    rw [←univ_product_univ, sum_product],
    simp [←mul_sum, B.has_sum, A.has_sum],
  end }

lemma prod_apply_fst {A : findist α} {B : findist β} :
  (A.prod B).apply prod.fst = A :=
begin
  ext j,
  simp only [findist.apply, findist.prod],
  have : univ.filter (λ i : α × β, i.fst = j) = {j} ×ˢ univ,
  { ext ⟨x, y⟩,
    simp [eq_comm] },
  rw this,
  simp only [finset.sum_product, sum_singleton, ←mul_sum, B.has_sum, mul_one],
  -- simp [-singleton_product],
  -- simp only [singleton_product, sum_map, function.embedding.coe_fn_mk, ←mul_sum, B.has_sum, mul_one]
end

lemma mem_I (A : findist α) {x} : A.w x ∈ unit_interval :=
begin
  refine ⟨A.nonneg x, _⟩,
  rw ←A.has_sum,
  exact single_le_sum (λ i _, A.nonneg i) (mem_univ _),
end

noncomputable def ent (b x : ℝ) : ℝ := - x * real.logb b x
@[simp] lemma ent_zero {b : ℝ} : ent b 0 = 0 := by simp [ent]

lemma le_h {b x : ℝ} (hb : 1 < b) (hx : x ∈ unit_interval) : 0 ≤ ent b x :=
mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.2 hx.1) (real.logb_nonpos hb hx.1 hx.2)

noncomputable def entropy (A : findist α) : ℝ := ∑ i, ent 2 (A.w i)

lemma concave_on_logb_Ioi (b : ℝ) (hb : 1 ≤ b) :
  concave_on ℝ (set.Ioi 0) (real.logb b) :=
begin
  have : real.logb b = λ x, (real.log b)⁻¹ • real.log x,
  { ext x,
    rw [smul_eq_mul, ←div_eq_inv_mul, real.log_div_log] },
  rw this,
  apply concave_on.smul,
  { simp,
    exact real.log_nonneg hb },
  apply strict_concave_on_log_Ioi.concave_on,
end

lemma gibbs {b : ℝ} (hb : 1 < b) (p q : findist α) (h : ∀ i, q.w i = 0 → p.w i = 0) :
  ∑ i, ent b (p.w i) ≤ ∑ i, - p.w i * real.logb b (q.w i) :=
begin
  let s : finset α := univ.filter (λ i, p.w i ≠ 0),
  have hs' : ∀ i ∈ s, p.w i ≠ 0 := λ i hi, (mem_filter.1 hi).2,
  have hs : ∀ i ∈ s, q.w i ≠ 0 := λ i hi hq, hs' i hi (h _ hq),
  simp only [ent],
  suffices : ∑ x in s, p.w x * real.logb b (q.w x / p.w x) ≤ 0,
  { have : ∑ x in s, p.w x * (real.logb b (q.w x) - real.logb b (p.w x)) ≤ 0,
    { refine this.trans_eq' (sum_congr rfl _),
      intros x hx,
      rw real.logb_div (hs _ hx) (hs' _ hx) },
    rw finset.sum_filter_of_ne at this,
    { simpa [mul_sub] using this },
    { intros x _ h h',
      apply h,
      rw [h', zero_mul] } },
  have : ∀ i ∈ s, q.w i / p.w i ∈ set.Ioi (0 : ℝ),
  { intros i hi,
    exact div_pos ((q.nonneg _).lt_of_ne' (hs _ hi)) ((p.nonneg _).lt_of_ne' (hs' _ hi)) },
  refine ((concave_on_logb_Ioi b hb.le).le_map_sum _ _ this).trans _,
  { intros i hi,
    exact p.nonneg i },
  { rw [sum_filter_ne_zero, p.has_sum] },
  refine real.logb_nonpos hb (sum_nonneg _) _,
  { intros i hi,
    exact smul_nonneg (p.nonneg _) (div_nonneg (q.nonneg _) (p.nonneg _)) },
  refine (sum_congr rfl (λ x hx, _)).trans_le
    ((sum_le_sum_of_subset_of_nonneg (subset_univ _) (λ i hi _, _)).trans_eq q.has_sum),
  { rw [smul_eq_mul, mul_div_cancel'],
    apply hs' _ hx },
  exact q.nonneg _
end

lemma entropy_uniform_on (s : finset α) (hs : s.nonempty) :
  entropy (uniform_on s hs) = real.logb 2 s.card :=
begin
  simp only [entropy, uniform_on, apply_ite (ent 2), ent_zero, sum_ite_mem, univ_inter, sum_const,
    nsmul_eq_mul],
  rw [ent, ←mul_assoc, mul_neg, mul_inv_cancel, real.logb_inv, neg_mul, one_mul, neg_neg],
  simp [hs.ne_empty],
end

lemma entropy_le (s : finset α) (p : findist α) (hp : ∀ i, i ∉ s → p.w i = 0) (hs : s.nonempty) :
  entropy p ≤ entropy (uniform_on s hs) :=
begin
  refine (gibbs one_lt_two p (uniform_on s hs) _).trans _,
  { intros i hi,
    apply hp i _,
    simpa [uniform_on, hs.ne_empty] using hi },
  rw entropy_uniform_on,
  simp only [entropy, uniform_on, apply_ite (ent 2), ent_zero, sum_ite_mem, univ_inter, sum_const,
    nsmul_eq_mul, apply_ite (real.logb 2), mul_ite, real.logb_zero, mul_zero, ←finset.sum_mul,
    real.logb_inv, sum_neg_distrib, neg_mul_neg],
  apply mul_le_of_le_one_left,
  { apply real.logb_nonneg one_lt_two,
    simpa [nat.succ_le_iff, finset.card_pos, hs.ne_empty] },
  refine ((sum_le_sum_of_subset_of_nonneg (subset_univ _) (λ i hi _, _)).trans_eq p.has_sum),
  exact p.nonneg _
end

lemma thm1 (a b : findist (finset α)) (ha : ∀ i : α, ∑ A : finset α, ite (i ∈ A) (a.w A) 0 ≤ 0.01) :
  1.26 * entropy a ≤ entropy (union a b) :=
begin
  sorry
end

lemma thm2 [nonempty α] (hF' : F ≠ {∅}) (hF : is_union_closed F) :
  ∃ i, (0.01 : ℝ) * F.card ≤ (F.filter (λ A, i ∈ A)).card :=
begin
  rcases eq_empty_or_nonempty F with rfl | hF'',
  { simp },
  by_cases F.card = 1,
  { rw card_eq_one at h,
    obtain ⟨A, hA⟩ := h,
    have : A.nonempty,
    { apply nonempty_of_ne_empty,
      rintro rfl,
      exact hF' hA },
    obtain ⟨i, hi⟩ := this,
    use i,
    simp only [hA, card_singleton, nat.cast_one, mul_one, filter_singleton, hi, if_true],
    norm_num },
  have : 1 < F.card := lt_of_le_of_ne' hF''.card_pos h,
  let a := uniform_on F hF'',
  let b := uniform_on F hF'',
  have hab : entropy (union a b) ≤ entropy a,
  { apply entropy_le,
    intros C hC,
    simp only [union_eq_zero_iff, uniform_on_w_eq_zero],
    intros X Y,
    by_contra',
    apply hC,
    rw ←this.2.2,
    apply hF this.1 this.2.1 },
  have : 0 < entropy a,
  { rw entropy_uniform_on,
    refine real.logb_pos one_lt_two _,
    exact_mod_cast this },
  by_contra' h',
  suffices : ∀ i : α, ∑ A : finset α, ite (i ∈ A) (a.w A) 0 ≤ 0.01,
  { linarith [thm1 a b this] },
  intro i,
  simp only [a, uniform_on, ←sum_filter, sum_const],
  rw [nsmul_eq_mul, filter_mem_eq_inter, filter_inter, univ_inter, mul_inv_le_iff'],
  apply (h' i).le,
  simp [hF''.card_pos],
end
