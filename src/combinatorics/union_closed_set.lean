import combinatorics.set_family.intersecting
import topology.unit_interval
import analysis.special_functions.log.base
import analysis.convex.jensen
import analysis.convex.specific_functions

open_locale big_operators
open finset

variables {Ω α β : Type*} [fintype Ω]
variables {γ : Type*} [add_comm_monoid γ] [module ℝ γ]

noncomputable theory

class finite_measure_space (Ω : Type*) [fintype Ω] :=
(w : Ω → ℝ)
(nonneg : ∀ x, 0 ≤ w x)
(has_sum : ∑ x : Ω, w x = 1)

variables [finite_measure_space Ω]

local notation `w` := finite_measure_space.w

lemma nonneg {i : Ω} : 0 ≤ w i := finite_measure_space.nonneg _
lemma whole_space : ∑ i : Ω, w i = 1 := finite_measure_space.has_sum

@[positivity]
meta def positivity_nonneg : expr → tactic tactic.positivity.strictness
| `(w %%a) := nonnegative <$> tactic.mk_app ``nonneg [a]
| e := tactic.failed

def expect (X : Ω → γ) : γ :=
∑ i, w i • X i

local notation `𝔼` binders `, ` r:(scoped:67 f, expect f) := r

lemma expect_add {X Y : Ω → γ} : 𝔼 i, (X i + Y i) = 𝔼 i, X i + 𝔼 i, Y i :=
by simp only [expect, smul_add, sum_add_distrib]

lemma expect_neg {γ : Type*} [add_comm_group γ] [module ℝ γ] {X : Ω → γ} :
  𝔼 i, (- X i) = - 𝔼 i, X i :=
by simp only [expect, smul_neg, sum_neg_distrib]

lemma expect_nonneg {X : Ω → ℝ} (hω : ∀ ω, 0 ≤ X ω) : 0 ≤ 𝔼 ω, X ω :=
sum_nonneg $ λ i hi, smul_nonneg nonneg (hω _)

def prob (X : Ω → α) (A : set α) : ℝ :=
by classical; exact ∑ ω in univ.filter (λ ω, X ω ∈ A), w ω

local notation `ℙ[` X ` in ` A `]` := prob X A

lemma prob_eq_exp (X : Ω → α) (A : set α) : ℙ[X in A] = 𝔼 i, ite (X i ∈ A) 1 0 :=
begin
  rw [prob, expect],
  simp only [smul_eq_mul, mul_boole],
  rw ←sum_filter,
end

lemma prob_nonneg (X : Ω → α) (A : set α) : 0 ≤ ℙ[X in A] :=
sum_nonneg (λ i hi, by positivity)

lemma prob_le_one (X : Ω → α) (A : set α) : ℙ[X in A] ≤ 1 :=
begin
  refine (sum_le_sum_of_subset_of_nonneg (subset_univ _) (λ _ _ _, _)).trans_eq whole_space,
  apply nonneg
end

lemma prob_le_prob {X : Ω → α} {Y : Ω → β} {A : set α} {B : set β}
  (h : ∀ ω : Ω, w ω ≠ 0 → X ω ∈ A → Y ω ∈ B) :
  ℙ[X in A] ≤ ℙ[Y in B] :=
begin
  change ∑ ω in univ.filter _, _ ≤ ∑ ω in univ.filter _, _,
  rw ←sum_filter_ne_zero,
  refine sum_le_sum_of_subset_of_nonneg _ (λ _ _ _, nonneg),
  simp only [finset.subset_iff, ne.def, mem_filter, mem_univ, true_and, and_imp],
  intros ω h₁ h₂,
  exact h ω h₂ h₁
end

lemma prob_le_prob_of_subset {X : Ω → α} {A A' : set α} (h : A ⊆ A') : ℙ[X in A] ≤ ℙ[X in A'] :=
prob_le_prob (λ ω hω hx, h hx)

def p (X : Ω → α) (a : α) : ℝ := ℙ[X in {a}]

lemma p_nonneg (X : Ω → α) (a : α) : 0 ≤ p X a := prob_nonneg _ _

@[positivity]
meta def positivity_prob : expr → tactic tactic.positivity.strictness
| `(prob %%X %%A) := nonnegative <$> tactic.mk_app ``prob_nonneg [X, A]
| `(p %%X %%a) := nonnegative <$> tactic.mk_app ``p_nonneg [X, a]
| e := tactic.failed

lemma p_embedding {X : Ω → α} {f : α → β} (hf : function.injective f) (a : α) :
  p (λ ω, f (X ω)) (f a) = p X a :=
by simp [p, prob, hf.eq_iff]


def ent (b x : ℝ) : ℝ := - x * real.logb b x
@[simp] lemma ent_zero {b : ℝ} : ent b 0 = 0 := by simp [ent]
@[simp] lemma ent_one {b : ℝ} : ent b 1 = 0 := by simp [ent]

lemma le_h {b x : ℝ} (hb : 1 < b) (hx : x ∈ unit_interval) : 0 ≤ ent b x :=
mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.2 hx.1) (real.logb_nonpos hb hx.1 hx.2)

def entropy (X : Ω → α) : ℝ := 𝔼 ω, - real.logb 2 (p X (X ω))

local notation `ℍ`:67 binders `, ` r:(scoped:67 f, entropy f) := r

lemma entropy_nonneg (X : Ω → α) : 0 ≤ ℍ ω, X ω :=
expect_nonneg $ λ ω, neg_nonneg.2 $ real.logb_nonpos one_lt_two (prob_nonneg _ _) (prob_le_one _ _)

lemma entropy_eq {X : Ω → α} : entropy X = ∑ i in univ.image X, ent 2 (p X i) :=
begin
  simp only [entropy, expect, ent, smul_eq_mul, p, prob, neg_mul, mul_neg, sum_neg_distrib,
    sum_mul, neg_inj, set.mem_singleton_iff],
  apply (sum_image' _ _).symm,
  intros c hc,
  refine sum_congr rfl (λ x hx, _),
  simp only [mem_filter, mem_univ, true_and] at hx,
  simp only [hx],
end

lemma entropy_eq' [fintype α] {X : Ω → α} : entropy X = ∑ i, ent 2 (p X i) :=
begin
  rw entropy_eq,
  refine sum_subset (subset_univ _) _,
  simp only [mem_univ, mem_image, not_exists, forall_true_left, p, prob, set.mem_singleton_iff],
  intros x hx,
  rw [filter_false_of_mem, sum_empty, ent_zero],
  simpa using hx
end

lemma entropy_const {X : Ω → α} (h : ∀ i j, X i = X j) : ℍ ω, X ω = 0 :=
begin
  casesI is_empty_or_nonempty Ω,
  { rw [entropy, expect],
    convert @fintype.sum_empty Ω _ _ _ (λ i, w i • -real.logb 2 (p X (X i))) },
  inhabit Ω,
  rw [entropy_eq],
  have : univ.image X = {X default},
  { rw eq_singleton_iff_unique_mem,
    simp [h _ default] },
  rw [this, sum_singleton],
  simp only [p, prob, set.mem_singleton_iff, h _ default, filter_true_of_mem, mem_univ,
    forall_const, whole_space, ent_one],
end

lemma entropy_empty [is_empty α] {X : Ω → α} : ℍ ω, X ω = 0 := entropy_const (by simp)

lemma entropy_injective {X : Ω → α} {f : α → β} (hf : function.injective f) :
  ℍ ω, f (X ω) = ℍ ω, X ω :=
begin
  rw [entropy_eq, entropy_eq],
  rw [←finset.image_image, finset.sum_image],
  { simp only [p_embedding hf] },
  simp only [hf.eq_iff, imp_self, implies_true_iff],
end

def cond_entropy (Y : Ω → β) (X : Ω → α) : ℝ :=
𝔼 ω, - real.logb 2 (p (λ k, (X k, Y k)) (X ω, Y ω) / p X (X ω))

local notation `ℍ` binders `, ` r:(scoped:67 f, f) ` | ` s:(scoped:67 g, g) := cond_entropy r s

lemma cond_entropy_nonneg (Y : Ω → β) (X : Ω → α) : 0 ≤ ℍ i, Y i | X i :=
begin
  refine expect_nonneg (λ ω, _),
  rw neg_nonneg,
  refine real.logb_nonpos one_lt_two _ _,
  { positivity },
  refine div_le_one_of_le _ (p_nonneg _ _),
  apply prob_le_prob,
  intros ω' hω',
  simp {contextual := tt}
end

def indep (X : Ω → α) (Y : Ω → β) : Prop :=
∀ x y, p (λ ω, (X ω, Y ω)) (x, y) = p X x * p Y y

lemma p_ne_zero_of_exists {ω : Ω} (hi : w ω ≠ 0) {X : Ω → α} : 0 < p X (X ω) :=
begin
  simp only [p, prob, set.mem_singleton_iff, sum_filter],
  refine sum_pos' _ ⟨ω, by simp, _⟩,
  { intros j hj,
    split_ifs;
    positivity },
  rw if_pos rfl,
  positivity,
end

lemma cond_entropy_chain (X : Ω → α) (Y : Ω → β) :
  cond_entropy Y X = ℍ ω, (X ω, Y ω) - entropy X :=
begin
  rw [cond_entropy, entropy, entropy, ←sub_eq_zero, ←sub_add, sub_eq_add_neg, ←expect_neg,
    ←expect_add, ←expect_add],
  refine sum_eq_zero _,
  rintro x -,
  dsimp,
  simp only [neg_neg, mul_eq_zero, or_iff_not_imp_left],
  intro h,
  rw real.logb_div,
  { simp },
  { apply (p_ne_zero_of_exists h).ne' },
  { apply (p_ne_zero_of_exists h).ne' },
end

lemma cond_entropy_chain' (X : Ω → α) (Y : Ω → β) :
  cond_entropy Y X + entropy X = ℍ ω, (X ω, Y ω) :=
by rw [cond_entropy_chain, sub_add_cancel]

lemma cond_entropy_chain_swap (X : Ω → α) (Y : Ω → β) :
  cond_entropy Y X = ℍ ω, (Y ω, X ω) - entropy X :=
begin
  rw [cond_entropy_chain, ←entropy_injective prod.swap_injective],
  simp only [prod.swap_prod_mk],
end

lemma cond_entropy_chain_swap' (X : Ω → α) (Y : Ω → β) :
  cond_entropy Y X + entropy X = ℍ ω, (Y ω, X ω) :=
by rw [cond_entropy_chain_swap, sub_add_cancel]

lemma cond_entropy_apply {X : Ω → α} {f : α → β} : ℍ ω, f (X ω) | X ω = 0 :=
begin
  let g : α → α × β := λ x, (x, f x),
  have hg : function.injective g,
  { intros x y,
    simp [g] {contextual := tt} },
  rw [cond_entropy_chain, entropy_injective hg, sub_self],
end

lemma entropy_apply {X : Ω → α} {f : α → β} : ℍ ω, f (X ω) ≤ ℍ ω, X ω :=
begin
  have : ℍ ω, (X ω, f (X ω)) = ℍ ω, X ω,
  { rw [←cond_entropy_chain', cond_entropy_apply, zero_add] },
  rw [←this, ←cond_entropy_chain_swap'],
  simp only [le_add_iff_nonneg_left],
  apply cond_entropy_nonneg
end

def restrict {δ : ℕ → Type*} (X : Π i, δ i) (n : ℕ) : Π i < n, δ i := λ i _, X i

lemma cond_entropy_long_chain {n : ℕ} {δ : ℕ → Type*}
  (X : Ω → Π i, δ i) :
  ℍ ω, restrict (X ω) n = ∑ i in range n, ℍ ω, X ω i | restrict (X ω) i :=
begin
  induction n with n ih,
  { simp only [range_zero, sum_empty],
    apply entropy_const,
    intros i j,
    ext k hk,
    simpa using hk },
  rw [finset.sum_range_succ, ←ih, add_comm, cond_entropy_chain'],
  let f : (Π i < n.succ, δ i) → (Π i < n, δ i) × δ n :=
    λ g, ⟨λ i hi, g i (hi.trans_le n.le_succ), g _ n.lt_succ_self⟩,
  have : ∀ ω, f (restrict (X ω) n.succ) = (restrict (X ω) n, X ω n),
  { intro ω,
    refl },
  simp only [←this],
  rw entropy_injective,
  rintro (g₁ g₂ : Π i < n.succ, δ i) h,
  simp only [prod.mk.inj_iff, function.funext_iff] at h,
  ext i hi,
  rcases nat.lt_succ_iff_lt_or_eq.1 hi with hi' | rfl,
  { rw h.1 _ hi' },
  { exact h.2 }
end

-- def pmf (ℙ : fin_space Ω) (X : Ω → α) (a : α) : ℝ := ∑ i in univ.filter (λ i, X i = a), ℙ i

-- def findist.apply (A : fin_space Ω) (X : Ω → β) :
--   findist β :=
-- { w := λ b, ∑ i in univ.filter (λ i, f i = b), A.w i,
--   nonneg := λ _, sum_nonneg (λ i _, A.nonneg _),
--   has_sum := by rw [sum_fiberwise, A.has_sum] }

-- def findist.prod (A : findist α) (B : findist β) : findist (α × β) :=
-- { w := λ x, A.w x.1 * B.w x.2,
--   nonneg := λ x, mul_nonneg (A.nonneg _) (B.nonneg _),
--   has_sum :=
--   begin
--     rw [←univ_product_univ, sum_product],
--     simp [←mul_sum, B.has_sum, A.has_sum],
--   end }

-- noncomputable def uniform_on (F : finset α) (hF : F.nonempty) : findist α :=
-- { w := λ Y, if Y ∈ F then F.card⁻¹ else 0,
--   nonneg := λ Y, by split_ifs; positivity,
--   has_sum :=
--   begin
--     rw [finset.sum_ite_mem, finset.univ_inter, finset.sum_const, nsmul_eq_mul, mul_inv_cancel],
--     simp [hF.ne_empty],
--   end }

-- lemma uniform_on_w_ne_zero {F : finset α} (hF : F.nonempty) (x : α) :
--   (uniform_on F hF).w x ≠ 0 ↔ x ∈ F :=
-- by simp [uniform_on, hF.ne_empty]

-- lemma uniform_on_w_eq_zero {F : finset α} (hF : F.nonempty) (x : α) :
--   (uniform_on F hF).w x = 0 ↔ x ∉ F :=
-- by simp [←uniform_on_w_ne_zero hF x]

-- def union (A B : findist (finset α)) : findist (finset α) :=
-- { w := λ Z, ∑ X, ∑ Y, A.w X * B.w Y * ite (X ∪ Y = Z) 1 0,
--   nonneg := λ Z, sum_nonneg $ λ X hX, sum_nonneg $ λ Y hY,
--     mul_nonneg (mul_nonneg (A.nonneg _) (B.nonneg _)) (by split_ifs; positivity),
--   has_sum :=
--   begin
--     rw sum_comm,
--     suffices : ∑ (X Y Z : finset α), A.w X * B.w Y * ite (X ∪ Y = Z) 1 0 = 1,
--     { refine (sum_congr rfl (λ X hX, _)).trans this,
--       exact sum_comm },
--     simp only [mul_boole, sum_ite_eq, mem_univ, if_true, ←mul_sum, B.has_sum, mul_one, A.has_sum]
--   end }

-- lemma union_eq_zero_iff {A B : findist (finset α)} (Z : finset α) :
--   (union A B).w Z = 0 ↔ ∀ X Y, A.w X = 0 ∨ B.w Y = 0 ∨ X ∪ Y ≠ Z :=
-- begin
--   simp only [union],
--   rw [sum_eq_zero_iff_of_nonneg],
--   simp only [mem_univ, forall_true_left],
--   refine forall_congr (λ X, _),
--   { rw [sum_eq_zero_iff_of_nonneg],
--     { simpa only [mem_univ, forall_true_left, mul_eq_zero, ite_eq_right_iff, one_ne_zero,
--         or_assoc] },
--     intros i hi,
--     refine mul_nonneg (mul_nonneg (A.nonneg _) (B.nonneg _)) _,
--     split_ifs; norm_num1 },
--   { intros i hi,
--     refine sum_nonneg (λ i hi, _),
--     refine mul_nonneg (mul_nonneg (A.nonneg _) (B.nonneg _)) _,
--     split_ifs; norm_num1 },
-- end

-- lemma union_ne_zero_iff {A B : findist (finset α)} (Z : finset α) :
--   (union A B).w Z ≠ 0 ↔ ∃ X Y, A.w X ≠ 0 ∧ B.w Y ≠ 0 ∧ X ∪ Y = Z :=
-- begin
--   rw [ne.def, union_eq_zero_iff],
--   simp only [not_forall, not_or_distrib, not_not],
-- end

-- def findist.apply (A : findist α) (f : α → β) :
--   findist β :=
-- { w := λ b, ∑ i in univ.filter (λ i, f i = b), A.w i,
--   nonneg := λ _, sum_nonneg (λ i _, A.nonneg _),
--   has_sum := by rw [sum_fiberwise, A.has_sum] }

-- def findist.prod (A : findist α) (B : findist β) : findist (α × β) :=
-- { w := λ x, A.w x.1 * B.w x.2,
--   nonneg := λ x, mul_nonneg (A.nonneg _) (B.nonneg _),
--   has_sum :=
--   begin
--     rw [←univ_product_univ, sum_product],
--     simp [←mul_sum, B.has_sum, A.has_sum],
--   end }

-- lemma prod_apply_fst {A : findist α} {B : findist β} :
--   (A.prod B).apply prod.fst = A :=
-- begin
--   ext j,
--   simp only [findist.apply, findist.prod],
--   have : univ.filter (λ i : α × β, i.fst = j) = {j} ×ˢ univ,
--   { ext ⟨x, y⟩,
--     simp [eq_comm] },
--   rw this,
--   simp only [finset.sum_product, sum_singleton, ←mul_sum, B.has_sum, mul_one],
-- end

-- lemma mem_I (A : findist α) {x} : A.w x ∈ unit_interval :=
-- begin
--   refine ⟨A.nonneg x, _⟩,
--   rw ←A.has_sum,
--   exact single_le_sum (λ i _, A.nonneg i) (mem_univ _),
-- end

-- noncomputable def ent (b x : ℝ) : ℝ := - x * real.logb b x
-- @[simp] lemma ent_zero {b : ℝ} : ent b 0 = 0 := by simp [ent]

-- lemma le_h {b x : ℝ} (hb : 1 < b) (hx : x ∈ unit_interval) : 0 ≤ ent b x :=
-- mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.2 hx.1) (real.logb_nonpos hb hx.1 hx.2)

-- noncomputable def entropy (A : findist α) : ℝ := ∑ i, ent 2 (A.w i)

-- lemma concave_on_logb_Ioi (b : ℝ) (hb : 1 ≤ b) :
--   concave_on ℝ (set.Ioi 0) (real.logb b) :=
-- begin
--   have : real.logb b = λ x, (real.log b)⁻¹ • real.log x,
--   { ext x,
--     rw [smul_eq_mul, ←div_eq_inv_mul, real.log_div_log] },
--   rw this,
--   apply concave_on.smul,
--   { simp,
--     exact real.log_nonneg hb },
--   apply strict_concave_on_log_Ioi.concave_on,
-- end

-- lemma gibbs {b : ℝ} (hb : 1 < b) (p q : findist α) (h : ∀ i, q.w i = 0 → p.w i = 0) :
--   ∑ i, ent b (p.w i) ≤ ∑ i, - p.w i * real.logb b (q.w i) :=
-- begin
--   let s : finset α := univ.filter (λ i, p.w i ≠ 0),
--   have hs' : ∀ i ∈ s, p.w i ≠ 0 := λ i hi, (mem_filter.1 hi).2,
--   have hs : ∀ i ∈ s, q.w i ≠ 0 := λ i hi hq, hs' i hi (h _ hq),
--   simp only [ent],
--   suffices : ∑ x in s, p.w x * real.logb b (q.w x / p.w x) ≤ 0,
--   { have : ∑ x in s, p.w x * (real.logb b (q.w x) - real.logb b (p.w x)) ≤ 0,
--     { refine this.trans_eq' (sum_congr rfl _),
--       intros x hx,
--       rw real.logb_div (hs _ hx) (hs' _ hx) },
--     rw finset.sum_filter_of_ne at this,
--     { simpa [mul_sub] using this },
--     { intros x _ h h',
--       apply h,
--       rw [h', zero_mul] } },
--   have : ∀ i ∈ s, q.w i / p.w i ∈ set.Ioi (0 : ℝ),
--   { intros i hi,
--     exact div_pos ((q.nonneg _).lt_of_ne' (hs _ hi)) ((p.nonneg _).lt_of_ne' (hs' _ hi)) },
--   refine ((concave_on_logb_Ioi b hb.le).le_map_sum _ _ this).trans _,
--   { intros i hi,
--     exact p.nonneg i },
--   { rw [sum_filter_ne_zero, p.has_sum] },
--   refine real.logb_nonpos hb (sum_nonneg _) _,
--   { intros i hi,
--     exact smul_nonneg (p.nonneg _) (div_nonneg (q.nonneg _) (p.nonneg _)) },
--   refine (sum_congr rfl (λ x hx, _)).trans_le
--     ((sum_le_sum_of_subset_of_nonneg (subset_univ _) (λ i hi _, _)).trans_eq q.has_sum),
--   { rw [smul_eq_mul, mul_div_cancel'],
--     apply hs' _ hx },
--   exact q.nonneg _
-- end

-- lemma entropy_uniform_on (s : finset α) (hs : s.nonempty) :
--   entropy (uniform_on s hs) = real.logb 2 s.card :=
-- begin
--   simp only [entropy, uniform_on, apply_ite (ent 2), ent_zero, sum_ite_mem, univ_inter, sum_const,
--     nsmul_eq_mul],
--   rw [ent, ←mul_assoc, mul_neg, mul_inv_cancel, real.logb_inv, neg_mul, one_mul, neg_neg],
--   simp [hs.ne_empty],
-- end

-- lemma entropy_le (s : finset α) (p : findist α) (hp : ∀ i, i ∉ s → p.w i = 0) (hs : s.nonempty) :
--   entropy p ≤ entropy (uniform_on s hs) :=
-- begin
--   refine (gibbs one_lt_two p (uniform_on s hs) _).trans _,
--   { intros i hi,
--     apply hp i _,
--     simpa [uniform_on, hs.ne_empty] using hi },
--   rw entropy_uniform_on,
--   simp only [entropy, uniform_on, apply_ite (ent 2), ent_zero, sum_ite_mem, univ_inter, sum_const,
--     nsmul_eq_mul, apply_ite (real.logb 2), mul_ite, real.logb_zero, mul_zero, ←finset.sum_mul,
--     real.logb_inv, sum_neg_distrib, neg_mul_neg],
--   apply mul_le_of_le_one_left,
--   { apply real.logb_nonneg one_lt_two,
--     simpa [nat.succ_le_iff, finset.card_pos, hs.ne_empty] },
--   refine ((sum_le_sum_of_subset_of_nonneg (subset_univ _) (λ i hi _, _)).trans_eq p.has_sum),
--   exact p.nonneg _
-- end
