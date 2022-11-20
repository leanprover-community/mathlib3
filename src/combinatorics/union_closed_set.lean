import combinatorics.set_family.intersecting
import topology.unit_interval
import analysis.special_functions.log.base
import analysis.convex.jensen
import analysis.convex.specific_functions

open_locale big_operators
open finset

variables {Ω α β : Type*} [fintype Ω] {X : Ω → α} {Y : Ω → β} {f : α → β}
variables {γ : Type*} [add_comm_monoid γ] [module ℝ γ]

noncomputable theory

class finite_measure_space (Ω : Type*) [fintype Ω] :=
(w : Ω → ℝ)
(pos : ∀ x, 0 < w x)
(has_sum : ∑ x : Ω, w x = 1)

variables [finite_measure_space Ω]

local notation `w` := finite_measure_space.w

lemma possible {ω : Ω} : 0 < w ω := finite_measure_space.pos _
lemma whole_space : ∑ ω : Ω, w ω = 1 := finite_measure_space.has_sum

@[positivity]
meta def positivity_nonneg : expr → tactic tactic.positivity.strictness
| `(w %%a) := positive <$> tactic.mk_app ``possible [a]
| e := tactic.failed

lemma nonneg {ω : Ω} : 0 ≤ w ω := by positivity

def expect (X : Ω → γ) : γ :=
∑ ω, w ω • X ω

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

lemma prob_eq_exp (A : set α) : ℙ[X in A] = 𝔼 i, ite (X i ∈ A) 1 0 :=
begin
  rw [prob, expect],
  simp only [smul_eq_mul, mul_boole],
  rw ←sum_filter,
end

lemma prob_nonneg (A : set α) : 0 ≤ ℙ[X in A] :=
sum_nonneg (λ i hi, by positivity)

lemma prob_le_one (A : set α) : ℙ[X in A] ≤ 1 :=
begin
  refine (sum_le_sum_of_subset_of_nonneg (subset_univ _) (λ _ _ _, _)).trans_eq whole_space,
  apply nonneg
end

lemma prob_union {A B : set α} (h : disjoint A B) :
  ℙ[X in A ∪ B] = ℙ[X in A] + ℙ[X in B] :=
begin
  classical,
  rw [prob, prob, prob, ←sum_union],
  simp_rw [←filter_or],
  convert rfl,
  rw disjoint_filter,
  rw set.disjoint_left at h,
  intros x _ hx hx',
  exact h hx hx'
end

lemma prob_le_prob {A : set α} {B : set β} (h : ∀ ω : Ω, w ω ≠ 0 → X ω ∈ A → Y ω ∈ B) :
  ℙ[X in A] ≤ ℙ[Y in B] :=
begin
  change ∑ ω in univ.filter _, _ ≤ ∑ ω in univ.filter _, _,
  rw ←sum_filter_ne_zero,
  refine sum_le_sum_of_subset_of_nonneg _ (λ _ _ _, nonneg),
  simp only [finset.subset_iff, ne.def, mem_filter, mem_univ, true_and, and_imp],
  intros ω h₁ h₂,
  exact h ω h₂ h₁
end

lemma prob_le_prob_of_subset {A A' : set α} (h : A ⊆ A') : ℙ[X in A] ≤ ℙ[X in A'] :=
prob_le_prob (λ ω hω hx, h hx)

def p (X : Ω → α) (a : α) : ℝ := ℙ[X in {a}]

lemma p_nonneg (X : Ω → α) (a : α) : 0 ≤ p X a := prob_nonneg _

@[positivity]
meta def positivity_prob : expr → tactic tactic.positivity.strictness
| `(prob %%X %%A) := nonnegative <$> tactic.mk_app ``prob_nonneg [X, A]
| `(p %%X %%a) := nonnegative <$> tactic.mk_app ``p_nonneg [X, a]
| e := tactic.failed

lemma p_embedding (hf : function.injective f) (a : α) :
  p (λ ω, f (X ω)) (f a) = p X a :=
by simp [p, prob, hf.eq_iff]

lemma p_eq_zero_iff {x : α} : p X x = 0 ↔ ∀ ω, X ω ≠ x :=
begin
  simp only [p, prob, set.mem_singleton_iff],
  rw sum_eq_zero_iff_of_nonneg,
  { simpa only [mem_filter, mem_univ, true_and, ne.def, possible.ne'] },
  intros i hi,
  apply nonneg
end

lemma p_pos_iff {x : α} : 0 < p X x ↔ ∃ ω, X ω = x :=
begin
  rw [has_le.le.lt_iff_ne, ne_comm, ne.def, p_eq_zero_iff],
  { simp },
  exact p_nonneg _ _
end

lemma p_ne_zero_iff {x : α} : p X x ≠ 0 ↔ ∃ ω, X ω = x :=
by { rw [ne.def, p_eq_zero_iff], simp }

lemma p_pos_of_exists {ω : Ω} : 0 < p X (X ω) := by { rw p_pos_iff, simp }

lemma p_whole_space {s : finset α} (hs : ∀ i ∉ s, p X i = 0) : ∑ x in s, p X x = 1 :=
begin
  simp only [p, prob, set.mem_singleton_iff],
  rw [@sum_fiberwise_of_maps_to _ _ _ _ _ _ _ X, whole_space],
  intros x hx,
  by_contra',
  exact p_pos_of_exists.ne' (hs (X x) this),
end

def ent (b x : ℝ) : ℝ := - x * real.logb b x
@[simp] lemma ent_zero {b : ℝ} : ent b 0 = 0 := by simp [ent]
@[simp] lemma ent_one {b : ℝ} : ent b 1 = 0 := by simp [ent]

lemma le_h {b x : ℝ} (hb : 1 < b) (hx : x ∈ unit_interval) : 0 ≤ ent b x :=
mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.2 hx.1) (real.logb_nonpos hb hx.1 hx.2)

def entropy (X : Ω → α) : ℝ := 𝔼 ω, - real.logb 2 (p X (X ω))

local notation `ℍ`:67 binders `, ` r:(scoped:67 f, entropy f) := r

lemma entropy_nonneg : 0 ≤ ℍ ω, X ω :=
expect_nonneg $ λ ω, neg_nonneg.2 $ real.logb_nonpos one_lt_two (prob_nonneg _) (prob_le_one _)

lemma entropy_eq : entropy X = ∑ i in univ.image X, ent 2 (p X i) :=
begin
  simp only [entropy, expect, ent, smul_eq_mul, p, prob, neg_mul, mul_neg, sum_neg_distrib,
    sum_mul, neg_inj, set.mem_singleton_iff],
  apply (sum_image' _ _).symm,
  intros c hc,
  refine sum_congr rfl (λ x hx, _),
  simp only [mem_filter, mem_univ, true_and] at hx,
  simp only [hx],
end

lemma entropy_eq' [fintype α] : entropy X = ∑ i, ent 2 (p X i) :=
begin
  rw entropy_eq,
  refine sum_subset (subset_univ _) _,
  simp only [mem_univ, mem_image, not_exists, forall_true_left, p, prob, set.mem_singleton_iff],
  intros x hx,
  rw [filter_false_of_mem, sum_empty, ent_zero],
  simpa using hx
end

lemma entropy_const (h : ∀ i j, X i = X j) : ℍ ω, X ω = 0 :=
begin
  casesI is_empty_or_nonempty Ω,
  { rw [entropy, expect],
    convert @fintype.sum_empty Ω _ _ _ (λ ω, w ω • -real.logb 2 (p X (X ω))) },
  inhabit Ω,
  rw [entropy_eq],
  have : univ.image X = {X default},
  { rw eq_singleton_iff_unique_mem,
    simp [h _ default] },
  rw [this, sum_singleton],
  simp only [p, prob, set.mem_singleton_iff, h _ default, filter_true_of_mem, mem_univ,
    forall_const, whole_space, ent_one],
end

lemma entropy_empty [is_empty α] : ℍ ω, X ω = 0 := entropy_const (by simp)

lemma entropy_injective (hf : function.injective f) :
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

lemma cond_entropy_nonneg : 0 ≤ ℍ i, Y i | X i :=
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

lemma cond_entropy_chain :
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
  { apply p_pos_of_exists.ne' },
  { apply p_pos_of_exists.ne' },
end

lemma cond_entropy_chain' :
  cond_entropy Y X + entropy X = ℍ ω, (X ω, Y ω) :=
by rw [cond_entropy_chain, sub_add_cancel]

lemma cond_entropy_chain_swap :
  cond_entropy Y X = ℍ ω, (Y ω, X ω) - entropy X :=
begin
  rw [cond_entropy_chain, ←entropy_injective prod.swap_injective],
  simp only [prod.swap_prod_mk],
end

lemma cond_entropy_chain_swap' :
  cond_entropy Y X + entropy X = ℍ ω, (Y ω, X ω) :=
by rw [cond_entropy_chain_swap, sub_add_cancel]

lemma cond_entropy_apply : ℍ ω, f (X ω) | X ω = 0 :=
begin
  let g : α → α × β := λ x, (x, f x),
  have hg : function.injective g,
  { intros x y,
    simp [g] {contextual := tt} },
  rw [cond_entropy_chain, entropy_injective hg, sub_self],
end

lemma entropy_apply : ℍ ω, f (X ω) ≤ ℍ ω, X ω :=
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

lemma gibbs {b : ℝ} (hb : 1 < b) (s : finset α) {X Y : Ω → α}
  (h : ∀ i, p Y i = 0 → p X i = 0) (hs : ∀ i ∉ s, p X i = 0) :
  ∑ i in s, ent b (p X i) ≤ ∑ i in s, - p X i * real.logb b (p Y i) :=
begin
  simp only [ent],
  rw [←sub_nonpos, ←sum_sub_distrib],
  simp only [neg_mul, neg_sub_neg, ←mul_sub],
  have : ∀ x ∈ s, p X x * (real.logb b (p Y x) - real.logb b (p X x)) ≠ 0 → p X x ≠ 0,
  { simp [not_or_distrib] {contextual := tt} },
  rw ←sum_filter_of_ne this,
  dsimp,
  have : ∑ x in s.filter (λ x, p X x ≠ 0), p X x * (real.logb b (p Y x) - real.logb b (p X x)) =
    ∑ x in s.filter (λ x, p X x ≠ 0), p X x * (real.logb b (p Y x / p X x)),
  { refine sum_congr rfl (λ x hx, _),
    simp only [mem_filter, mem_univ, ne.def, true_and] at hx,
    rw real.logb_div (λ h', hx.2 (h _ h')) hx.2 },
  rw this,
  refine ((concave_on_logb_Ioi b hb.le).le_map_sum _ _ _).trans _,
  { intros i hi,
    apply p_nonneg },
  { rw [sum_filter_ne_zero, p_whole_space hs] },
  { intros i hi,
    simp only [ne.def, mem_filter, mem_univ, true_and] at hi,
    exact div_pos
      ((p_nonneg _ _).lt_of_ne' (λ h', hi.2 (h _ h')))
      ((p_nonneg _ _).lt_of_ne' hi.2) },
  refine real.logb_nonpos hb (sum_nonneg _) _,
  { intros i hi,
    positivity },
  have : ∑ i in s.filter (λ x, p X x ≠ 0), p X i • (p Y i / p X i) =
    ∑ i in s.filter (λ x, p X x ≠ 0), p Y i,
  { refine sum_congr rfl (λ x hx, _),
    simp only [mem_filter, ne.def] at hx,
    rw [smul_eq_mul, mul_div_cancel'],
    exact hx.2 },
  rw [this],
  have : s.filter (λ x, p X x ≠ 0) ⊆ univ.image Y,
  { simp only [finset.subset_iff, ne.def, mem_filter, mem_image, mem_univ, exists_true_left,
      and_imp, ←p_ne_zero_iff],
    intros x hx hx' hx'',
    exact hx' (h _ hx'') },
  refine (sum_le_sum_of_subset_of_nonneg this _).trans_eq _,
  { intros,
    apply p_nonneg },
  rw p_whole_space,
  simp [p_eq_zero_iff],
end

lemma cond_entropy_le : ℍ i, X i | Y i ≤ ℍ i, X i :=
begin
  sorry
  -- rw [cond_entropy_chain_swap, sub_le_iff_le_add],
  -- simp only [entropy],
  -- rw [←expect_add],
end
