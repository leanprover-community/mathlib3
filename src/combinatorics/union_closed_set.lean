import combinatorics.set_family.intersecting
import topology.unit_interval
import analysis.special_functions.log.base
import analysis.convex.jensen
import analysis.convex.specific_functions

open_locale big_operators
open finset

variables {Ω α β δ : Type*} [fintype Ω] {X : Ω → α} {Y : Ω → β}
variables {γ : Type*} [add_comm_monoid γ] [module ℝ γ]

noncomputable theory

class finite_measure_space (Ω : Type*) [fintype Ω] :=
(w : Ω → ℝ)
(pos : ∀ x, 0 < w x)
(has_sum : ∑ x : Ω, w x = 1)

variables [finite_measure_space Ω]

@[reducible] def function.product {Ω α β : Type*} (X : Ω → α) (Y : Ω → β) (ω : Ω) : α × β :=
(X ω, Y ω)

local infixr ` ×ᶠ `:82 := function.product

local notation `w` := finite_measure_space.w

lemma possible {ω : Ω} : 0 < w ω := finite_measure_space.pos _
lemma whole_space : ∑ ω : Ω, w ω = 1 := finite_measure_space.has_sum
instance finite_measure_space.nonempty : nonempty Ω :=
begin
  rw ←not_is_empty_iff,
  introI h,
  have : ∑ ω : Ω, w ω = 0,
  { convert @fintype.sum_empty Ω _ _ _ w },
  rw whole_space at this,
  simpa using this
end

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

lemma expect_mul {X : Ω → ℝ} {r : ℝ} : 𝔼 i, (r * X i) = r * 𝔼 i, X i :=
by simp only [expect, mul_sum, mul_left_comm, smul_eq_mul]

lemma expect_nonneg {X : Ω → ℝ} (hω : ∀ ω, 0 ≤ X ω) : 0 ≤ 𝔼 ω, X ω :=
sum_nonneg $ λ i hi, smul_nonneg nonneg (hω _)

lemma expect_empty [is_empty Ω] {X : Ω → γ} : 𝔼 i, X i = 0 :=
by { rw expect, convert fintype.sum_empty (λ i, w i • X i) }

def prob {α : Type*} (X : Ω → α) (A : set α) [decidable_pred (∈ A)] : ℝ :=
∑ ω in univ.filter (λ ω, X ω ∈ A), w ω

def cond_prob {α : Type*} (X : Ω → α) (A : set α) (B : set Ω)
  [decidable_pred (∈ A)] [decidable_pred (∈ B)] : ℝ :=
prob (X ×ᶠ id) (A ×ˢ B) / prob id B

local notation `ℙ[` X ` in ` A `]` := prob X A
local notation `ℙ[` X ` in ` A ` | ` B `]` := cond_prob X A B

lemma cond_prob_univ (A : set α) [decidable_pred (∈ A)] : ℙ[X in A] = ℙ[X in A | set.univ] :=
begin
  simp only [cond_prob, prob, set.prod_mk_mem_set_prod_eq, set.mem_univ, and_true, forall_const,
    filter_true_of_mem, mem_univ, whole_space, div_one],
end

lemma prob_eq_exp (A : set α) [decidable_pred (∈ A)] : ℙ[X in A] = 𝔼 i, ite (X i ∈ A) 1 0 :=
begin
  rw [prob, expect],
  simp only [smul_eq_mul, mul_boole],
  rw ←sum_filter,
end

lemma prob_nonneg (A : set α) [decidable_pred (∈ A)] : 0 ≤ ℙ[X in A] :=
sum_nonneg (λ i hi, by positivity)

lemma prob_le_one (A : set α) [decidable_pred (∈ A)] : ℙ[X in A] ≤ 1 :=
begin
  refine (sum_le_sum_of_subset_of_nonneg (subset_univ _) (λ _ _ _, _)).trans_eq whole_space,
  apply nonneg
end

lemma prob_union {A B : set α} [decidable_pred (∈ A)] [decidable_pred (∈ B)]
  (h : disjoint A B) :
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

lemma prob_le_prob {A : set α} {B : set β} [decidable_pred (∈ A)] [decidable_pred (∈ B)]
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

lemma prob_le_prob_of_subset {A A' : set α} [decidable_pred (∈ A)] [decidable_pred (∈ A')]
  (h : A ⊆ A') : ℙ[X in A] ≤ ℙ[X in A'] :=
prob_le_prob (λ ω hω hx, h hx)

variables [decidable_eq α] [decidable_eq β] [decidable_eq δ]

def p (X : Ω → α) (a : α) : ℝ := ℙ[X in {a}]

lemma p_nonneg (X : Ω → α) (a : α) : 0 ≤ p X a := prob_nonneg _

@[positivity]
meta def positivity_prob : expr → tactic tactic.positivity.strictness
| `(prob %%X %%A) := nonnegative <$> tactic.mk_app ``prob_nonneg [X, A]
| `(p %%X %%a) := nonnegative <$> tactic.mk_app ``p_nonneg [X, a]
| e := tactic.failed

lemma p_embedding {f : α → β} (hf : function.injective f) (a : α) :
  p (f ∘ X) (f a) = p X a :=
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

lemma p_pos {ω : Ω} : 0 < p X (X ω) := by { rw p_pos_iff, simp }

lemma p_whole_space (s : finset α) (hs : ∀ i ∉ s, p X i = 0) :
  ∑ x in s, p X x = 1 :=
begin
  simp only [p, prob, set.mem_singleton_iff],
  rw [@sum_fiberwise_of_maps_to _ _ _ _ _ _ _ X, whole_space],
  intros x hx,
  by_contra',
  exact p_pos.ne' (hs (X x) this),
end

lemma p_whole_space' (X : Ω → α) : ∑ x in univ.image X, p X x = 1 :=
p_whole_space _ (by simp [p_eq_zero_iff])

lemma p_cond {y : β} :
  ∑ x in univ.image X, p (X ×ᶠ Y) (x, y) = p Y y :=
begin
  simp only [p, prob, set.mem_singleton_iff, prod.mk.inj_iff],
  rw [sum_filter, sum_image'],
  intros c hc,
  simp only [←sum_filter, filter_filter],
end

lemma expect_eq [decidable_eq γ] {X : Ω → γ} : 𝔼 i, X i = ∑ x in univ.image X, p X x • x :=
begin
  simp only [expect, p, prob, set.mem_singleton_iff, sum_smul],
  rw sum_image',
  exact λ c hc, sum_congr rfl (by simp {contextual := tt})
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

lemma entropy_eq' {s : finset α} (hs : ∀ i ∉ s, p X i = 0) :
  entropy X = ∑ i in s, ent 2 (p X i) :=
begin
  rw entropy_eq,
  refine sum_subset _ _,
  { simp only [finset.subset_iff, mem_image, mem_univ, exists_true_left, forall_exists_index,
      forall_apply_eq_imp_iff'],
    intros ω,
    by_contra,
    apply p_pos.ne' (hs _ h) },
  simp only [mem_univ, mem_image, not_exists, forall_true_left, p, prob, set.mem_singleton_iff],
  intros x hx hx',
  rw [filter_false_of_mem, sum_empty, ent_zero],
  simpa using hx'
end

def cond_event_entropy (X : Ω → α) (A : set Ω) [decidable_pred (∈ A)] : ℝ :=
  ∑ i in univ.image X, ent 2 ℙ[X in {i} | A]

lemma entropy_const (h : ∀ i j, X i = X j) : ℍ ω, X ω = 0 :=
begin
  inhabit Ω,
  rw [entropy_eq],
  have : univ.image X = {X default},
  { rw eq_singleton_iff_unique_mem,
    simp [h _ default] },
  rw [this, sum_singleton],
  simp only [p, prob, set.mem_singleton_iff, h _ default, filter_true_of_mem, mem_univ,
    forall_const, whole_space, ent_one],
end

lemma entropy_injective {f : α → β} (hf : function.injective f) :
  ℍ ω, f (X ω) = ℍ ω, X ω :=
begin
  rw [entropy_eq, entropy_eq],
  rw [←finset.image_image, finset.sum_image],
  { simp only [p_embedding hf] },
  simp only [hf.eq_iff, imp_self, implies_true_iff],
end

def indep (X : Ω → α) (Y : Ω → β) : Prop :=
∀ x y, p (X ×ᶠ Y) (x, y) = p X x * p Y y

lemma indep.swap (h : indep Y X) : indep X Y :=
begin
  intros x y,
  rw [mul_comm, ←h y x, ←p_embedding prod.swap_injective],
  refl,
end

lemma indep.comm : indep Y X ↔ indep X Y := ⟨indep.swap, indep.swap⟩

lemma indep.entropy_prod (h : indep X Y) :
  ℍ ω, (X ω, Y ω) = ℍ ω, X ω + ℍ ω, Y ω :=
begin
  rw [entropy, entropy, entropy, ←expect_add],
  congr' 1,
  ext ω,
  rw [h, real.logb_mul p_pos.ne' p_pos.ne', neg_add],
end

def cond_entropy (Y : Ω → β) (X : Ω → α) : ℝ :=
𝔼 ω, - real.logb 2 (p (X ×ᶠ Y) (X ω, Y ω) / p X (X ω))

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
  { apply p_pos.ne' },
  { apply p_pos.ne' },
end

lemma cond_entropy_chain' :
  cond_entropy Y X + entropy X = ℍ ω, (X ω, Y ω) :=
by rw [cond_entropy_chain, sub_add_cancel]

lemma cond_entropy_chain_swap :
  cond_entropy Y X = ℍ ω, (Y ω, X ω) - entropy X :=
by { rw [cond_entropy_chain, ←entropy_injective prod.swap_injective], refl }

lemma cond_entropy_chain_swap' :
  cond_entropy Y X + entropy X = ℍ ω, (Y ω, X ω) :=
by rw [cond_entropy_chain_swap, sub_add_cancel]

lemma cond_entropy_apply {f : α → β} : ℍ ω, f (X ω) | X ω = 0 :=
begin
  let g : α → α × β := λ x, (x, f x),
  have hg : function.injective g,
  { intros x y,
    simp [g] {contextual := tt} },
  rw [cond_entropy_chain, entropy_injective hg, sub_self],
end

lemma cond_entropy_injective_right {f : α → δ} (hf : function.injective f) :
  ℍ ω, Y ω | f (X ω) = ℍ ω, Y ω | X ω :=
begin
  rw [cond_entropy_chain, cond_entropy_chain, entropy_injective hf, sub_left_inj],
  let g : α × β → δ × β := λ i, (f i.1, i.2),
  have : function.injective g,
  { rintro ⟨a, b⟩ ⟨a', b'⟩,
    simp [g, hf.eq_iff] {contextual := tt} },
  rw [←entropy_injective this],
end

lemma cond_entropy_injective_left {f : α → δ} (hf : function.injective f) :
  ℍ ω, f (X ω) | Y ω = ℍ ω, X ω | Y ω :=
begin
  rw [cond_entropy_chain, cond_entropy_chain, sub_left_inj],
  let g : β × α → β × δ := λ i, (i.1, f i.2),
  have : function.injective g,
  { rintro ⟨a, b⟩ ⟨a', b'⟩,
    simp [g, hf.eq_iff] {contextual := tt} },
  rw [←entropy_injective this],
end

lemma entropy_apply {f : α → β} : ℍ ω, f (X ω) ≤ ℍ ω, X ω :=
begin
  have : ℍ ω, (X ω, f (X ω)) = ℍ ω, X ω,
  { rw [←cond_entropy_chain', cond_entropy_apply, zero_add] },
  rw [←this, ←cond_entropy_chain_swap'],
  simp only [le_add_iff_nonneg_left],
  apply cond_entropy_nonneg
end

def restrict {δ : ℕ → Type*} (X : Π i, δ i) (n : ℕ) : Π i < n, δ i := λ i _, X i

instance decidable_eq_ball {δ : ℕ → Type*} {n : ℕ} [∀ i, decidable_eq (δ i)] :
  decidable_eq (Π i < n, δ i) :=
begin
  intros x y,
  have : x = y ↔ ∀ i < n, x i H = y i H,
  { simp only [function.funext_iff] },
  exact decidable_of_iff' _ this,
end

lemma cond_entropy_long_chain {n : ℕ} {δ : ℕ → Type*} [∀ i, decidable_eq (δ i)]
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

lemma gibbs {b : ℝ} (hb : 1 < b) (s : finset α) {X : Ω → α} (y : α → ℝ) (hy : ∀ i, 0 ≤ y i)
  (hy' : ∑ i in s, y i ≤ 1)
  (h : ∀ i, y i = 0 → p X i = 0) (hs : ∀ i ∉ s, p X i = 0) :
  ∑ i in s, ent b (p X i) ≤ ∑ i in s, - p X i * real.logb b (y i) :=
begin
  simp only [ent],
  rw [←sub_nonpos, ←sum_sub_distrib],
  simp only [neg_mul, neg_sub_neg, ←mul_sub],
  have : ∀ x ∈ s, p X x * (real.logb b (y x) - real.logb b (p X x)) ≠ 0 → p X x ≠ 0,
  { simp [not_or_distrib] {contextual := tt} },
  rw ←sum_filter_of_ne this,
  dsimp,
  have : ∑ x in s.filter (λ x, p X x ≠ 0), p X x * (real.logb b (y x) - real.logb b (p X x)) =
    ∑ x in s.filter (λ x, p X x ≠ 0), p X x * (real.logb b (y x / p X x)),
  { refine sum_congr rfl (λ x hx, _),
    simp only [mem_filter, mem_univ, ne.def, true_and] at hx,
    rw real.logb_div (λ h', hx.2 (h _ h')) hx.2 },
  rw this,
  refine ((concave_on_logb_Ioi b hb.le).le_map_sum _ _ _).trans _,
  { intros i hi,
    apply p_nonneg },
  { rw [sum_filter_ne_zero, p_whole_space _ hs] },
  { intros i hi,
    simp only [ne.def, mem_filter, mem_univ, true_and] at hi,
    exact div_pos
      ((hy _).lt_of_ne' (λ h', hi.2 (h _ h')))
      ((p_nonneg _ _).lt_of_ne' hi.2) },
  refine real.logb_nonpos hb (sum_nonneg _) _,
  { intros i hi,
    have := hy i,
    positivity },
  have : ∑ i in s.filter (λ x, p X x ≠ 0), p X i • (y i / p X i) =
    ∑ i in s.filter (λ x, p X x ≠ 0), y i,
  { refine sum_congr rfl (λ x hx, _),
    simp only [mem_filter, ne.def] at hx,
    rw [smul_eq_mul, mul_div_cancel'],
    exact hx.2 },
  rw [this],
  refine (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) _).trans hy',
  { intros,
    apply hy },
end

lemma cond_entropy_indep (h : indep X Y) : ℍ ω, Y ω | X ω = ℍ ω, Y ω :=
by { rw [cond_entropy_chain, h.entropy_prod], simp }

lemma cond_entropy_extra {δ : Type*} [decidable_eq δ] {Z : Ω → δ} :
  ℍ ω, X ω | (Y ω, Z ω) ≤ ℍ ω, X ω | Z ω :=
begin
  rw [cond_entropy_chain_swap, cond_entropy_chain_swap, sub_le_iff_le_add, entropy_eq],
  rw [entropy, entropy, entropy, sub_eq_add_neg, ←expect_neg, ←expect_add, ←expect_add],
  have : ∑ (ω : Ω), w ω • (-real.logb 2 (p (X ×ᶠ Z) (X ω, Z ω)) +
    - -real.logb 2 (p Z (Z ω)) + -real.logb 2 (p (Y ×ᶠ Z) (Y ω, Z ω))) =
    ∑ i in univ.image (X ×ᶠ Y ×ᶠ Z),
      -p (X ×ᶠ Y ×ᶠ Z) i *
        real.logb 2 (p (X ×ᶠ Z) (i.1, i.2.2) * p (Y ×ᶠ Z) (i.2.1, i.2.2) /
          p Z i.2.2),
  { rw sum_image',
    intros c hc,
    rw @sum_congr _ _ _ _ _
      (λ x, -w x • real.logb 2
        (p (X ×ᶠ Z) (X c, Z c) * p (Y ×ᶠ Z) (Y c, Z c) / p Z (Z c))) _ rfl,
    { simp only [smul_eq_mul, ←sum_mul, p, prob, set.mem_singleton_iff, sum_neg_distrib] },
    intros x hx,
    simp only [prod.mk.inj_iff, mem_filter, mem_univ, true_and] at hx,
    simp only [neg_neg, smul_eq_mul, mul_neg, hx.1, hx.2.1, hx.2.2],
    rw [real.logb_div (mul_ne_zero p_pos.ne' p_pos.ne') p_pos.ne',
      real.logb_mul p_pos.ne' p_pos.ne'],
    ring },
  rw [expect, this],
  refine gibbs one_lt_two _ _ _ _ _ _,
  { intro i,
    positivity },
  { have h' : univ.image (X ×ᶠ Y ×ᶠ Z) ⊆ univ.image X ×ˢ (univ.image (Y ×ᶠ Z)),
    { simp only [finset.subset_iff, mem_image, mem_univ, exists_true_left, mem_product,
        forall_exists_index, prod.forall, prod.mk.inj_iff, and_imp],
      rintro _ _ x rfl rfl,
      exact ⟨⟨_, rfl⟩, _, rfl⟩, },
    refine (sum_le_sum_of_subset_of_nonneg h' _).trans_eq _,
    { intros i _ _,
      positivity },
    rw [sum_product, sum_comm],
    simp only [mul_div_assoc, ←sum_mul, p_cond],
    rw ←p_whole_space' (Y ×ᶠ Z),
    refine sum_congr rfl _,
    simp only [mem_image, mem_univ, exists_true_left, forall_exists_index, prod.forall,
      prod.mk.inj_iff, and_imp],
    rintro _ _ ω rfl rfl,
    rw mul_div_cancel',
    apply p_pos.ne' },
  { rintro ⟨i, j, k⟩,
    simp only [div_eq_zero_iff, mul_eq_zero, p_eq_zero_iff, or_imp_distrib],
    simp {contextual := tt} },
  { simp [p_eq_zero_iff] },
end

lemma indep_const (h : ∀ i j, Y i = Y j) : indep X Y :=
begin
  inhabit Ω,
  intros x y,
  simp only [p, prob, set.mem_singleton_iff, prod.mk.inj_iff],
  have : ∀ ω, Y ω = Y (arbitrary Ω),
  { exact λ ω, h ω _ },
  rcases eq_or_ne (Y (arbitrary Ω)) y with rfl | hy,
  { simp [this, whole_space] },
  simp only [this],
  simp [hy],
end

lemma cond_entropy_right_const (h : ∀ i j, Y i = Y j) :
  ℍ ω, X ω | Y ω = ℍ ω, X ω :=
begin
  rw cond_entropy_indep,
  rw indep.comm,
  apply indep_const h,
end

lemma cond_entropy_right {δ : Type*} [decidable_eq δ] (f : α → δ) :
  ℍ ω, Y ω | X ω ≤ ℍ ω, Y ω | f (X ω) :=
begin
  have : ℍ ω, Y ω | (X ω, f (X ω)) = ℍ ω, Y ω | X ω,
  { let g : α → α × δ := λ x, (x, f x),
    have hg : function.injective g,
    { simp [function.injective, g] {contextual := tt} },
    rw ←cond_entropy_injective_right hg },
  rw ←this,
  apply cond_entropy_extra
end

lemma cond_entropy_le : ℍ i, X i | Y i ≤ ℍ i, X i :=
begin
  refine (cond_entropy_right (λ i, unit.star)).trans_eq _,
  rw cond_entropy_right_const,
  simp
end

def uniform_on (X : Ω → α) (s : finset α) : Prop := ∀ i ∈ s, p X i = s.card⁻¹

lemma uniform_on.not_in {s : finset α} (h : uniform_on X s) (hs : s.nonempty) {i : α} (hi : i ∉ s) :
  p X i = 0 :=
begin
  have h1 : ∑ i in s, p X i = 1,
  { rw sum_congr rfl h,
    simp only [sum_const, nsmul_eq_mul],
    rw [mul_inv_cancel],
    rw [nat.cast_ne_zero, ne.def, card_eq_zero],
    apply hs.ne_empty },
  have subs : s ⊆ univ.image X,
  { simp only [finset.subset_iff, mem_image, mem_univ, exists_true_left, ←p_pos_iff],
    intros x hx,
    rw h x hx,
    simpa [card_pos] },
  have := p_whole_space' X,
  have h' : ∑ j in univ.image X \ s, p X j = 0,
  { rwa [←sum_sdiff subs, h1, add_left_eq_self] at this },
  rw sum_eq_zero_iff_of_nonneg at h',
  { by_contra',
    obtain ⟨ω, rfl⟩ := p_ne_zero_iff.1 this,
    apply this,
    apply h',
    simp [hi] },
  intros i hi,
  apply p_nonneg
end

lemma uniform_on.p_eq_zero_iff {s : finset α} (h : uniform_on X s) (hs : s.nonempty) {i : α} :
  p X i = 0 ↔ i ∉ s :=
⟨λ h' h'', by simpa [h _ h'', hs.ne_empty] using h', h.not_in hs⟩

lemma uniform_on.p_ne_zero_iff {s : finset α} (h : uniform_on X s) (hs : s.nonempty) {i : α} :
  p X i ≠ 0 ↔ i ∈ s :=
by rw [ne.def, h.p_eq_zero_iff hs, not_not]

lemma uniform_on.p_pos_iff {s : finset α} (h : uniform_on X s) (hs : s.nonempty) {i : α} :
  0 < p X i ↔ i ∈ s :=
(has_le.le.lt_iff_ne (p_nonneg _ _)).trans (ne_comm.trans (h.p_ne_zero_iff hs))

lemma uniform_on.image_eq_on {s : finset α} (h : uniform_on X s) (hs : s.nonempty) :
  univ.image X = s :=
begin
  ext i,
  simp only [mem_image, mem_univ, exists_true_left, ←p_ne_zero_iff],
  exact h.p_ne_zero_iff hs,
end

lemma entropy_uniform {s : finset α} (h : uniform_on X s) (hs : s.nonempty) :
  entropy X = real.logb 2 s.card :=
begin
  rw [entropy_eq, h.image_eq_on hs],
  have : ∀ i ∈ s, ent 2 (p X i) = ent 2 s.card⁻¹,
  { intros i hi,
    rw h i hi },
  rw [sum_congr rfl this, sum_const, ent, nsmul_eq_mul, real.logb_inv, neg_mul_neg, ←mul_assoc,
    mul_inv_cancel, one_mul],
  simpa using hs.ne_empty,
end

lemma entropy_le_support {s : finset α} (hs : ∀ i ∉ s, p X i = 0) :
  entropy X ≤ real.logb 2 s.card :=
begin
  rcases eq_empty_or_nonempty s with rfl | hs',
  { simp only [not_mem_empty, not_false_iff, forall_true_left] at hs,
    rw [entropy_eq],
    simp only [hs, ent_zero, sum_const_zero, card_empty, coe_zero, real.logb_zero] },
  let y : α → ℝ := λ i, s.card⁻¹,
  rw [entropy_eq' hs],
  refine (gibbs one_lt_two s y _ _ _ hs).trans_eq _,
  { intros i,
    simp only [y],
    positivity },
  { simp only [y, sum_const, nsmul_eq_mul],
    rw mul_inv_cancel,
    simp [hs'.ne_empty] },
  { simp [y, hs'.ne_empty] },
  simp only [y, ←sum_mul, sum_neg_distrib, p_whole_space _ hs],
  simp
end

lemma entropy_le_uniform {Y : Ω → α} {s : finset α} (hs : s.nonempty) (hX : ∀ i ∉ s, p X i = 0)
  (hY : uniform_on Y s) :
  entropy X ≤ entropy Y :=
begin
  rw [entropy_uniform hY hs],
  apply entropy_le_support hX,
end

lemma markov {X : Ω → ℝ} (hX : ∀ ω, 0 ≤ X ω) {x : ℝ} (hx : 0 < x) :
  ℙ[X in set.Ici x] ≤ (𝔼 i, X i) / x :=
begin
  rw [prob_eq_exp, le_div_iff hx, mul_comm, ←expect_mul],
  apply sum_le_sum,
  intros i hi,
  refine smul_le_smul_of_nonneg _ nonneg,
  dsimp,
  split_ifs,
  { simpa using h },
  { simpa using hX i }
end

lemma markov' {X : Ω → ℝ} (hX : ∀ ω, 0 ≤ X ω) {x : ℝ} (hx : 0 < x) :
  ℙ[X in set.Ioi x] ≤ (𝔼 i, X i) / x :=
(prob_le_prob_of_subset set.Ioi_subset_Ici_self).trans (markov hX hx)

-- tt is 1

lemma lemma1 {S : finset α} (p : α → ℝ) {C C' : Ω → α} (hC : ∀ ω, C ω ∈ S) (hC' : ∀ ω, C' ω ∈ S)
  (hCC : indep C C')
  (X X' : Ω → Prop)
  (hX : ∀ c ∈ S, ℙ[X in {true} | {ω | C ω = c}] = p c)
  (hX' : ∀ c ∈ S, ℙ[X' in {true} | {ω | C' ω = c}] = p c)
  (hXX : indep X X') (hCX' : indep C X') (hC'X : indep C' X) :
  1.26 * ℍ ω, X ω | C ω ≤ ℍ ω, (X ω ∨ X' ω) | (C ×ᶠ C') :=
sorry

def component {n : ℕ} (A : finset (fin n)) (i : ℕ) : Prop := i ∈ A.image (λ j : fin n, (j : ℕ))

lemma theorem1 {n : ℕ} {A B : Ω → finset (fin n)} (hAB : indep A B)
  (h : ∀ i < n, p (λ ω, component (A ω) i) true ≤ 0.01) :
  ℍ ω, A ω ≤ ℍ ω, (A ω ∪ B ω) :=
begin

end
