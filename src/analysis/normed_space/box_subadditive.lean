import data.real.ennreal
import topology.metric_space.basic
import linear_algebra.affine_space.ordered
import analysis.normed_space.add_torsor
import analysis.specific_limits

variables {ι α M : Type*}

open set (univ ord_connected pi) function finset (hiding univ pi) filter
open_locale big_operators topological_space

noncomputable theory

def box_subadditive_on [decidable_eq ι] [preorder α] [ordered_add_comm_monoid M]
  (f : (ι → α) → (ι → α) → M) (s : set (ι → α)) :=
∀ ⦃lo : ι → α⦄ (hlo : lo ∈ s) ⦃hi : ι → α⦄ (hhi : hi ∈ s) ⦃i x⦄,
  lo i ≤ x → x ≤ hi i → f lo hi ≤ f lo (update hi i x) + f (update lo i x) hi

namespace box_subadditive_on

section ordered_monoid

variables [decidable_eq ι] [preorder α] [ordered_add_comm_monoid M]
  {f : (ι → α) → (ι → α) → M} {s : set (ι → α)} [ord_connected s] {lo mid hi : ι → α}

lemma le_sum_finset_subboxes (h : box_subadditive_on f s) (hlo : lo ∈ s) (hhi : hi ∈ s)
  (h₁ : lo ≤ mid) (h₂ : mid ≤ hi) (t : finset ι) :
  f lo hi ≤ ∑ t' in t.powerset, f (t'.piecewise mid lo) (t'.piecewise hi $ t.piecewise mid hi) :=
begin
  induction t using finset.induction_on with j t hj iht, { simp [le_rfl] },
  simp only [sum_powerset_insert hj, piecewise_insert, ← sum_add_distrib],
  refine trans iht (sum_le_sum $ λ t' ht', _),
  rw [mem_powerset] at ht',
  have hj' : j ∉ t' := λ hj', hj (ht' hj'),
  have hmid : mid ∈ s := set.mem_of_le_of_le hlo hhi h₁ h₂,
  convert h _ _ _ _;
    try { simp only [update_piecewise_of_not_mem _ _ _ hj, update_piecewise_of_not_mem _ _ _ hj',
                      update_idem, update_eq_self, piecewise_eq_of_not_mem _ _ _ hj,
                      piecewise_eq_of_not_mem _ _ _ hj', h₁ j, h₂ j] },
  apply_rules [set.mem_of_le_of_le hlo hmid, le_piecewise_of_le_of_le, piecewise_le_of_le_of_le];
    refl',
  apply_rules [set.mem_of_le_of_le hmid hhi, le_piecewise_of_le_of_le, piecewise_le_of_le_of_le];
    refl'
end

variables [fintype ι]

lemma le_sum_subboxes (h : box_subadditive_on f s) (hlo : lo ∈ s) (hhi : hi ∈ s)
  (h₁ : lo ≤ mid) (h₂ : mid ≤ hi) :
  f lo hi ≤ ∑ t : finset ι, f (t.piecewise mid lo) (t.piecewise hi mid) :=
by simpa using le_sum_finset_subboxes h hlo hhi h₁ h₂ finset.univ

end ordered_monoid

section preorder

variables {R : Type*} [decidable_eq ι] [fintype ι] [preorder α]
  [canonically_linear_ordered_comm_semiring R]
  {f g : (ι → α) → (ι → α) → R} {s : set (ι → α)} [ord_connected s] {lo mid hi : ι → α}

lemma exists_subbox_mul_lt_of_mul_lt (hf : box_subadditive_on f s)
  (hg : @box_subadditive_on ι α (order_dual R) _ _ _ g s) (hlo : lo ∈ s) (hhi : hi ∈ s)
  (h₁ : lo ≤ mid) (h₂ : mid ≤ hi) {c : R} (hlt : c * g lo hi < f lo hi) :
  ∃ t : finset ι, c * g (t.piecewise mid lo) (t.piecewise hi mid) <
    f (t.piecewise mid lo) (t.piecewise hi mid) :=
begin
  contrapose! hlt,
  calc f lo hi ≤ ∑ t : finset ι, f (t.piecewise mid lo) (t.piecewise hi mid) :
    hf.le_sum_subboxes hlo hhi h₁ h₂
  ... ≤ ∑ t : finset ι, c * g (t.piecewise mid lo) (t.piecewise hi mid) :
    sum_le_sum (λ t _, hlt t)
  ... = c * ∑ t : finset ι, g (t.piecewise mid lo) (t.piecewise hi mid) :
    mul_sum.symm
  ... ≤ c * g lo hi :
    canonically_ordered_semiring.mul_le_mul_left' (hg.le_sum_subboxes hlo hhi h₁ h₂) c
end

end preorder

variables {R : Type*} [decidable_eq ι] [fintype ι] [canonically_linear_ordered_comm_semiring R]

structure subbox_lt (s : set (ι → ℝ)) (f g : (ι → ℝ) → (ι → ℝ) → R) (c : R) :=
(lo : ι → ℝ)
(hi : ι → ℝ)
(lo_mem : lo ∈ s)
(hi_mem : hi ∈ s)
(lo_le_hi : lo ≤ hi)
(hlt : c * g lo hi < f lo hi)

namespace subbox_lt

variables {s : set (ι → ℝ)} {f g : (ι → ℝ) → (ι → ℝ) → R} {c : R}

def size (b : subbox_lt s f g c) : ℝ := dist b.lo b.hi

def mid (b : subbox_lt s f g c) : ι → ℝ := midpoint ℝ b.lo b.hi

lemma lo_le_mid (b : subbox_lt s f g c) : b.lo ≤ b.mid :=
left_le_midpoint.2 b.lo_le_hi

lemma mid_le_hi (b : subbox_lt s f g c) : b.mid ≤ b.hi :=
midpoint_le_right.2 b.lo_le_hi

instance : preorder (subbox_lt s f g c) :=
{ le := λ b b', b'.lo ≤ b.lo ∧ b.hi ≤ b'.hi,
  le_refl := λ b, ⟨le_rfl, le_rfl⟩,
  le_trans := λ a b c hab hbc, ⟨hbc.1.trans hab.1, hab.2.trans hbc.2⟩ }

variables [ord_connected s]

lemma mid_mem (b : subbox_lt s f g c) : b.mid ∈ s :=
set.mem_of_le_of_le b.lo_mem b.hi_mem b.lo_le_mid b.mid_le_hi

def next (hf : box_subadditive_on f s)
  (hg : @box_subadditive_on ι ℝ (order_dual R) _ _ _ g s) (b : subbox_lt s f g c) :
  {b' : subbox_lt s f g c // b' ≤ b ∧ b'.size = b.size / 2} :=
begin
  rcases classical.indefinite_description _ (exists_subbox_mul_lt_of_mul_lt hf hg b.lo_mem b.hi_mem
    b.lo_le_mid b.mid_le_hi b.hlt) with ⟨t, ht⟩,
  have h_left : b.lo ≤ t.piecewise b.mid b.lo := t.le_piecewise_of_le_of_le b.lo_le_mid le_rfl,
  have h_right : t.piecewise b.hi b.mid ≤ b.hi := t.piecewise_le_of_le_of_le le_rfl b.mid_le_hi,
  refine ⟨{ hlt := ht, .. }, ⟨h_left, h_right⟩, _⟩,
  { exact set.mem_of_le_of_le b.lo_mem b.mid_mem h_left
      (t.piecewise_le_of_le_of_le le_rfl b.lo_le_mid) },
  { exact set.mem_of_le_of_le b.mid_mem b.hi_mem (t.le_piecewise_of_le_of_le b.mid_le_hi le_rfl)
      h_right },
  { intros i, by_cases hi : i ∈ t; simp [hi, b.mid_le_hi i, b.lo_le_mid i] },
  { simp only [size, pi.dist_def],
    norm_cast,
    rw [div_eq_inv_mul, nnreal.mul_finset_sup],
    congr' with i : 2,
    by_cases hi : i ∈ t,
    { simp [t.piecewise_eq_of_mem _ _ hi, mid] },
    { simp [t.piecewise_eq_of_not_mem _ _ hi, mid] } }
end

lemma next_le (hf : box_subadditive_on f s)
  (hg : @box_subadditive_on ι ℝ (order_dual R) _ _ _ g s) (b : subbox_lt s f g c) :
  ↑(b.next hf hg) ≤ b :=
(b.next hf hg).2.1 

lemma size_next (hf : box_subadditive_on f s)
  (hg : @box_subadditive_on ι ℝ (order_dual R) _ _ _ g s) (b : subbox_lt s f g c) :
  size (b.next hf hg : subbox_lt s f g c) = size b / 2 :=
(b.next hf hg).2.2

def seq (b : subbox_lt s f g c) (hf : box_subadditive_on f s)
  (hg : @box_subadditive_on ι ℝ (order_dual R) _ _ _ g s) (n : ℕ) :
  subbox_lt s f g c :=
(λ b : subbox_lt s f g c, b.next hf hg)^[n] b

lemma seq_zero (b : subbox_lt s f g c) (hf : box_subadditive_on f s)
  (hg : @box_subadditive_on ι ℝ (order_dual R) _ _ _ g s) :
  b.seq hf hg 0 = b := rfl

lemma mono_decr_seq (b : subbox_lt s f g c) (hf : box_subadditive_on f s)
  (hg : @box_subadditive_on ι ℝ (order_dual R) _ _ _ g s) ⦃m n : ℕ⦄ (h : m ≤ n) :
  b.seq hf hg n ≤ b.seq hf hg m :=
begin
  refine @monotone_of_monotone_nat (order_dual (subbox_lt s f g c)) _ _ (λ n, _) _ _ h,
  simp only [seq, iterate_succ_apply'],
  exact next_le hf hg _
end

lemma size_seq (b : subbox_lt s f g c) (hf : box_subadditive_on f s)
  (hg : @box_subadditive_on ι ℝ (order_dual R) _ _ _ g s) (n : ℕ) :
  (b.seq hf hg n).size = b.size / 2^n :=
begin
  induction n with n ihn, { simp [seq] },
  dsimp only [seq] at *,
  simp [iterate_succ_apply', size_next hf hg _, ihn, div_div_eq_div_mul, pow_succ']
end

lemma tendsto_size_seq  (b : subbox_lt s f g c) (hf : box_subadditive_on f s)
  (hg : @box_subadditive_on ι ℝ (order_dual R) _ _ _ g s) :
  tendsto (λ n, (b.seq hf hg n).size) at_top (𝓝 0) :=
begin
  simp only [b.size_seq hf hg, div_eq_mul_inv, ← inv_pow'],
  rw [← mul_zero b.size],
  exact tendsto_const_nhds.mul (tendsto_pow_at_top_nhds_0_of_lt_1 (inv_nonneg.2 zero_le_two)
    (inv_lt_one one_lt_two))
end

def fix (b : subbox_lt s f g c) (hf : box_subadditive_on f s)
  (hg : @box_subadditive_on ι ℝ (order_dual R) _ _ _ g s) :
  ι → ℝ :=
⨆ n, (b.seq hf hg n).lo

lemma fix_mem_Inter_Icc (b : subbox_lt s f g c) (hf : box_subadditive_on f s)
  (hg : @box_subadditive_on ι ℝ (order_dual R) _ _ _ g s) :
  b.fix hf hg ∈ ⋂ n, set.Icc (b.seq hf hg n).lo (b.seq hf hg n).hi :=
csupr_mem_Inter_Icc (λ m n h, (b.mono_decr_seq hf hg h).1) (λ m n h, (b.mono_decr_seq hf hg h).2) $
  λ n, lo_le_hi _

lemma fix_mem_Icc_seq (b : subbox_lt s f g c) (hf : box_subadditive_on f s)
  (hg : @box_subadditive_on ι ℝ (order_dual R) _ _ _ g s) (n : ℕ) :
  b.fix hf hg ∈ set.Icc (b.seq hf hg n).lo (b.seq hf hg n).hi :=
by simpa only using set.mem_Inter.1 (b.fix_mem_Inter_Icc hf hg) n

lemma fix_mem_Icc (b : subbox_lt s f g c) (hf : box_subadditive_on f s)
  (hg : @box_subadditive_on ι ℝ (order_dual R) _ _ _ g s) :
  b.fix hf hg ∈ set.Icc b.lo b.hi :=
b.fix_mem_Icc_seq hf hg 0

lemma fix_mem (b : subbox_lt s f g c) (hf : box_subadditive_on f s)
  (hg : @box_subadditive_on ι ℝ (order_dual R) _ _ _ g s) :
  b.fix hf hg ∈ s :=
set.mem_of_le_of_le b.lo_mem b.hi_mem (b.fix_mem_Icc hf hg).1 (b.fix_mem_Icc hf hg).2

lemma tendsto_lo_fix (b : subbox_lt s f g c) (hf : box_subadditive_on f s)
  (hg : @box_subadditive_on ι ℝ (order_dual R) _ _ _ g s) :
  tendsto (λ n, (b.seq hf hg n).lo) at_top (𝓝[set.Iic (b.fix hf hg)] (b.fix hf hg)) :=
begin
  refine tendsto_inf.2 ⟨tendsto_iff_dist_tendsto_zero.2 $
    squeeze_zero (λ _, dist_nonneg) (λ n, _) (b.tendsto_size_seq hf hg),
    tendsto_principal.2 $ eventually_of_forall $ λ n, (b.fix_mem_Icc_seq hf hg n).1⟩,
  refine (pi.dist_le_iff dist_nonneg).2 (λ i, le_trans _ (pi.le_dist _ _ i)),
  exact real.dist_left_le_of_mem_interval (set.Icc_subset_interval $
    ⟨(b.fix_mem_Icc_seq hf hg _).1 _, (b.fix_mem_Icc_seq hf hg _).2 _⟩)
end

lemma tendsto_hi_fix (b : subbox_lt s f g c) (hf : box_subadditive_on f s)
  (hg : @box_subadditive_on ι ℝ (order_dual R) _ _ _ g s) :
  tendsto (λ n, (b.seq hf hg n).hi) at_top (𝓝[set.Ici (b.fix hf hg)] (b.fix hf hg)) :=
begin
  refine tendsto_inf.2 ⟨tendsto_iff_dist_tendsto_zero.2 $
    squeeze_zero (λ _, dist_nonneg) (λ n, _) (b.tendsto_size_seq hf hg),
    tendsto_principal.2 $ eventually_of_forall $ λ n, (b.fix_mem_Icc_seq hf hg n).2⟩,
  refine (pi.dist_le_iff dist_nonneg).2 (λ i, le_trans _ (pi.le_dist _ _ i)),
  rw dist_comm,
  exact real.dist_right_le_of_mem_interval (set.Icc_subset_interval $
    ⟨(b.fix_mem_Icc_seq hf hg _).1 _, (b.fix_mem_Icc_seq hf hg _).2 _⟩)
end

lemma frequently_mul_lt (b : subbox_lt s f g c) (hf : box_subadditive_on f s)
  (hg : @box_subadditive_on ι ℝ (order_dual R) _ _ _ g s) :
  ∃ᶠ p in (𝓝[(set.Iic (b.fix hf hg)).prod (set.Ici (b.fix hf hg))] (b.fix hf hg, b.fix hf hg)),
    c * g (prod.fst p) (prod.snd p) < f p.1 p.2 :=
begin
  rw [nhds_within_prod_eq],
  exact ((b.tendsto_lo_fix hf hg).prod_mk (b.tendsto_hi_fix hf hg)).frequently
    (frequently_of_forall (λ n, (b.seq hf hg n).hlt))
end

end subbox_lt

variables {s : set (ι → ℝ)} [ord_connected s]

lemma le_mul_of_forall_eventually_le_mul {f g : (ι → ℝ) → (ι → ℝ) → R}
  (hf : box_subadditive_on f s) (hg : @box_subadditive_on ι ℝ (order_dual R) _ _ _ g s) {c : R}
  (Hc : ∀ (b ∈ s), ∀ᶠ p in 𝓝[(set.Iic b).prod (set.Ici b)] (b, b),
    f (prod.fst p) p.2 ≤ c * g p.1 p.2) {lo hi} (hlo : lo ∈ s) (hhi : hi ∈ s)
  (hle : lo ≤ hi) : f lo hi ≤ c * g lo hi :=
begin
  contrapose! Hc,
  set b : subbox_lt s f g c := ⟨lo, hi, hlo, hhi, hle, Hc⟩,
  refine ⟨b.fix hf hg, b.fix_mem hf hg, _⟩,
  simpa only [not_eventually, not_le] using b.frequently_mul_lt hf hg
end

lemma eq_of_forall_eventually_le_mul {f g : (ι → ℝ) → (ι → ℝ) → ennreal}
  (hf : box_subadditive_on f s) (hg : @box_subadditive_on ι ℝ (order_dual ennreal) _ _ _ g s)
  (Hc : ∀ (b ∈ s) (c > 0), ∀ᶠ p in 𝓝[(set.Iic b).prod (set.Ici b)] (b, b),
    f (prod.fst p) p.2 ≤ c * g p.1 p.2) {lo hi} (hlo : lo ∈ s) (hhi : hi ∈ s)
  (hle : lo ≤ hi) (h_inf : g lo hi < ⊤) : f lo hi = 0 :=
begin
  by_contra h0, replace h0 := zero_lt_iff_ne_zero.2 h0,
  rcases exists_between h0 with ⟨c, hc0, hcf⟩,
  have : f lo hi ≤ (c / g lo hi) * g lo hi :=
    le_mul_of_forall_eventually_le_mul hf hg (λ b hb, Hc b hb _
      (ennreal.div_pos_iff.2 ⟨hc0.ne', h_inf.ne⟩)) hlo hhi hle,
  by_cases hg0 : g lo hi = 0, { refine h0.ne' _, by simpa [hg0] },
  refine hcf.not_le _,
  rwa [ennreal.div_def, mul_assoc, ennreal.inv_mul_cancel hg0 h_inf.ne, mul_one] at this
end

open asymptotics

lemma eq_of_forall_is_o {f g : (ι → ℝ) → (ι → ℝ) → ennreal}
  (hf : box_subadditive_on f s) (hg : @box_subadditive_on ι ℝ (order_dual ennreal) _ _ _ g s)
  (Hc : ∀ (b ∈ s) (c > 0), ∀ᶠ p in 𝓝[(set.Iic b).prod (set.Ici b)] (b, b),
    f (prod.fst p) p.2 ≤ c * g p.1 p.2) {lo hi} (hlo : lo ∈ s) (hhi : hi ∈ s)
  (hle : lo ≤ hi) (h_inf : g lo hi < ⊤) : f lo hi = 0 :=

end box_subadditive_on
