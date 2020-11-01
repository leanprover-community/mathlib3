import data.real.ennreal
import topology.metric_space.basic
import linear_algebra.affine_space.ordered
import analysis.normed_space.add_torsor
import analysis.specific_limits
import analysis.asymptotics

variables {ι α M : Type*}

open set (univ ord_connected pi) function finset (hiding univ pi) filter
open_locale big_operators topological_space nnreal

noncomputable theory

def box_subadditive_on [decidable_eq ι] [preorder α] [ordered_add_comm_monoid M]
  (f : (ι → α) → (ι → α) → M) (s : set (ι → α)) :=
∀ ⦃lo : ι → α⦄ (hlo : lo ∈ s) ⦃hi : ι → α⦄ (hhi : hi ∈ s) ⦃i x⦄,
  lo i ≤ x → x ≤ hi i → f lo hi ≤ f lo (update hi i x) + f (update lo i x) hi

def box_supadditive_on [decidable_eq ι] [preorder α] [ordered_add_comm_monoid M]
  (f : (ι → α) → (ι → α) → M) (s : set (ι → α)) :=
∀ ⦃lo : ι → α⦄ (hlo : lo ∈ s) ⦃hi : ι → α⦄ (hhi : hi ∈ s) ⦃i x⦄,
  lo i ≤ x → x ≤ hi i → f lo (update hi i x) + f (update lo i x) hi ≤ f lo hi

namespace box_subadditive_on

variables [decidable_eq ι] [preorder α] [ordered_add_comm_monoid M] {s : set (ι → α)}

lemma coe_ennreal {f : (ι → α) → (ι → α) → ℝ≥0} :
  box_subadditive_on (λ x y, (f x y : ennreal)) s ↔ box_subadditive_on f s :=
by simp only [box_subadditive_on, ← ennreal.coe_add, ennreal.coe_le_coe]

lemma coe_nnreal {f : (ι → α) → (ι → α) → ℝ≥0} :
  box_subadditive_on (λ x y, (f x y : ℝ)) s ↔ box_subadditive_on f s :=
by simp only [box_subadditive_on, ← nnreal.coe_add, nnreal.coe_le_coe]

variables  {f : (ι → α) → (ι → α) → M} [ord_connected s] {lo mid hi : ι → α}

lemma le_sum_finset_subboxes (h : box_subadditive_on f s) (hlo : lo ∈ s) (hhi : hi ∈ s)
  (h₁ : lo ≤ mid) (h₂ : mid ≤ hi) (t : finset ι) :
  f lo hi ≤ ∑ t' in t.powerset, f (t'.piecewise mid lo) (t'.piecewise hi $ t.piecewise mid hi) :=
begin
  induction t using finset.induction_on with j t hj iht, { simp [le_rfl] },
  simp only [sum_powerset_insert hj, piecewise_insert, ← sum_add_distrib],
  refine trans iht (sum_le_sum $ λ t' ht', _),
  rw [mem_powerset] at ht',
  have hj' : j ∉ t' := λ hj', hj (ht' hj'),
  have hmid : mid ∈ s := s.Icc_subset hlo hhi ⟨h₁, h₂⟩,
  convert h _ _ _ _;
    try { simp only [update_piecewise_of_not_mem _ _ _ hj, update_piecewise_of_not_mem _ _ _ hj',
                      update_idem, update_eq_self, piecewise_eq_of_not_mem _ _ _ hj,
                      piecewise_eq_of_not_mem _ _ _ hj', h₁ j, h₂ j] },
  exact s.Icc_subset hlo hmid (piecewise_mem_Icc' _ h₁),
  exact s.Icc_subset hmid hhi (t'.piecewise_mem_Icc_of_mem_of_mem (set.right_mem_Icc.2 h₂) $
    t.piecewise_mem_Icc h₂)
end

variables [fintype ι]

lemma le_sum_subboxes (h : box_subadditive_on f s) (hlo : lo ∈ s) (hhi : hi ∈ s)
  (h₁ : lo ≤ mid) (h₂ : mid ≤ hi) :
  f lo hi ≤ ∑ t : finset ι, f (t.piecewise mid lo) (t.piecewise hi mid) :=
by simpa using le_sum_finset_subboxes h hlo hhi h₁ h₂ finset.univ

end box_subadditive_on

namespace box_supadditive_on

variables [decidable_eq ι] [preorder α] [ordered_add_comm_monoid M] {s : set (ι → α)}

lemma coe_ennreal {f : (ι → α) → (ι → α) → ℝ≥0} :
  box_supadditive_on (λ x y, (f x y : ennreal)) s ↔ box_supadditive_on f s :=
by simp only [box_supadditive_on, ← ennreal.coe_add, ennreal.coe_le_coe]

lemma coe_nnreal {f : (ι → α) → (ι → α) → ℝ≥0} :
  box_supadditive_on (λ x y, (f x y : ℝ)) s ↔ box_supadditive_on f s :=
by simp only [box_supadditive_on, ← nnreal.coe_add, nnreal.coe_le_coe]

protected lemma order_dual {f : (ι → α) → (ι → α) → M} (hf : box_supadditive_on f s) :
  @box_subadditive_on ι α (order_dual M) _ _ _ f s :=
hf

protected lemma abs {f : (ι → α) → (ι → α) → ℝ} (hf : box_supadditive_on f s)
  (h₀ : ∀ x y, 0 ≤ f x y) : box_supadditive_on (λ x y, abs (f x y)) s :=
by simpa only [abs_of_nonneg (h₀ _ _)]

variables  {f : (ι → α) → (ι → α) → M} [ord_connected s] {lo mid hi : ι → α}

lemma sum_finset_subboxes_le (h : box_supadditive_on f s) (hlo : lo ∈ s) (hhi : hi ∈ s)
  (h₁ : lo ≤ mid) (h₂ : mid ≤ hi) (t : finset ι) :
  ∑ t' in t.powerset, f (t'.piecewise mid lo) (t'.piecewise hi $ t.piecewise mid hi) ≤ f lo hi :=
h.order_dual.le_sum_finset_subboxes hlo hhi h₁ h₂ t

variables [fintype ι]

lemma sum_subboxes_le (h : box_supadditive_on f s) (hlo : lo ∈ s) (hhi : hi ∈ s)
  (h₁ : lo ≤ mid) (h₂ : mid ≤ hi) :
  ∑ t : finset ι, f (t.piecewise mid lo) (t.piecewise hi mid) ≤ f lo hi :=
h.order_dual.le_sum_subboxes hlo hhi h₁ h₂

end box_supadditive_on

lemma box_supadditive_prod_dist [decidable_eq ι] [fintype ι] (s : set (ι → ℝ)) :
  box_supadditive_on (λ f g, ∏ i, dist (f i) (g i)) s :=
begin
  rintros lo - hi - i x lo_le le_hi,
  refine le_of_eq _,
  have := function.apply_update (λ j, dist (lo j)) hi i x,
  have := function.apply_update (λ j y, dist y (hi j)) lo i x,
  simp only at *,
  simp only [*, prod_update_of_mem, mem_univ, ← add_mul],
  rw [← prod_mul_prod_compl {i}, prod_singleton]; try { apply_instance },
  congr,
  simp only [real.dist_eq, abs_of_nonpos, sub_nonpos, *, lo_le.trans le_hi,
    neg_sub, sub_add_sub_cancel']
end

lemma box_supadditive_prod_nndist [decidable_eq ι] [fintype ι] (s : set (ι → ℝ)) :
  box_supadditive_on (λ f g, ∏ i, nndist (f i) (g i)) s :=
by simp_rw [← box_supadditive_on.coe_nnreal, nnreal.coe_prod, coe_nndist, box_supadditive_prod_dist]

lemma box_supadditive_prod_edist [decidable_eq ι] [fintype ι] (s : set (ι → ℝ)) :
  box_supadditive_on (λ f g, ∏ i, edist (f i) (g i)) s :=
by simp_rw [edist_nndist, ← ennreal.coe_finset_prod, box_supadditive_on.coe_ennreal,
  box_supadditive_prod_nndist]

namespace box_subadditive_on

section preorder

variables [decidable_eq ι] [fintype ι] [preorder α]
  {f g : (ι → α) → (ι → α) → ennreal} {s : set (ι → α)} [ord_connected s] {lo mid hi : ι → α}

lemma exists_subbox_mul_lt_of_mul_lt (hf : box_subadditive_on f s)
  (hg : box_supadditive_on g s) (hlo : lo ∈ s) (hhi : hi ∈ s)
  (h₁ : lo ≤ mid) (h₂ : mid ≤ hi) {c : ennreal} (hlt : c * g lo hi < f lo hi) :
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
    canonically_ordered_semiring.mul_le_mul_left' (hg.sum_subboxes_le hlo hhi h₁ h₂) c
end

end preorder

variables [decidable_eq ι] [fintype ι]

structure subbox_lt (s : set (ι → ℝ)) (f g : (ι → ℝ) → (ι → ℝ) → ennreal) (c : ennreal) :=
(lo : ι → ℝ)
(hi : ι → ℝ)
(lo_mem : lo ∈ s)
(hi_mem : hi ∈ s)
(lo_le_hi : lo ≤ hi)
(hlt : c * g lo hi < f lo hi)

namespace subbox_lt

variables {s : set (ι → ℝ)} {f g : (ι → ℝ) → (ι → ℝ) → ennreal} {c : ennreal}

def size (b : subbox_lt s f g c) : ℝ := dist b.lo b.hi

def mid (b : subbox_lt s f g c) : ι → ℝ := midpoint ℝ b.lo b.hi

lemma lo_le_mid (b : subbox_lt s f g c) : b.lo ≤ b.mid :=
left_le_midpoint.2 b.lo_le_hi

lemma mid_le_hi (b : subbox_lt s f g c) : b.mid ≤ b.hi :=
midpoint_le_right.2 b.lo_le_hi

protected def Icc (b : subbox_lt s f g c) := set.Icc b.lo b.hi

instance : preorder (subbox_lt s f g c) :=
{ le := λ b b', b'.lo ≤ b.lo ∧ b.hi ≤ b'.hi,
  le_refl := λ b, ⟨le_rfl, le_rfl⟩,
  le_trans := λ a b c hab hbc, ⟨hbc.1.trans hab.1, hab.2.trans hbc.2⟩ }

lemma Icc_mono : monotone (subbox_lt.Icc : subbox_lt s f g c → set (ι → ℝ)) :=
λ b b' hb, set.Icc_subset_Icc hb.1 hb.2

variables [ord_connected s]

lemma mid_mem (b : subbox_lt s f g c) : b.mid ∈ s :=
s.Icc_subset b.lo_mem b.hi_mem ⟨b.lo_le_mid, b.mid_le_hi⟩

def next (hf : box_subadditive_on f s)
  (hg : box_supadditive_on g s) (b : subbox_lt s f g c) :
  {b' : subbox_lt s f g c // b' ≤ b ∧ b'.size = b.size / 2} :=
begin
  rcases classical.indefinite_description _ (exists_subbox_mul_lt_of_mul_lt hf hg b.lo_mem b.hi_mem
    b.lo_le_mid b.mid_le_hi b.hlt) with ⟨t, ht⟩,
  have h_left : b.lo ≤ t.piecewise b.mid b.lo := t.le_piecewise_of_le_of_le b.lo_le_mid le_rfl,
  have h_right : t.piecewise b.hi b.mid ≤ b.hi := t.piecewise_le_of_le_of_le le_rfl b.mid_le_hi,
  refine ⟨{ hlt := ht, .. }, ⟨h_left, h_right⟩, _⟩,
  { exact s.Icc_subset b.lo_mem b.mid_mem (t.piecewise_mem_Icc' b.lo_le_mid) },
  { exact s.Icc_subset b.mid_mem b.hi_mem (t.piecewise_mem_Icc' b.mid_le_hi) },
  { intros i, by_cases hi : i ∈ t; simp [hi, b.mid_le_hi i, b.lo_le_mid i] },
  { simp only [size, dist_pi_def],
    norm_cast,
    rw [div_eq_inv_mul, nnreal.mul_finset_sup],
    congr' with i : 2,
    by_cases hi : i ∈ t,
    { simp [t.piecewise_eq_of_mem _ _ hi, mid] },
    { simp [t.piecewise_eq_of_not_mem _ _ hi, mid] } }
end

lemma next_le (hf : box_subadditive_on f s)
  (hg : box_supadditive_on g s) (b : subbox_lt s f g c) :
  ↑(b.next hf hg) ≤ b :=
(b.next hf hg).2.1 

lemma size_next (hf : box_subadditive_on f s)
  (hg : box_supadditive_on g s) (b : subbox_lt s f g c) :
  size (b.next hf hg : subbox_lt s f g c) = size b / 2 :=
(b.next hf hg).2.2

def seq (b : subbox_lt s f g c) (hf : box_subadditive_on f s)
  (hg : box_supadditive_on g s) (n : ℕ) :
  subbox_lt s f g c :=
(λ b : subbox_lt s f g c, b.next hf hg)^[n] b

lemma seq_zero (b : subbox_lt s f g c) (hf : box_subadditive_on f s)
  (hg : box_supadditive_on g s) :
  b.seq hf hg 0 = b := rfl

lemma mono_decr_seq (b : subbox_lt s f g c) (hf : box_subadditive_on f s)
  (hg : box_supadditive_on g s) ⦃m n : ℕ⦄ (h : m ≤ n) :
  b.seq hf hg n ≤ b.seq hf hg m :=
begin
  refine @monotone_of_monotone_nat (order_dual (subbox_lt s f g c)) _ _ (λ n, _) _ _ h,
  simp only [seq, iterate_succ_apply'],
  exact next_le hf hg _
end

lemma mono_decr_seq_Icc (b : subbox_lt s f g c) (hf : box_subadditive_on f s)
  (hg : box_supadditive_on g s) ⦃m n : ℕ⦄ (h : m ≤ n) :
  (b.seq hf hg n).Icc ⊆ (b.seq hf hg m).Icc :=
Icc_mono $ b.mono_decr_seq hf hg h

lemma size_seq (b : subbox_lt s f g c) (hf : box_subadditive_on f s)
  (hg : box_supadditive_on g s) (n : ℕ) :
  (b.seq hf hg n).size = b.size / 2^n :=
begin
  induction n with n ihn, { simp [seq] },
  dsimp only [seq] at *,
  simp [iterate_succ_apply', size_next hf hg _, ihn, div_div_eq_div_mul, pow_succ']
end

lemma tendsto_size_seq  (b : subbox_lt s f g c) (hf : box_subadditive_on f s)
  (hg : box_supadditive_on g s) :
  tendsto (λ n, (b.seq hf hg n).size) at_top (𝓝 0) :=
begin
  simp only [b.size_seq hf hg, div_eq_mul_inv, ← inv_pow'],
  rw [← mul_zero b.size],
  exact tendsto_const_nhds.mul (tendsto_pow_at_top_nhds_0_of_lt_1 (inv_nonneg.2 zero_le_two)
    (inv_lt_one one_lt_two))
end

def fix (b : subbox_lt s f g c) (hf : box_subadditive_on f s)
  (hg : box_supadditive_on g s) :
  ι → ℝ :=
⨆ n, (b.seq hf hg n).lo

lemma fix_mem_Inter_Icc (b : subbox_lt s f g c) (hf : box_subadditive_on f s)
  (hg : box_supadditive_on g s) :
  b.fix hf hg ∈ ⋂ n, (b.seq hf hg n).Icc :=
csupr_mem_Inter_Icc_of_mono_decr_Icc (b.mono_decr_seq_Icc hf hg) $ λ n, lo_le_hi _

lemma fix_mem_Icc_seq (b : subbox_lt s f g c) (hf : box_subadditive_on f s)
  (hg : box_supadditive_on g s) (n : ℕ) :
  b.fix hf hg ∈ (b.seq hf hg n).Icc :=
by simpa only using set.mem_Inter.1 (b.fix_mem_Inter_Icc hf hg) n

lemma fix_mem_Icc (b : subbox_lt s f g c) (hf : box_subadditive_on f s)
  (hg : box_supadditive_on g s) :
  b.fix hf hg ∈ b.Icc :=
b.fix_mem_Icc_seq hf hg 0

lemma fix_mem (b : subbox_lt s f g c) (hf : box_subadditive_on f s)
  (hg : box_supadditive_on g s) :
  b.fix hf hg ∈ s :=
s.Icc_subset b.lo_mem b.hi_mem (b.fix_mem_Icc hf hg)

lemma tendsto_lo_fix (b : subbox_lt s f g c) (hf : box_subadditive_on f s)
  (hg : box_supadditive_on g s) :
  tendsto (λ n, (b.seq hf hg n).lo) at_top (𝓝[set.Iic (b.fix hf hg)] (b.fix hf hg)) :=
begin
  refine tendsto_inf.2 ⟨tendsto_iff_dist_tendsto_zero.2 $
    squeeze_zero (λ _, dist_nonneg) (λ n, _) (b.tendsto_size_seq hf hg),
    tendsto_principal.2 $ eventually_of_forall $ λ n, (b.fix_mem_Icc_seq hf hg n).1⟩,
  refine (dist_pi_le_iff dist_nonneg).2 (λ i, le_trans _ (dist_le_pi_dist _ _ i)),
  exact real.dist_left_le_of_mem_interval (set.Icc_subset_interval $
    ⟨(b.fix_mem_Icc_seq hf hg _).1 _, (b.fix_mem_Icc_seq hf hg _).2 _⟩)
end

lemma tendsto_hi_fix (b : subbox_lt s f g c) (hf : box_subadditive_on f s)
  (hg : box_supadditive_on g s) :
  tendsto (λ n, (b.seq hf hg n).hi) at_top (𝓝[set.Ici (b.fix hf hg)] (b.fix hf hg)) :=
begin
  refine tendsto_inf.2 ⟨tendsto_iff_dist_tendsto_zero.2 $
    squeeze_zero (λ _, dist_nonneg) (λ n, _) (b.tendsto_size_seq hf hg),
    tendsto_principal.2 $ eventually_of_forall $ λ n, (b.fix_mem_Icc_seq hf hg n).2⟩,
  refine (dist_pi_le_iff dist_nonneg).2 (λ i, le_trans _ (dist_le_pi_dist _ _ i)),
  rw dist_comm,
  exact real.dist_right_le_of_mem_interval (set.Icc_subset_interval $
    ⟨(b.fix_mem_Icc_seq hf hg _).1 _, (b.fix_mem_Icc_seq hf hg _).2 _⟩)
end

lemma frequently_mul_lt (b : subbox_lt s f g c) (hf : box_subadditive_on f s)
  (hg : box_supadditive_on g s) :
  ∃ᶠ p in (𝓝[(set.Iic (b.fix hf hg)).prod (set.Ici (b.fix hf hg))] (b.fix hf hg, b.fix hf hg)),
    c * g (prod.fst p) (prod.snd p) < f p.1 p.2 :=
begin
  rw [nhds_within_prod_eq],
  exact ((b.tendsto_lo_fix hf hg).prod_mk (b.tendsto_hi_fix hf hg)).frequently
    (frequently_of_forall (λ n, (b.seq hf hg n).hlt))
end

end subbox_lt

variables {s : set (ι → ℝ)} [ord_connected s] {f g : (ι → ℝ) → (ι → ℝ) → ennreal} {c : ennreal}

lemma le_mul_of_forall_eventually_le_mul (hf : box_subadditive_on f s) (hg : box_supadditive_on g s)
  (Hc : ∀ (b ∈ s), ∀ᶠ p in 𝓝[(set.Iic b).prod (set.Ici b)] (b, b),
    f (prod.fst p) p.2 ≤ c * g p.1 p.2) {lo hi} (hlo : lo ∈ s) (hhi : hi ∈ s)
  (hle : lo ≤ hi) : f lo hi ≤ c * g lo hi :=
begin
  contrapose! Hc,
  set b : subbox_lt s f g c := ⟨lo, hi, hlo, hhi, hle, Hc⟩,
  refine ⟨b.fix hf hg, b.fix_mem hf hg, _⟩,
  simpa only [not_eventually, not_le] using b.frequently_mul_lt hf hg
end

lemma eq_of_forall_eventually_le_mul (hf : box_subadditive_on f s) (hg : box_supadditive_on g s)
  (Hc : ∀ (b ∈ s) (c : ℝ≥0), 0 < c → ∀ᶠ p in 𝓝[(set.Iic b).prod (set.Ici b)] (b, b),
    f (prod.fst p) p.2 ≤ c * g p.1 p.2) {lo hi} (hlo : lo ∈ s) (hhi : hi ∈ s)
  (hle : lo ≤ hi) (h_inf : g lo hi < ⊤) : f lo hi = 0 :=
begin
  by_contra h0,
  rcases ennreal.exists_nnreal_pos_mul_lt h_inf.ne h0 with ⟨c, cpos, hc⟩,
  exact hc.not_le
    (le_mul_of_forall_eventually_le_mul hf hg (λ b hb, Hc b hb _ cpos) hlo hhi hle)
end

open asymptotics function

lemma eq_of_forall_is_o {E F : Type*} [normed_group E] [normed_group F]
  {f : (ι → ℝ) → (ι → ℝ) → E} {g : (ι → ℝ) → (ι → ℝ) → F}
  (hf : box_subadditive_on (λ x y, ∥f x y∥) s)
  (hg : box_supadditive_on (λ x y, ∥g x y∥) s)
  (Hc : ∀ (b ∈ s), is_o (uncurry f) (uncurry g) (𝓝[(set.Iic b).prod (set.Ici b)] (b, b)))
  {lo hi} (hlo : lo ∈ s) (hhi : hi ∈ s) (hle : lo ≤ hi) : f lo hi = 0 :=
begin
  simp only [← coe_nnnorm, coe_nnreal, ← coe_ennreal] at hf,
  simp only [← coe_nnnorm, box_supadditive_on.coe_nnreal, ← box_supadditive_on.coe_ennreal] at hg,
  rw [← nnnorm_eq_zero, ← ennreal.coe_eq_zero],
  refine eq_of_forall_eventually_le_mul hf hg _ hlo hhi hle ennreal.coe_lt_top,
  intros b hb c hc,
  simpa [← coe_nnnorm, uncurry, ← nnreal.coe_mul, ← ennreal.coe_mul] using (Hc b hb).def hc
end

lemma eq_of_forall_is_o_prod {E : Type*} [normed_group E] {f : (ι → ℝ) → (ι → ℝ) → E}
  (hf : box_subadditive_on (λ x y, ∥f x y∥) s)
  (Hc : ∀ (b ∈ s), is_o (uncurry f) (λ p, ∏ i, (p.1 i - p.2 i))
    (𝓝[(set.Iic b).prod (set.Ici b)] (b, b)))
  {lo hi} (hlo : lo ∈ s) (hhi : hi ∈ s) (hle : lo ≤ hi) : f lo hi = 0 :=
begin
  have := (box_supadditive_prod_dist s).abs (λ _ _, prod_nonneg $ λ _ _, dist_nonneg),
  simp only [← real.norm_eq_abs] at this,
  refine eq_of_forall_is_o hf this _ hlo hhi hle,
  simpa only [dist_eq_norm, ← normed_field.norm_prod, uncurry, is_o_norm_right]
end

end box_subadditive_on
