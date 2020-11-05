/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury G. Kudryashov
-/
import data.real.ennreal
import topology.metric_space.basic
import linear_algebra.affine_space.ordered
import analysis.normed_space.add_torsor
import analysis.specific_limits
import analysis.asymptotics

/-!
# Sub/sup-additive functions on boxes

Let `s` be a set in `ι → ℝ`. A subbox of `s` (called `set.subinterval` because it shares definition
with the `1`-dimensional case) is a product of closed intervals which is included by `s`.

A function `f : (ι → ℝ) → (ι → ℝ) → M` defines a function on `subinterval s` given by `λ I, f I.left
I.right`. It is called `box_subadditive_on`/`box_additive_on`/`box_supadditive_on` if for any `I :
subinterval s` and any hyperplane `x i = c`, `I.left i ≤ c ≤ I.right i`, the sum of its values on
the two subboxes `I ∩ (Iic c)` and `I ∩ (Ici c)` is greater than or equal/equal/less than or equal
to its value on `I`.

The main result of this file is theorem `box_subadditive_on.eq_zero_of_forall_is_o_prod`. It says
that a `box_subadditive_on`function `f` which is `o(volume I)` near each point of `s` is equal to
zero on any subinterval of `s`.
-/

variables {ι α β M : Type*}

open set (univ ord_connected pi Icc subinterval) function finset (hiding univ pi) filter
open_locale big_operators topological_space nnreal

/-!
### Definitions and basic properties

In this section we define `box_subadditive_on`, `box_additive_on`, and `box_supadditive_on`, and
prove some basic properties.
-/

/-- A function `f : (ι → α) → (ι → α) → M` is called `box_subadditive_on` a set `s : set (ι → α)`
if for any rectangular box `I ⊆ s` and a hyperplane `x i = c`, `I.left i ≤ c ≤ I.right i`, we have
`f' I ≤ f' (I ∩ {x | x i ≤ c}) + f' (I ∩ {x | c ≤ x i})`, where `f' I` means `f I.left I.right`. -/
def box_subadditive_on [decidable_eq ι] [preorder α] [ordered_add_comm_monoid M]
  (f : (ι → α) → (ι → α) → M) (s : set (ι → α)) :=
∀ ⦃I : subinterval s⦄ ⦃m : ι → α⦄ (hm : m ∈ I) i,
  f I.left I.right ≤ f I.left (update I.right i (m i)) + f (update I.left i (m i)) I.right

/-- A function `f : (ι → α) → (ι → α) → M` is called `box_additive_on` a set `s : set (ι → α)`
if for any rectangular box `I ⊆ s` and a hyperplane `x i = c`, `I.left i ≤ c ≤ I.right i`, we have
`f' (I ∩ {x | x i ≤ c}) + f' (I ∩ {x | c ≤ x i}) = f' I`, where `f' I` means `f I.left I.right`. -/
def box_additive_on [decidable_eq ι] [preorder α] [has_add M] (f : (ι → α) → (ι → α) → M)
  (s : set (ι → α)) :=
∀ ⦃I : subinterval s⦄ ⦃m : ι → α⦄ (hm : m ∈ I) i,
  f I.left (update I.right i (m i)) + f (update I.left i (m i)) I.right = f I.left I.right

/-- A function `f : (ι → α) → (ι → α) → M` is called `box_subadditive_on` a set `s : set (ι → α)`
if for any rectangular box `I ⊆ s` and a hyperplane `x i = c`, `I.left i ≤ c ≤ I.right i`, we have
`f' (I ∩ {x | x i ≤ c}) + f' (I ∩ {x | c ≤ x i}) ≤ f' I`, where `f' I` means `f I.left I.right`. -/
def box_supadditive_on [decidable_eq ι] [preorder α] [ordered_add_comm_monoid M]
  (f : (ι → α) → (ι → α) → M) (s : set (ι → α)) :=
∀ ⦃I : subinterval s⦄ ⦃m : ι → α⦄ (hm : m ∈ I) i,
  f I.left (update I.right i (m i)) + f (update I.left i (m i)) I.right ≤ f I.left I.right

namespace box_subadditive_on

variables [decidable_eq ι] [preorder α] [ordered_add_comm_monoid M] {s : set (ι → α)}
  {f : (ι → α) → (ι → α) → M}

lemma le_sum_finset_subboxes (h : box_subadditive_on f s) (I : s.subinterval) {m} (hm : m ∈ I)
  (t : finset ι) :
  f I.left I.right ≤ ∑ t' in t.powerset,
    f (I.pi_subbox m hm t' (t \ t')).left (I.pi_subbox m hm t' (t \ t')).right :=
begin
  induction t using finset.induction_on with j t hj iht, { simp },
  simp only [sum_powerset_insert hj, piecewise_insert, ← sum_add_distrib],
  refine iht.trans (sum_le_sum $ λ t' ht', _),
  rw [mem_powerset] at ht',
  simp [hj, mt (@ht' _) hj, insert_sdiff_of_not_mem, sdiff_insert_of_not_mem,
    h (I.mem_pi_subbox m hm _ _) j],
end

variables [fintype ι]

/-- Take a rectangular box `[lo, hi]` in `ι → α` and a point `mid ∈ [lo, hi]`. The hyperplanes `x i
= mid i` split the box `[lo, hi]` into `2^n` subboxes, where `n = card ι`.  If `f` is subadditive on
subboxes, then its value on `[lo, hi]` is less than or equal to the sum of its values on these `2^n`
subboxes. -/
lemma le_sum_subboxes (h : box_subadditive_on f s) (I : s.subinterval) {m} (hm : m ∈ I) :
  f I.left I.right ≤ ∑ t : finset ι, f (I.pi_subbox m hm t tᶜ).left (I.pi_subbox m hm t tᶜ).right :=
by simpa using h.le_sum_finset_subboxes I hm finset.univ

end box_subadditive_on

namespace box_additive_on

open set.subinterval

variables {G : Type*} [decidable_eq ι] [preorder α] {s : set (ι → α)}

lemma abs_of_nonneg [linear_ordered_add_comm_group G] {f : (ι → α) → (ι → α) → G}
  (h : box_additive_on f s) (h₀ : ∀ I : subinterval s, 0 ≤ f I.left I.right) :
  box_additive_on (λ x y, abs (f x y)) s :=
begin
  intros I m hm i,
  have A := h₀ (I.pi_subbox m hm ∅ {i}),
  have B := h₀ (I.pi_subbox m hm {i} ∅),
  simp only [pi_subbox_empty_left, pi_subbox_empty_right, pi_subbox_single_right,
    pi_subbox_single_left] at A B,
  simp only [abs_of_nonneg, h hm, *]
end

protected lemma add [add_comm_semigroup M] {f g : (ι → α) → (ι → α) → M}
  (hf : box_additive_on f s) (hg : box_additive_on g s) :
  box_additive_on (f + g) s :=
λ I m hm i, by simp [hf hm i, hg hm i, add_add_add_comm _ (g _ _)]

protected lemma neg [add_comm_group G] {f : (ι → α) → (ι → α) → G} (hf : box_additive_on f s) :
  box_additive_on (-f) s :=
λ I m hm i, by simp [← hf hm i, add_comm]

protected lemma sub [add_comm_group G] {f g : (ι → α) → (ι → α) → G}
  (hf : box_additive_on f s) (hg : box_additive_on g s) :
  box_additive_on (f - g) s :=
hf.add hg.neg

protected lemma prod [fintype ι] {R} [comm_semiring R] (f : α → α → R)
  (hf : ∀ ⦃x y z⦄, x ≤ y → y ≤ z → f x y + f y z = f x z) :
  box_additive_on (λ x y, ∏ i : ι, f (x i) (y i)) s :=
begin
  intros I m hm i,
  have := function.apply_update (λ j, f (I.left j)) I.right i (m i),
  have := function.apply_update (λ j y, f y (I.right j)) I.left i (m i),
  simp only at *,
  simp only [*, prod_update_of_mem, mem_univ, ← add_mul],
  rw [← prod_mul_prod_compl {i}, prod_singleton, compl_eq_univ_sdiff, hf (hm.1 i) (hm.2 i)]
end

protected lemma box_subadditive_on [ordered_add_comm_monoid M] {f : (ι → α) → (ι → α) → M}
  (hf : box_additive_on f s) : box_subadditive_on f s :=
λ I m hm i, (hf hm i).ge

protected lemma box_supadditive_on [ordered_add_comm_monoid M] {f : (ι → α) → (ι → α) → M}
  (hf : box_additive_on f s) : box_supadditive_on f s :=
λ I m hm i, (hf hm i).le

lemma norm_subadditive_on {E : Type*} [normed_group E] {f : (ι → α) → (ι → α) → E}
  (hf : box_additive_on f s) : box_subadditive_on (λ x y, ∥f x y∥) s :=
λ I m hm i, by simp only [← hf hm i, norm_add_le]

end box_additive_on

namespace box_supadditive_on

variables [decidable_eq ι] [preorder α] [ordered_add_comm_monoid M] {s : set (ι → α)}

protected lemma order_dual {f : (ι → α) → (ι → α) → M} (hf : box_supadditive_on f s) :
  @box_subadditive_on ι α (order_dual M) _ _ _ f s :=
hf

variables {f : (ι → α) → (ι → α) → M}

lemma le_sum_finset_subboxes (h : box_supadditive_on f s) (I : s.subinterval) {m} (hm : m ∈ I)
  (t : finset ι) :
  ∑ t' in t.powerset, f (I.pi_subbox m hm t' (t \ t')).left (I.pi_subbox m hm t' (t \ t')).right ≤
    f I.left I.right :=
h.order_dual.le_sum_finset_subboxes  I hm t

variables [fintype ι]

/-- Take a rectangular box `[lo, hi]` in `ι → α` and a point `mid ∈ [lo, hi]`. The hyperplanes `x i
= mid i` split the box `[lo, hi]` into `2^n` subboxes, where `n = card ι`.  If `f` is supadditive on
subboxes, then its value on `[lo, hi]` is greater than or equal to the sum of its values on these
`2^n` subboxes. -/
lemma sum_subboxes_le (h : box_supadditive_on f s) (I : s.subinterval) {m} (hm : m ∈ I) :
  ∑ t : finset ι, f (I.pi_subbox m hm t tᶜ).left (I.pi_subbox m hm t tᶜ).right ≤ f I.left I.right :=
h.order_dual.le_sum_subboxes I hm

end box_supadditive_on

section coe

variables {N : Type*} [decidable_eq ι] [preorder α] {s : set (ι → α)}

lemma box_subsupadditive_coe_helper [add_monoid M] [add_monoid N] {c : M → N} (rM : M → M → Prop)
  (rN : N → N → Prop) (hr : ∀ x y, rN (c x) (c y) ↔ rM x y)
  (hadd : ∀ x y, c (x + y) = c x + c y) {f : (ι → α) → (ι → α) → M} :
  (∀ ⦃I : subinterval s⦄ ⦃m : ι → α⦄ (hm : m ∈ I) i, rN (c $ f I.left I.right) $
    (c $ f I.left (update I.right i (m i))) + (c $ f (update I.left i (m i)) I.right)) ↔
  (∀ ⦃I : subinterval s⦄ ⦃m : ι → α⦄ (hm : m ∈ I) i, rM (f I.left I.right) $
    f I.left (update I.right i (m i)) + f (update I.left i (m i)) I.right) :=
by simp only [← hadd, hr]

variables {f g : (ι → α) → (ι → α) → ℝ≥0}

@[simp, norm_cast]
lemma box_subadditive_on.coe_ennreal :
  box_subadditive_on (λ x y, (f x y : ennreal)) s ↔ box_subadditive_on f s :=
box_subsupadditive_coe_helper (≤) (≤) (λ _ _, ennreal.coe_le_coe) (λ _ _, ennreal.coe_add)

@[simp, norm_cast]
lemma box_additive_on.coe_ennreal :
  box_additive_on (λ l r, (f l r : ennreal)) s ↔ box_additive_on f s :=
box_subsupadditive_coe_helper (flip (=)) (flip (=)) (λ _ _, ennreal.coe_eq_coe)
  (λ _ _, ennreal.coe_add)

@[simp, norm_cast]
lemma box_supadditive_on.coe_ennreal :
  box_supadditive_on (λ l r, (f l r : ennreal)) s ↔ box_supadditive_on f s :=
box_subsupadditive_coe_helper (≥) (≥) (λ _ _, ennreal.coe_le_coe) (λ _ _, ennreal.coe_add)

@[simp, norm_cast]
lemma box_subadditive_on.coe_nnreal :
  box_subadditive_on (λ x y, (f x y : ℝ)) s ↔ box_subadditive_on f s :=
box_subsupadditive_coe_helper (≤) (≤) (λ _ _, nnreal.coe_le_coe) nnreal.coe_add

@[simp, norm_cast]
lemma box_additive_on.coe_nnreal :
  box_additive_on (λ l r, (f l r : ℝ)) s ↔ box_additive_on f s :=
box_subsupadditive_coe_helper (flip (=)) (flip (=)) (λ _ _, nnreal.coe_eq) nnreal.coe_add

@[simp, norm_cast]
lemma box_supadditive_on.coe_nnreal :
  box_supadditive_on (λ l r, (f l r : ℝ)) s ↔ box_supadditive_on f s :=
box_subsupadditive_coe_helper (≥) (≥) (λ _ _, nnreal.coe_le_coe) nnreal.coe_add

end coe

/-!
### Examples of `box_additive`, `box_subadditive, and `box_supadditive` functions
-/

section

open set.subinterval

lemma box_additive_on_prod_sub [decidable_eq ι] [fintype ι] (s : set (ι → ℝ)) :
  box_additive_on (λ l r, ∏ i, (r i - l i)) s :=
box_additive_on.prod (λ x y : ℝ, y - x) $ λ x y z _ _, sub_add_sub_cancel' _ _ _

lemma box_additive_on_prod_dist [decidable_eq ι] [fintype ι] (s : set (ι → ℝ)) :
  box_additive_on (λ l r, ∏ i, dist (l i) (r i)) s :=
by simpa only [real.dist_eq, abs_prod, abs_sub] using (box_additive_on_prod_sub s).abs_of_nonneg
    (λ I, prod_nonneg $ λ i _, sub_nonneg.2 $ I.nontrivial i)

lemma box_additive_on_prod_nndist [decidable_eq ι] [fintype ι] (s : set (ι → ℝ)) :
  box_additive_on (λ l r, ∏ i, nndist (l i) (r i)) s :=
by simpa only [← box_additive_on.coe_nnreal, nnreal.coe_prod, coe_nndist]
  using box_additive_on_prod_dist s

lemma box_additive_on_prod_edist [decidable_eq ι] [fintype ι] (s : set (ι → ℝ)) :
  box_additive_on (λ l r, ∏ i, edist (l i) (r i)) s :=
by simpa only [edist_nndist, ← ennreal.coe_finset_prod, box_additive_on.coe_ennreal]
  using box_additive_on_prod_nndist s

end

namespace box_subadditive_on

section preorder

variables [decidable_eq ι] [fintype ι] [preorder α]
  {s : set (ι → α)} {f g : (ι → α) → (ι → α) → ennreal}
  {I : s.subinterval} {m : ι → α}

lemma exists_subbox_mul_lt_of_mul_lt (hf : box_subadditive_on f s)
  (hg : box_supadditive_on g s) (hm : m ∈ I) {c : ennreal}
  (hlt : c * g I.left I.right < f I.left I.right) :
  ∃ t : finset ι,
    c * g (I.pi_subbox m hm t tᶜ).left (I.pi_subbox m hm t tᶜ).right <
      f (I.pi_subbox m hm t tᶜ).left (I.pi_subbox m hm t tᶜ).right :=
begin
  contrapose! hlt,
  calc f I.left I.right
      ≤ ∑ t : finset ι, f (I.pi_subbox m hm t tᶜ).left (I.pi_subbox m hm t tᶜ).right :
    hf.le_sum_subboxes I hm
  ... ≤ ∑ t : finset ι, c * g (I.pi_subbox m hm t tᶜ).left (I.pi_subbox m hm t tᶜ).right  :
    sum_le_sum (λ t _, hlt t)
  ... = c * ∑ t : finset ι, g (I.pi_subbox m hm t tᶜ).left (I.pi_subbox m hm t tᶜ).right :
    mul_sum.symm
  ... ≤ c * g I.left I.right :
    canonically_ordered_semiring.mul_le_mul_left' (hg.sum_subboxes_le I hm) c
end

end preorder

variables [decidable_eq ι] [fintype ι]

noncomputable theory

variables {s : set (ι → ℝ)}

section ennreal

variables {f g : (ι → ℝ) → (ι → ℝ) → ennreal} {c : ennreal}

/-- An auxiliary sequence of `set.subinterval`s for the proof of
`box_subadditive_on.eq_zero_of_forall_eventually_le_mul`. -/
def seq (hf : box_subadditive_on f s) (hg : box_supadditive_on g s)
  (I : subinterval s) (hI : c * g I.left I.right < f I.left I.right) (n : ℕ) :
  {I : subinterval s // c * g I.left I.right < f I.left I.right} :=
(λ I, ⟨_, (classical.indefinite_description _
  (hf.exists_subbox_mul_lt_of_mul_lt hg (I.1.midpoint_mem ℝ) I.2)).2⟩)^[n] ⟨I, hI⟩

lemma seq_zero (hf : box_subadditive_on f s) (hg : box_supadditive_on g s) (I : subinterval s)
  (hI : c * g I.left I.right < f I.left I.right) :
  ↑(seq hf hg I hI 0) = I := rfl

lemma seq_succ_le (hf : box_subadditive_on f s) (hg : box_supadditive_on g s) (I : subinterval s)
  (hI : c * g I.left I.right < f I.left I.right) (n : ℕ) :
  seq hf hg I hI (n + 1) ≤ seq hf hg I hI n :=
begin
  simp only [seq, iterate_succ_apply'],
  apply set.subinterval.pi_subbox_le
end

lemma size_seq_succ (hf : box_subadditive_on f s) (hg : box_supadditive_on g s) (I : subinterval s)
  (hI : c * g I.left I.right < f I.left I.right) (n : ℕ) :
  (seq hf hg I hI (n + 1) : subinterval s).size = (seq hf hg I hI n : subinterval s).size / 2 :=
begin
  simp only [seq, iterate_succ_apply'],
  apply set.subinterval.size_pi_subbox_midpoint
end

lemma size_seq (hf : box_subadditive_on f s) (hg : box_supadditive_on g s) (I : subinterval s)
  (hI : c * g I.left I.right < f I.left I.right) (n : ℕ) :
  (seq hf hg I hI n : subinterval s).size = I.size / 2 ^ n :=
begin
  induction n with n ihn, { simp [seq_zero] },
  simp [size_seq_succ, ihn, div_div_eq_div_mul, pow_succ']
end

lemma seq_mul_lt (hf : box_subadditive_on f s) (hg : box_supadditive_on g s) (I : subinterval s)
  (hI : c * g I.left I.right < f I.left I.right) (n : ℕ) :
  c * g (seq hf hg I hI n : subinterval s).left (seq hf hg I hI n : subinterval s).right <
    f (seq hf hg I hI n : subinterval s).left (seq hf hg I hI n : subinterval s).right :=
(seq hf hg I hI n).2

lemma tendsto_size_seq (hf : box_subadditive_on f s) (hg : box_supadditive_on g s) 
  (I : subinterval s) (hI : c * g I.left I.right < f I.left I.right) :
  tendsto (λ n, (seq hf hg I hI n : subinterval s).size) at_top (𝓝 0) :=
begin
  simp only [size_seq, div_eq_mul_inv, ← inv_pow'],
  rw [← mul_zero I.size],
  exact tendsto_const_nhds.mul (tendsto_pow_at_top_nhds_0_of_lt_1 (inv_nonneg.2 zero_le_two)
    (inv_lt_one one_lt_two))
end

/-- An auxiliary definition for `box_subadditive_on.eq_zero_of_forall_eventually_le_mul`:
the limit point of the sequence `box_subadditive_on.seq hf hg I hI`. -/
def fix (hf : box_subadditive_on f s) (hg : box_supadditive_on g s) (I : subinterval s)
  (hI : c * g I.left I.right < f I.left I.right) :
  ι → ℝ :=
⨆ n, (seq hf hg I hI n : subinterval s).left

lemma fix_mem_seq (hf : box_subadditive_on f s) (hg : box_supadditive_on g s) (I : subinterval s)
  (hI : c * g I.left I.right < f I.left I.right) (n : ℕ) :
  fix hf hg I hI ∈ (seq hf hg I hI n : subinterval s) :=
set.subinterval.csupr_mem_nat (λ n, seq_succ_le _ _ _ _ n) n

lemma fix_mem (hf : box_subadditive_on f s) (hg : box_supadditive_on g s) (I : subinterval s)
  (hI : c * g I.left I.right < f I.left I.right) :
  fix hf hg I hI ∈ I :=
fix_mem_seq hf hg I hI 0

lemma fix_mem_set (hf : box_subadditive_on f s) (hg : box_supadditive_on g s) (I : subinterval s)
  (hI : c * g I.left I.right < f I.left I.right) :
  fix hf hg I hI ∈ s :=
I.coe_subset $ fix_mem hf hg I hI

lemma tendsto_left_fix (hf : box_subadditive_on f s) (hg : box_supadditive_on g s)
  (I : subinterval s) (hI : c * g I.left I.right < f I.left I.right) :
  tendsto (λ n, (seq hf hg I hI n : subinterval s).left) at_top
    (𝓝[set.Iic (fix hf hg I hI)] (fix hf hg I hI)) :=
begin
  refine tendsto_inf.2 ⟨tendsto_iff_dist_tendsto_zero.2 $
    squeeze_zero (λ _, dist_nonneg) (λ n, _) (tendsto_size_seq hf hg I hI),
    tendsto_principal.2 $ eventually_of_forall $ λ n, (fix_mem_seq hf hg I hI n).1⟩,
  refine (dist_pi_le_iff dist_nonneg).2 (λ i, le_trans _ (dist_le_pi_dist _ _ i)),
  exact real.dist_left_le_of_mem_interval (set.Icc_subset_interval $
    ⟨(fix_mem_seq hf hg I hI _).1 _, (fix_mem_seq hf hg I hI _).2 _⟩)
end

lemma tendsto_right_fix (hf : box_subadditive_on f s) (hg : box_supadditive_on g s)
  (I : subinterval s) (hI : c * g I.left I.right < f I.left I.right) :
  tendsto (λ n, (seq hf hg I hI n : subinterval s).right) at_top
    (𝓝[set.Ici (fix hf hg I hI)] (fix hf hg I hI)) :=
begin
  refine tendsto_inf.2 ⟨tendsto_iff_dist_tendsto_zero.2 $
    squeeze_zero (λ _, dist_nonneg) (λ n, _) (tendsto_size_seq hf hg I hI),
    tendsto_principal.2 $ eventually_of_forall $ λ n, (fix_mem_seq hf hg I hI n).2⟩,
  refine (dist_pi_le_iff dist_nonneg).2 (λ i, le_trans _ (dist_le_pi_dist _ _ i)),
  rw dist_comm,
  exact real.dist_right_le_of_mem_interval (set.Icc_subset_interval $
    ⟨(fix_mem_seq hf hg I hI _).1 _, (fix_mem_seq hf hg I hI _).2 _⟩)
end

lemma frequently_mul_lt (hf : box_subadditive_on f s) (hg : box_supadditive_on g s)
  (I : subinterval s) (hI : c * g I.left I.right < f I.left I.right) :
  ∃ᶠ p in (𝓝[(set.Iic (fix hf hg I hI)).prod (set.Ici (fix hf hg I hI))]
    (fix hf hg I hI, fix hf hg I hI)), c * g (prod.fst p) (prod.snd p) < f p.1 p.2 :=
begin
  rw [nhds_within_prod_eq],
  exact ((tendsto_left_fix hf hg I hI).prod_mk (tendsto_right_fix hf hg I hI)).frequently
    (frequently_of_forall (λ n, seq_mul_lt hf hg I hI n))
end

lemma le_mul_of_forall_eventually_le_mul (hf : box_subadditive_on f s) (hg : box_supadditive_on g s)
  (Hc : ∀ (b ∈ s), ∀ᶠ p in 𝓝[(set.Iic b).prod (set.Ici b)] (b, b),
    f (prod.fst p) p.2 ≤ c * g p.1 p.2) (I : subinterval s) :
  f I.left I.right ≤ c * g I.left I.right :=
begin
  contrapose! Hc,
  simp only [not_eventually, not_le],
  exact ⟨fix hf hg I Hc, fix_mem_set hf hg I Hc, frequently_mul_lt hf hg I Hc⟩
end

lemma eq_zero_of_forall_eventually_le_mul (hf : box_subadditive_on f s)
  (hg : box_supadditive_on g s)
  (Hc : ∀ (b ∈ s) (c : ℝ≥0), 0 < c → ∀ᶠ p in 𝓝[(set.Iic b).prod (set.Ici b)] (b, b),
    f (prod.fst p) p.2 ≤ c * g p.1 p.2) (I : subinterval s) (h_inf : g I.left I.right < ⊤) :
  f I.left I.right = 0 :=
begin
  by_contra h0,
  rcases ennreal.exists_nnreal_pos_mul_lt h_inf.ne h0 with ⟨c, cpos, hc⟩,
  exact hc.not_le (le_mul_of_forall_eventually_le_mul hf hg (λ b hb, Hc b hb _ cpos) I)
end

end ennreal

section normed_group

variables {E F : Type*} [normed_group E] [normed_group F]
  {f : (ι → ℝ) → (ι → ℝ) → E} {g : (ι → ℝ) → (ι → ℝ) → F}

open asymptotics function

lemma eq_zero_of_forall_is_o (hf : box_subadditive_on (λ x y, ∥f x y∥) s)
  (hg : box_supadditive_on (λ x y, ∥g x y∥) s)
  (Hc : ∀ (b ∈ s), is_o (uncurry f) (uncurry g) (𝓝[(set.Iic b).prod (set.Ici b)] (b, b)))
  (I : subinterval s) : f I.left I.right = 0 :=
begin
  simp only [← coe_nnnorm, coe_nnreal, ← coe_ennreal] at hf,
  simp only [← coe_nnnorm, box_supadditive_on.coe_nnreal,
    ← box_supadditive_on.coe_ennreal] at hg,
  rw [← nnnorm_eq_zero, ← ennreal.coe_eq_zero],
  refine eq_zero_of_forall_eventually_le_mul hf hg _ I ennreal.coe_lt_top,
  intros b hb c hc,
  simpa [← coe_nnnorm, uncurry, ← nnreal.coe_mul, ← ennreal.coe_mul] using (Hc b hb).def hc
end

lemma eq_zero_of_forall_is_o_prod (hf : box_subadditive_on (λ x y, ∥f x y∥) s)
  (Hc : ∀ (b ∈ s), is_o (uncurry f) (λ p, ∏ i, (p.1 i - p.2 i))
    (𝓝[(set.Iic b).prod (set.Ici b)] (b, b)))
  (I : subinterval s) : f I.left I.right = 0 :=
begin
  have : box_supadditive_on (λ l r, ∥∏ (i : ι), dist (l i) (r i)∥) s :=
    ((box_additive_on_prod_dist s).abs_of_nonneg
      (λ _, prod_nonneg $ λ _ _, dist_nonneg)).box_supadditive_on,
  refine eq_zero_of_forall_is_o hf this _ I,
  simpa only [dist_eq_norm, ← normed_field.norm_prod, uncurry, is_o_norm_right]
end

end normed_group

end box_subadditive_on
