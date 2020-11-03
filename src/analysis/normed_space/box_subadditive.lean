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
-/

variables {ι α β M : Type*}

namespace set

open function

@[ext] structure subinterval [preorder α] (s : set α) :=
(left right : α)
(nontrivial : left ≤ right)
(Icc_subset : set.Icc left right ⊆ s)

namespace subinterval

section preorder

variables [preorder α] {s : set α} (I : subinterval s)

instance : has_coe_t (subinterval s) (set α) :=
⟨λ I, Icc I.left I.right⟩

instance : has_mem α (subinterval s) :=
⟨λ x I, x ∈ (I : set α)⟩

@[simp, norm_cast] lemma mem_coe {I : subinterval s} {x : α} :
  x ∈ (I : set α) ↔ x ∈ I :=
iff.rfl

lemma coe_subset : ↑I ⊆ s := I.Icc_subset

lemma coe_nonempty : (I : set α).nonempty := nonempty_Icc.2 I.nontrivial

instance : nonempty (I : set α) := I.coe_nonempty.to_subtype

instance : preorder (subinterval s) :=
{ le := λ I₁ I₂, I₂.left ≤ I₁.left ∧ I₁.right ≤ I₂.right,
  le_refl := λ I, ⟨le_rfl, le_rfl⟩,
  le_trans := λ I₁ I₂ I₃ h₁₂ h₂₃, ⟨h₂₃.1.trans h₁₂.1, h₁₂.2.trans h₂₃.2⟩ }

@[simp, norm_cast]
lemma coe_subset_coe {I₁ I₂ : subinterval s} :
  (I₁ : set α) ⊆ I₂ ↔ I₁ ≤ I₂ :=
Icc_subset_Icc_iff I₁.nontrivial

@[simp, norm_cast]
lemma coe_ssubset_coe {I₁ I₂ : subinterval s} :
  (I₁ : set α) ⊂ I₂ ↔ I₁ < I₂ :=
show (I₁ : set α) < I₂ ↔ I₁ < I₂,
from lt_iff_lt_of_le_iff_le' coe_subset_coe coe_subset_coe

lemma strict_mono_coe : strict_mono (coe : subinterval s → set α) :=
λ _ _, coe_ssubset_coe.2

lemma mono_coe : monotone (coe : subinterval s → set α) :=
λ _ _, coe_subset_coe.2

@[simps] def to_subset (x y : α) (hx : I.left ≤ x) (hxy: x ≤ y) (hy : y ≤ I.right) :
  subinterval s :=
{ left := x,
  right := y,
  nontrivial := hxy,
  Icc_subset := subset.trans (Icc_subset_Icc hx hy) I.Icc_subset }

@[simp] lemma coe_to_subset {x y} (hx : I.left ≤ x) (hxy: x ≤ y) (hy : y ≤ I.right) :
  (I.to_subset x y hx hxy hy : set α) = Icc x y :=
rfl

lemma to_subset_le {x y : α} (hx : I.left ≤ x) (hxy: x ≤ y) (hy : y ≤ I.right) :
  I.to_subset x y hx hxy hy ≤ I :=
⟨hx, hy⟩

end preorder

section partial_order

variables [partial_order α] {s : set α} (I : subinterval s)

instance : partial_order (subinterval s) :=
{ le_antisymm := λ I₁ I₂ I₁₂ I₂₁, ext _ _ (le_antisymm I₂₁.1 I₁₂.1) (le_antisymm I₁₂.2 I₂₁.2),
  .. subinterval.preorder }

lemma injective_coe : injective (coe : subinterval s → set α) :=
λ I₁ I₂ h, le_antisymm (coe_subset_coe.1 h.le) (coe_subset_coe.1 h.ge)

@[simp, norm_cast]
lemma coe_inj {I₁ I₂ : subinterval s} : (I₁ : set α) = I₂ ↔ I₁ = I₂ :=
injective_coe.eq_iff

end partial_order

section conditionally_complete_lattice

variables [conditionally_complete_lattice α] [nonempty β] [semilattice_sup β] {s : set α}

lemma csupr_mem_Inter_coe {f : β → subinterval s} (h : ∀ ⦃i j⦄, i ≤ j → f j ≤ f i) :
  (⨆ i, (f i).left) ∈ ⋂ i, (f i : set α) :=
csupr_mem_Inter_Icc_of_mono_decr_Icc (λ i j hij, coe_subset_coe.2 (h hij)) (λ i, (f i).nontrivial)

lemma csupr_mem_Inter_coe_nat {f : ℕ → subinterval s} (h : ∀ n, f (n + 1) ≤ f n) :
  (⨆ i, (f i).left) ∈ ⋂ i, (f i : set α) :=
csupr_mem_Inter_Icc_of_mono_decr_Icc_nat (λ i, coe_subset_coe.2 (h i)) (λ i, (f i).nontrivial)

lemma csupr_mem {f : β → subinterval s} (h : ∀ ⦃i j⦄, i ≤ j → f j ≤ f i) (n : β) :
  (⨆ i, (f i).left) ∈ f n :=
by simpa only using mem_Inter.1 (csupr_mem_Inter_coe h) n

lemma csupr_mem_nat {f : ℕ → subinterval s} (h : ∀ n, f (n + 1) ≤ f n) (n : ℕ) :
  (⨆ i, (f i).left) ∈ f n :=
by simpa only using mem_Inter.1 (csupr_mem_Inter_coe_nat h) n

end conditionally_complete_lattice

section pi_preorder

variables [preorder α] {s : set (ι → α)}

lemma piecewise_mem {I : subinterval s} {f g : ι → α}
  (hf : f ∈ I) (hg : g ∈ I) (t : finset ι) [Π i, decidable (i ∈ t)] :
  t.piecewise f g ∈ I :=
t.piecewise_mem_Icc_of_mem_of_mem hf hg

variables [decidable_eq ι]

def pi_subbox (I : subinterval s) (m : ι → α) (hm : m ∈ I) (l r : finset ι) : subinterval s :=
I.to_subset (l.piecewise m I.left) (r.piecewise m I.right)
  (l.le_piecewise_of_le_of_le hm.1 le_rfl)
  (l.piecewise_le_of_le_of_le
    (r.le_piecewise_of_le_of_le le_rfl hm.2)
    (r.le_piecewise_of_le_of_le hm.1 I.nontrivial))
  (r.piecewise_le_of_le_of_le hm.2 le_rfl)

variables (I : subinterval s) (m : ι → α) (hm : m ∈ I) (i : ι)

lemma pi_subbox_le (l r) : I.pi_subbox m hm l r ≤ I :=
to_subset_le _ _ _ _

lemma mem_pi_subbox (l r) : m ∈ I.pi_subbox m hm l r :=
⟨l.piecewise_le_of_le_of_le le_rfl hm.1, r.le_piecewise_of_le_of_le le_rfl hm.2⟩

lemma pi_subbox_left (l r : finset ι) : (I.pi_subbox m hm l r).left = l.piecewise m I.left := rfl

lemma pi_subbox_right (l r : finset ι) :
  (I.pi_subbox m hm l r).right = r.piecewise m I.right := rfl

@[simp] lemma pi_subbox_empty_left (t : finset ι) : (I.pi_subbox m hm ∅ t).left = I.left :=
finset.piecewise_empty _ _

@[simp] lemma pi_subbox_empty_right (t : finset ι) : (I.pi_subbox m hm t ∅).right = I.right :=
finset.piecewise_empty _ _

@[simp] lemma pi_subbox_empty_empty : I.pi_subbox m hm ∅ ∅ = I := by ext; simp

@[simp] lemma pi_subbox_single_left (t : finset ι) :
  (I.pi_subbox m hm {i} t).left = update I.left i (m i) :=
finset.piecewise_singleton _ _ _

@[simp] lemma pi_subbox_single_right (t : finset ι) :
  (I.pi_subbox m hm t {i}).right = update I.right i (m i) :=
finset.piecewise_singleton _ _ _

@[simp] lemma pi_subbox_insert_left (l r : finset ι) :
  I.pi_subbox m hm (insert i l) r =
    (I.pi_subbox m hm l r).pi_subbox m (I.mem_pi_subbox m hm l r) {i} ∅ :=
by ext; simp [pi_subbox, finset.piecewise_insert, finset.piecewise_singleton]

@[simp] lemma pi_subbox_insert_right (l r : finset ι) :
  I.pi_subbox m hm l (insert i r) =
    (I.pi_subbox m hm l r).pi_subbox m (I.mem_pi_subbox m hm l r) ∅ {i} :=
by ext; simp [pi_subbox, finset.piecewise_insert, finset.piecewise_singleton]

end pi_preorder

def size [preorder α] [metric_space α] {s : set α} (I : subinterval s) : ℝ :=
dist I.left I.right

protected def midpoint (R : Type*) {V P : Type*} [add_comm_group V] [ring R] [semimodule R V]
  [invertible (2 : R)] [add_torsor V P] [preorder P] {s : set P} (I : subinterval s) : P :=
midpoint R I.left I.right

lemma midpoint_mem (k : Type*) {V : Type*} [ordered_add_comm_group V] [linear_ordered_field k]
  [semimodule k V] [ordered_semimodule k V] {s : set V} (I : subinterval s) :
  I.midpoint k ∈ I :=
⟨left_le_midpoint.2 I.nontrivial, midpoint_le_right.2 I.nontrivial⟩

lemma size_pi_subbox_midpoint [fintype ι] [decidable_eq ι]
  {s : set (ι → ℝ)} (I : subinterval s) (t : finset ι) :
  (I.pi_subbox (I.midpoint ℝ) (I.midpoint_mem ℝ) t tᶜ).size = I.size / 2 :=
begin
  simp only [size, dist_pi_def, pi_subbox_left, pi_subbox_right, subinterval.midpoint],
  norm_cast,
  rw [div_eq_inv_mul, nnreal.mul_finset_sup],
  congr' with i : 2,
  push_cast,
  by_cases hi : i ∈ t,
  { have : i ∉ tᶜ, by simp [hi], simp [*] },
  { simp [*] }
end

end subinterval

end set

open set (univ ord_connected pi Icc subinterval) function finset (hiding univ pi) filter
open_locale big_operators topological_space nnreal

/-!
### Definitions and basic properties

In this section we define `box_subadditive` and `box_supadditive`, and prove some basic
properties of these predicates.
-/


/-- Take two vectors `lo hi : ι → α`, an index `i : ι` and a value `x ∈ [lo i, hi i]`. The
hyperplane `v i = x` splits the box `[lo, hi]` into two subboxes. We say that a function `f` on
pairs of vectors `v : ι → α` is subadditive on boxes if its value on a box is less than or equal to
the sum of its values on the two subboxes described above. -/
def box_subadditive [decidable_eq ι] [preorder α] [ordered_add_comm_monoid M] {s : set (ι → α)}
  (f : subinterval s → M) :=
∀ ⦃I : subinterval s⦄ ⦃m⦄ (hm : m ∈ I) i,
  f I ≤ f (I.pi_subbox m hm ∅ {i}) + f (I.pi_subbox m hm {i} ∅)

/-- Take two vectors `lo hi : ι → α`, an index `i : ι` and a value `x ∈ [lo i, hi i]`. The
hyperplane `v i = x` splits the box `[lo, hi]` into two subboxes. We say that a function `f` on
pairs of vectors `v : ι → α` is supadditive on boxes if the sum of its values on the two subboxes
described above is less than or equal to its value on the original box. -/
def box_supadditive [decidable_eq ι] [preorder α] [ordered_add_comm_monoid M] {s : set (ι → α)}
  (f : subinterval s → M) :=
∀ ⦃I : subinterval s⦄ ⦃m⦄ (hm : m ∈ I) i,
  f (I.pi_subbox m hm ∅ {i}) + f (I.pi_subbox m hm {i} ∅) ≤ f I

def box_subadditive_on [decidable_eq ι] [preorder α] [ordered_add_comm_monoid M]
  (f : (ι → α) → (ι → α) → M) (s : set (ι → α)) :=
box_subadditive (λ I : subinterval s, f I.left I.right)

def box_supadditive_on [decidable_eq ι] [preorder α] [ordered_add_comm_monoid M]
  (f : (ι → α) → (ι → α) → M) (s : set (ι → α)) :=
box_supadditive (λ I : subinterval s, f I.left I.right)

namespace box_subadditive

variables [decidable_eq ι] [preorder α] [ordered_add_comm_monoid M] {s : set (ι → α)}
  {f : s.subinterval → M}

lemma le_sum_finset_subboxes (h : box_subadditive f) (I : s.subinterval) {m} (hm : m ∈ I)
  (t : finset ι) :
  f I ≤ ∑ t' in t.powerset, f (I.pi_subbox m hm t' (t \ t')) :=
begin
  induction t using finset.induction_on with j t hj iht, { simp },
  simp only [sum_powerset_insert hj, piecewise_insert, ← sum_add_distrib],
  refine iht.trans (sum_le_sum $ λ t' ht', _),
  rw [mem_powerset] at ht',
  have hj' : j ∉ t' := mt (@ht' _) hj,
  simp [hj, hj', insert_sdiff_of_not_mem, sdiff_insert_of_not_mem, h _ j]
end

variables [fintype ι]

/-- Take a rectangular box `[lo, hi]` in `ι → α` and a point `mid ∈ [lo, hi]`. The hyperplanes `x i
= mid i` split the box `[lo, hi]` into `2^n` subboxes, where `n = card ι`.  If `f` is subadditive on
subboxes, then its value on `[lo, hi]` is less than or equal to the sum of its values on these `2^n`
subboxes. -/
lemma le_sum_subboxes (h : box_subadditive f) (I : s.subinterval) {m} (hm : m ∈ I) :
  f I ≤ ∑ t : finset ι, f (I.pi_subbox m hm t tᶜ) :=
by simpa using h.le_sum_finset_subboxes I hm finset.univ

end box_subadditive

namespace box_supadditive

variables [decidable_eq ι] [preorder α] [ordered_add_comm_monoid M] {s : set (ι → α)}

protected lemma order_dual {f : s.subinterval → M} (hf : box_supadditive f) :
  @box_subadditive ι α (order_dual M) _ _ _ s f :=
hf

protected lemma abs {f : s.subinterval → ℝ} (hf : box_supadditive f) (h₀ : ∀ I, 0 ≤ f I) :
  box_supadditive (λ I, abs (f I)) :=
by simpa only [abs_of_nonneg (h₀ _)]

variables {f : s.subinterval → M}

lemma le_sum_finset_subboxes (h : box_supadditive f) (I : s.subinterval) {m} (hm : m ∈ I)
  (t : finset ι) :
  ∑ t' in t.powerset, f (I.pi_subbox m hm t' (t \ t')) ≤ f I :=
h.order_dual.le_sum_finset_subboxes  I hm t

variables [fintype ι]

/-- Take a rectangular box `[lo, hi]` in `ι → α` and a point `mid ∈ [lo, hi]`. The hyperplanes `x i
= mid i` split the box `[lo, hi]` into `2^n` subboxes, where `n = card ι`.  If `f` is supadditive on
subboxes, then its value on `[lo, hi]` is greater than or equal to the sum of its values on these
`2^n` subboxes. -/
lemma sum_subboxes_le (h : box_supadditive f) (I : s.subinterval) {m} (hm : m ∈ I) :
  ∑ t : finset ι, f (I.pi_subbox m hm t tᶜ) ≤ f I :=
h.order_dual.le_sum_subboxes I hm

end box_supadditive

section coe

variables {N : Type*} [decidable_eq ι] [preorder α] [ordered_add_comm_monoid M]
  [ordered_add_comm_monoid N] {s : set (ι → α)}

lemma box_subadditive.coe_helper {c : M → N} (hle : ∀ x y, c x ≤ c y ↔ x ≤ y)
  (hadd : ∀ x y, c (x + y) = c x + c y) {f : s.subinterval → M} :
  box_subadditive (c ∘ f) ↔ box_subadditive f :=
begin
  repeat { refine forall_congr (λ _, _) },
  simp only [(∘), ← hadd, hle]
end

lemma box_supadditive.coe_helper {c : M → N} (hle : ∀ x y, c x ≤ c y ↔ x ≤ y)
  (hadd : ∀ x y, c (x + y) = c x + c y) {f : s.subinterval → M} :
  box_supadditive (c ∘ f) ↔ box_supadditive f :=
@box_subadditive.coe_helper _ _ (order_dual M) (order_dual N) _ _ _ _ _ c (λ x y, hle y x) hadd _

variables {f : subinterval s → ℝ≥0} {g : (ι → α) → (ι → α) → ℝ≥0}

@[simp, norm_cast]
lemma box_subadditive.coe_ennreal : box_subadditive (λ I, (f I : ennreal)) ↔ box_subadditive f :=
box_subadditive.coe_helper (λ _ _, ennreal.coe_le_coe) (λ _ _, ennreal.coe_add)

@[simp, norm_cast]
lemma box_subadditive_on.coe_ennreal :
  box_subadditive_on (λ l r, (g l r : ennreal)) s ↔ box_subadditive_on g s :=
box_subadditive.coe_ennreal

@[simp, norm_cast]
lemma box_supadditive.coe_ennreal : box_supadditive (λ I, (f I : ennreal)) ↔ box_supadditive f :=
box_supadditive.coe_helper (λ _ _, ennreal.coe_le_coe) (λ _ _, ennreal.coe_add)

@[simp, norm_cast]
lemma box_supadditive_on.coe_ennreal :
  box_supadditive_on (λ l r, (g l r : ennreal)) s ↔ box_supadditive_on g s :=
box_supadditive.coe_ennreal

@[simp, norm_cast]
lemma box_subadditive.coe_nnreal : box_subadditive (λ I, (f I : ℝ)) ↔ box_subadditive f :=
box_subadditive.coe_helper (λ _ _, nnreal.coe_le_coe) nnreal.coe_add

@[simp, norm_cast]
lemma box_subadditive_on.coe_nnreal :
  box_subadditive_on (λ l r, (g l r : ℝ)) s ↔ box_subadditive_on g s :=
box_subadditive.coe_nnreal

@[simp, norm_cast]
lemma box_supadditive.coe_nnreal : box_supadditive (λ I, (f I : ℝ)) ↔ box_supadditive f :=
box_supadditive.coe_helper (λ _ _, nnreal.coe_le_coe) nnreal.coe_add

@[simp, norm_cast]
lemma box_supadditive_on.coe_nnreal :
  box_supadditive_on (λ l r, (g l r : ℝ)) s ↔ box_supadditive_on g s :=
box_supadditive.coe_nnreal

end coe

/-!
### Examples of `box_supadditive` functions
-/

section

open set.subinterval

lemma box_supadditive_on_prod_sub [decidable_eq ι] [fintype ι] (s : set (ι → ℝ)) :
  box_supadditive_on (λ l r, ∏ i, (r i - l i)) s :=
begin
  refine (λ I m hm i, le_of_eq _),
  simp only [pi_subbox_empty_left, pi_subbox_empty_right, pi_subbox_single_right,
    pi_subbox_single_left],
  have := function.apply_update (λ j y, y - I.left j) I.right i (m i),
  have := function.apply_update (λ j y, I.right j - y) I.left i (m i),
  simp only at *,
  simp only [*, prod_update_of_mem, mem_univ, ← add_mul],
  rw [← prod_mul_prod_compl {i}, prod_singleton, sub_add_sub_cancel', compl_eq_univ_sdiff]
end

lemma box_supadditive_on_prod_dist [decidable_eq ι] [fintype ι] (s : set (ι → ℝ)) :
  box_supadditive_on (λ l r, ∏ i, dist (l i) (r i)) s :=
begin
  have : ∀ (I : subinterval s) i, I.left i ≤ I.right i := λ I i, I.nontrivial i,
  simp only [box_supadditive_on, real.dist_eq, abs_of_nonpos (sub_nonpos.2 $ this _ _), neg_sub],
  apply box_supadditive_on_prod_sub
end

lemma box_supadditive_on_prod_nndist [decidable_eq ι] [fintype ι] (s : set (ι → ℝ)) :
  box_supadditive_on (λ l r, ∏ i, nndist (l i) (r i)) s :=
by simpa only [box_supadditive_on, ← box_supadditive.coe_nnreal, nnreal.coe_prod, coe_nndist]
  using box_supadditive_on_prod_dist s

lemma box_supadditive_on_prod_edist [decidable_eq ι] [fintype ι] (s : set (ι → ℝ)) :
  box_supadditive_on (λ l r, ∏ i, edist (l i) (r i)) s :=
by simpa only [box_supadditive_on, edist_nndist, ← ennreal.coe_finset_prod,
  box_supadditive.coe_ennreal] using box_supadditive_on_prod_nndist s

lemma box_subadditive_norm_of_additive {E : Type*} [decidable_eq ι] [normed_group E] [preorder α]
  (s : set (ι → α)) (f : s.subinterval → E)
  (hf : ∀ I m hm i, f (pi_subbox I m hm ∅ {i}) + f (I.pi_subbox m hm {i} ∅) = f I) :
  box_subadditive (λ I, ∥f I∥) :=
begin
  intros I m hm i,
  simp only [← hf I m hm i, norm_add_le]
end

end

namespace box_subadditive

section preorder

variables [decidable_eq ι] [fintype ι] [preorder α]
  {s : set (ι → α)} {f g : s.subinterval → ennreal}
  {I : s.subinterval} {m : ι → α}

lemma exists_subbox_mul_lt_of_mul_lt (hf : box_subadditive f)
  (hg : box_supadditive g) (hm : m ∈ I) {c : ennreal} (hlt : c * g I < f I) :
  ∃ t : finset ι, c * g (I.pi_subbox m hm t tᶜ) < f (I.pi_subbox m hm t tᶜ) :=
begin
  contrapose! hlt,
  calc f I ≤ ∑ t : finset ι, f (I.pi_subbox m hm t tᶜ) :
    hf.le_sum_subboxes I hm
  ... ≤ ∑ t : finset ι, c * g (I.pi_subbox m hm t tᶜ) :
    sum_le_sum (λ t _, hlt t)
  ... = c * ∑ t : finset ι, g (I.pi_subbox m hm t tᶜ) :
    mul_sum.symm
  ... ≤ c * g I :
    canonically_ordered_semiring.mul_le_mul_left' (hg.sum_subboxes_le I hm) c
end

end preorder

variables [decidable_eq ι] [fintype ι]

noncomputable theory

variables {s : set (ι → ℝ)} {f g : subinterval s → ennreal} {c : ennreal}

def seq (hf : box_subadditive f) (hg : box_supadditive g)
  (I : subinterval s) (hI : c * g I < f I) (n : ℕ) :
  {I : subinterval s // c * g I < f I} :=
(λ I, ⟨_, (classical.indefinite_description _
  (hf.exists_subbox_mul_lt_of_mul_lt hg (I.1.midpoint_mem ℝ) I.2)).2⟩)^[n] ⟨I, hI⟩

lemma seq_zero (hf : box_subadditive f) (hg : box_supadditive g) (I : subinterval s)
  (hI : c * g I < f I) :
  ↑(seq hf hg I hI 0) = I := rfl

lemma seq_succ_le (hf : box_subadditive f) (hg : box_supadditive g) (I : subinterval s)
  (hI : c * g I < f I) (n : ℕ) :
  seq hf hg I hI (n + 1) ≤ seq hf hg I hI n :=
begin
  simp only [seq, iterate_succ_apply'],
  apply set.subinterval.pi_subbox_le
end

lemma size_seq_succ (hf : box_subadditive f) (hg : box_supadditive g) (I : subinterval s)
  (hI : c * g I < f I) (n : ℕ) :
  (seq hf hg I hI (n + 1) : subinterval s).size = (seq hf hg I hI n : subinterval s).size / 2 :=
begin
  simp only [seq, iterate_succ_apply'],
  apply set.subinterval.size_pi_subbox_midpoint
end

lemma size_seq (hf : box_subadditive f) (hg : box_supadditive g) (I : subinterval s)
  (hI : c * g I < f I) (n : ℕ) :
  (seq hf hg I hI n : subinterval s).size = I.size / 2 ^ n :=
begin
  induction n with n ihn, { simp [seq_zero] },
  simp [size_seq_succ, ihn, div_div_eq_div_mul, pow_succ']
end

lemma seq_mul_lt (hf : box_subadditive f) (hg : box_supadditive g) (I : subinterval s)
  (hI : c * g I < f I) (n : ℕ) :
  c * g (seq hf hg I hI n) < f (seq hf hg I hI n) :=
(seq hf hg I hI n).2

lemma tendsto_size_seq (hf : box_subadditive f) (hg : box_supadditive g) (I : subinterval s)
  (hI : c * g I < f I) :
  tendsto (λ n, (seq hf hg I hI n : subinterval s).size) at_top (𝓝 0) :=
begin
  simp only [size_seq, div_eq_mul_inv, ← inv_pow'],
  rw [← mul_zero I.size],
  exact tendsto_const_nhds.mul (tendsto_pow_at_top_nhds_0_of_lt_1 (inv_nonneg.2 zero_le_two)
    (inv_lt_one one_lt_two))
end

def fix (hf : box_subadditive f) (hg : box_supadditive g) (I : subinterval s)
  (hI : c * g I < f I) :
  ι → ℝ :=
⨆ n, (seq hf hg I hI n : subinterval s).left

lemma fix_mem_seq (hf : box_subadditive f) (hg : box_supadditive g) (I : subinterval s)
  (hI : c * g I < f I) (n : ℕ) :
  fix hf hg I hI ∈ (seq hf hg I hI n : subinterval s) :=
set.subinterval.csupr_mem_nat (λ n, seq_succ_le _ _ _ _ n) n

lemma fix_mem (hf : box_subadditive f) (hg : box_supadditive g) (I : subinterval s)
  (hI : c * g I < f I) :
  fix hf hg I hI ∈ I :=
fix_mem_seq hf hg I hI 0

lemma fix_mem_set (hf : box_subadditive f) (hg : box_supadditive g) (I : subinterval s)
  (hI : c * g I < f I) :
  fix hf hg I hI ∈ s :=
I.coe_subset $ fix_mem hf hg I hI

lemma tendsto_left_fix (hf : box_subadditive f) (hg : box_supadditive g) (I : subinterval s)
  (hI : c * g I < f I) :
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

lemma tendsto_right_fix (hf : box_subadditive f) (hg : box_supadditive g) (I : subinterval s)
  (hI : c * g I < f I) :
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

end box_subadditive

namespace box_subadditive_on

variables [decidable_eq ι] [fintype ι] {s : set (ι → ℝ)} {c : ennreal}

open box_subadditive

section ennreal

variables {f g : (ι → ℝ) → (ι → ℝ) → ennreal}

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
    (box_supadditive_on_prod_dist s).abs (λ _, prod_nonneg $ λ _ _, dist_nonneg),
  refine eq_zero_of_forall_is_o hf this _ I,
  simpa only [dist_eq_norm, ← normed_field.norm_prod, uncurry, is_o_norm_right]
end

end normed_group

end box_subadditive_on
