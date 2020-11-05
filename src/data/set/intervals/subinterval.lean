/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury Kudryashov
-/
import order.conditionally_complete_lattice

/-!
# Closed subintervals of a set

In this file we define the structure `set.subinterval (s : set α)` representing a closed nonempty
subinterval of `s`.

We define the following instances on `set.subinterval s`:

* coercion to `set`,
* `preorder`,
* `partial_order` if `α` is a `partial_order.

Then we restate a few versions of the nested intervals lemma in terms of `set.subinterval`s.

Then we define two operations on subintervals: `set.subinterval.to_subset` and
`set.subinterval.pi_subbox`.

## Implementation notes

We use `finset`s in `set.subinterval.pi_subbox` and related lemmas because this is the setting
useful for `box_subadditive`. If this construction will prove itself useful in some other settings,
we may migrate it to `set`s and `set.piecewise`.

## Tags

closed interval, subinterval
-/

variables {α β ι : Type*}

open function

namespace set

/-- A nonempty closed subinterval of set `α`. -/
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

/-- If `I` is a subinterval of `s` and `I.left ≤ x ≤ y ≤ I.right`, then `[x, y]` is a subinterval of
`s` as well. -/
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

/-- Let `I` be a subinterval of `s : set (ι → α)`; let `m` be a point in `I`.  Let `l` and `r` be
two `finset`s of coordinates. The hyperplanes `x i = m i`, `i ∈ l ∪ r`, split `I` into smaller
boxes. `I.pi_subbox m hm l r` is one of these boxes. It corresponds to the product of
`[I.left i, m i]` over `i` in `r`, `[m i, I.right]` over `i` in `l`, `[I.left i, I.right i]`
over `i` in `(l ∪ r)ᶜ`, and `[m i, m i]` over `i` in `l ∩ r`.

While we do not require `l` and `r` to be disjoint, currently in all applications they are disjoint,
so there are no intervals `[m i, m i]` among projections of `pi_subbox`. -/
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

end subinterval

end set
