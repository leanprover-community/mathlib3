/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import order.preorder_hom

/-!
# Nontrivial intervals

In this file we define `nontrivial_interval α` to be a structure holding two elements
`left right : α` together with a proof `left_lt_right : left < right`. We also define a partial
order on `nontrivial_interval α` based on `I ≤ J ↔ J.left ≤ I.left ∧ I.right ≤ J.right` and four
bundled monotone maps from `nontrivial_interval α` to `set α`:

- `nontrivial_interval.Icc I = set.Icc I.left I.right`;
- `nontrivial_interval.Ico I = set.Ico I.left I.right`;
- `nontrivial_interval.Ioc I = set.Ioc I.left I.right`;
- `nontrivial_interval.Ioo I = set.Ioo I.left I.right`.

## Tags

interval
-/

namespace set

/-- A nontrivial interval is a pair of numbers `(left, right)` together with a proof
`left_lt_right : left < right`. -/
@[ext, protect_proj, nolint inhabited_instance]
structure nontrivial_interval (α : Type*) [has_lt α] :=
(left right : α) (left_lt_right : left < right)

namespace nontrivial_interval

variables {α : Type*}

instance nonempty_of_sup [semilattice_sup α] [nontrivial α] :
  nonempty (nontrivial_interval α) :=
let ⟨a, b, h⟩ := exists_lt_of_sup α in ⟨⟨a, b, h⟩⟩

instance nonempty_of_inf [semilattice_inf α] [nontrivial α] :
  nonempty (nontrivial_interval α) :=
let ⟨a, b, h⟩ := exists_lt_of_inf α in ⟨⟨a, b, h⟩⟩

instance [preorder α] : preorder (nontrivial_interval α) :=
{ le := λ I J, J.left ≤ I.left ∧ I.right ≤ J.right,
  .. preorder.lift (λ I : nontrivial_interval α, (order_dual.to_dual I.left, I.right)) }

instance [partial_order α] : partial_order (nontrivial_interval α) :=
{ .. nontrivial_interval.preorder,
  .. partial_order.lift (λ I : nontrivial_interval α, (order_dual.to_dual I.left, I.right))
    (λ I J h, ext I J (prod.ext_iff.1 h).1 (prod.ext_iff.1 h).2) }

variable [preorder α]

lemma left_le_right (I : nontrivial_interval α) : I.left ≤ I.right := I.left_lt_right.le

lemma le_def {I J : nontrivial_interval α} : I ≤ J ↔ J.left ≤ I.left ∧ I.right ≤ J.right := iff.rfl

lemma antitone_left : antitone (nontrivial_interval.left : nontrivial_interval α → α) :=
λ I J h, h.1

lemma monotone_right : monotone (nontrivial_interval.right : nontrivial_interval α → α) :=
λ I J h, h.2

/-- The closed interval corresponding to `I : nontrivial_interval α`. -/
def Icc : nontrivial_interval α →ₘ set α :=
{ to_fun := λ I, Icc I.left I.right,
  monotone' := λ I J Hle, Icc_subset_Icc Hle.1 Hle.2 }

/-- The closed-open interval corresponding to `I : nontrivial_interval α`. -/
def Ico : nontrivial_interval α →ₘ set α :=
{ to_fun := λ I, Ico I.left I.right,
  monotone' := λ I J Hle, Ico_subset_Ico Hle.1 Hle.2 }

/-- The open-closed interval corresponding to `I : nontrivial_interval α`. -/
def Ioc : nontrivial_interval α →ₘ set α :=
{ to_fun := λ I, Ioc I.left I.right,
  monotone' := λ I J Hle, Ioc_subset_Ioc Hle.1 Hle.2 }

/-- The open interval corresponding to `I : nontrivial_interval α`. -/
def Ioo : nontrivial_interval α →ₘ set α :=
{ to_fun := λ I, Ioo I.left I.right,
  monotone' := λ I J Hle, Ioo_subset_Ioo Hle.1 Hle.2 }

lemma nonempty_Ioo [densely_ordered α] (I : nontrivial_interval α) :
  I.Ioo.nonempty :=
nonempty_Ioo.2 I.left_lt_right

end nontrivial_interval

end set
