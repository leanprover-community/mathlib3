/-
Copyright (c) 2021 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Bryan Gin-ge Chen, Yaël Dillies
-/

import order.boolean_algebra
import logic.equiv.basic

/-!
# Symmetric difference and bi-implication

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the symmetric difference and bi-implication operators in (co-)Heyting algebras.

## Examples

Some examples are
* The symmetric difference of two sets is the set of elements that are in either but not both.
* The symmetric difference on propositions is `xor`.
* The symmetric difference on `bool` is `bxor`.
* The equivalence of propositions. Two propositions are equivalent if they imply each other.
* The symmetric difference translates to addition when considering a Boolean algebra as a Boolean
  ring.

## Main declarations

* `symm_diff`: The symmetric difference operator, defined as `(a \ b) ⊔ (b \ a)`
* `bihimp`: The bi-implication operator, defined as `(b ⇨ a) ⊓ (a ⇨ b)`

In generalized Boolean algebras, the symmetric difference operator is:

* `symm_diff_comm`: commutative, and
* `symm_diff_assoc`: associative.

## Notations

* `a ∆ b`: `symm_diff a b`
* `a ⇔ b`: `bihimp a b`

## References

The proof of associativity follows the note "Associativity of the Symmetric Difference of Sets: A
Proof from the Book" by John McCuan:

* <https://people.math.gatech.edu/~mccuan/courses/4317/symmetricdifference.pdf>

## Tags

boolean ring, generalized boolean algebra, boolean algebra, symmetric difference, bi-implication,
Heyting
-/

open function order_dual

variables {ι α β : Type*} {π : ι → Type*}

/-- The symmetric difference operator on a type with `⊔` and `\` is `(A \ B) ⊔ (B \ A)`. -/
def symm_diff [has_sup α] [has_sdiff α] (a b : α) : α := a \ b ⊔ b \ a

/-- The Heyting bi-implication is `(b ⇨ a) ⊓ (a ⇨ b)`. This generalizes equivalence of
propositions. -/
def bihimp [has_inf α] [has_himp α] (a b : α) : α := (b ⇨ a) ⊓ (a ⇨ b)

/- This notation might conflict with the Laplacian once we have it. Feel free to put it in locale
`order` or `symm_diff` if that happens. -/
infix ` ∆ `:100 := symm_diff
infix ` ⇔ `:100 := bihimp

lemma symm_diff_def [has_sup α] [has_sdiff α] (a b : α) : a ∆ b = (a \ b) ⊔ (b \ a) := rfl
lemma bihimp_def [has_inf α] [has_himp α] (a b : α) : a ⇔ b = (b ⇨ a) ⊓ (a ⇨ b):= rfl

lemma symm_diff_eq_xor (p q : Prop) : p ∆ q = xor p q := rfl
@[simp] lemma bihimp_iff_iff {p q : Prop} : p ⇔ q ↔ (p ↔ q) :=
(iff_iff_implies_and_implies _ _).symm.trans iff.comm

@[simp] lemma bool.symm_diff_eq_bxor : ∀ p q : bool, p ∆ q = bxor p q := dec_trivial

section generalized_coheyting_algebra
variables [generalized_coheyting_algebra α] (a b c d : α)

@[simp] lemma to_dual_symm_diff : to_dual (a ∆ b) = to_dual a ⇔ to_dual b := rfl
@[simp] lemma of_dual_bihimp (a b : αᵒᵈ) : of_dual (a ⇔ b) = of_dual a ∆ of_dual b := rfl

lemma symm_diff_comm : a ∆ b = b ∆ a := by simp only [(∆), sup_comm]

instance symm_diff_is_comm : is_commutative α (∆) := ⟨symm_diff_comm⟩

@[simp] lemma symm_diff_self : a ∆ a = ⊥ := by rw [(∆), sup_idem, sdiff_self]
@[simp] lemma symm_diff_bot : a ∆ ⊥ = a := by rw [(∆), sdiff_bot, bot_sdiff, sup_bot_eq]
@[simp] lemma bot_symm_diff : ⊥ ∆ a = a := by rw [symm_diff_comm, symm_diff_bot]

@[simp] lemma symm_diff_eq_bot {a b : α} : a ∆ b = ⊥ ↔ a = b :=
by simp_rw [symm_diff, sup_eq_bot_iff, sdiff_eq_bot_iff, le_antisymm_iff]

lemma symm_diff_of_le {a b : α} (h : a ≤ b) : a ∆ b = b \ a :=
by rw [symm_diff, sdiff_eq_bot_iff.2 h, bot_sup_eq]

lemma symm_diff_of_ge {a b : α} (h : b ≤ a) : a ∆ b = a \ b :=
by rw [symm_diff, sdiff_eq_bot_iff.2 h, sup_bot_eq]

lemma symm_diff_le {a b c : α} (ha : a ≤ b ⊔ c) (hb : b ≤ a ⊔ c) : a ∆ b ≤ c :=
sup_le (sdiff_le_iff.2 ha) $ sdiff_le_iff.2 hb

lemma symm_diff_le_iff {a b c : α} : a ∆ b ≤ c ↔ a ≤ b ⊔ c ∧ b ≤ a ⊔ c :=
by simp_rw [symm_diff, sup_le_iff, sdiff_le_iff]

@[simp] lemma symm_diff_le_sup {a b : α} : a ∆ b ≤ a ⊔ b := sup_le_sup sdiff_le sdiff_le

lemma symm_diff_eq_sup_sdiff_inf : a ∆ b = (a ⊔ b) \ (a ⊓ b) := by simp [sup_sdiff, symm_diff]

lemma disjoint.symm_diff_eq_sup {a b : α} (h : disjoint a b) : a ∆ b = a ⊔ b :=
by rw [(∆), h.sdiff_eq_left, h.sdiff_eq_right]

lemma symm_diff_sdiff : (a ∆ b) \ c = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) :=
by rw [symm_diff, sup_sdiff_distrib, sdiff_sdiff_left, sdiff_sdiff_left]

@[simp] lemma symm_diff_sdiff_inf : a ∆ b \ (a ⊓ b) = a ∆ b :=
by { rw symm_diff_sdiff, simp [symm_diff] }

@[simp] lemma symm_diff_sdiff_eq_sup : a ∆ (b \ a) = a ⊔ b :=
begin
  rw [symm_diff, sdiff_idem],
  exact le_antisymm (sup_le_sup sdiff_le sdiff_le)
    (sup_le le_sdiff_sup $ le_sdiff_sup.trans $ sup_le le_sup_right le_sdiff_sup),
end

@[simp] lemma sdiff_symm_diff_eq_sup : (a \ b) ∆ b = a ⊔ b :=
by rw [symm_diff_comm, symm_diff_sdiff_eq_sup, sup_comm]

@[simp] lemma symm_diff_sup_inf : a ∆ b ⊔ a ⊓ b = a ⊔ b :=
begin
  refine le_antisymm (sup_le symm_diff_le_sup inf_le_sup) _,
  rw [sup_inf_left, symm_diff],
  refine sup_le (le_inf le_sup_right _) (le_inf _ le_sup_right),
  { rw sup_right_comm,
    exact le_sup_of_le_left le_sdiff_sup },
  { rw sup_assoc,
    exact le_sup_of_le_right le_sdiff_sup }
end

@[simp] lemma inf_sup_symm_diff : a ⊓ b ⊔ a ∆ b = a ⊔ b := by rw [sup_comm, symm_diff_sup_inf]

@[simp] lemma symm_diff_symm_diff_inf : a ∆ b ∆ (a ⊓ b) = a ⊔ b :=
by rw [←symm_diff_sdiff_inf a, sdiff_symm_diff_eq_sup, symm_diff_sup_inf]

@[simp] lemma inf_symm_diff_symm_diff : (a ⊓ b) ∆ (a ∆ b) = a ⊔ b :=
by rw [symm_diff_comm, symm_diff_symm_diff_inf]

lemma symm_diff_triangle : a ∆ c ≤ a ∆ b ⊔ b ∆ c :=
begin
  refine (sup_le_sup (sdiff_triangle a b c) $ sdiff_triangle _ b _).trans_eq _,
  rw [@sup_comm _ _ (c \ b), sup_sup_sup_comm, symm_diff, symm_diff],
end

end generalized_coheyting_algebra

section generalized_heyting_algebra
variables [generalized_heyting_algebra α] (a b c d : α)

@[simp] lemma to_dual_bihimp : to_dual (a ⇔ b) = to_dual a ∆ to_dual b := rfl
@[simp] lemma of_dual_symm_diff (a b : αᵒᵈ) : of_dual (a ∆ b) = of_dual a ⇔ of_dual b := rfl

lemma bihimp_comm : a ⇔ b = b ⇔ a := by simp only [(⇔), inf_comm]

instance bihimp_is_comm : is_commutative α (⇔) := ⟨bihimp_comm⟩

@[simp] lemma bihimp_self : a ⇔ a = ⊤ := by rw [(⇔), inf_idem, himp_self]
@[simp] lemma bihimp_top : a ⇔ ⊤ = a := by rw [(⇔), himp_top, top_himp, inf_top_eq]
@[simp] lemma top_bihimp : ⊤ ⇔ a = a := by rw [bihimp_comm, bihimp_top]

@[simp] lemma bihimp_eq_top {a b : α} : a ⇔ b = ⊤ ↔ a = b := @symm_diff_eq_bot αᵒᵈ _ _ _

lemma bihimp_of_le {a b : α} (h : a ≤ b) : a ⇔ b = b ⇨ a :=
by rw [bihimp, himp_eq_top_iff.2 h, inf_top_eq]

lemma bihimp_of_ge {a b : α} (h : b ≤ a) : a ⇔ b = a ⇨ b :=
by rw [bihimp, himp_eq_top_iff.2 h, top_inf_eq]

lemma le_bihimp {a b c : α} (hb : a ⊓ b ≤ c) (hc : a ⊓ c ≤ b) : a ≤ b ⇔ c :=
le_inf (le_himp_iff.2 hc) $ le_himp_iff.2 hb

lemma le_bihimp_iff {a b c : α} : a ≤ b ⇔ c ↔ a ⊓ b ≤ c ∧ a ⊓ c ≤ b :=
by simp_rw [bihimp, le_inf_iff, le_himp_iff, and.comm]

@[simp] lemma inf_le_bihimp {a b : α} : a ⊓ b ≤ a ⇔ b := inf_le_inf le_himp le_himp

lemma bihimp_eq_inf_himp_inf : a ⇔ b = (a ⊔ b) ⇨ (a ⊓ b) := by simp [himp_inf_distrib, bihimp]

lemma codisjoint.bihimp_eq_inf {a b : α} (h : codisjoint a b) : a ⇔ b = a ⊓ b :=
by rw [(⇔), h.himp_eq_left, h.himp_eq_right]

lemma himp_bihimp : a ⇨ (b ⇔ c) = ((a ⊓ c) ⇨ b) ⊓ ((a ⊓ b) ⇨ c) :=
by rw [bihimp, himp_inf_distrib, himp_himp, himp_himp]

@[simp] lemma sup_himp_bihimp : (a ⊔ b) ⇨ (a ⇔ b) = a ⇔ b :=
by { rw himp_bihimp, simp [bihimp] }

@[simp] lemma bihimp_himp_eq_inf : a ⇔ (a ⇨ b) = a ⊓ b := @symm_diff_sdiff_eq_sup αᵒᵈ _ _ _
@[simp] lemma himp_bihimp_eq_inf : (b ⇨ a) ⇔ b = a ⊓ b := @sdiff_symm_diff_eq_sup αᵒᵈ _ _ _

@[simp] lemma bihimp_inf_sup : a ⇔ b ⊓ (a ⊔ b) = a ⊓ b := @symm_diff_sup_inf αᵒᵈ _ _ _
@[simp] lemma sup_inf_bihimp : (a ⊔ b) ⊓ a ⇔ b = a ⊓ b := @inf_sup_symm_diff αᵒᵈ _ _ _

@[simp] lemma bihimp_bihimp_sup : a ⇔ b ⇔ (a ⊔ b) = a ⊓ b := @symm_diff_symm_diff_inf αᵒᵈ _ _ _
@[simp] lemma sup_bihimp_bihimp : (a ⊔ b) ⇔ (a ⇔ b) = a ⊓ b := @inf_symm_diff_symm_diff αᵒᵈ _ _ _

lemma bihimp_triangle : a ⇔ b ⊓ b ⇔ c ≤ a ⇔ c := @symm_diff_triangle αᵒᵈ _ _ _ _

end generalized_heyting_algebra

section coheyting_algebra
variables [coheyting_algebra α] (a : α)

@[simp] lemma symm_diff_top' : a ∆ ⊤ = ￢a := by simp [symm_diff]
@[simp] lemma top_symm_diff' : ⊤ ∆ a = ￢a := by simp [symm_diff]

@[simp] lemma hnot_symm_diff_self : (￢a) ∆ a = ⊤ :=
begin
  rw [eq_top_iff, symm_diff, hnot_sdiff, sup_sdiff_self],
  exact codisjoint.top_le codisjoint_hnot_left
end

@[simp] lemma symm_diff_hnot_self : a ∆ ￢a = ⊤ := by rw [symm_diff_comm, hnot_symm_diff_self]

lemma is_compl.symm_diff_eq_top {a b : α} (h : is_compl a b) : a ∆ b = ⊤ :=
by rw [h.eq_hnot, hnot_symm_diff_self]

end coheyting_algebra

section heyting_algebra
variables [heyting_algebra α] (a : α)

@[simp] lemma bihimp_bot : a ⇔ ⊥ = aᶜ := by simp [bihimp]
@[simp] lemma bot_bihimp : ⊥ ⇔ a = aᶜ := by simp [bihimp]

@[simp] lemma compl_bihimp_self : aᶜ ⇔ a = ⊥ := @hnot_symm_diff_self αᵒᵈ _ _
@[simp] lemma bihimp_hnot_self : a ⇔ aᶜ = ⊥ := @symm_diff_hnot_self αᵒᵈ _ _

lemma is_compl.bihimp_eq_bot {a b : α} (h : is_compl a b) : a ⇔ b = ⊥ :=
by rw [h.eq_compl, compl_bihimp_self]

end heyting_algebra

section generalized_boolean_algebra
variables [generalized_boolean_algebra α] (a b c d : α)

@[simp] lemma sup_sdiff_symm_diff : (a ⊔ b) \ (a ∆ b) = a ⊓ b :=
sdiff_eq_symm inf_le_sup (by rw symm_diff_eq_sup_sdiff_inf)

lemma disjoint_symm_diff_inf : disjoint (a ∆ b) (a ⊓ b) :=
begin
  rw [symm_diff_eq_sup_sdiff_inf],
  exact disjoint_sdiff_self_left,
end

lemma inf_symm_diff_distrib_left : a ⊓ (b ∆ c) = (a ⊓ b) ∆ (a ⊓ c) :=
by rw [symm_diff_eq_sup_sdiff_inf, inf_sdiff_distrib_left, inf_sup_left, inf_inf_distrib_left,
  symm_diff_eq_sup_sdiff_inf]

lemma inf_symm_diff_distrib_right : (a ∆ b) ⊓ c = (a ⊓ c) ∆ (b ⊓ c) :=
by simp_rw [@inf_comm _ _ _ c, inf_symm_diff_distrib_left]

lemma sdiff_symm_diff : c \ (a ∆ b) = (c ⊓ a ⊓ b) ⊔ ((c \ a) ⊓ (c \ b)) :=
by simp only [(∆), sdiff_sdiff_sup_sdiff']

lemma sdiff_symm_diff' : c \ (a ∆ b) = (c ⊓ a ⊓ b) ⊔ (c \ (a ⊔ b)) :=
by rw [sdiff_symm_diff, sdiff_sup, sup_comm]

@[simp] lemma symm_diff_sdiff_left : (a ∆ b) \ a = b \ a :=
by rw [symm_diff_def, sup_sdiff, sdiff_idem, sdiff_sdiff_self, bot_sup_eq]

@[simp] lemma symm_diff_sdiff_right : (a ∆ b) \ b = a \ b :=
by rw [symm_diff_comm, symm_diff_sdiff_left]

@[simp] lemma sdiff_symm_diff_left : a \ (a ∆ b) = a ⊓ b := by simp [sdiff_symm_diff]
@[simp] lemma sdiff_symm_diff_right : b \ (a ∆ b) = a ⊓ b :=
by rw [symm_diff_comm, inf_comm, sdiff_symm_diff_left]

lemma symm_diff_eq_sup : a ∆ b = a ⊔ b ↔ disjoint a b :=
begin
  refine ⟨λ h, _, disjoint.symm_diff_eq_sup⟩,
  rw [symm_diff_eq_sup_sdiff_inf, sdiff_eq_self_iff_disjoint] at h,
  exact h.of_disjoint_inf_of_le le_sup_left,
end

@[simp] lemma le_symm_diff_iff_left : a ≤ a ∆ b ↔ disjoint a b :=
begin
  refine ⟨λ h, _, λ h, h.symm_diff_eq_sup.symm ▸ le_sup_left⟩,
  rw symm_diff_eq_sup_sdiff_inf at h,
  exact disjoint_iff_inf_le.mpr (le_sdiff_iff.1 $ inf_le_of_left_le h).le,
end

@[simp] lemma le_symm_diff_iff_right : b ≤ a ∆ b ↔ disjoint a b :=
by rw [symm_diff_comm, le_symm_diff_iff_left, disjoint.comm]

lemma symm_diff_symm_diff_left :
  a ∆ b ∆ c = (a \ (b ⊔ c)) ⊔ (b \ (a ⊔ c)) ⊔ (c \ (a ⊔ b)) ⊔ (a ⊓ b ⊓ c) :=
calc a ∆ b ∆ c = ((a ∆ b) \ c) ⊔ (c \ (a ∆ b))   : symm_diff_def _ _
           ... = (a \ (b ⊔ c)) ⊔ (b \ (a ⊔ c)) ⊔
                   ((c \ (a ⊔ b)) ⊔ (c ⊓ a ⊓ b)) :
                                by rw [sdiff_symm_diff', @sup_comm _ _ (c ⊓ a ⊓ b), symm_diff_sdiff]
           ... = (a \ (b ⊔ c)) ⊔ (b \ (a ⊔ c)) ⊔
                   (c \ (a ⊔ b)) ⊔ (a ⊓ b ⊓ c)   : by ac_refl

lemma symm_diff_symm_diff_right :
  a ∆ (b ∆ c) = (a \ (b ⊔ c)) ⊔ (b \ (a ⊔ c)) ⊔ (c \ (a ⊔ b)) ⊔ (a ⊓ b ⊓ c) :=
calc a ∆ (b ∆ c) = (a \ (b ∆ c)) ⊔ ((b ∆ c) \ a) : symm_diff_def _ _
             ... = (a \ (b ⊔ c)) ⊔ (a ⊓ b ⊓ c) ⊔
                     (b \ (c ⊔ a) ⊔ c \ (b ⊔ a))   :
                                by rw [sdiff_symm_diff', @sup_comm _ _ (a ⊓ b ⊓ c), symm_diff_sdiff]
             ... = (a \ (b ⊔ c)) ⊔ (b \ (a ⊔ c)) ⊔
                     (c \ (a ⊔ b)) ⊔ (a ⊓ b ⊓ c)   : by ac_refl

lemma symm_diff_assoc : a ∆ b ∆ c = a ∆ (b ∆ c) :=
by rw [symm_diff_symm_diff_left, symm_diff_symm_diff_right]

instance symm_diff_is_assoc : is_associative α (∆) := ⟨symm_diff_assoc⟩

lemma symm_diff_left_comm : a ∆ (b ∆ c) = b ∆ (a ∆ c) :=
by simp_rw [←symm_diff_assoc, symm_diff_comm]

lemma symm_diff_right_comm : a ∆ b ∆ c = a ∆ c ∆ b := by simp_rw [symm_diff_assoc, symm_diff_comm]

lemma symm_diff_symm_diff_symm_diff_comm : (a ∆ b) ∆ (c ∆ d) = (a ∆ c) ∆ (b ∆ d) :=
by simp_rw [symm_diff_assoc, symm_diff_left_comm]

@[simp] lemma symm_diff_symm_diff_cancel_left : a ∆ (a ∆ b) = b := by simp [←symm_diff_assoc]
@[simp] lemma symm_diff_symm_diff_cancel_right : b ∆ a ∆ a = b := by simp [symm_diff_assoc]

@[simp] lemma symm_diff_symm_diff_self' : a ∆ b ∆ a = b :=
by rw [symm_diff_comm,symm_diff_symm_diff_cancel_left]

lemma symm_diff_left_involutive (a : α) : involutive (∆ a) := symm_diff_symm_diff_cancel_right _
lemma symm_diff_right_involutive (a : α) : involutive ((∆) a) := symm_diff_symm_diff_cancel_left _
lemma symm_diff_left_injective (a : α) : injective (∆ a) := (symm_diff_left_involutive _).injective
lemma symm_diff_right_injective (a : α) : injective ((∆) a) :=
(symm_diff_right_involutive _).injective
lemma symm_diff_left_surjective (a : α) : surjective (∆ a) :=
(symm_diff_left_involutive _).surjective
lemma symm_diff_right_surjective (a : α) : surjective ((∆) a) :=
(symm_diff_right_involutive _).surjective

variables {a b c}

@[simp] lemma symm_diff_left_inj : a ∆ b = c ∆ b ↔ a = c := (symm_diff_left_injective _).eq_iff
@[simp] lemma symm_diff_right_inj : a ∆ b = a ∆ c ↔ b = c := (symm_diff_right_injective _).eq_iff

@[simp] lemma symm_diff_eq_left : a ∆ b = a ↔ b = ⊥ :=
calc a ∆ b = a ↔ a ∆ b = a ∆ ⊥ : by rw symm_diff_bot
           ... ↔     b = ⊥     : by rw symm_diff_right_inj

@[simp] lemma symm_diff_eq_right : a ∆ b = b ↔ a = ⊥ := by rw [symm_diff_comm, symm_diff_eq_left]

protected lemma disjoint.symm_diff_left (ha : disjoint a c) (hb : disjoint b c) :
  disjoint (a ∆ b) c :=
by { rw symm_diff_eq_sup_sdiff_inf, exact (ha.sup_left hb).disjoint_sdiff_left }

protected lemma disjoint.symm_diff_right (ha : disjoint a b) (hb : disjoint a c) :
  disjoint a (b ∆ c) :=
(ha.symm.symm_diff_left hb.symm).symm

lemma symm_diff_eq_iff_sdiff_eq (ha : a ≤ c) : a ∆ b = c ↔ c \ a = b :=
begin
  rw ←symm_diff_of_le ha,
  exact ((symm_diff_right_involutive a).to_perm _).apply_eq_iff_eq_symm_apply.trans eq_comm,
end

end generalized_boolean_algebra

section boolean_algebra
variables [boolean_algebra α] (a b c d : α)

/- `cogeneralized_boolean_algebra` isn't actually a typeclass, but the lemmas in here are dual to
the `generalized_boolean_algebra` ones -/
section cogeneralized_boolean_algebra

@[simp] lemma inf_himp_bihimp : (a ⇔ b) ⇨ (a ⊓ b) = a ⊔ b := @sup_sdiff_symm_diff αᵒᵈ _ _ _

lemma codisjoint_bihimp_sup : codisjoint (a ⇔ b) (a ⊔ b) := @disjoint_symm_diff_inf αᵒᵈ _ _ _

@[simp] lemma himp_bihimp_left : a ⇨ (a ⇔ b) = a ⇨ b := @symm_diff_sdiff_left αᵒᵈ _ _ _
@[simp] lemma himp_bihimp_right : b ⇨ (a ⇔ b) = b ⇨ a := @symm_diff_sdiff_right αᵒᵈ _ _ _

@[simp] lemma bihimp_himp_left : (a ⇔ b) ⇨ a = a ⊔ b := @sdiff_symm_diff_left αᵒᵈ _ _ _
@[simp] lemma bihimp_himp_right : (a ⇔ b) ⇨ b = a ⊔ b := @sdiff_symm_diff_right αᵒᵈ _ _ _

@[simp] lemma bihimp_eq_inf : a ⇔ b = a ⊓ b ↔ codisjoint a b := @symm_diff_eq_sup αᵒᵈ _ _ _

@[simp] lemma bihimp_le_iff_left : a ⇔ b ≤ a ↔ codisjoint a b := @le_symm_diff_iff_left αᵒᵈ _ _ _
@[simp] lemma bihimp_le_iff_right : a ⇔ b ≤ b ↔ codisjoint a b := @le_symm_diff_iff_right αᵒᵈ _ _ _

lemma bihimp_assoc : a ⇔ b ⇔ c = a ⇔ (b ⇔ c) := @symm_diff_assoc αᵒᵈ _ _ _ _

instance bihimp_is_assoc : is_associative α (⇔) := ⟨bihimp_assoc⟩

lemma bihimp_left_comm : a ⇔ (b ⇔ c) = b ⇔ (a ⇔ c) := by simp_rw [←bihimp_assoc, bihimp_comm]
lemma bihimp_right_comm : a ⇔ b ⇔ c = a ⇔ c ⇔ b := by simp_rw [bihimp_assoc, bihimp_comm]

lemma bihimp_bihimp_bihimp_comm : (a ⇔ b) ⇔ (c ⇔ d) = (a ⇔ c) ⇔ (b ⇔ d) :=
by simp_rw [bihimp_assoc, bihimp_left_comm]

@[simp] lemma bihimp_bihimp_cancel_left : a ⇔ (a ⇔ b) = b := by simp [←bihimp_assoc]
@[simp] lemma bihimp_bihimp_cancel_right : b ⇔ a ⇔ a = b := by simp [bihimp_assoc]

@[simp] lemma bihimp_bihimp_self : a ⇔ b ⇔ a = b := by rw [bihimp_comm, bihimp_bihimp_cancel_left]

lemma bihimp_left_involutive (a : α) : involutive (⇔ a) := bihimp_bihimp_cancel_right _
lemma bihimp_right_involutive (a : α) : involutive ((⇔) a) := bihimp_bihimp_cancel_left _
lemma bihimp_left_injective (a : α) : injective (⇔ a) := @symm_diff_left_injective αᵒᵈ  _ _
lemma bihimp_right_injective (a : α) : injective ((⇔) a) := @symm_diff_right_injective αᵒᵈ  _ _
lemma bihimp_left_surjective (a : α) : surjective (⇔ a) := @symm_diff_left_surjective αᵒᵈ  _ _
lemma bihimp_right_surjective (a : α) : surjective ((⇔) a) := @symm_diff_right_surjective αᵒᵈ  _ _

variables {a b c}

@[simp] lemma bihimp_left_inj : a ⇔ b = c ⇔ b ↔ a = c := (bihimp_left_injective _).eq_iff
@[simp] lemma bihimp_right_inj : a ⇔ b = a ⇔ c ↔ b = c := (bihimp_right_injective _).eq_iff

@[simp] lemma bihimp_eq_left : a ⇔ b = a ↔ b = ⊤ := @symm_diff_eq_left αᵒᵈ _ _ _
@[simp] lemma bihimp_eq_right : a ⇔ b = b ↔ a = ⊤ := @symm_diff_eq_right αᵒᵈ _ _ _

protected lemma codisjoint.bihimp_left (ha : codisjoint a c) (hb : codisjoint b c) :
  codisjoint (a ⇔ b) c :=
(ha.inf_left hb).mono_left inf_le_bihimp

protected lemma codisjoint.bihimp_right (ha : codisjoint a b) (hb : codisjoint a c) :
  codisjoint a (b ⇔ c) :=
(ha.inf_right hb).mono_right inf_le_bihimp

end cogeneralized_boolean_algebra

lemma symm_diff_eq : a ∆ b = (a ⊓ bᶜ) ⊔ (b ⊓ aᶜ) := by simp only [(∆), sdiff_eq]
lemma bihimp_eq : a ⇔ b = (a ⊔ bᶜ) ⊓ (b ⊔ aᶜ) := by simp only [(⇔), himp_eq]

lemma symm_diff_eq' : a ∆ b = (a ⊔ b) ⊓ (aᶜ ⊔ bᶜ) :=
by rw [symm_diff_eq_sup_sdiff_inf, sdiff_eq, compl_inf]

lemma bihimp_eq' : a ⇔ b = (a ⊓ b) ⊔ (aᶜ ⊓ bᶜ) := @symm_diff_eq' αᵒᵈ _ _ _

lemma symm_diff_top : a ∆ ⊤ = aᶜ := symm_diff_top' _
lemma top_symm_diff : ⊤ ∆ a = aᶜ := top_symm_diff' _

@[simp] lemma compl_symm_diff : (a ∆ b)ᶜ = a ⇔ b :=
by simp_rw [symm_diff, compl_sup_distrib, compl_sdiff, bihimp, inf_comm]

@[simp] lemma compl_bihimp : (a ⇔ b)ᶜ = a ∆ b := @compl_symm_diff αᵒᵈ _ _ _

@[simp] lemma compl_symm_diff_compl : aᶜ ∆ bᶜ = a ∆ b :=
sup_comm.trans $ by simp_rw [compl_sdiff_compl, sdiff_eq, symm_diff_eq]

@[simp] lemma compl_bihimp_compl : aᶜ ⇔ bᶜ = a ⇔ b := @compl_symm_diff_compl αᵒᵈ _ _ _

@[simp] lemma symm_diff_eq_top : a ∆ b = ⊤ ↔ is_compl a b :=
by rw [symm_diff_eq', ←compl_inf, inf_eq_top_iff, compl_eq_top, is_compl_iff, disjoint_iff,
 codisjoint_iff, and.comm]

@[simp] lemma bihimp_eq_bot : a ⇔ b = ⊥ ↔ is_compl a b :=
by rw [bihimp_eq', ←compl_sup, sup_eq_bot_iff, compl_eq_bot, is_compl_iff, disjoint_iff,
 codisjoint_iff]

@[simp] lemma compl_symm_diff_self : aᶜ ∆ a = ⊤ := hnot_symm_diff_self _
@[simp] lemma symm_diff_compl_self : a ∆ aᶜ = ⊤ := symm_diff_hnot_self _

lemma symm_diff_symm_diff_right' :
  a ∆ (b ∆ c) = (a ⊓ b ⊓ c) ⊔ (a ⊓ bᶜ ⊓ cᶜ) ⊔ (aᶜ ⊓ b ⊓ cᶜ) ⊔ (aᶜ ⊓ bᶜ ⊓ c) :=
calc a ∆ (b ∆ c) = (a ⊓ ((b ⊓ c) ⊔ (bᶜ ⊓ cᶜ))) ⊔
                     (((b ⊓ cᶜ) ⊔ (c ⊓ bᶜ)) ⊓ aᶜ)  : by rw [symm_diff_eq, compl_symm_diff,
                                                           bihimp_eq', symm_diff_eq]
             ... = (a ⊓ b ⊓ c) ⊔ (a ⊓ bᶜ ⊓ cᶜ) ⊔
                     (b ⊓ cᶜ ⊓ aᶜ) ⊔ (c ⊓ bᶜ ⊓ aᶜ) : by rw [inf_sup_left, inf_sup_right,
                                                            ←sup_assoc, ←inf_assoc, ←inf_assoc]
             ... = (a ⊓ b ⊓ c) ⊔ (a ⊓ bᶜ ⊓ cᶜ) ⊔
                     (aᶜ ⊓ b ⊓ cᶜ) ⊔ (aᶜ ⊓ bᶜ ⊓ c) : begin
                                                       congr' 1,
                                                       { congr' 1,
                                                         rw [inf_comm, inf_assoc], },
                                                       { apply inf_left_right_swap }
                                                     end

variables {a b c}

lemma disjoint.le_symm_diff_sup_symm_diff_left (h : disjoint a b) : c ≤ a ∆ c ⊔ b ∆ c :=
begin
  transitivity c \ (a ⊓ b),
  { rw [h.eq_bot, sdiff_bot] },
  { rw sdiff_inf,
    exact sup_le_sup le_sup_right le_sup_right }
end

lemma disjoint.le_symm_diff_sup_symm_diff_right (h : disjoint b c) : a ≤ a ∆ b ⊔ a ∆ c :=
by { simp_rw symm_diff_comm a, exact h.le_symm_diff_sup_symm_diff_left }

lemma codisjoint.bihimp_inf_bihimp_le_left (h : codisjoint a b) : a ⇔ c ⊓ b ⇔ c ≤ c :=
h.dual.le_symm_diff_sup_symm_diff_left

lemma codisjoint.bihimp_inf_bihimp_le_right (h : codisjoint b c) : a ⇔ b ⊓ a ⇔ c ≤ a :=
h.dual.le_symm_diff_sup_symm_diff_right

end boolean_algebra

/-! ### Prod -/

section prod

@[simp] lemma symm_diff_fst [generalized_coheyting_algebra α] [generalized_coheyting_algebra β]
  (a b : α × β) :
  (a ∆ b).1 = a.1 ∆ b.1 := rfl
@[simp] lemma symm_diff_snd [generalized_coheyting_algebra α] [generalized_coheyting_algebra β]
  (a b : α × β) :
  (a ∆ b).2 = a.2 ∆ b.2 := rfl

@[simp] lemma bihimp_fst [generalized_heyting_algebra α] [generalized_heyting_algebra β]
  (a b : α × β) :
  (a ⇔ b).1 = a.1 ⇔ b.1 := rfl
@[simp] lemma bihimp_snd [generalized_heyting_algebra α] [generalized_heyting_algebra β]
  (a b : α × β) :
  (a ⇔ b).2 = a.2 ⇔ b.2 := rfl

end prod

/-! ### Pi -/

namespace pi

lemma symm_diff_def [Π i, generalized_coheyting_algebra (π i)] (a b : Π i, π i) :
  a ∆ b = λ i, a i ∆ b i := rfl

lemma bihimp_def [Π i, generalized_heyting_algebra (π i)] (a b : Π i, π i) :
  a ⇔ b = λ i, a i ⇔ b i := rfl

@[simp] lemma symm_diff_apply [Π i, generalized_coheyting_algebra (π i)] (a b : Π i, π i) (i : ι) :
  (a ∆ b) i = a i ∆ b i := rfl

@[simp] lemma bihimp_apply [Π i, generalized_heyting_algebra (π i)] (a b : Π i, π i) (i : ι) :
  (a ⇔ b) i = a i ⇔ b i := rfl

end pi
