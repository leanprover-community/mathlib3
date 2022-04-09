/-
Copyright (c) 2021 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Bryan Gin-ge Chen
-/

import order.boolean_algebra

/-!
# Symmetric difference

The symmetric difference or disjunctive union of sets `A` and `B` is the set of elements that are
in either `A` or `B` but not both. Translated into propositions, the symmetric difference is `xor`.

The symmetric difference operator (`symm_diff`) is defined in this file for any type with `⊔` and
`\` via the formula `(A \ B) ⊔ (B \ A)`, however the theorems proved about it only hold for
`generalized_boolean_algebra`s and `boolean_algebra`s.

The symmetric difference is the addition operator in the Boolean ring structure on Boolean algebras.

## Main declarations

* `symm_diff`: the symmetric difference operator, defined as `(A \ B) ⊔ (B \ A)`

In generalized Boolean algebras, the symmetric difference operator is:

* `symm_diff_comm`: commutative, and
* `symm_diff_assoc`: associative.

## Notations

* `a ∆ b`: `symm_diff a b`

## References

The proof of associativity follows the note "Associativity of the Symmetric Difference of Sets: A
Proof from the Book" by John McCuan:

* <https://people.math.gatech.edu/~mccuan/courses/4317/symmetricdifference.pdf>

## Tags
boolean ring, generalized boolean algebra, boolean algebra, symmetric differences
-/

/-- The symmetric difference operator on a type with `⊔` and `\` is `(A \ B) ⊔ (B \ A)`. -/
def symm_diff {α : Type*} [has_sup α] [has_sdiff α] (A B : α) : α := (A \ B) ⊔ (B \ A)

/- This notation might conflict with the Laplacian once we have it. Feel free to put it in locale
`order` or `symm_diff` if that happens. -/
infix ` ∆ `:100 := symm_diff

lemma symm_diff_def {α : Type*} [has_sup α] [has_sdiff α] (A B : α) :
  A ∆ B = (A \ B) ⊔ (B \ A) :=
rfl

lemma symm_diff_eq_xor (p q : Prop) : p ∆ q = xor p q := rfl

section generalized_boolean_algebra
variables {α : Type*} [generalized_boolean_algebra α] (a b c : α)

lemma symm_diff_comm : a ∆ b = b ∆ a := by simp only [(∆), sup_comm]

instance symm_diff_is_comm : is_commutative α (∆) := ⟨symm_diff_comm⟩

@[simp] lemma symm_diff_self : a ∆ a = ⊥ := by rw [(∆), sup_idem, sdiff_self]
@[simp] lemma symm_diff_bot : a ∆ ⊥ = a := by rw [(∆), sdiff_bot, bot_sdiff, sup_bot_eq]
@[simp] lemma bot_symm_diff : ⊥ ∆ a = a := by rw [symm_diff_comm, symm_diff_bot]

lemma symm_diff_eq_sup_sdiff_inf : a ∆ b = (a ⊔ b) \ (a ⊓ b) :=
by simp [sup_sdiff, sdiff_inf, sup_comm, (∆)]

@[simp] lemma sup_sdiff_symm_diff : (a ⊔ b) \ (a ∆ b) = a ⊓ b :=
sdiff_eq_symm inf_le_sup (by rw symm_diff_eq_sup_sdiff_inf)

lemma disjoint_symm_diff_inf : disjoint (a ∆ b) (a ⊓ b) :=
begin
  rw [symm_diff_eq_sup_sdiff_inf],
  exact disjoint_sdiff_self_left,
end

lemma symm_diff_le_sup : a ∆ b ≤ a ⊔ b := by { rw symm_diff_eq_sup_sdiff_inf, exact sdiff_le }

lemma inf_symm_diff_distrib_left : a ⊓ (b ∆ c) = (a ⊓ b) ∆ (a ⊓ c) :=
by rw [symm_diff_eq_sup_sdiff_inf, inf_sdiff_distrib_left, inf_sup_left, inf_inf_distrib_left,
  symm_diff_eq_sup_sdiff_inf]

lemma inf_symm_diff_distrib_right : (a ∆ b) ⊓ c = (a ⊓ c) ∆ (b ⊓ c) :=
by simp_rw [@inf_comm _ _ _ c, inf_symm_diff_distrib_left]

lemma sdiff_symm_diff : c \ (a ∆ b) = (c ⊓ a ⊓ b) ⊔ ((c \ a) ⊓ (c \ b)) :=
by simp only [(∆), sdiff_sdiff_sup_sdiff']

lemma sdiff_symm_diff' : c \ (a ∆ b) = (c ⊓ a ⊓ b) ⊔ (c \ (a ⊔ b)) :=
by rw [sdiff_symm_diff, sdiff_sup, sup_comm]

lemma symm_diff_sdiff : (a ∆ b) \ c = (a \ (b ⊔ c)) ⊔ (b \ (a ⊔ c)) :=
by rw [symm_diff_def, sup_sdiff, sdiff_sdiff_left, sdiff_sdiff_left]

@[simp] lemma symm_diff_sdiff_left : (a ∆ b) \ a = b \ a :=
by rw [symm_diff_def, sup_sdiff, sdiff_idem, sdiff_sdiff_self, bot_sup_eq]

@[simp] lemma symm_diff_sdiff_right : (a ∆ b) \ b = a \ b :=
by rw [symm_diff_comm, symm_diff_sdiff_left]

@[simp] lemma sdiff_symm_diff_self : a \ (a ∆ b) = a ⊓ b := by simp [sdiff_symm_diff]

lemma symm_diff_eq_iff_sdiff_eq {a b c : α} (ha : a ≤ c) :
  a ∆ b = c ↔ c \ a = b :=
begin
  split; intro h,
  { have hba : disjoint (a ⊓ b) c := begin
      rw [←h, disjoint.comm],
      exact disjoint_symm_diff_inf _ _,
    end,
    have hca : _ := congr_arg (\ a) h,
    rw [symm_diff_sdiff_left] at hca,
    rw [←hca, sdiff_eq_self_iff_disjoint],
    exact hba.of_disjoint_inf_of_le ha },
  { have hd : disjoint a b := by { rw ←h, exact disjoint_sdiff_self_right },
    rw [symm_diff_def, hd.sdiff_eq_left, hd.sdiff_eq_right, ←h, sup_sdiff_cancel_right ha] }
end

lemma disjoint.symm_diff_eq_sup {a b : α} (h : disjoint a b) : a ∆ b = a ⊔ b :=
by rw [(∆), h.sdiff_eq_left, h.sdiff_eq_right]

lemma symm_diff_eq_sup : a ∆ b = a ⊔ b ↔ disjoint a b :=
begin
  split; intro h,
  { rw [symm_diff_eq_sup_sdiff_inf, sdiff_eq_self_iff_disjoint] at h,
    exact h.of_disjoint_inf_of_le le_sup_left, },
  { exact h.symm_diff_eq_sup, },
end

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

@[simp] lemma symm_diff_symm_diff_self : a ∆ (a ∆ b) = b := by simp [←symm_diff_assoc]

@[simp] lemma symm_diff_symm_diff_self' : a ∆ b ∆ a = b :=
by rw [symm_diff_comm, ←symm_diff_assoc, symm_diff_self, bot_symm_diff]

@[simp] lemma symm_diff_right_inj : a ∆ b = a ∆ c ↔ b = c :=
begin
  split; intro h,
  { have H1 := congr_arg ((∆) a) h,
    rwa [symm_diff_symm_diff_self, symm_diff_symm_diff_self] at H1, },
  { rw h, },
end

@[simp] lemma symm_diff_left_inj : a ∆ b = c ∆ b ↔ a = c :=
by rw [symm_diff_comm a b, symm_diff_comm c b, symm_diff_right_inj]

@[simp] lemma symm_diff_eq_left : a ∆ b = a ↔ b = ⊥ :=
calc a ∆ b = a ↔ a ∆ b = a ∆ ⊥ : by rw symm_diff_bot
           ... ↔     b = ⊥     : by rw symm_diff_right_inj

@[simp] lemma symm_diff_eq_right : a ∆ b = b ↔ a = ⊥ := by rw [symm_diff_comm, symm_diff_eq_left]

@[simp] lemma symm_diff_eq_bot : a ∆ b = ⊥ ↔ a = b :=
calc a ∆ b = ⊥ ↔ a ∆ b = a ∆ a : by rw symm_diff_self
           ... ↔     a = b     : by rw [symm_diff_right_inj, eq_comm]

@[simp] lemma symm_diff_symm_diff_inf : a ∆ b ∆ (a ⊓ b) = a ⊔ b :=
by rw [symm_diff_eq_iff_sdiff_eq (symm_diff_le_sup _ _), sup_sdiff_symm_diff]

@[simp] lemma inf_symm_diff_symm_diff : (a ⊓ b) ∆ (a ∆ b) = a ⊔ b :=
by rw [symm_diff_comm, symm_diff_symm_diff_inf]

variables {a b c}

protected lemma disjoint.symm_diff_left (ha : disjoint a c) (hb : disjoint b c) :
  disjoint (a ∆ b) c :=
by { rw symm_diff_eq_sup_sdiff_inf, exact (ha.sup_left hb).disjoint_sdiff_left }

protected lemma disjoint.symm_diff_right (ha : disjoint a b) (hb : disjoint a c) :
  disjoint a (b ∆ c) :=
(ha.symm.symm_diff_left hb.symm).symm

end generalized_boolean_algebra

section boolean_algebra
variables {α : Type*} [boolean_algebra α] (a b c : α)

lemma symm_diff_eq : a ∆ b = (a ⊓ bᶜ) ⊔ (b ⊓ aᶜ) := by simp only [(∆), sdiff_eq]

@[simp] lemma symm_diff_top : a ∆ ⊤ = aᶜ := by simp [symm_diff_eq]
@[simp] lemma top_symm_diff : ⊤ ∆ a = aᶜ := by rw [symm_diff_comm, symm_diff_top]

lemma compl_symm_diff : (a ∆ b)ᶜ = (a ⊓ b) ⊔ (aᶜ ⊓ bᶜ) :=
by simp only [←top_sdiff, sdiff_symm_diff, top_inf_eq]

lemma symm_diff_eq_top_iff : a ∆ b = ⊤ ↔ is_compl a b :=
by rw [symm_diff_eq_iff_sdiff_eq le_top, top_sdiff, compl_eq_iff_is_compl]

lemma is_compl.symm_diff_eq_top (h : is_compl a b) : a ∆ b = ⊤ := (symm_diff_eq_top_iff a b).2 h

@[simp] lemma compl_symm_diff_self : aᶜ ∆ a = ⊤ :=
by simp only [symm_diff_eq, compl_compl, inf_idem, compl_sup_eq_top]

@[simp] lemma symm_diff_compl_self : a ∆ aᶜ = ⊤ := by rw [symm_diff_comm, compl_symm_diff_self]

lemma symm_diff_symm_diff_right' :
  a ∆ (b ∆ c) = (a ⊓ b ⊓ c) ⊔ (a ⊓ bᶜ ⊓ cᶜ) ⊔ (aᶜ ⊓ b ⊓ cᶜ) ⊔ (aᶜ ⊓ bᶜ ⊓ c) :=
calc a ∆ (b ∆ c) = (a ⊓ ((b ⊓ c) ⊔ (bᶜ ⊓ cᶜ))) ⊔
                     (((b ⊓ cᶜ) ⊔ (c ⊓ bᶜ)) ⊓ aᶜ)  : by rw [symm_diff_eq, compl_symm_diff,
                                                            symm_diff_eq]
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

end boolean_algebra
