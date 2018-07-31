/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Chris Hughes

mu2 is the group with 2 elements, 1 and -1
-/
import data.fintype

@[derive decidable_eq] inductive mu2
|     one : mu2
| neg_one : mu2

namespace mu2

def neg : mu2 → mu2
|     one := neg_one
| neg_one :=     one

instance : has_one mu2 := ⟨one⟩
instance : has_neg mu2 := ⟨neg⟩
instance : fintype mu2 := ⟨{one, neg_one}, λ a, by cases a; simp⟩
instance : has_repr mu2 := ⟨λ a, mu2.rec_on a "1" "-1"⟩

@[simp] lemma card_mu2 : fintype.card mu2 = 2 := rfl

def mul : mu2 → mu2 → mu2
|   1    1  :=  1
|   1  (-1) := -1
| (-1)   1  := -1
| (-1) (-1) :=  1

instance : comm_group mu2 :=
by refine_struct {mul := mul, inv := id, one := 1}; exact dec_trivial

@[simp] lemma ne_neg_one_iff : ∀ {a : mu2}, a ≠ -1 ↔ a = 1 := dec_trivial
@[simp] lemma ne_one_iff : ∀ {a : mu2}, a ≠ 1 ↔ a = -1 := dec_trivial

instance {α : Type*} [has_one α] [has_neg α] : has_coe mu2 α :=
⟨λ a, mu2.rec_on a 1 (-1)⟩

@[simp] lemma coe_one {α : Type*} [has_one α] [has_neg α] : ((1 : mu2) : α) = 1 := rfl

@[simp] lemma coe_neg {α : Type*} [ring α] (a : mu2) : ((-a : mu2) : α) = -a :=
mu2.rec_on a rfl (neg_neg _).symm

@[simp] lemma coe_mul {α : Type*} [ring α] : ∀ a b : mu2, ((a * b : mu2) : α) = a * b
|     one     one := (one_mul _).symm
| neg_one     one := (mul_one _).symm
|     one neg_one := (one_mul _).symm
| neg_one neg_one := show (1 : α) = -1 * -1, by simp

end mu2