/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/

import algebra.module

class has_tp (A : Type*) := (tp : A → A → A → A )

notation ⦃ a, b, c ⦄ := has_tp.tp a b c

class is_tp (A : Type*) [has_tp A] [has_add A] [has_sub A]  :=
(comm : ∀ (a b c : A), ⦃ a, b, c ⦄ = ⦃ c, b, a ⦄)
(ladd : ∀ (a b c d : A), ⦃ (a+b), c, d ⦄ = ⦃ a, c, d ⦄ + ⦃ b, c, d ⦄)
(madd : ∀ (a b c d : A), ⦃ a, (b+c), d ⦄ = ⦃ a, b, d ⦄ + ⦃ a, c, d ⦄)

namespace is_tp

variables {A : Type*} [has_tp A]

lemma radd [has_add A] [has_sub A] [is_tp A] (a b c d : A) :
  ⦃ a, b, c + d ⦄ = ⦃ a, b, c ⦄ + ⦃ a, b, d ⦄ := by rw [comm, ladd, comm, comm d]

lemma lzero [add_group A] [is_tp A] (b c : A) : ⦃0, b, c⦄ = 0 :=
(add_monoid_hom.mk' (λ (a : A), ⦃a, b, c⦄) (λ a₁ a₂, ladd a₁ a₂ b c )).map_zero

lemma mzero [add_group A] [is_tp A] (a c : A) : ⦃a, 0, c⦄ = 0 :=
(add_monoid_hom.mk' (λ (b : A), ⦃a, b, c⦄) (λ b₁ b₂ , madd a b₁ b₂ c)).map_zero

lemma rzero [add_group A] [is_tp A] (a b : A) : ⦃a, b, 0⦄ = 0 :=
by rw [comm, lzero]

lemma lgsmul [add_group A] [is_tp A] (a b c : A) (z : ℤ) : ⦃z•a, b, c⦄ = z•⦃a, b, c⦄ :=
add_monoid_hom.map_zsmul ⟨λ (a : A), ⦃a, b, c⦄, lzero b c, λ _ _, ladd _ _ _ _⟩ _ _

lemma mgsmul [add_group A] [is_tp A]  (a b c : A) (z : ℤ) : ⦃a, z•b, c⦄ = z•⦃a, b, c⦄ :=
add_monoid_hom.map_zsmul ⟨λ (b : A), ⦃a, b, c⦄, mzero a c, λ _ _, madd _ _ _ _⟩ _ _

lemma rgsmul [add_group A] [is_tp A] (a b : A) (z : ℤ) (c : A) : ⦃a, b, z•c⦄ = z•⦃a, b, c⦄ :=
  by rw [comm, lgsmul, comm]

lemma lneg [add_group A] [is_tp A] (a b c : A) : ⦃-a, b, c⦄ = -⦃a, b, c⦄ :=
  by rw [←sub_eq_zero, sub_neg_eq_add, ←ladd, neg_add_self, lzero]

lemma mneg [add_group A] [is_tp A] (a b c : A): ⦃a, -b, c⦄ = -⦃a, b, c⦄ :=
  by rw [←sub_eq_zero, sub_neg_eq_add, ←madd, neg_add_self, mzero]

lemma rneg [add_group A] [is_tp A] (a b c : A): ⦃a, b, -c⦄ = -⦃a, b, c⦄ := by rw [comm, lneg, comm]

end is_tp

class is_jordan_tp (A : Type*) [has_tp A] [has_add A] [has_sub A] :=
(jordan : ∀ (a b c d e: A), ⦃ a, b, ⦃ c, d, e ⦄ ⦄  =
  ⦃ ⦃ a, b, c ⦄, d, e ⦄ - ⦃ c, ⦃ b, a, d ⦄,  e ⦄ + ⦃ c, d, ⦃ a, b, e ⦄ ⦄)
