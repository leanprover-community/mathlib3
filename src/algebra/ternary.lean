/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/

import algebra.group.hom
import algebra.group_power.basic

/-!
# Ternary product

This file defines a ternary product and shows that when the product is is triadditive it is
trilinear over ℤ. Jordan triples, ternary rings and ternary Lie algebras all have triadditive maps.
-/

/-- Notation class for ternary product -/
class has_tp (A : Type*) := (tp : A → A → A → A )

class has_trilinear_tp (A : Type*) [has_add A] extends has_tp A :=
(ladd : ∀ (a₁ a₂ b c : A), tp (a₁+a₂) b c = tp a₁ b c + tp a₂ b c)
(madd : ∀ (a b₁ b₂ c : A), tp a (b₁+b₂) c = tp a b₁ c + tp a b₂ c)
(radd : ∀ (a b c₁ c₂ : A), tp a b (c₁ + c₂) = tp a b c₁ + tp a b c₂)

namespace has_trilinear_tp

open has_tp (tp)

variables {A : Type*}  [add_group A] [has_trilinear_tp A]

lemma lzero (b c : A) : tp 0 b c = 0 :=
(add_monoid_hom.mk' (λ (a : A), tp a b c) (λ a₁ a₂, ladd a₁ a₂ b c )).map_zero

lemma mzero (a c : A) : tp a 0 c = 0 :=
(add_monoid_hom.mk' (λ (b : A), tp a b c) (λ b₁ b₂ , madd a b₁ b₂ c)).map_zero

lemma rzero (a b : A) : tp a b 0 = 0 :=
(add_monoid_hom.mk' (λ (c : A), tp a b c) (λ c₁ c₂ , radd a b c₁ c₂)).map_zero

lemma lzsmul (a b c : A) (z : ℤ) : tp (z•a) b c = z•tp a b c :=
add_monoid_hom.map_zsmul ⟨λ (a : A), tp a b c, lzero b c, λ _ _, ladd _ _ _ _⟩ _ _

lemma mzsmul (a b c : A) (z : ℤ) : tp a (z•b) c = z•tp a b c :=
add_monoid_hom.map_zsmul ⟨λ (b : A), tp a b c, mzero a c, λ _ _, madd _ _ _ _⟩ _ _

lemma rzsmul (a b : A) (z : ℤ) (c : A) : tp a b (z•c) = z•tp a b c :=
add_monoid_hom.map_zsmul ⟨λ (c : A), tp a b c, rzero a b , λ _ _, ladd _ _ _ _⟩ _ _

lemma lneg (a b c : A) : tp (-a) b c = -tp a b c :=
by rw [←sub_eq_zero, sub_neg_eq_add, ←ladd, neg_add_self, lzero]

lemma mneg (a b c : A): tp a (-b) c = -tp a b c :=
by rw [←sub_eq_zero, sub_neg_eq_add, ←madd, neg_add_self, mzero]

lemma rneg (a b c : A): tp a b (-c) = -tp a b c :=
by rw [←sub_eq_zero, sub_neg_eq_add, ←radd, neg_add_self, rzero]

lemma lsub (a b c d : A) : tp (a - d) b c = tp a b c - tp d b c :=
by rw [eq_sub_iff_add_eq, ← ladd, sub_add_cancel]

lemma msub (a b c d : A) : tp a (b - c) d = tp a b d - tp a c d :=
by rw [eq_sub_iff_add_eq, ← madd, sub_add_cancel]

lemma rsub (a b c d : A) : tp a b (c - d) = tp a b c - tp a b d :=
by rw [eq_sub_iff_add_eq, ← radd, sub_add_cancel]

lemma lr_bilinear (a₁ a₂ b c₁ c₂ : A) : tp (a₁ + a₂) b (c₁ + c₂) =
  tp a₁ b c₁ + tp a₁ b c₂ + tp a₂ b c₁ + tp a₂ b c₂ :=
calc tp (a₁ + a₂) b (c₁ + c₂) = tp a₁ b (c₁ + c₂) + tp a₂ b (c₁ + c₂) : by rw ladd
... = tp a₁ b c₁ + tp a₁ b c₂ + tp a₂ b (c₁ + c₂) : by rw radd
... = tp a₁ b c₁ + tp a₁ b c₂ + (tp a₂ b c₁ + tp a₂ b c₂) : by rw radd
... = tp a₁ b c₁ + tp a₁ b c₂ + tp a₂ b c₁ + tp a₂ b c₂ : by rw ← add_assoc

end  has_trilinear_tp
