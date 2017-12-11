/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl

Quotient construction on modules
-/

import algebra.linear_algebra.basic

namespace is_submodule

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}
variables [ring α] [module α β] [module α γ] (s : set β) [hs : is_submodule s]
include α s hs

open function

def quotient_rel : setoid β :=
⟨λb₁ b₂, b₁ - b₂ ∈ s,
  assume b, by simp [zero],
  assume b₁ b₂ hb,
  have - (b₁ - b₂) ∈ s, from is_submodule.neg hb,
  by simpa using this,
  assume b₁ b₂ b₃ hb₁₂ hb₂₃,
  have (b₁ - b₂) + (b₂ - b₃) ∈ s, from add hb₁₂ hb₂₃,
  by simpa using this⟩

local attribute [instance] quotient_rel

lemma quotient_rel_eq {b₁ b₂ : β} : (b₁ ≈ b₂) = (b₁ - b₂ ∈ s) := rfl

section
variable (β)
def quotient : Type v := quotient (quotient_rel s)
end

local notation ` Q ` := quotient β s

instance quotient.has_zero : has_zero Q := ⟨⟦ 0 ⟧⟩

instance quotient.has_add : has_add Q :=
⟨λa b, quotient.lift_on₂ a b (λa b, ⟦a + b⟧) $
  assume a₁ a₂ b₁ b₂ (h₁ : a₁ - b₁ ∈ s) (h₂ : a₂ - b₂ ∈ s),
  quotient.sound $
  have (a₁ - b₁) + (a₂ - b₂) ∈ s, from add h₁ h₂,
  show (a₁ + a₂) - (b₁ + b₂) ∈ s, by simpa⟩

instance quotient.has_neg : has_neg Q :=
⟨λa, quotient.lift_on a (λa, ⟦- a⟧) $ assume a b (h : a - b ∈ s),
  quotient.sound $
  have - (a - b) ∈ s, from neg h,
  show (-a) - (-b) ∈ s, by simpa⟩

instance quotient.has_scalar : has_scalar α Q :=
⟨λa b, quotient.lift_on b (λb, ⟦a • b⟧) $ assume b₁ b₂ (h : b₁ - b₂ ∈ s),
  quotient.sound $
  have a • (b₁ - b₂) ∈ s, from is_submodule.smul a h,
  show a • b₁ - a • b₂ ∈ s, by simpa [smul_add]⟩

instance quotient.module : module α Q :=
{ module .
  zero := 0,
  add  := (+),
  neg  := has_neg.neg,
  smul := (•),
  add_assoc    := assume a b c, quotient.induction_on₃ a b c $ assume a b c, quotient.sound $
    by simp,
  add_comm     := assume a b, quotient.induction_on₂ a b $ assume a b, quotient.sound $
    by simp,
  add_zero     := assume a, quotient.induction_on a $ assume a, quotient.sound $
    by simp,
  zero_add     := assume a, quotient.induction_on a $ assume a, quotient.sound $
    by simp,
  add_left_neg := assume a, quotient.induction_on a $ assume a, quotient.sound $
    by simp,
  one_smul     := assume a, quotient.induction_on a $ assume a, quotient.sound $
    by simp,
  mul_smul     := assume a b c, quotient.induction_on c $ assume c, quotient.sound $
    by simp [mul_smul],
  smul_add     := assume a b c, quotient.induction_on₂ b c $ assume b c, quotient.sound $
    by simp [smul_add],
  add_smul     := assume a b c, quotient.induction_on c $ assume c, quotient.sound $
    by simp [add_smul] }

instance quotient.inhabited : inhabited Q := ⟨0⟩

lemma is_linear_map_quotient_mk : @is_linear_map _ _ Q _ _ _ (λb, ⟦b⟧ : β → Q) :=
by refine {..}; intros; refl

def quotient.lift {f : β → γ} (hf : is_linear_map f) (h : ∀x∈s, f x = 0) (b : Q) : γ :=
b.lift_on f $ assume a b (hab : a - b ∈ s),
  have f a - f b = 0, by rw [←hf.sub]; exact h _ hab,
  show f a = f b, from eq_of_sub_eq_zero this

@[simp] lemma quotient.lift_mk {f : β → γ} (hf : is_linear_map f) (h : ∀x∈s, f x = 0) (b : β) :
  quotient.lift s hf h ⟦b⟧ = f b :=
rfl

lemma is_linear_map_quotient_lift {f : β → γ} {h : ∀x y, x - y ∈ s → f x = f y}
  (hf : is_linear_map f) : is_linear_map (λq:Q, quotient.lift_on q f h) :=
⟨assume b₁ b₂, quotient.induction_on₂ b₁ b₂ $ assume b₁ b₂, hf.add b₁ b₂,
  assume a b, quotient.induction_on b $ assume b, hf.smul a b⟩

lemma quotient.injective_lift [is_submodule s] {f : β → γ} (hf : is_linear_map f)
  (hs : s = {x | f x = 0}) : injective (quotient.lift s hf $ le_of_eq hs) :=
assume a b, quotient.induction_on₂ a b $ assume a b (h : f a = f b), quotient.sound $
  have f (a - b) = 0, by rw [hf.sub]; simp [h],
  show a - b ∈ s, from hs.symm ▸ this

end is_submodule