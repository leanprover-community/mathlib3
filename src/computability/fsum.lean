/-
Copyright (c) 2020 Pim Spelier, Daan van Gent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Spelier, Daan van Gent.
-/

import tactic.basic
import data.fintype.basic

def quot.lift_on' {α : Type*} [s : setoid α]
{t : α → Type*} {ht : ∀ a b : α, a ≈ b → t a = t b}
(f : ∀ a : α, t a) (hf : ∀ a b : α, a ≈ b → f a == f b) : ∀ q : quotient s, quot.lift_on q t ht :=
λ q, quotient.hrec_on q f hf

def sum.elim' {α β: Type*} {tα : α → Type*} {tβ : β → Type*} (f : ∀ x, tα x) (g : ∀ x, tβ x) :
∀ x : α ⊕ β, sum.elim tα tβ x := λ x, sum.cases_on x (λ y, f y) (λ y, g y)


namespace fsum
section
parameters {α β : Type*} (a : α) (b : β)

def fsum_rel : (α ⊕ β) → (α ⊕ β) → Prop :=
λ u v, sum.cases_on u
  (λ x, sum.cases_on v
    (λ y, x = y)
    (λ y, (x = a) ∧ (y = b)))
  (λ x, sum.cases_on v
    (λ y, (x = b) ∧ (y = a))
    (λ y, x = y))

def fsum_setoid : setoid (α ⊕ β) := ⟨fsum_rel, by tidy⟩

instance fsum_setoid.decidable_rel [dα : decidable_eq α] [dβ : decidable_eq β]:
decidable_rel fsum_setoid.r := begin
  intros x y,
  cases x; cases y,
  exact dα x y,
  exact and.decidable,
  exact and.decidable,
  exact dβ x y,
end

def fsum : Type* := quotient fsum_setoid

def inl (x : α) : fsum := quotient.mk' (sum.inl x)
def inr (y : β) : fsum := quotient.mk' (sum.inr y)

lemma point_eq : inl a = inr b :=
quotient.eq'.mpr ⟨rfl, rfl⟩
lemma inl_eq_inr (x : α) (y : β) :
inl x = inr y ↔ ( x = a ∧ y = b ) := quotient.eq'
lemma inl_eq_inr' (x : α) (y : β) :
fsum_rel (sum.inl x) (sum.inr y) ↔ ( x = a ∧ y = b ) := iff.rfl
lemma inr_eq_inl' (y : β) (x : α) :
fsum_rel (sum.inr y) (sum.inl x) ↔ ( x = a ∧ y = b ) := and.comm

lemma inl_eq_inl (x y : α) :
inl x = inl y ↔ x = y := ⟨λ h, quotient.exact' h, λ h, by rw h⟩
lemma inr_eq_inr (x y : α) :
inl x = inl y ↔ x = y := ⟨λ h, quotient.exact' h, λ h, by rw h⟩

def elim_rel {γ : Type*} (f : α ⊕ β → γ) (h : f (sum.inl a) = f (sum.inr b)) :
∀ x y, fsum_rel x y → f x = f y := by tidy
def elim_aux {γ : Type*} (f : α ⊕ β → γ) (h : f (sum.inl a) = f (sum.inr b)) : fsum → γ :=
λ q, quot.lift_on q f (elim_rel f h)

def elim {γ : Type*} (f : α → γ) (g : β → γ) (h : f a = g b) : fsum → γ :=
elim_aux (sum.elim f g) h

@[simp] lemma elim_inl {γ : Type*} (f : α → γ) (g : β → γ)
{h : f a = g b} (x : α) : elim f g h (inl x) = f x := rfl
@[simp] lemma elim_inr {γ : Type*} (f : α → γ) (g : β → γ)
{h : f a = g b} (y : β) : elim f g h (inr y) = g y := rfl

def elim_rel' {t : α ⊕ β → Type*} {ht : t (sum.inl a) = t (sum.inr b)}
(f : ∀ x : α ⊕ β, t x) (hf : f (sum.inl a) == f (sum.inr b)) : ∀ x y, fsum_rel x y → f x == f y := by tidy
def elim_aux' {t : α ⊕ β → Type*} {ht : t (sum.inl a) = t (sum.inr b)}
(f : ∀ x : α ⊕ β, t x) (hf : f (sum.inl a) == f (sum.inr b)) : ∀ x : fsum, elim_aux t ht x :=
@quot.lift_on' _ fsum_setoid t (elim_rel t ht) f (@elim_rel' t ht f hf)

def elim' {t₁ : α → Type*} {t₂ : β → Type*} {ht : t₁ a = t₂ b}
(f : ∀ x : α, t₁ x) (g : ∀ x : β, t₂ x) (hf : f a == g b) : ∀ x : fsum, elim t₁ t₂ ht x :=
@elim_aux' (sum.elim t₁ t₂) ht (sum.elim' f g) hf

instance inhabited_fsum : inhabited fsum := ⟨inl a⟩
instance decidable_eq_fsum [dα : decidable_eq α] [dβ : decidable_eq β] : decidable_eq fsum :=
@quotient.decidable_eq (α ⊕ β) fsum_setoid fsum_setoid.decidable_rel

instance fintype [hα : fintype α] [hβ : fintype β] [hα' : decidable_eq α] [hβ' : decidable_eq β] :
fintype fsum := @quotient.fintype _ (sum.fintype α β) fsum_setoid fsum_setoid.decidable_rel

end
end fsum


/-

def lift [hβ : decidable_eq β] (x : fsum) : α ⊕ β :=
begin
  induction x with x x y h,
  cases x,
  exact sum.inl x,
  exact ite (x=b) (sum.inl a) (sum.inr x),
  tidy,
end


-/
