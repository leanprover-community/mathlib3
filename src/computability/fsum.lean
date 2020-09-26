/-
Copyright (c) 2020 Pim Spelier, Daan van Gent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Spelier, Daan van Gent.
-/

import tactic.basic
import data.fintype.basic

def quot.lift_on' {α : Type*} [s : setoid α]
{t : α → Type*} {C : Type* → Type*} {ht : ∀ a b : α, a ≈ b → t a = t b}
(f : ∀ a : α, C (t a)) (hf : ∀ a b : α, a ≈ b → f a == f b) :
∀ q : quotient s, C (quot.lift_on q t ht) := λ q, quotient.hrec_on q f hf

/-def sum.elim' {α β: Type*} {tα : α → Type*} {tβ : β → Type*} (f : ∀ x, tα x) (g : ∀ x, tβ x) :
∀ x : α ⊕ β, sum.elim tα tβ x := λ x, sum.cases_on x f g-/

def sum.elim' {α β: Type*} {tα : α → Type*} {tβ : β → Type*} {C : Type* → Type*}
(f : ∀ x, C (tα x)) (g : ∀ x, C (tβ x)) :
∀ x : α ⊕ β, C (sum.elim tα tβ x) := λ x, sum.cases_on x f g

@[simp] lemma sum.elim_inl' {α β : Type*} {tα : α → Type*} {tβ : β → Type*} {C : Type* → Type*}
(f : ∀ x, C (tα x)) (g : ∀ x, C (tβ x)) (x : α) : sum.elim' f g (sum.inl x) = f x := rfl
@[simp] lemma sum.elim_inr' {α β : Type*} {tα : α → Type*} {tβ : β → Type*} {C : Type* → Type*}
(f : ∀ x, C (tα x)) (g : ∀ x, C (tβ x)) (y : β) : sum.elim' f g (sum.inr y) = g y := rfl

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

/--/
def liftl' [hβ : decidable_eq β] (x : α ⊕ β) : α ⊕ β :=
sum.cases_on x (λ x, sum.inl x) (λ y, ite (y = b) (sum.inl a) (sum.inr y))
lemma liftl_nb' [hβ : decidable_eq β] (x : α ⊕ β) : liftl' x ≠ sum.inr b :=
begin
  cases x; unfold liftl',
  apply sum.no_confusion,
  intro h,
  cases em (x = b) with e e, {
    rw if_pos e at h,
    exact sum.no_confusion h,
  },
  rw if_neg e at h,
  apply e,
  exact sum.inr.inj h,
end

def liftl [hβ : decidable_eq β] (q : fsum) : α ⊕ β :=
elim_aux (λ x, liftl' x) begin
  unfold liftl',
  rw if_pos,
  refl,
end q

lemma liftl_nb [hβ : decidable_eq β] (q : fsum) : liftl q ≠ sum.inr b :=
begin
  sorry,
end-/

def liftr [hα : decidable_eq α] (q : fsum) : α ⊕ β := begin
  induction q,
  cases q with x y h,
  exact ite (x = a) (sum.inr b) (sum.inl x),
  exact sum.inr y,
  tidy,
end

@[simp] lemma elim_inl {γ : Type*} (f : α → γ) (g : β → γ)
{h : f a = g b} (x : α) : elim f g h (inl x) = f x := rfl
@[simp] lemma elim_inr {γ : Type*} (f : α → γ) (g : β → γ)
{h : f a = g b} (y : β) : elim f g h (inr y) = g y := rfl

def eliml [hβ : decidable_eq β] {γ : Type*} (f : α → γ) (g : β → γ) : fsum → γ :=
elim_aux (sum.elim f (λ y, ite (y = b) (f a) (g y))) (by simp)
def elimr [hα : decidable_eq α] {γ : Type*} (f : α → γ) (g : β → γ) : fsum → γ :=
elim_aux (sum.elim (λ x, ite (x = a) (g b) (f x)) g) (by simp)

set_option pp.proofs true

@[simp] lemma eliml_inl [hβ : decidable_eq β] {γ : Type*} (f : α → γ) (g : β → γ) (x : α):
eliml f g (inl x) = f x := by refl
@[simp] lemma elimr_inr [hα : decidable_eq α] {γ : Type*} (f : α → γ) (g : β → γ) (y : β):
elimr f g (inr y) = g y := by refl

lemma eliml_eq_elim [hβ : decidable_eq β] {γ : Type*} (f : α → γ) (g : β → γ) (h : f a = g b):
eliml f g = elim f g h := begin
  unfold eliml elim,
  suffices h' : (λ (y : β), ite (y = b) (f a) (g y)) = g, {
    simp [h'],
    rw proof_irrel h,
  },
  ext y,
  cases em (y = b) with h' h', {
    rw [if_pos h',h'],
    exact h,
  },
  rw if_neg h',
end

lemma elimr_eq_elim [hα : decidable_eq α] {γ : Type*} (f : α → γ) (g : β → γ) (h : f a = g b):
elimr f g = elim f g h := begin
  unfold elimr elim,
  suffices h' : (λ (x : α), ite (x = a) (g b) (f x)) = f, {
    simp [h'],
    rw proof_irrel h,
  },
  ext x,
  cases em (x = a) with h' h', {
    rw [if_pos h',h'],
    symmetry,
    exact h,
  },
  rw if_neg h',
end

def elim_prod_rel {t : α ⊕ β → Type*} {C : Type* → Type*} {ht : t (sum.inl a) = t (sum.inr b)}
(f : ∀ x : α ⊕ β, C (t x)) (hf : f (sum.inl a) == f (sum.inr b)) : ∀ x y, fsum_rel x y → f x == f y := by tidy
def elim_prod_aux {t : α ⊕ β → Type*} {C : Type* → Type*} {ht : t (sum.inl a) = t (sum.inr b)}
(f : ∀ x : α ⊕ β, C (t x)) (hf : f (sum.inl a) == f (sum.inr b)) : ∀ x : fsum, C (elim_aux t ht x) :=
@quot.lift_on' _ fsum_setoid t C (elim_rel t ht) f (@elim_prod_rel t C ht f hf)
def elim_prod {t₁ : α → Type*} {t₂ : β → Type*} {C : Type* → Type*} {ht : t₁ a = t₂ b}
(f : ∀ x : α, C (t₁ x)) (g : ∀ x : β, C (t₂ x)) (hf : f a == g b) : ∀ x : fsum, C (elim t₁ t₂ ht x) :=
@elim_prod_aux (sum.elim t₁ t₂) C ht (sum.elim' f g) hf


def eliml_prod [hβ : decidable_eq β] {t₁ : α → Type*} {t₂ : β → Type*} {C : Type* → Type*}
(f : ∀ x : α, C (t₁ x)) (g : ∀ y : β, C (t₂ y)) : ∀ q : fsum, C (eliml t₁ t₂ q) :=
elim_prod_aux (sum.elim' f (λ y, dite (y = b)
(λ h, by{ rw if_pos h, exact f a }) (λ h, by{ rw if_neg h, exact g y })))
(by{ apply heq.symm, simp })

def elimr_prod [hα : decidable_eq α] {t₁ : α → Type*} {t₂ : β → Type*} {C : Type* → Type*}
(f : ∀ x : α, C (t₁ x)) (g : ∀ y : β, C (t₂ y)) : ∀ q : fsum, C (elimr t₁ t₂ q) :=
elim_prod_aux (sum.elim' (λ x, dite (x = a)
(λ h, by{ rw if_pos h, exact g b}) (λ h, by{ rw if_neg h, exact f x})) g)
(by simp)


def extendl_value {γ : Type*} [h : decidable_eq β] (f : α → γ) (c : γ) : fsum → γ :=
elim f (λ y, ite (y = b) (f a) c) (by {rw if_pos, refl})
def extendr_value {γ : Type*} [h : decidable_eq α] (g : β → γ) (c : γ) : fsum → γ :=
elim (λ x, ite (x = a) (g b) c) g (by {rw if_pos, refl})

def extendl {γ : Type*} (f : α → γ) : fsum → γ := elim f (λ y, f a) rfl
def extendr {γ : Type*} (g : β → γ) : fsum → γ := elim (λ y, g b) g rfl

def extendl_prod {γ : Type*} {t : α → Type*} {C : Type* → Type*} (f : ∀ x : α, C (t x))
: ∀ q : fsum, C (extendl t q) := elim_prod f (λ y, f a) (congr_arg_heq f rfl)
def extendr_prod {γ : Type*} {t : β → Type*} {C : Type* → Type*} (g : ∀ y : β, C (t y))
: ∀ q : fsum, C (extendr t q) := elim_prod (λ x, g b) g (congr_arg_heq g rfl)


instance inhabited_fsum : inhabited fsum := ⟨inl a⟩
instance decidable_eq_fsum [dα : decidable_eq α] [dβ : decidable_eq β] : decidable_eq fsum :=
@quotient.decidable_eq (α ⊕ β) fsum_setoid fsum_setoid.decidable_rel
instance fintype_fsum [hα : fintype α] [hβ : fintype β] [hα' : decidable_eq α] [hβ' : decidable_eq β] :
fintype fsum := @quotient.fintype _ (sum.fintype α β) fsum_setoid fsum_setoid.decidable_rel

end

def inl' {α β : Type*} {a : α} {b : β} (x : α) : fsum a b := inl a b x
def inr' {α β : Type*} {a : α} {b : β} (y : β) : fsum a b := inr a b y
def extendl' {α β γ : Type*} {a : α} {b : β} (f : α → γ) : fsum a b → γ := extendl a b f
def extendr' {α β γ : Type*} {a : α} {b : β} (g : β → γ) : fsum a b → γ := extendr a b g

lemma point_eq' {α β : Type*} {a : α} {b : β}: @inl' _ _ a b a = inr' b := point_eq a b

end fsum

def map_rec_codomain {α : Type*} {t₁ t₂ : α → Type*} (ft : ∀ a : α, t₁ a → t₂ a) (f : ∀ a : α, t₁ a)
: ∀ a : α, t₂ a := λ a, ft a (f a)

def map_rec_domain {α β : Type*} {t₁ : α → Type*} {t₂ : β → Type*} (ft : α → β)
(h : ∀ a : α, t₁ a = t₂ (ft a)) (f : ∀ b : β, t₂ b) : ∀ a : α, t₁ a := λ a,
begin rw h a, exact f (ft a), end


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
