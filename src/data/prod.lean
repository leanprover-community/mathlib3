/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Extends theory on products
-/

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

@[simp] theorem prod.forall {p : α × β → Prop} : (∀ x, p x) ↔ (∀ a b, p (a, b)) :=
⟨assume h a b, h (a, b), assume h ⟨a, b⟩, h a b⟩

@[simp] theorem prod.exists {p : α × β → Prop} : (∃ x, p x) ↔ (∃ a b, p (a, b)) :=
⟨assume ⟨⟨a, b⟩, h⟩, ⟨a, b, h⟩, assume ⟨a, b, h⟩, ⟨⟨a, b⟩, h⟩⟩

namespace prod

attribute [simp] prod.map

@[simp] lemma map_fst (f : α → γ) (g : β → δ) : ∀(p : α × β), (map f g p).1 = f (p.1)
| ⟨a, b⟩ := rfl

@[simp] lemma map_snd (f : α → γ) (g : β → δ) : ∀(p : α × β), (map f g p).2 = g (p.2)
| ⟨a, b⟩ := rfl

@[simp] theorem mk.inj_iff {a₁ a₂ : α} {b₁ b₂ : β} : (a₁, b₁) = (a₂, b₂) ↔ (a₁ = a₂ ∧ b₁ = b₂) :=
⟨prod.mk.inj, by cc⟩

lemma ext_iff {p q : α × β} : p = q ↔ p.1 = q.1 ∧ p.2 = q.2 :=
by rw [← @mk.eta _ _ p, ← @mk.eta _ _ q, mk.inj_iff]

lemma ext {α β} {p q : α × β} (h₁ : p.1 = q.1) (h₂ : p.2 = q.2) : p = q :=
ext_iff.2 ⟨h₁, h₂⟩

lemma id_prod : (λ (p : α × α), (p.1, p.2)) = id :=
funext $ λ ⟨a, b⟩, rfl

/-- Swap the factors of a product. `swap (a, b) = (b, a)` -/
def swap : α × β → β × α := λp, (p.2, p.1)

@[simp] lemma swap_swap : ∀ x : α × β, swap (swap x) = x
| ⟨a, b⟩ := rfl

@[simp] lemma fst_swap {p : α × β} : (swap p).1 = p.2 := rfl

@[simp] lemma snd_swap {p : α × β} : (swap p).2 = p.1 := rfl

@[simp] lemma swap_prod_mk {a : α} {b : β} : swap (a, b) = (b, a) := rfl

@[simp] lemma swap_swap_eq : swap ∘ swap = @id (α × β) :=
funext swap_swap

@[simp] lemma swap_left_inverse : function.left_inverse (@swap α β) swap :=
swap_swap

@[simp] lemma swap_right_inverse : function.right_inverse (@swap α β) swap :=
swap_swap

lemma eq_iff_fst_eq_snd_eq : ∀{p q : α × β}, p = q ↔ (p.1 = q.1 ∧ p.2 = q.2)
| ⟨p₁, p₂⟩ ⟨q₁, q₂⟩ := by simp

theorem lex_def (r : α → α → Prop) (s : β → β → Prop)
  {p q : α × β} : prod.lex r s p q ↔ r p.1 q.1 ∨ p.1 = q.1 ∧ s p.2 q.2 :=
⟨λ h, by cases h; simp *,
 λ h, match p, q, h with
 | (a, b), (c, d), or.inl h := lex.left _ _ _ h
 | (a, b), (c, d), or.inr ⟨e, h⟩ :=
   by change a = c at e; subst e; exact lex.right _ _ h
 end⟩

instance lex.decidable [decidable_eq α] [decidable_eq β]
  (r : α → α → Prop) (s : β → β → Prop) [decidable_rel r] [decidable_rel s] :
  decidable_rel (prod.lex r s) :=
λ p q, decidable_of_decidable_of_iff (by apply_instance) (lex_def r s).symm

end prod
