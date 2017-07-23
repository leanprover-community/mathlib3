/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad
-/
open eq function

/- TODO: automatic construction of dual definitions / theorems -/

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

section monotone
variables [weak_order α] [weak_order β] [weak_order γ]

def monotone (f : α → β) := ∀{{a b}}, a ≤ b → f a ≤ f b

lemma monotone_id : @monotone α α _ _ id := assume x y h, h

lemma monotone_const {b : β} : monotone (λ(a:α), b) := assume x y h, le_refl b

lemma monotone_comp {f : α → β} {g : β → γ} (m_f : monotone f) (m_g : monotone g) :
  monotone (g ∘ f) :=
assume a b h, m_g (m_f h)

end monotone

section
  variable [decidable_linear_order α]
  variables {a b c d : α}
  open decidable

  theorem le_max_left_iff_true (a b : α) : a ≤ max a b ↔ true :=
  iff_true_intro (le_max_left a b)

  theorem le_max_right_iff_true (a b : α) : b ≤ max a b ↔ true :=
  iff_true_intro (le_max_right a b)

  theorem min_right_comm (a b c : α) : min (min a b) c = min (min a c) b :=
  right_comm min min_comm min_assoc a b c

  theorem max.left_comm (a b c : α) : max a (max b c) = max b (max a c) :=
  left_comm max max_comm max_assoc a b c

  theorem max.right_comm (a b c : α) : max (max a b) c = max (max a c) b :=
  right_comm max max_comm max_assoc a b c
end

/- order instances -/

instance weak_order_fun [weak_order β] : weak_order (α → β) :=
{ le := λx y, ∀b, x b ≤ y b,
  le_refl := λf b, le_refl (f b),
  le_trans := λf g h h1 h2 b, le_trans (h1 b) (h2 b),
  le_antisymm := λf g h1 h2, funext (λb, le_antisymm (h1 b) (h2 b))
}

def weak_order_dual (wo : weak_order α) : weak_order α :=
{ le := λx y, y ≤ x,
  le_refl := le_refl,
  le_trans := assume a b c h₁ h₂, le_trans h₂ h₁,
  le_antisymm := assume a b h₁ h₂, le_antisymm h₂ h₁ }

lemma le_dual_eq_le {α : Type} (wo : weak_order α) (a b : α) :
  @has_le.le _ (@weak_order.to_has_le _ (weak_order_dual wo)) a b =
  @has_le.le _ (@weak_order.to_has_le _ wo) b a :=
rfl

lemma comp_le_comp_left_of_monotone [weak_order α] [weak_order β] [weak_order γ]
  {f : β → α} {g h : γ → β} (m_f : monotone f) (le_gh : g ≤ h) : has_le.le.{max w u} (f ∘ g) (f ∘ h) :=
assume x, m_f (le_gh x)

section monotone
variables [weak_order α] [weak_order γ]

lemma monotone_lam {f : α → β → γ} (m : ∀b, monotone (λa, f a b)) : monotone f :=
assume a a' h b, m b h

lemma monotone_app (f : β → α → γ) (b : β) (m : monotone (λa b, f b a)) : monotone (f b) :=
assume a a' h, m h b

end monotone
