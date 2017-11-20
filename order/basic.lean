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
variables [preorder α] [preorder β] [preorder γ]

def monotone (f : α → β) := ∀{{a b}}, a ≤ b → f a ≤ f b

theorem monotone_id : @monotone α α _ _ id := assume x y h, h

theorem monotone_const {b : β} : monotone (λ(a:α), b) := assume x y h, le_refl b

theorem monotone_comp {f : α → β} {g : β → γ} (m_f : monotone f) (m_g : monotone g) :
  monotone (g ∘ f) :=
assume a b h, m_g (m_f h)

end monotone

section increasing
variables [preorder α]

definition increasing (f : α → α) := ∀a, a ≤ f a

end increasing

section decreasing
variables [preorder α]

definition decreasing (f : α → α) := ∀a, f a ≤ a
end decreasing

section linear_order
variables [linear_order α] {a b : α}

lemma not_le_iff : ¬ (a ≤ b) ↔ b < a := (lt_iff_not_ge b a).symm
lemma not_lt_iff : ¬ (a < b) ↔ b ≤ a := ⟨le_of_not_gt, not_lt_of_ge⟩

end linear_order

section decidable_linear_order
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
end decidable_linear_order

/- order instances -/

def preorder_dual (o : preorder α) : preorder α :=
{ le       := λx y, y ≤ x,
  le_refl  := le_refl,
  le_trans := assume a b c h₁ h₂, le_trans h₂ h₁ }

instance preorder_fun {ι : Type u} {α : ι → Type v} [∀i, preorder (α i)] : preorder (Πi, α i) :=
{ le       := λx y, ∀i, x i ≤ y i,
  le_refl  := assume a i, le_refl (a i),
  le_trans := assume a b c h₁ h₂ i, le_trans (h₁ i) (h₂ i) }

-- instance preorder_fun [preorder β] : preorder (α → β) := by apply_instance

instance partial_order_fun {ι : Type u} {α : ι → Type v} [∀i, partial_order (α i)] : partial_order (Πi, α i) :=
{ le_antisymm := λf g h1 h2, funext (λb, le_antisymm (h1 b) (h2 b)),
  ..preorder_fun }

def partial_order_dual (wo : partial_order α) : partial_order α :=
{ le          := λx y, y ≤ x,
  le_refl     := le_refl,
  le_trans    := assume a b c h₁ h₂, le_trans h₂ h₁,
  le_antisymm := assume a b h₁ h₂, le_antisymm h₂ h₁ }

theorem le_dual_eq_le {α : Type} (wo : partial_order α) (a b : α) :
  @has_le.le _ (@preorder.to_has_le _ (@partial_order.to_preorder _ (partial_order_dual wo))) a b =
  @has_le.le _ (@preorder.to_has_le _ (@partial_order.to_preorder _ wo)) b a :=
rfl

theorem comp_le_comp_left_of_monotone [preorder α] [preorder β] [preorder γ]
  {f : β → α} {g h : γ → β} (m_f : monotone f) (le_gh : g ≤ h) : has_le.le.{max w u} (f ∘ g) (f ∘ h) :=
assume x, m_f (le_gh x)

section monotone
variables [preorder α] [preorder γ]

theorem monotone_lam {f : α → β → γ} (m : ∀b, monotone (λa, f a b)) : monotone f :=
assume a a' h b, m b h

theorem monotone_app (f : β → α → γ) (b : β) (m : monotone (λa b, f b a)) : monotone (f b) :=
assume a a' h, m h b

end monotone

/- additional order classes -/

/-- order without a top element; somtimes called cofinal -/
class no_top_order (α : Type u) [preorder α] : Prop :=
(no_top : ∀a:α, ∃a', a < a')

lemma no_top [preorder α] [no_top_order α] : ∀a:α, ∃a', a < a' :=
no_top_order.no_top

/-- order without a bottom element; somtimes called coinitial or dense -/
class no_bot_order (α : Type u) [preorder α] : Prop :=
(no_bot : ∀a:α, ∃a', a' < a)

lemma no_bot [preorder α] [no_bot_order α] : ∀a:α, ∃a', a' < a :=
no_bot_order.no_bot

class densely_ordered (α : Type u) [preorder α] : Prop :=
(dense : ∀a₁ a₂:α, a₁ < a₂ → ∃a, a₁ < a ∧ a < a₂)

lemma dense [preorder α] [densely_ordered α] : ∀{a₁ a₂:α}, a₁ < a₂ → ∃a, a₁ < a ∧ a < a₂ :=
densely_ordered.dense

lemma le_of_forall_le [linear_order α] [densely_ordered α] {a₁ a₂ : α} (h : ∀a₃>a₂, a₁ ≤ a₃) :
  a₁ ≤ a₂ :=
le_of_not_gt $ assume ha,
  let ⟨a, ha₁, ha₂⟩ := dense ha in
  lt_irrefl a $ lt_of_lt_of_le ‹a < a₁› (h _ ‹a₂ < a›)

lemma eq_of_le_of_forall_le [linear_order α] [densely_ordered α] {a₁ a₂ : α}
  (h₁ : a₂ ≤ a₁) (h₂ : ∀a₃>a₂, a₁ ≤ a₃) : a₁ = a₂ :=
le_antisymm (le_of_forall_le h₂) h₁

lemma le_of_forall_ge [linear_order α] [densely_ordered α] {a₁ a₂ : α}(h : ∀a₃<a₁, a₂ ≥ a₃) :
  a₁ ≤ a₂ :=
le_of_not_gt $ assume ha,
  let ⟨a, ha₁, ha₂⟩ := dense ha in
  lt_irrefl a $ lt_of_le_of_lt (h _ ‹a < a₁›) ‹a₂ < a›

lemma eq_of_le_of_forall_ge [linear_order α] [densely_ordered α] {a₁ a₂ : α}
  (h₁ : a₂ ≤ a₁) (h₂ : ∀a₃<a₁, a₂ ≥ a₃) : a₁ = a₂ :=
le_antisymm (le_of_forall_ge h₂) h₁
