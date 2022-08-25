/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import order.rel_classes

/-!
# Lexicographic ordering of lists.

The lexicographic order on `list α` is defined by `L < M` iff
* `[] < (a :: L)` for any `a` and `L`,
* `(a :: L) < (b :: M)` where `a < b`, or
* `(a :: L) < (a :: M)` where `L < M`.

## See also

Related files are:
* `data.finset.colex`: Colexicographic order on finite sets.
* `data.psigma.order`: Lexicographic order on `Σ' i, α i`.
* `data.pi.lex`: Lexicographic order on `Πₗ i, α i`.
* `data.sigma.order`: Lexicographic order on `Σ i, α i`.
* `data.prod.lex`: Lexicographic order on `α × β`.
-/

namespace list

open nat

universes u

variables {α : Type u}

/-! ### lexicographic ordering -/

/-- Given a strict order `<` on `α`, the lexicographic strict order on `list α`, for which
`[a0, ..., an] < [b0, ..., b_k]` if `a0 < b0` or `a0 = b0` and `[a1, ..., an] < [b1, ..., bk]`.
The definition is given for any relation `r`, not only strict orders. -/
inductive lex (r : α → α → Prop) : list α → list α → Prop
| nil {a l} : lex [] (a :: l)
| cons {a l₁ l₂} (h : lex l₁ l₂) : lex (a :: l₁) (a :: l₂)
| rel {a₁ l₁ a₂ l₂} (h : r a₁ a₂) : lex (a₁ :: l₁) (a₂ :: l₂)

namespace lex
theorem cons_iff {r : α → α → Prop} [is_irrefl α r] {a l₁ l₂} :
  lex r (a :: l₁) (a :: l₂) ↔ lex r l₁ l₂ :=
⟨λ h, by cases h with _ _ _ _ _ h _ _ _ _ h;
  [exact h, exact (irrefl_of r a h).elim], lex.cons⟩

@[simp] theorem not_nil_right (r : α → α → Prop) (l : list α) : ¬ lex r l [].

instance is_order_connected (r : α → α → Prop)
  [is_order_connected α r] [is_trichotomous α r] :
  is_order_connected (list α) (lex r) :=
⟨λ l₁, match l₁ with
| _,     [],    c::l₃, nil    := or.inr nil
| _,     [],    c::l₃, rel _ := or.inr nil
| _,     [],    c::l₃, cons _ := or.inr nil
| _,     b::l₂, c::l₃, nil := or.inl nil
| a::l₁, b::l₂, c::l₃, rel h :=
  (is_order_connected.conn _ b _ h).imp rel rel
| a::l₁, b::l₂, _::l₃, cons h := begin
    rcases trichotomous_of r a b with ab | rfl | ab,
    { exact or.inl (rel ab) },
    { exact (_match _ l₂ _ h).imp cons cons },
    { exact or.inr (rel ab) }
  end
end⟩

instance is_trichotomous (r : α → α → Prop) [is_trichotomous α r] :
  is_trichotomous (list α) (lex r) :=
⟨λ l₁, match l₁ with
| [], [] := or.inr (or.inl rfl)
| [], b::l₂ := or.inl nil
| a::l₁, [] := or.inr (or.inr nil)
| a::l₁, b::l₂ := begin
    rcases trichotomous_of r a b with ab | rfl | ab,
    { exact or.inl (rel ab) },
    { exact (_match l₁ l₂).imp cons
      (or.imp (congr_arg _) cons) },
    { exact or.inr (or.inr (rel ab)) }
  end
end⟩

instance is_asymm (r : α → α → Prop)
  [is_asymm α r] : is_asymm (list α) (lex r) :=
⟨λ l₁, match l₁ with
| a::l₁, b::l₂, lex.rel h₁, lex.rel h₂ := asymm h₁ h₂
| a::l₁, b::l₂, lex.rel h₁, lex.cons h₂ := asymm h₁ h₁
| a::l₁, b::l₂, lex.cons h₁, lex.rel h₂ := asymm h₂ h₂
| a::l₁, b::l₂, lex.cons h₁, lex.cons h₂ :=
  by exact _match _ _ h₁ h₂
end⟩

instance is_strict_total_order (r : α → α → Prop)
  [is_strict_total_order' α r] : is_strict_total_order' (list α) (lex r) :=
{..is_strict_weak_order_of_is_order_connected}

instance decidable_rel [decidable_eq α] (r : α → α → Prop)
  [decidable_rel r] : decidable_rel (lex r)
| l₁ [] := is_false $ λ h, by cases h
| [] (b::l₂) := is_true lex.nil
| (a::l₁) (b::l₂) := begin
  haveI := decidable_rel l₁ l₂,
  refine decidable_of_iff (r a b ∨ a = b ∧ lex r l₁ l₂) ⟨λ h, _, λ h, _⟩,
  { rcases h with h | ⟨rfl, h⟩,
    { exact lex.rel h },
    { exact lex.cons h } },
  { rcases h with _|⟨_,_,_,h⟩|⟨_,_,_,_,h⟩,
    { exact or.inr ⟨rfl, h⟩ },
    { exact or.inl h } }
end

theorem append_right (r : α → α → Prop) :
  ∀ {s₁ s₂} t, lex r s₁ s₂ → lex r s₁ (s₂ ++ t)
| _ _ t nil      := nil
| _ _ t (cons h) := cons (append_right _ h)
| _ _ t (rel r)  := rel r

theorem append_left (R : α → α → Prop) {t₁ t₂} (h : lex R t₁ t₂) :
  ∀ s, lex R (s ++ t₁) (s ++ t₂)
| []      := h
| (a::l) := cons (append_left l)

theorem imp {r s : α → α → Prop} (H : ∀ a b, r a b → s a b) :
  ∀ l₁ l₂, lex r l₁ l₂ → lex s l₁ l₂
| _ _ nil      := nil
| _ _ (cons h) := cons (imp _ _ h)
| _ _ (rel r)  := rel (H _ _ r)

theorem to_ne : ∀ {l₁ l₂ : list α}, lex (≠) l₁ l₂ → l₁ ≠ l₂
| _ _ (cons h) e := to_ne h (list.cons.inj e).2
| _ _ (rel r)  e := r (list.cons.inj e).1

theorem _root_.decidable.list.lex.ne_iff [decidable_eq α]
  {l₁ l₂ : list α} (H : length l₁ ≤ length l₂) : lex (≠) l₁ l₂ ↔ l₁ ≠ l₂ :=
⟨to_ne, λ h, begin
  induction l₁ with a l₁ IH generalizing l₂; cases l₂ with b l₂,
  { contradiction },
  { apply nil },
  { exact (not_lt_of_ge H).elim (succ_pos _) },
  { by_cases ab : a = b,
    { subst b, apply cons,
      exact IH (le_of_succ_le_succ H) (mt (congr_arg _) h) },
    { exact rel ab } }
end⟩

theorem ne_iff {l₁ l₂ : list α} (H : length l₁ ≤ length l₂) : lex (≠) l₁ l₂ ↔ l₁ ≠ l₂ :=
by classical; exact decidable.list.lex.ne_iff H

end lex

--Note: this overrides an instance in core lean
instance has_lt' [has_lt α] : has_lt (list α) := ⟨lex (<)⟩

theorem nil_lt_cons [has_lt α] (a : α) (l : list α) : [] < a :: l :=
lex.nil

instance [linear_order α] : linear_order (list α) :=
linear_order_of_STO' (lex (<))

--Note: this overrides an instance in core lean
instance has_le' [linear_order α] : has_le (list α) :=
preorder.to_has_le _

end list
