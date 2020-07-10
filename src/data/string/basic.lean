/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

Supplementary theorems about the `string` type.
-/
import data.list.basic
import data.char

namespace string

def ltb : iterator → iterator → bool
| s₁ s₂ := begin
  cases s₂.has_next, {exact ff},
  cases h₁ : s₁.has_next, {exact tt},
  exact if s₁.curr = s₂.curr then
    have s₁.next.2.length < s₁.2.length, from
    match s₁, h₁ with ⟨_, a::l⟩, h := nat.lt_succ_self _ end,
    ltb s₁.next s₂.next
  else s₁.curr < s₂.curr,
end
using_well_founded {rel_tac :=
  λ _ _, `[exact ⟨_, measure_wf (λ s, s.1.2.length)⟩]}

instance has_lt' : has_lt string :=
⟨λ s₁ s₂, ltb s₁.mk_iterator s₂.mk_iterator⟩

instance decidable_lt : @decidable_rel string (<) := by apply_instance -- short-circuit type class inference

@[simp] theorem lt_iff_to_list_lt :
  ∀ {s₁ s₂ : string}, s₁ < s₂ ↔ s₁.to_list < s₂.to_list
| ⟨i₁⟩ ⟨i₂⟩ :=
  suffices ∀ {p₁ p₂ s₁ s₂}, ltb ⟨p₁, s₁⟩ ⟨p₂, s₂⟩ ↔ s₁ < s₂, from this,
  begin
    intros,
    induction s₁ with a s₁ IH generalizing p₁ p₂ s₂;
      cases s₂ with b s₂; rw ltb; simp [iterator.has_next],
    { exact iff_of_false bool.ff_ne_tt (lt_irrefl _) },
    { exact iff_of_true rfl list.lex.nil },
    { exact iff_of_false bool.ff_ne_tt (not_lt_of_lt list.lex.nil) },
    { dsimp [iterator.has_next,
        iterator.curr, iterator.next],
      split_ifs,
      { subst b, exact IH.trans list.lex.cons_iff.symm },
      { simp, refine ⟨list.lex.rel, λ e, _⟩,
        cases e, {cases h rfl}, assumption } }
  end

instance has_le : has_le string := ⟨λ s₁ s₂, ¬ s₂ < s₁⟩

instance decidable_le : @decidable_rel string (≤) := by apply_instance -- short-circuit type class inference

@[simp] theorem le_iff_to_list_le
  {s₁ s₂ : string} : s₁ ≤ s₂ ↔ s₁.to_list ≤ s₂.to_list :=
(not_congr lt_iff_to_list_lt).trans not_lt

theorem to_list_inj : ∀ {s₁ s₂}, to_list s₁ = to_list s₂ ↔ s₁ = s₂
| ⟨s₁⟩ ⟨s₂⟩ := ⟨congr_arg _, congr_arg _⟩

instance : decidable_linear_order string :=
by refine_struct {
    lt := (<), le := (≤),
    decidable_lt := by apply_instance,
    decidable_le := string.decidable_le,
    decidable_eq := by apply_instance, .. };
  { simp only [le_iff_to_list_le, lt_iff_to_list_lt, ← to_list_inj], introv,
    apply_field }

end string
