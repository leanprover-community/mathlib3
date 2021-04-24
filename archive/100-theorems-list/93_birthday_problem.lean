/-
Copyright (c) 2020 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import data.fintype.card
import data.nat.factorial
import data.equiv.fin
import tactic
open_locale classical nat

open finset function nat
variables {α β : Type*} [fintype α] [fintype β]
local notation `|` x `|` := finset.card x
local notation `‖` x `‖` := fintype.card x

/-- desc_fac n k = (n + k)! / n! with no divisions -/
def desc_fac (n : ℕ) : ℕ → ℕ
| 0 := 1
| (k + 1) := (n + k + 1) * desc_fac k

@[simp] lemma desc_fac_zero (n : ℕ) : desc_fac n 0 = 1 := rfl

@[simp] lemma zero_desc_fac (k : ℕ) : desc_fac 0 k = k! :=
begin
  induction k with t ht, refl,
  unfold desc_fac, rw [ht, zero_add, factorial_succ]
end

theorem eval_desc_fac (n : ℕ) : ∀ k : ℕ, (n + k)! = n! * desc_fac n k
| 0 := by simp!
| (k + 1) := by unfold desc_fac; rw [←mul_assoc, mul_comm n!, mul_assoc, ←eval_desc_fac]; simp!

def embedding_of_subtype (α β) [fintype α] [fintype β] : (α ↪ β) ≃ {f : α → β // injective f} :=
{ to_fun := λ f, ⟨f, f.injective⟩,
  inv_fun := λ f, ⟨f.val, f.property⟩,
  left_inv := λ f, by {ext, simp},
  right_inv := λ f, by simp }

-- `decidable_pred (@injective α β)` and various variations didn't give me an instance 🤷‍♂️
noncomputable instance fintype.embedding {α β} [fintype α] [fintype β] : fintype (α ↪ β) :=
fintype.of_equiv {f : α → β // injective f} (embedding_of_subtype α β).symm

-- I can never quite figure out ▸ :(
lemma less_injs {α β} [fintype α] [fintype β] : ‖α ↪ β‖ ≤ ‖α → β‖ :=
by {rw fintype.of_equiv_card, exact fintype.card_subtype_le injective}

lemma card_inj' (n : ℕ) (β) [fintype β] (h : n ≤ ‖β‖) : ‖fin n ↪ β‖ = desc_fac (‖β‖ - n) n :=
begin
  induction n with n hn,
    rw [desc_fac_zero], nontriviality (fin 0 ↪ β),
    obtain ⟨f, g, ne⟩ := exists_pair_ne (fin 0 ↪ β),
    exfalso, apply ne, ext x, exact fin.elim0 x,

  let extend : (fin n → β) → β → fin n.succ → β :=
    λ f : fin n → β, λ b : β, fin.cons b f,

  let equiv_classes : (fin n ↪ β) → finset (fin n.succ ↪ β) :=
    λ f : fin n ↪ β, univ.filter (λ g : fin n.succ ↪ β, ∃ k : β, extend f k = g),

  have all_injf_covered : univ = univ.bUnion equiv_classes, sorry, /-
    apply subset.antisymm,
    { rintros f -, rw mem_bUnion,
      refine ⟨⟨fin.tail f, λ _ _ h, fin.succ_inj.mp $ f.injective h⟩, _⟩,
      suffices : ∃ (a : β), extend (fin.tail ⇑f) a = ⇑f, by simpa,
      use f 0, simp only [extend], exact fin.cons_self_tail _ },
    { exact subset_univ _ }, -/

  have equiv_class_size : ∀ f : fin n ↪ β, |equiv_classes f| = ‖β‖ - n,
  {
    intro f, let poss_vals := univ \ finset.map ⟨f, f.inj'⟩ univ,
    have num_poss_vals : |poss_vals| = ‖β‖ - n, by simp [poss_vals, card_univ, card_sdiff],
    apply le_antisymm, sorry, /-
    { by_contra card_too_big, let first := λ g : fin n.succ ↪ β, g 0,
      -- (if I just write down x 0 = y 0, it won't work! need this shim)
      suffices : ∃ x ∈ equiv_classes f, ∃ y ∈ equiv_classes f, x ≠ y ∧ first x = first y,
      { obtain ⟨x, x_equiv, y, y_equiv, x_ne_y, x_y_agree⟩ := this,
        simp only [true_and, mem_filter, mem_univ, fin.coe_eq_cast_succ] at x_equiv y_equiv,
        obtain ⟨x_zero, x_equiv⟩ := x_equiv, obtain ⟨y_zero, y_equiv⟩ := y_equiv,
        simp only [extend, first] at x_y_agree x_equiv y_equiv,

        apply x_ne_y, ext t, revert t,
        refine fin.induction _ _,
          exact x_y_agree,
        rintros t -, rw [←x_equiv, ←y_equiv, fin.cons_succ, fin.cons_succ] },
      apply finset.exists_ne_map_eq_of_card_lt_of_maps_to,
      push_neg at card_too_big, rw ←num_poss_vals at card_too_big, exact card_too_big,

      intros g g_equiv, simp [first, extend] at g_equiv ⊢, obtain ⟨k, g_equiv⟩ := g_equiv,
      have : g 0 = k, by rw [←g_equiv, fin.cons_zero],
      intros x eq, have : g x.succ = g 0, by rw [←eq, ←g_equiv, fin.cons_succ],
      apply fin.succ_ne_zero x, exact g.injective this }, -/
    {
      let extended : finset (fin n.succ ↪ β) :=
        finset.map ⟨λ x : {x // x ∈ poss_vals}, ⟨extend f x, _⟩, _⟩ poss_vals.attach,
      rotate,
      { intros a₁ a₂ eq, simp only [extend] at eq, sorry },
      { intros a₁ a₂ eq, simp only [extend] at eq,
        ext, rw funext_iff at eq,
        specialize eq 0, rwa [fin.cons_zero, fin.cons_zero] at eq },
      have : |extended| = ‖β‖ - n, by simp [extended, poss_vals, card_sdiff, card_univ],
      rw ←this, apply card_le_of_subset, rintros g g_extended,
      simp only [extend, true_and, mem_filter, mem_univ],
      use g 0, ext t, revert t,
      refine fin.induction (by rw fin.cons_zero) _,
      rintros i -, sorry
    }
  },
  rw [←card_univ, all_injf_covered, card_bUnion], simp [equiv_class_size], unfold desc_fac,
  -- use hn and stuff
  sorry, sorry,
end

/-
theorem birthday : 2 * ‖fin 23 ↪ fin 365‖ < ‖fin 23 → fin 365‖ :=
begin
  rw [card_inj, fintype.card_fun, fintype.card_fin, fintype.card_fin],
  norm_num [desc_fac],
  norm_num,
end

theorem birthday' : 2 * ‖fin 22 ↪ fin 365‖ > ‖fin 22 → fin 365‖ :=
begin
  rw [card_inj, fintype.card_fun, fintype.card_fin, fintype.card_fin],
  norm_num [desc_fac],
  norm_num,
end

-/
