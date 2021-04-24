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

lemma lt_of_ne_last {n : ℕ} {i : fin n.succ} (h : i ≠ fin.last n) : i.1 < n :=
begin
  rw fin.ne_iff_vne at h,
  simp only [fin.val_eq_coe, fin.coe_last] at h ⊢,
  exact lt_of_le_of_ne (lt_succ_iff.mp i.property) h
end

def fin.cast_ne {n : ℕ} (i : fin n.succ) (h : i ≠ fin.last n) : fin n := i.cast_lt $ lt_of_ne_last h

@[simp] lemma fin.cast_succ_cast_ne {n : ℕ} (i : fin n.succ) (h : i ≠ fin.last n)
  : fin.cast_succ (i.cast_ne h) = i := fin.cast_succ_cast_lt i _

lemma card_inj' (n : ℕ) (β) [fintype β] (h : n ≤ ‖β‖) : ‖fin n ↪ β‖ = desc_fac (‖β‖ - n) n :=
begin
  induction n with n hn,
    rw [desc_fac_zero], nontriviality (fin 0 ↪ β),
    obtain ⟨f, g, ne⟩ := exists_pair_ne (fin 0 ↪ β),
    exfalso, apply ne, ext x, exact fin.elim0 x,

  let equiv_classes : (fin n ↪ β) → finset (fin n.succ ↪ β) :=
    λ f : fin n ↪ β, univ.filter (λ g : fin n.succ ↪ β, ∀ k : fin n, f k = g k.succ),

  --let add_one : (fin n → β) → β → fin n.succ → β:= λ f : fin n → β, λ b : β, fin.cons _ f b,

  --let equiv_classes' : (fin n ↪ β) → finset (fin n.succ ↪ β) :=
    --λ f : fin n ↪ β, univ.filter (λ g : fin n.succ ↪ β, ∃ k : β, fin.cons _ f k = g),

  have all_injf_covered : univ = univ.bUnion equiv_classes,
    apply subset.antisymm,
    { rintros f -, rw mem_bUnion,
      exact ⟨⟨λ x, f x.succ, λ _ _ h, fin.succ_inj.mp $ f.injective h⟩, by simp⟩ },
    { exact subset_univ _ },

  have equiv_class_size : ∀ f : fin n ↪ β, |equiv_classes f| = ‖β‖ - n,
  {
    intro f, let poss_vals := univ \ finset.map ⟨f, f.inj'⟩ univ,
    have num_poss_vals : |poss_vals| = ‖β‖ - n, by simp [poss_vals, card_univ, card_sdiff],
    apply le_antisymm,
    { by_contra h, push_neg at h, let first := λ g : fin n.succ ↪ β, g 0,
      suffices : ∃ x ∈ equiv_classes f, ∃ y ∈ equiv_classes f, x ≠ y ∧ first x = first y,
      {
        obtain ⟨x, x_equiv, y, y_equiv, x_ne_y, x_y_agree⟩ := this,
        apply x_ne_y,
        simp only [true_and, mem_filter, mem_univ, fin.coe_eq_cast_succ] at x_equiv y_equiv,

        ext t,
        by_cases h : t = 0,
        { subst h, exact x_y_agree },
        { specialize x_equiv (t.cast_ne h), specialize y_equiv (t.cast_ne h),
          rw fin.cast_succ_cast_ne at x_equiv y_equiv,
          rw [←x_equiv, ←y_equiv] },
      },
      apply finset.exists_ne_map_eq_of_card_lt_of_maps_to,
      rw ←num_poss_vals at h, exact h,

      intros g g_equiv, simp [last] at g_equiv ⊢, by_contra not_inj, push_neg at not_inj,
      -- change simps here
      obtain ⟨a, not_inj⟩ := not_inj, rw g_equiv at not_inj,
      have := g.injective not_inj,
      suffices : fin.cast_succ a ≠ fin.last n, by contradiction,
      exact (fin.cast_succ_lt_last a).ne },
    sorry, /-
    {
      let extend : β → fin n.succ → β := λ b, fin.snoc f b, -- if I don't λ, typechecker &$@!?
      let extender : {x // x ∈ poss_vals} ↪ (fin n.succ ↪ β)
        := ⟨λ b, ⟨extend b, _⟩, _⟩, rotate,
      { intros a₁ a₂ f_eqs, sorry,
      },
      { sorry },
      sorry
    } -/
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
