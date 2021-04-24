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
    λ f : fin n ↪ β, univ.filter (λ g : fin n.succ ↪ β, ∀ k : fin n, f k = g k),

  have all_injf_covered : univ = univ.bUnion equiv_classes, sorry, /-
    apply subset.antisymm,
    { rintros f -, rw mem_bUnion, use (λ x : fin n, f x),
      { intros a b hab, replace hab := f.inj' hab,
        simp only [fin.coe_eq_cast_succ, order_embedding.eq_iff_eq] at hab, exact hab },
      simp only [mem_filter, embedding.coe_fn_mk, mem_univ,
                 implies_true_iff, eq_self_iff_true, and_self] }, -- check this simp only after
    { exact subset_univ _ }, -/

  have equiv_class_size : ∀ f : fin n ↪ β, |equiv_classes f| = ‖β‖ - n,
  {
    intro f, let poss_vals := univ \ finset.map ⟨f, f.inj'⟩ univ,
    have num_poss_vals : |poss_vals| = ‖β‖ - n, by simp [poss_vals, card_univ, card_sdiff],
    apply le_antisymm, /-
    { by_contra h, push_neg at h, let last := λ g : fin n.succ ↪ β, g (fin.last n),
      suffices : ∃ x ∈ equiv_classes f, ∃ y ∈ equiv_classes f, x ≠ y ∧ last x = last y,
      {
        obtain ⟨x, x_equiv, y, y_equiv, x_ne_y, x_y_agree⟩ := this,
        apply x_ne_y,
        simp only [true_and, mem_filter, mem_univ, fin.coe_eq_cast_succ] at x_equiv y_equiv,

        rw ←embedding.ext_iff, intro t,
        by_cases h : t = fin.last n,
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
      exact (fin.cast_succ_lt_last a).ne }, -/
    sorry,
    {
      let my_fun : {x // x ∈ poss_vals} ↪ (fin n.succ ↪ β)
       := ⟨λ val, ⟨λ t, if h : t = fin.last n then val else f (t.cast_ne h), _⟩, _⟩, rotate,
      { intros a₁ a₂ f_eq, dsimp only at f_eq, split_ifs at f_eq with h₁ h₂ h₂,
        { substs h₁ h₂ },
        { sorry }, -- working on making these not `tidy`! but it works for now
        { sorry }, -- these just unfold stuff about `coe`s basically
        { have := f.injective f_eq, sorry } },
      { intros a₁ a₂ f_eq, dsimp only at f_eq,
        rw ←embedding.ext_iff at f_eq, specialize f_eq (fin.last n),
        simp only [dif_pos, embedding.coe_fn_mk] at f_eq, ext, assumption },
      let some_embeds : finset (fin n.succ ↪ β)
        := finset.map my_fun poss_vals.attach,
      have : |some_embeds| = ‖β‖ - n, by simpa, rw ←this, apply finset.card_le_of_subset,
      intros one two, simp at two, simp [two],
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
