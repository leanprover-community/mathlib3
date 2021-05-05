/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import data.fintype.card
import data.equiv.fin
import data.nat.factorial

/-!
# Birthday Problem

This file establishes the cardinality of `α ↪ β` in full generality.
-/

open finset

local notation `|` x `|` := finset.card x
local notation `‖` x `‖` := fintype.card x

open_locale nat

namespace fintype

-- why does `ᶜ` not work here but elsewhere it does? aren't they defeq due to the instance?
def to_be_named {α β γ : Type*} :
((α ⊕ β) ↪ γ) ≃ (Σ f : α ↪ γ, β ↪ (set.range f).compl) :=
{ to_fun := λ f, ⟨function.embedding.inl.trans f, -- α ↪ γ
  ⟨λ b, ⟨f (sum.inr b), -- β → (f α)ᶜ

    begin --proving membership in not the range
      apply set.mem_compl,
      suffices : ∀ (x : α), ¬f (sum.inl x) = f (sum.inr b), by simpa,
      intros x,
      rw [function.injective.eq_iff f.injective],
      simp only [not_false_iff]
    end⟩,

  begin -- prove injective(β → (f α)ᶜ)
    intros a b f_eq,
    simp only [subtype.mk_eq_mk] at f_eq,
    apply_fun @sum.inr α β using sum.inr_injective,
    apply_fun f using function.embedding.injective f,
    exact f_eq
  end⟩⟩,

  inv_fun := λ ⟨f, g⟩,
    ⟨(equiv.sum_arrow_equiv_prod_arrow _ _ _).symm ⟨f, (λ x, g x)⟩, -- implicit coe here

  begin -- prove that this amalgamation is injective; think this is the best way
    rintros (a₁|b₁) (a₂|b₂) f_eq;
    rw equiv.sum_arrow_equiv_prod_arrow at f_eq;
    simp only [equiv.coe_fn_symm_mk, sum.elim_inl, sum.elim_inr] at f_eq,
    { rw f.injective f_eq },
    { exfalso, apply (g b₂).property, rw [subtype.val_eq_coe, ←f_eq], simp },
    { exfalso, apply (g b₁).property, rw [subtype.val_eq_coe, f_eq], simp },
    { rw g.injective (subtype.coe_injective f_eq) }
  end⟩,

  left_inv := λ f, by { ext, cases x; simp! [equiv.sum_arrow_equiv_prod_arrow] },

  right_inv := λ ⟨g, h⟩, by begin
    dsimp only,
    have : { function.embedding . to_fun := ⇑h, inj' := h.injective } = h, by { ext, simp },
    ext; simp! [equiv.sum_arrow_equiv_prod_arrow, this]
  end }

def some_other_nameless_thing {α β : Type*} [unique α] : (α ↪ β) ≃ β :=
{ to_fun := λ f, f (default α),
  inv_fun := λ x, ⟨λ _, x, λ _ _ _, subsingleton.elim _ _⟩,
  left_inv := λ _, by { ext, simp_rw [function.embedding.coe_fn_mk], congr },
  right_inv := λ _, by simp }

-- replace infinite embedding instance
def function.embedding.subsingleton {α β} [infinite α] [fintype β] : subsingleton (α ↪ β) :=
⟨λ f, let ⟨_, _, ne, f_eq⟩ := fintype.exists_ne_map_eq_of_infinite f
      in false.elim $ ne $ f.injective f_eq⟩

noncomputable def fintype_of_not_infinite {α : Type*} (h : ¬ infinite α) : fintype α :=
by rw [←not_nonempty_fintype, not_not] at h; exact h.some

@[priority 900] -- would rather have the more restrictive, computable instance
noncomputable instance function.embedding.fintype'' {α β : Type*} [fintype β] : fintype (α ↪ β) :=
begin
  by_cases h : infinite α,
  { resetI, apply_instance },
  { haveI := fintype_of_not_infinite h, classical, apply_instance },
end

-- αβ not needed in original file
lemma fintype.exists_infinite_fiber {α β} [infinite α] [fintype β] (f : α → β) :
  ∃ y : β, infinite (f ⁻¹' {y}) :=
begin
  classical,
  by_contra hf,
  push_neg at hf,

  haveI := λ y, fintype_of_not_infinite $ hf y,
  let key : fintype α :=
  { elems := univ.bUnion (λ (y : β), (f ⁻¹' {y}).to_finset),
    complete := by simp },
  exact infinite.not_fintype key,
end

-- make equiv_inj_subtype non-private, rename subtype_injective_equiv_embedding,
-- move to data/equiv/basic

private lemma card_embedding_aux (n : ℕ) (β) [fintype β] [decidable_eq β] (h : n ≤ ‖β‖) :
  ‖fin n ↪ β‖ = nat.desc_fac (‖β‖ - n) n :=
begin
  induction n with n hn,
  { nontriviality (fin 0 ↪ β),
    rw [nat.desc_fac_zero, fintype.card_eq_one_iff],
    refine ⟨nonempty.some nontrivial.to_nonempty, λ x, function.embedding.ext fin.elim0⟩ },

  rw [nat.succ_eq_add_one, ←card_congr (equiv.embedding_congr fin_sum_fin_equiv (equiv.refl β))],
  rw card_congr to_be_named,
  all_goals { try { apply_instance } },

  have : ∀ (f : fin n ↪ β), ‖fin 1 ↪ ↥((set.range f).compl)‖ = ‖β‖ - n,
  {
    intro f, rw card_congr some_other_nameless_thing; try {apply_instance}, -- swap the `rw` here

    rw card_of_finset' (finset.map f univ)ᶜ,
    { simp [card_compl, card_map] },
    { -- further evidence `ᶜ` is defeq, something odd
    change ∀ x, x ∈ (map f univ)ᶜ ↔ x ∈ (set.range ⇑f)ᶜ,
    simp }
  },

  rw card_sigma,
  simp_rw this,
  rw [sum_const, card_univ, nsmul_eq_mul, nat.cast_id],
  unfold nat.desc_fac,

  rw hn (nat.lt_of_succ_le h).le,
  set t := ‖β‖ - n.succ with ht,
  have : ‖β‖ - n = t.succ,
  { rw [ht, nat.succ_eq_add_one, ←nat.sub_sub_assoc, nat.succ_sub_one],
    exact h,
    exact nat.succ_pos _ },
  rw [this, mul_comm, nat.succ_desc_fac]
end

variables {α β : Type*} [fintype α] [fintype β] [decidable_eq α] [decidable_eq β]

/- Establishes the cardinality of the type of all injections, if any exist.  -/
@[simp] theorem card_embedding (h : ‖α‖ ≤ ‖β‖) : ‖α ↪ β‖ = (nat.desc_fac (‖β‖ - ‖α‖) ‖α‖) :=
begin
  trunc_cases fintype.equiv_fin α with eq,
  rw fintype.card_congr (equiv.embedding_congr eq (equiv.refl β)),
  exact card_embedding_aux _ _ h,
end

/-- If `‖β‖ < ‖α‖` there is no embeddings `α ↪ β`. This is the pigeonhole principle. -/
@[simp] theorem card_embedding_eq_zero (h : ‖β‖ < ‖α‖) : ‖α ↪ β‖ = 0 :=
begin
  rw card_eq_zero_iff,
  intro f,
  obtain ⟨x, y, eq, fne⟩ := fintype.exists_ne_map_eq_of_card_lt f h,
  have := f.injective fne, contradiction
end

theorem card_embedding_eq_if: ‖α ↪ β‖ = if ‖α‖ ≤ ‖β‖ then nat.desc_fac (‖β‖ - ‖α‖) ‖α‖ else 0 :=
begin
  split_ifs with h,
    exact card_embedding h,
    exact card_embedding_eq_zero (not_le.mp h)
end

lemma card_embedding_eq_infinite {α β} [infinite α] [fintype β] : fintype.card (α ↪ β) = 0 :=
by erw [card, univ, function.embedding.fintype', finset.card_empty]

end fintype
