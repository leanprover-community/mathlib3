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

local notation `|` x `|` := finset.card x
local notation `‖` x `‖` := fintype.card x

open_locale nat

namespace fintype

section function_embedding

open function.embedding

@[simp] lemma why_isn't_this_simp_yet {α β : Type*} (f : α ↪ β) : ∀ inj, (⟨f, inj⟩ : α ↪ β) = f :=
λ _, by ext; simp

def to_be_named_pre {α β γ : Type*} :
((α ⊕ β) ↪ γ) ≃ {f : (α ↪ γ) × (β ↪ γ) // disjoint (set.range f.1) (set.range f.2)} :=
{ to_fun := λ f, ⟨(inl.trans f, inr.trans f),
  begin
    rintros _ ⟨⟨a, h⟩, ⟨b, rfl⟩⟩,
    simp only [trans_apply, inl_apply, inr_apply] at h,
    have : sum.inl a = sum.inr b := f.injective h,
    simp only at this,
    assumption
  end⟩,

  inv_fun := λ ⟨⟨f, g⟩, disj⟩,
    ⟨λ x, match x with
    | (sum.inl a) := f a
    | (sum.inr b) := g b
    end,
    begin
      rintros (a₁|b₁) (a₂|b₂) f_eq;
      simp only [equiv.coe_fn_symm_mk, sum.elim_inl, sum.elim_inr] at f_eq,
      { rw f.injective f_eq },
      { simp! only at f_eq, exfalso, exact disj ⟨⟨a₁, by simp⟩, ⟨b₂, by simp [f_eq]⟩⟩  },
      { simp! only at f_eq, exfalso, exact disj ⟨⟨a₂, by simp⟩, ⟨b₁, by simp [f_eq]⟩⟩  },
      { rw g.injective f_eq }
    end⟩,

  left_inv := λ f, by { dsimp only, ext, cases x; simp! },
  right_inv := λ ⟨⟨f, g⟩, _⟩, by { simp only [prod.mk.inj_iff], split; ext; simp! } }

def to_be_named' {α β γ : Type*} :
  {f : (α ↪ γ) × (β ↪ γ) // disjoint (set.range f.1) (set.range f.2)} ≃
  (Σ f : α ↪ γ, β ↪ (set.range f).compl) :=
{ to_fun := λ ⟨⟨f, g⟩, disj⟩, ⟨f, ⟨λ b, ⟨g b, set.disjoint_right.mp disj (⟨b, rfl⟩)⟩,
  λ _ _ eq, by { rw subtype.mk_eq_mk at eq, exact g.injective eq }⟩⟩, -- one day I'll figure out ▸

  inv_fun := λ ⟨f, g⟩, ⟨⟨f, g.trans (function.embedding.subtype _)⟩,
  begin
    dsimp only,
    have : set.range (g.trans (function.embedding.subtype (λ x, x ∈ (set.range f).compl)))
      ⊆ (set.range f).compl,
    { rintros _ ⟨t, rfl⟩, simp },
    exact set.disjoint_of_subset_right this disjoint_compl_right
  end⟩,

  right_inv := λ ⟨_,_⟩, by simp!,
  left_inv := λ ⟨⟨_,_⟩,_⟩, by { dsimp only, ext; simp! } }

def to_be_named {α β γ : Type*} : ((α ⊕ β) ↪ γ) ≃ (Σ f : α ↪ γ, β ↪ (set.range f).compl)
:= equiv.trans to_be_named_pre to_be_named'

def some_other_nameless_thing {α β : Type*} [unique α] : (α ↪ β) ≃ β :=
{ to_fun := λ f, f (default α),
  inv_fun := λ x, ⟨λ _, x, λ _ _ _, subsingleton.elim _ _⟩,
  left_inv := λ _, by { ext, simp_rw [function.embedding.coe_fn_mk], congr },
  right_inv := λ _, by simp }

end function_embedding

section fintype

open fintype

-- replace infinite embedding instance
def function.embedding.subsingleton {α β} [infinite α] [fintype β] : subsingleton (α ↪ β) :=
⟨λ f, let ⟨_, _, ne, f_eq⟩ := exists_ne_map_eq_of_infinite f in false.elim $ ne $ f.injective f_eq⟩

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
  { elems := finset.univ.bUnion (λ (y : β), (f ⁻¹' {y}).to_finset),
    complete := by simp },
  exact infinite.not_fintype key,
end

end fintype

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

    rw card_of_finset' (finset.map f finset.univ)ᶜ,
    { simp [finset.card_compl, finset.card_map] },
    { -- further evidence `ᶜ` is defeq, something odd
    change ∀ x, x ∈ (finset.map f finset.univ)ᶜ ↔ x ∈ (set.range ⇑f)ᶜ,
    simp }
  },

  rw card_sigma,
  simp_rw this,
  rw [finset.sum_const, finset.card_univ, nsmul_eq_mul, nat.cast_id],
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
by erw [fintype.card, finset.univ, function.embedding.fintype', finset.card_empty]

end fintype
