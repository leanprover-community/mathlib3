/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

Injective functions.
-/
import data.equiv.basic data.option.basic

universes u v w x

namespace function

structure embedding (α : Sort*) (β : Sort*) :=
(to_fun : α → β)
(inj    : injective to_fun)

infixr ` ↪ `:25 := embedding

instance {α : Sort u} {β : Sort v} : has_coe_to_fun (α ↪ β) := ⟨_, embedding.to_fun⟩

end function

protected def equiv.to_embedding {α : Sort u} {β : Sort v} (f : α ≃ β) : α ↪ β :=
⟨f, f.bijective.1⟩

@[simp] theorem equiv.to_embedding_coe_fn {α : Sort u} {β : Sort v} (f : α ≃ β) :
  (f.to_embedding : α → β) = f := rfl

namespace function
namespace embedding

@[simp] theorem to_fun_eq_coe {α β} (f : α ↪ β) : to_fun f = f := rfl

@[simp] theorem coe_fn_mk {α β} (f : α → β) (i) :
  (@mk _ _ f i : α → β) = f := rfl

theorem inj' {α β} : ∀ (f : α ↪ β), injective f
| ⟨f, hf⟩ := hf

@[refl] protected def refl (α : Sort*) : α ↪ α :=
⟨id, injective_id⟩

@[trans] protected def trans {α β γ} (f : α ↪ β) (g : β ↪ γ) : α ↪ γ :=
⟨_, injective_comp g.inj' f.inj'⟩

@[simp] theorem refl_apply {α} (x : α) : embedding.refl α x = x := rfl

@[simp] theorem trans_apply {α β γ} (f : α ↪ β) (g : β ↪ γ) (a : α) :
  (f.trans g) a = g (f a) := rfl

protected def congr {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort x}
  (e₁ : α ≃ β) (e₂ : γ ≃ δ) (f : α ↪ γ) : (β ↪ δ) :=
(equiv.to_embedding e₁.symm).trans (f.trans e₂.to_embedding)

protected noncomputable def of_surjective {α β} {f : β → α} (hf : surjective f) :
  α ↪ β :=
⟨surj_inv hf, injective_surj_inv _⟩

protected noncomputable def equiv_of_surjective {α β} (f : α ↪ β) (hf : surjective f) :
  α ≃ β :=
equiv.of_bijective ⟨f.inj, hf⟩

protected def of_not_nonempty {α β} (hα : ¬ nonempty α) : α ↪ β :=
⟨λa, (hα ⟨a⟩).elim, assume a, (hα ⟨a⟩).elim⟩

noncomputable def set_value {α β} (f : α ↪ β) (a : α) (b : β) : α ↪ β :=
by haveI := classical.dec; exact
if h : ∃ a', f a' = b then
  (equiv.swap a (classical.some h)).to_embedding.trans f
else
  ⟨λ a', if a' = a then b else f a',
   λ a₁ a₂ e, begin
    simp at e, split_ifs at e with h₁ h₂,
    { cc },
    { cases h ⟨_, e.symm⟩ },
    { cases h ⟨_, e⟩ },
    { exact f.2 e }
   end⟩

theorem set_value_eq {α β} (f : α ↪ β) (a : α) (b : β) : set_value f a b a = b :=
begin
  rw [set_value],
  cases classical.dec (∃ a', f a' = b);
    dsimp [dite], {simp},
  simp [equiv.swap_apply_left],
  apply classical.some_spec h
end

/-- Embedding into `option` -/
protected def some {α} : α ↪ option α :=
⟨some, option.injective_some α⟩

def subtype {α} (p : α → Prop) : subtype p ↪ α :=
⟨subtype.val, λ _ _, subtype.eq'⟩

/-- Restrict the codomain of an embedding. -/
def cod_restrict {α β} (p : set β) (f : α ↪ β) (H : ∀ a, f a ∈ p) : α ↪ p :=
⟨λ a, ⟨f a, H a⟩, λ a b h, f.inj (@congr_arg _ _ _ _ subtype.val h)⟩

@[simp] theorem cod_restrict_apply {α β} (p) (f : α ↪ β) (H a) :
  cod_restrict p f H a = ⟨f a, H a⟩ := rfl

def prod_congr {α β γ δ : Type*} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : α × γ ↪ β × δ :=
⟨assume ⟨a, b⟩, (e₁ a, e₂ b),
  assume ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h,
  have a₁ = a₂ ∧ b₁ = b₂, from (prod.mk.inj h).imp (assume h, e₁.inj h) (assume h, e₂.inj h),
  this.left ▸ this.right ▸ rfl⟩

section sum
open sum

def sum_congr {α β γ δ : Type*} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : α ⊕ γ ↪ β ⊕ δ :=
⟨assume s, match s with inl a := inl (e₁ a) | inr b := inr (e₂ b) end,
    assume s₁ s₂ h, match s₁, s₂, h with
    | inl a₁, inl a₂, h := congr_arg inl $ e₁.inj $ inl.inj h
    | inr b₁, inr b₂, h := congr_arg inr $ e₂.inj $ inr.inj h
    end⟩

@[simp] theorem sum_congr_apply_inl {α β γ δ}
  (e₁ : α ↪ β) (e₂ : γ ↪ δ) (a) : sum_congr e₁ e₂ (inl a) = inl (e₁ a) := rfl

@[simp] theorem sum_congr_apply_inr {α β γ δ}
  (e₁ : α ↪ β) (e₂ : γ ↪ δ) (b) : sum_congr e₁ e₂ (inr b) = inr (e₂ b) := rfl

end sum

section sigma
open sigma

def sigma_congr_right {α : Type*} {β γ : α → Type*} (e : ∀ a, β a ↪ γ a) : sigma β ↪ sigma γ :=
⟨λ ⟨a, b⟩, ⟨a, e a b⟩, λ ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h, begin
  injection h with h₁ h₂, subst a₂,
  congr,
  exact (e a₁).2 (eq_of_heq h₂)
end⟩

end sigma

def Pi_congr_right {α : Sort*} {β γ : α → Sort*} (e : ∀ a, β a ↪ γ a) : (Π a, β a) ↪ (Π a, γ a) :=
⟨λf a, e a (f a), λ f₁ f₂ h, funext $ λ a, (e a).inj (congr_fun h a)⟩

def arrow_congr_left {α : Sort u} {β : Sort v} {γ : Sort w}
  (e : α ↪ β) : (γ → α) ↪ (γ → β) :=
Pi_congr_right (λ _, e)

noncomputable def arrow_congr_right {α : Sort u} {β : Sort v} {γ : Sort w} [inhabited γ]
  (e : α ↪ β) : (α → γ) ↪ (β → γ) :=
by haveI := classical.prop_decidable; exact
let f' : (α → γ) → (β → γ) := λf b, if h : ∃c, e c = b then f (classical.some h) else default γ in
⟨f', assume f₁ f₂ h, funext $ assume c,
  have ∃c', e c' = e c, from ⟨c, rfl⟩,
  have eq' : f' f₁ (e c) = f' f₂ (e c), from congr_fun h _,
  have eq_b : classical.some this = c, from e.inj $ classical.some_spec this,
  by simp [f', this, if_pos, eq_b] at eq'; assumption⟩

end embedding
end function

namespace set

/-- The injection map is an embedding between subsets. -/
def embedding_of_subset {α} {s t : set α} (h : s ⊆ t) : s ↪ t :=
⟨λ x, ⟨x.1, h x.2⟩, λ ⟨x, hx⟩ ⟨y, hy⟩ h, by congr; injection h⟩

end set
