/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import data.equiv.basic
import data.sigma.basic
import algebra.group.defs

/-!
# Injective functions
-/

universes u v w x

namespace function

/-- `α ↪ β` is a bundled injective function. -/
@[nolint has_inhabited_instance] -- depending on cardinalities, an injective function may not exist
structure embedding (α : Sort*) (β : Sort*) :=
(to_fun : α → β)
(inj'   : injective to_fun)

infixr ` ↪ `:25 := embedding

instance {α : Sort u} {β : Sort v} : has_coe_to_fun (α ↪ β) := ⟨_, embedding.to_fun⟩

initialize_simps_projections embedding (to_fun → apply)

end function

/-- Convert an `α ≃ β` to `α ↪ β`. -/
@[simps]
protected def equiv.to_embedding {α : Sort u} {β : Sort v} (f : α ≃ β) : α ↪ β :=
⟨f, f.injective⟩

namespace function
namespace embedding

@[ext] lemma ext {α β} {f g : embedding α β} (h : ∀ x, f x = g x) : f = g :=
by cases f; cases g; simpa using funext h

lemma ext_iff {α β} {f g : embedding α β} : (∀ x, f x = g x) ↔ f = g :=
⟨ext, λ h _, by rw h⟩

@[simp] theorem to_fun_eq_coe {α β} (f : α ↪ β) : to_fun f = f := rfl

@[simp] theorem coe_fn_mk {α β} (f : α → β) (i) :
  (@mk _ _ f i : α → β) = f := rfl

theorem injective {α β} (f : α ↪ β) : injective f := f.inj'

@[refl, simps {simp_rhs := tt}]
protected def refl (α : Sort*) : α ↪ α :=
⟨id, injective_id⟩

@[trans, simps {simp_rhs := tt}]
protected def trans {α β γ} (f : α ↪ β) (g : β ↪ γ) : α ↪ γ :=
⟨g ∘ f, g.injective.comp f.injective⟩

@[simp]
lemma equiv_to_embedding_trans_symm_to_embedding {α β : Sort*} (e : α ≃ β) :
  e.to_embedding.trans e.symm.to_embedding = embedding.refl _ :=
by { ext, simp, }

@[simp]
lemma equiv_symm_to_embedding_trans_to_embedding {α β : Sort*} (e : α ≃ β) :
  e.symm.to_embedding.trans e.to_embedding = embedding.refl _ :=
by { ext, simp, }

protected def congr {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort x}
  (e₁ : α ≃ β) (e₂ : γ ≃ δ) (f : α ↪ γ) : (β ↪ δ) :=
(equiv.to_embedding e₁.symm).trans (f.trans e₂.to_embedding)

/-- A right inverse `surj_inv` of a surjective function as an `embedding`. -/
protected noncomputable def of_surjective {α β} (f : β → α) (hf : surjective f) :
  α ↪ β :=
⟨surj_inv hf, injective_surj_inv _⟩

/-- Convert a surjective `embedding` to an `equiv` -/
protected noncomputable def equiv_of_surjective {α β} (f : α ↪ β) (hf : surjective f) :
  α ≃ β :=
equiv.of_bijective f ⟨f.injective, hf⟩

protected def of_not_nonempty {α β} (hα : ¬ nonempty α) : α ↪ β :=
⟨λa, (hα ⟨a⟩).elim, assume a, (hα ⟨a⟩).elim⟩

/-- Change the value of an embedding `f` at one point. If the prescribed image
is already occupied by some `f a'`, then swap the values at these two points. -/
def set_value {α β} (f : α ↪ β) (a : α) (b : β) [∀ a', decidable (a' = a)]
  [∀ a', decidable (f a' = b)] : α ↪ β :=
⟨λ a', if a' = a then b else if f a' = b then f a else f a',
  begin
    intros x y h,
    dsimp at h,
    split_ifs at h; try { substI b }; try { simp only [f.injective.eq_iff] at * }; cc
  end⟩

theorem set_value_eq {α β} (f : α ↪ β) (a : α) (b : β) [∀ a', decidable (a' = a)]
  [∀ a', decidable (f a' = b)] : set_value f a b a = b :=
by simp [set_value]

/-- Embedding into `option` -/
protected def some {α} : α ↪ option α :=
⟨some, option.some_injective α⟩

/-- Embedding of a `subtype`. -/
def subtype {α} (p : α → Prop) : subtype p ↪ α :=
⟨coe, λ _ _, subtype.ext_val⟩

@[simp] lemma coe_subtype {α} (p : α → Prop) : ⇑(subtype p) = coe := rfl

/-- Choosing an element `b : β` gives an embedding of `punit` into `β`. -/
def punit {β : Sort*} (b : β) : punit ↪ β :=
⟨λ _, b, by { rintros ⟨⟩ ⟨⟩ _, refl, }⟩

/-- Fixing an element `b : β` gives an embedding `α ↪ α × β`. -/
def sectl (α : Sort*) {β : Sort*} (b : β) : α ↪ α × β :=
⟨λ a, (a, b), λ a a' h, congr_arg prod.fst h⟩

/-- Fixing an element `a : α` gives an embedding `β ↪ α × β`. -/
def sectr {α : Sort*} (a : α) (β : Sort*): β ↪ α × β :=
⟨λ b, (a, b), λ b b' h, congr_arg prod.snd h⟩

/-- Restrict the codomain of an embedding. -/
def cod_restrict {α β} (p : set β) (f : α ↪ β) (H : ∀ a, f a ∈ p) : α ↪ p :=
⟨λ a, ⟨f a, H a⟩, λ a b h, f.injective (@congr_arg _ _ _ _ subtype.val h)⟩

@[simp] theorem cod_restrict_apply {α β} (p) (f : α ↪ β) (H a) :
  cod_restrict p f H a = ⟨f a, H a⟩ := rfl

/-- If `e₁` and `e₂` are embeddings, then so is `prod.map e₁ e₂ : (a, b) ↦ (e₁ a, e₂ b)`. -/
def prod_map {α β γ δ : Type*} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : α × γ ↪ β × δ :=
⟨prod.map e₁ e₂, e₁.injective.prod_map e₂.injective⟩

@[simp] lemma coe_prod_map {α β γ δ : Type*} (e₁ : α ↪ β) (e₂ : γ ↪ δ) :
  ⇑(e₁.prod_map e₂) = prod.map e₁ e₂ :=
rfl

section sum
open sum

/-- If `e₁` and `e₂` are embeddings, then so is `sum.map e₁ e₂`. -/
def sum_map {α β γ δ : Type*} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : α ⊕ γ ↪ β ⊕ δ :=
⟨sum.map e₁ e₂,
    assume s₁ s₂ h, match s₁, s₂, h with
    | inl a₁, inl a₂, h := congr_arg inl $ e₁.injective $ inl.inj h
    | inr b₁, inr b₂, h := congr_arg inr $ e₂.injective $ inr.inj h
    end⟩

@[simp] theorem coe_sum_map {α β γ δ} (e₁ : α ↪ β) (e₂ : γ ↪ δ) :
  ⇑(sum_map e₁ e₂) = sum.map e₁ e₂ :=
rfl

/-- The embedding of `α` into the sum `α ⊕ β`. -/
@[simps] def inl {α β : Type*} : α ↪ α ⊕ β :=
⟨sum.inl, λ a b, sum.inl.inj⟩

/-- The embedding of `β` into the sum `α ⊕ β`. -/
@[simps] def inr {α β : Type*} : β ↪ α ⊕ β :=
⟨sum.inr, λ a b, sum.inr.inj⟩

end sum

section sigma

variables {α α' : Type*} {β : α → Type*} {β' : α' → Type*}

/-- `sigma.mk` as an `function.embedding`. -/
@[simps apply] def sigma_mk (a : α) : β a ↪ Σ x, β x :=
⟨sigma.mk a, sigma_mk_injective⟩

/-- If `f : α ↪ α'` is an embedding and `g : Π a, β α ↪ β' (f α)` is a family
of embeddings, then `sigma.map f g` is an embedding. -/
@[simps apply] def sigma_map (f : α ↪ α') (g : Π a, β a ↪ β' (f a)) :
  (Σ a, β a) ↪ Σ a', β' a' :=
⟨sigma.map f (λ a, g a), f.injective.sigma_map (λ a, (g a).injective)⟩

end sigma

def Pi_congr_right {α : Sort*} {β γ : α → Sort*} (e : ∀ a, β a ↪ γ a) : (Π a, β a) ↪ (Π a, γ a) :=
⟨λf a, e a (f a), λ f₁ f₂ h, funext $ λ a, (e a).injective (congr_fun h a)⟩

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
  have eq_b : classical.some this = c, from e.injective $ classical.some_spec this,
  by simp [f', this, if_pos, eq_b] at eq'; assumption⟩

protected def subtype_map {α β} {p : α → Prop} {q : β → Prop} (f : α ↪ β)
  (h : ∀{{x}}, p x → q (f x)) : {x : α // p x} ↪ {y : β // q y} :=
⟨subtype.map f h, subtype.map_injective h f.2⟩

open set

/-- `set.image` as an embedding `set α ↪ set β`. -/
@[simps apply] protected def image {α β} (f : α ↪ β) : set α ↪ set β :=
⟨image f, f.2.image_injective⟩

lemma swap_apply {α β : Type*} [decidable_eq α] [decidable_eq β] (f : α ↪ β) (x y z : α) :
  equiv.swap (f x) (f y) (f z) = f (equiv.swap x y z) :=
f.injective.swap_apply x y z

lemma swap_comp {α β : Type*} [decidable_eq α] [decidable_eq β] (f : α ↪ β) (x y : α) :
  equiv.swap (f x) (f y) ∘ f = f ∘ equiv.swap x y :=
f.injective.swap_comp x y

end embedding
end function

namespace equiv

@[simp]
lemma refl_to_embedding {α : Type*} : (equiv.refl α).to_embedding = function.embedding.refl α := rfl

@[simp]
lemma trans_to_embedding {α β γ : Type*} (e : α ≃ β) (f : β ≃ γ) :
  (e.trans f).to_embedding = e.to_embedding.trans f.to_embedding := rfl

end equiv

namespace set

/-- The injection map is an embedding between subsets. -/
@[simps apply] def embedding_of_subset {α} (s t : set α) (h : s ⊆ t) : s ↪ t :=
⟨λ x, ⟨x.1, h x.2⟩, λ ⟨x, hx⟩ ⟨y, hy⟩ h, by { congr, injection h }⟩

end set

-- TODO: these two definitions probably belong somewhere else, so that we can remove the
-- `algebra.group.defs` import.

/--
The embedding of a left cancellative semigroup into itself
by left multiplication by a fixed element.
 -/
@[to_additive
  "The embedding of a left cancellative additive semigroup into itself
   by left translation by a fixed element.", simps]
def mul_left_embedding {G : Type u} [left_cancel_semigroup G] (g : G) : G ↪ G :=
{ to_fun := λ h, g * h, inj' := mul_right_injective g }

/--
The embedding of a right cancellative semigroup into itself
by right multiplication by a fixed element.
 -/
@[to_additive
  "The embedding of a right cancellative additive semigroup into itself
   by right translation by a fixed element.", simps]
def mul_right_embedding {G : Type u} [right_cancel_semigroup G] (g : G) : G ↪ G :=
{ to_fun := λ h, h * g, inj' := mul_left_injective g }
