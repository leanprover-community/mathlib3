/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro

In the standard library we cannot assume the univalence axiom.
We say two types are equivalent if they are isomorphic.

Two equivalent types have the same cardinality.
-/
import data.prod data.nat.pairing logic.function tactic data.set.lattice
import algebra.group
open function

universes u v w
variables {α : Sort u} {β : Sort v} {γ : Sort w}

namespace subtype

/-- Restriction of a function to a function on subtypes. -/
def map {p : α → Prop} {q : β → Prop} (f : α → β) (h : ∀a, p a → q (f a)) :
  subtype p → subtype q
| ⟨v, hv⟩ := ⟨f v, h v hv⟩

theorem map_comp {p : α → Prop} {q : β → Prop} {r : γ → Prop} {x : subtype p}
  (f : α → β) (h : ∀a, p a → q (f a)) (g : β → γ) (l : ∀a, q a → r (g a)) :
  map g l (map f h x) = map (g ∘ f) (assume a ha, l (f a) $ h a ha) x :=
by cases x with v h; refl

theorem map_id {p : α → Prop} {h : ∀a, p a → p (id a)} : map (@id α) h = id :=
funext $ assume ⟨v, h⟩, rfl

end subtype

namespace function

theorem left_inverse.f_g_eq_id {f : α → β} {g : β → α} (h : left_inverse f g) : f ∘ g = id :=
funext $ h

theorem right_inverse.g_f_eq_id {f : α → β} {g : β → α} (h : right_inverse f g) : g ∘ f = id :=
funext $ h

theorem left_inverse.comp {f : α → β} {g : β → α} {h : β → γ} {i : γ → β}
  (hf : left_inverse f g) (hh : left_inverse h i) : left_inverse (h ∘ f) (g ∘ i) :=
assume a, show h (f (g (i a))) = a, by rw [hf (i a), hh a]

theorem right_inverse.comp {f : α → β} {g : β → α} {h : β → γ} {i : γ → β}
  (hf : right_inverse f g) (hh : right_inverse h i) : right_inverse (h ∘ f) (g ∘ i) :=
left_inverse.comp hh hf

end function

/-- `α ≃ β` is the type of functions from `α → β` with a two-sided inverse. -/
structure equiv (α : Sort*) (β : Sort*) :=
(to_fun    : α → β)
(inv_fun   : β → α)
(left_inv  : left_inverse inv_fun to_fun)
(right_inv : right_inverse inv_fun to_fun)

namespace equiv
/-- `perm α` is the type of bijections from `α` to itself. -/
@[reducible] def perm (α : Sort*) := equiv α α

infix ` ≃ `:50 := equiv

instance : has_coe_to_fun (α ≃ β) :=
⟨_, to_fun⟩

@[simp] theorem coe_fn_mk (f : α → β) (g l r) : (equiv.mk f g l r : α → β) = f :=
rfl

theorem eq_of_to_fun_eq : ∀ {e₁ e₂ : equiv α β}, (e₁ : α → β) = e₂ → e₁ = e₂
| ⟨f₁, g₁, l₁, r₁⟩ ⟨f₂, g₂, l₂, r₂⟩ h :=
  have f₁ = f₂, from h,
  have g₁ = g₂, from funext $ assume x,
    have f₁ (g₁ x) = f₂ (g₂ x), from (r₁ x).trans (r₂ x).symm,
    have f₁ (g₁ x) = f₁ (g₂ x), by subst f₂; exact this,
    show g₁ x = g₂ x,           from injective_of_left_inverse l₁ this,
  by simp *

lemma ext (f g : equiv α β) (H : ∀ x, f x = g x) : f = g :=
eq_of_to_fun_eq (funext H)

@[refl] protected def refl (α : Sort*) : α ≃ α := ⟨id, id, λ x, rfl, λ x, rfl⟩

@[symm] protected def symm (e : α ≃ β) : β ≃ α := ⟨e.inv_fun, e.to_fun, e.right_inv, e.left_inv⟩

@[trans] protected def trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
⟨e₂.to_fun ∘ e₁.to_fun, e₁.inv_fun ∘ e₂.inv_fun,
  e₂.left_inv.comp e₁.left_inv, e₂.right_inv.comp e₁.right_inv⟩

protected theorem bijective : ∀ f : α ≃ β, bijective f
| ⟨f, g, h₁, h₂⟩ :=
  ⟨injective_of_left_inverse h₁, surjective_of_has_right_inverse ⟨_, h₂⟩⟩

protected theorem subsingleton (e : α ≃ β) : ∀ [subsingleton β], subsingleton α
| ⟨H⟩ := ⟨λ a b, e.bijective.1 (H _ _)⟩

protected def decidable_eq (e : α ≃ β) [H : decidable_eq β] : decidable_eq α
| a b := decidable_of_iff _ e.bijective.1.eq_iff

protected def cast {α β : Sort*} (h : α = β) : α ≃ β :=
⟨cast h, cast h.symm, λ x, by cases h; refl, λ x, by cases h; refl⟩

@[simp] theorem coe_fn_symm_mk (f : α → β) (g l r) : ((equiv.mk f g l r).symm : β → α) = g :=
rfl

@[simp] theorem refl_apply (x : α) : equiv.refl α x = x := rfl

@[simp] theorem trans_apply : ∀ (f : α ≃ β) (g : β ≃ γ) (a : α), (f.trans g) a = g (f a)
| ⟨f₁, g₁, l₁, r₁⟩ ⟨f₂, g₂, l₂, r₂⟩ a := rfl

@[simp] theorem apply_inverse_apply : ∀ (e : α ≃ β) (x : β), e (e.symm x) = x
| ⟨f₁, g₁, l₁, r₁⟩ x := by simp [equiv.symm]; rw r₁

@[simp] theorem inverse_apply_apply : ∀ (e : α ≃ β) (x : α), e.symm (e x) = x
| ⟨f₁, g₁, l₁, r₁⟩ x := by simp [equiv.symm]; rw l₁

@[simp] theorem apply_eq_iff_eq : ∀ (f : α ≃ β) (x y : α), f x = f y ↔ x = y
| ⟨f₁, g₁, l₁, r₁⟩ x y := (injective_of_left_inverse l₁).eq_iff

@[simp] theorem cast_apply {α β} (h : α = β) (x : α) : equiv.cast h x = cast h x := rfl

theorem apply_eq_iff_eq_inverse_apply : ∀ (f : α ≃ β) (x : α) (y : β), f x = y ↔ x = f.symm y
| ⟨f₁, g₁, l₁, r₁⟩ x y := by simp [equiv.symm];
  show f₁ x = y ↔ x = g₁ y; from
  ⟨λ e : f₁ x = y, e ▸ (l₁ x).symm,
   λ e : x = g₁ y, e.symm ▸ r₁ y⟩

/- The group of permutations (self-equivalences) of a type `α` -/
instance perm_group {α : Type u} : group (perm α) :=
begin
  refine { mul := λ f g, equiv.trans g f, one := equiv.refl α, inv:= equiv.symm, ..};
  intros; apply equiv.ext; try { apply trans_apply },
  apply inverse_apply_apply
end

def equiv_empty (h : α → false) : α ≃ empty :=
⟨λ x, (h x).elim, λ e, e.rec _, λ x, (h x).elim, λ e, e.rec _⟩

def false_equiv_empty : false ≃ empty :=
equiv_empty _root_.id

def empty_of_not_nonempty {α : Sort*} (h : ¬ nonempty α) : α ≃ empty :=
⟨assume a, (h ⟨a⟩).elim, assume e, e.rec_on _, assume a, (h ⟨a⟩).elim, assume e, e.rec_on _⟩

protected def ulift {α : Type u} : ulift α ≃ α :=
⟨ulift.down, ulift.up, ulift.up_down, λ a, rfl⟩

protected def plift : plift α ≃ α :=
⟨plift.down, plift.up, plift.up_down, plift.down_up⟩

@[congr] def arrow_congr {α₁ β₁ α₂ β₂ : Sort*} : α₁ ≃ α₂ → β₁ ≃ β₂ → (α₁ → β₁) ≃ (α₂ → β₂)
| ⟨f₁, g₁, l₁, r₁⟩ ⟨f₂, g₂, l₂, r₂⟩ :=
  ⟨λ (h : α₁ → β₁) (a : α₂), f₂ (h (g₁ a)),
   λ (h : α₂ → β₂) (a : α₁), g₂ (h (f₁ a)),
   λ h, by funext a; dsimp; rw [l₁, l₂],
   λ h, by funext a; dsimp; rw [r₁, r₂]⟩

def punit_equiv_punit : punit.{v} ≃ punit.{w} :=
⟨λ _, punit.star, λ _, punit.star, λ u, by cases u; refl, λ u, by cases u; reflexivity⟩

section
@[simp] def arrow_unit_equiv_unit (α : Sort*) : (α → punit.{v}) ≃ punit.{w} :=
⟨λ f, punit.star, λ u f, punit.star, λ f, by funext x; cases f x; refl, λ u, by cases u; reflexivity⟩

@[simp] def unit_arrow_equiv (α : Sort*) : (punit.{u} → α) ≃ α :=
⟨λ f, f punit.star, λ a u, a, λ f, by funext x; cases x; refl, λ u, rfl⟩

@[simp] def empty_arrow_equiv_unit (α : Sort*) : (empty → α) ≃ punit.{u} :=
⟨λ f, punit.star, λ u e, e.rec _, λ f, funext $ λ x, x.rec _, λ u, by cases u; refl⟩

@[simp] def false_arrow_equiv_unit (α : Sort*) : (false → α) ≃ punit.{u} :=
calc (false → α) ≃ (empty → α) : arrow_congr false_equiv_empty (equiv.refl _)
             ... ≃ punit       : empty_arrow_equiv_unit _

def arrow_empty_unit {α : Sort*} : (empty → α) ≃ punit.{u} :=
⟨λf, punit.star, λu e, e.rec_on _, assume f, funext $ assume e, e.rec_on _, assume u, punit_eq _ _⟩

end

@[congr] def prod_congr {α₁ β₁ α₂ β₂ : Sort*} : α₁ ≃ α₂ → β₁ ≃ β₂ → (α₁ × β₁) ≃ (α₂ × β₂)
| ⟨f₁, g₁, l₁, r₁⟩ ⟨f₂, g₂, l₂, r₂⟩ :=
  ⟨λ ⟨a, b⟩, (f₁ a, f₂ b), λ ⟨a, b⟩, (g₁ a, g₂ b),
   λ ⟨a, b⟩, show (g₁ (f₁ a), g₂ (f₂ b)) = (a, b), by rw [l₁ a, l₂ b],
   λ ⟨a, b⟩, show (f₁ (g₁ a), f₂ (g₂ b)) = (a, b), by rw [r₁ a, r₂ b]⟩

@[simp] theorem prod_congr_apply {α₁ β₁ α₂ β₂ : Sort*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) (a : α₁) (b : β₁) :
  prod_congr e₁ e₂ (a, b) = (e₁ a, e₂ b) :=
by cases e₁; cases e₂; refl

@[simp] def prod_comm (α β : Sort*) : (α × β) ≃ (β × α) :=
⟨λ p, (p.2, p.1), λ p, (p.2, p.1), λ⟨a, b⟩, rfl, λ⟨a, b⟩, rfl⟩

@[simp] def prod_assoc (α β γ : Sort*) : ((α × β) × γ) ≃ (α × (β × γ)) :=
⟨λ p, ⟨p.1.1, ⟨p.1.2, p.2⟩⟩, λp, ⟨⟨p.1, p.2.1⟩, p.2.2⟩, λ ⟨⟨a, b⟩, c⟩, rfl, λ ⟨a, ⟨b, c⟩⟩, rfl⟩

@[simp] theorem prod_assoc_apply {α β γ : Sort*} (p : (α × β) × γ) :
  prod_assoc α β γ p = ⟨p.1.1, ⟨p.1.2, p.2⟩⟩ := rfl

section
@[simp] def prod_unit (α : Sort*) : (α × punit.{u+1}) ≃ α :=
⟨λ p, p.1, λ a, (a, punit.star), λ ⟨_, punit.star⟩, rfl, λ a, rfl⟩

@[simp] theorem prod_unit_apply {α : Sort*} (a : α × punit.{u+1}) : prod_unit α a = a.1 := rfl

@[simp] def unit_prod (α : Sort*) : (punit.{u+1} × α) ≃ α :=
calc (punit × α) ≃ (α × punit) : prod_comm _ _
  ... ≃ α          : prod_unit _

@[simp] theorem unit_prod_apply {α : Sort*} (a : punit.{u+1} × α) : unit_prod α a = a.2 := rfl

@[simp] def prod_empty (α : Sort*) : (α × empty) ≃ empty :=
equiv_empty (λ ⟨_, e⟩, e.rec _)

@[simp] def empty_prod (α : Sort*) : (empty × α) ≃ empty :=
equiv_empty (λ ⟨e, _⟩, e.rec _)
end

section
open sum
def psum_equiv_sum (α β : Sort*) : psum α β ≃ (α ⊕ β) :=
⟨λ s, psum.cases_on s inl inr,
 λ s, sum.cases_on s psum.inl psum.inr,
 λ s, by cases s; refl,
 λ s, by cases s; refl⟩

def sum_congr {α₁ β₁ α₂ β₂ : Sort*} : α₁ ≃ α₂ → β₁ ≃ β₂ → (α₁ ⊕ β₁) ≃ (α₂ ⊕ β₂)
| ⟨f₁, g₁, l₁, r₁⟩ ⟨f₂, g₂, l₂, r₂⟩ :=
  ⟨λ s, match s with inl a₁ := inl (f₁ a₁) | inr b₁ := inr (f₂ b₁) end,
   λ s, match s with inl a₂ := inl (g₁ a₂) | inr b₂ := inr (g₂ b₂) end,
   λ s, match s with inl a := congr_arg inl (l₁ a) | inr a := congr_arg inr (l₂ a) end,
   λ s, match s with inl a := congr_arg inl (r₁ a) | inr a := congr_arg inr (r₂ a) end⟩

@[simp] theorem sum_congr_apply_inl {α₁ β₁ α₂ β₂ : Sort*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) (a : α₁) :
  sum_congr e₁ e₂ (inl a) = inl (e₁ a) :=
by cases e₁; cases e₂; refl

@[simp] theorem sum_congr_apply_inr {α₁ β₁ α₂ β₂ : Sort*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) (b : β₁) :
  sum_congr e₁ e₂ (inr b) = inr (e₂ b) :=
by cases e₁; cases e₂; refl

def bool_equiv_unit_sum_unit : bool ≃ (punit.{u+1} ⊕ punit.{v+1}) :=
⟨λ b, cond b (inl punit.star) (inr punit.star),
 λ s, sum.rec_on s (λ_, tt) (λ_, ff),
 λ b, by cases b; refl,
 λ s, by rcases s with ⟨⟨⟩⟩ | ⟨⟨⟩⟩; refl⟩

noncomputable def Prop_equiv_bool : Prop ≃ bool :=
⟨λ p, @to_bool p (classical.prop_decidable _),
 λ b, b, λ p, by simp, λ b, by simp⟩

@[simp] def sum_comm (α β : Sort*) : (α ⊕ β) ≃ (β ⊕ α) :=
⟨λ s, match s with inl a := inr a | inr b := inl b end,
 λ s, match s with inl b := inr b | inr a := inl a end,
 λ s, by cases s; refl,
 λ s, by cases s; refl⟩

@[simp] def sum_assoc (α β γ : Sort*) : ((α ⊕ β) ⊕ γ) ≃ (α ⊕ (β ⊕ γ)) :=
⟨λ s, match s with inl (inl a) := inl a | inl (inr b) := inr (inl b) | inr c := inr (inr c) end,
 λ s, match s with inl a := inl (inl a) | inr (inl b) := inl (inr b) | inr (inr c) := inr c end,
 λ s, by rcases s with ⟨_ | _⟩ | _; refl,
 λ s, by rcases s with _ | _ | _; refl⟩

@[simp] theorem sum_assoc_apply_in1 {α β γ} (a) : sum_assoc α β γ (inl (inl a)) = inl a := rfl
@[simp] theorem sum_assoc_apply_in2 {α β γ} (b) : sum_assoc α β γ (inl (inr b)) = inr (inl b) := rfl
@[simp] theorem sum_assoc_apply_in3 {α β γ} (c) : sum_assoc α β γ (inr c) = inr (inr c) := rfl

@[simp] def sum_empty (α : Sort*) : (α ⊕ empty) ≃ α :=
⟨λ s, match s with inl a := a | inr e := empty.rec _ e end,
 inl,
 λ s, by rcases s with _ | ⟨⟨⟩⟩; refl,
 λ a, rfl⟩

@[simp] def empty_sum (α : Sort*) : (empty ⊕ α) ≃ α :=
(sum_comm _ _).trans $ sum_empty _

@[simp] def option_equiv_sum_unit (α : Sort*) : option α ≃ (α ⊕ punit.{u+1}) :=
⟨λ o, match o with none := inr punit.star | some a := inl a end,
 λ s, match s with inr _ := none | inl a := some a end,
 λ o, by cases o; refl,
 λ s, by rcases s with _ | ⟨⟨⟩⟩; refl⟩

def sum_equiv_sigma_bool (α β : Sort*) : (α ⊕ β) ≃ (Σ b: bool, cond b α β) :=
⟨λ s, match s with inl a := ⟨tt, a⟩ | inr b := ⟨ff, b⟩ end,
 λ s, match s with ⟨tt, a⟩ := inl a | ⟨ff, b⟩ := inr b end,
 λ s, by cases s; refl,
 λ s, by rcases s with ⟨_|_, _⟩; refl⟩

def equiv_fib {α β : Type*} (f : α → β) :
  α ≃ Σ y : β, {x // f x = y} :=
⟨λ x, ⟨f x, x, rfl⟩, λ x, x.2.1, λ x, rfl, λ ⟨y, x, rfl⟩, rfl⟩

end

section

def Pi_congr_right {α} {β₁ β₂ : α → Sort*} (F : ∀ a, β₁ a ≃ β₂ a) : (Π a, β₁ a) ≃ (Π a, β₂ a) :=
⟨λ H a, F a (H a), λ H a, (F a).symm (H a),
 λ H, funext $ by simp, λ H, funext $ by simp⟩

end

section
def psigma_equiv_sigma {α} (β : α → Sort*) : psigma β ≃ sigma β :=
⟨λ ⟨a, b⟩, ⟨a, b⟩, λ ⟨a, b⟩, ⟨a, b⟩, λ ⟨a, b⟩, rfl, λ ⟨a, b⟩, rfl⟩

def sigma_congr_right {α} {β₁ β₂ : α → Sort*} (F : ∀ a, β₁ a ≃ β₂ a) : sigma β₁ ≃ sigma β₂ :=
⟨λ ⟨a, b⟩, ⟨a, F a b⟩, λ ⟨a, b⟩, ⟨a, (F a).symm b⟩,
 λ ⟨a, b⟩, congr_arg (sigma.mk a) $ inverse_apply_apply (F a) b,
 λ ⟨a, b⟩, congr_arg (sigma.mk a) $ apply_inverse_apply (F a) b⟩

def sigma_congr_left {α₁ α₂} {β : α₂ → Sort*} : ∀ f : α₁ ≃ α₂, (Σ a:α₁, β (f a)) ≃ (Σ a:α₂, β a)
| ⟨f, g, l, r⟩ :=
  ⟨λ ⟨a, b⟩, ⟨f a, b⟩, λ ⟨a, b⟩, ⟨g a, @@eq.rec β b (r a).symm⟩,
   λ ⟨a, b⟩, match g (f a), l a : ∀ a' (h : a' = a),
       @sigma.mk _ (β ∘ f) _ (@@eq.rec β b (congr_arg f h.symm)) = ⟨a, b⟩ with
     | _, rfl := rfl end,
   λ ⟨a, b⟩, match f (g a), _ : ∀ a' (h : a' = a), sigma.mk a' (@@eq.rec β b h.symm) = ⟨a, b⟩ with
     | _, rfl := rfl end⟩

def sigma_equiv_prod (α β : Sort*) : (Σ_:α, β) ≃ (α × β) :=
⟨λ ⟨a, b⟩, ⟨a, b⟩, λ ⟨a, b⟩, ⟨a, b⟩, λ ⟨a, b⟩, rfl, λ ⟨a, b⟩, rfl⟩

def sigma_equiv_prod_of_equiv {α β} {β₁ : α → Sort*} (F : ∀ a, β₁ a ≃ β) : sigma β₁ ≃ (α × β) :=
(sigma_congr_right F).trans (sigma_equiv_prod α β)

end

section
def arrow_prod_equiv_prod_arrow (α β γ : Type*) : (γ → α × β) ≃ ((γ → α) × (γ → β)) :=
⟨λ f, (λ c, (f c).1, λ c, (f c).2),
 λ p c, (p.1 c, p.2 c),
 λ f, funext $ λ c, prod.mk.eta,
 λ p, by cases p; refl⟩

def arrow_arrow_equiv_prod_arrow (α β γ : Sort*) : (α → β → γ) ≃ (α × β → γ) :=
⟨λ f, λ p, f p.1 p.2,
 λ f, λ a b, f (a, b),
 λ f, rfl,
 λ f, by funext p; cases p; refl⟩

open sum
def sum_arrow_equiv_prod_arrow (α β γ : Type*) : ((α ⊕ β) → γ) ≃ ((α → γ) × (β → γ)) :=
⟨λ f, (f ∘ inl, f ∘ inr),
 λ p s, sum.rec_on s p.1 p.2,
 λ f, by funext s; cases s; refl,
 λ p, by cases p; refl⟩

def sum_prod_distrib (α β γ : Sort*) : ((α ⊕ β) × γ) ≃ ((α × γ) ⊕ (β × γ)) :=
⟨λ p, match p with (inl a, c) := inl (a, c) | (inr b, c) := inr (b, c) end,
 λ s, match s with inl (a, c) := (inl a, c) | inr (b, c) := (inr b, c) end,
 λ p, by rcases p with ⟨_ | _, _⟩; refl,
 λ s, by rcases s with ⟨_, _⟩ | ⟨_, _⟩; refl⟩

@[simp] theorem sum_prod_distrib_apply_left {α β γ} (a : α) (c : γ) :
   sum_prod_distrib α β γ (sum.inl a, c) = sum.inl (a, c) := rfl
@[simp] theorem sum_prod_distrib_apply_right {α β γ} (b : β) (c : γ) :
   sum_prod_distrib α β γ (sum.inr b, c) = sum.inr (b, c) := rfl

def prod_sum_distrib (α β γ : Sort*) : (α × (β ⊕ γ)) ≃ ((α × β) ⊕ (α × γ)) :=
calc (α × (β ⊕ γ)) ≃ ((β ⊕ γ) × α)       : prod_comm _ _
             ...   ≃ ((β × α) ⊕ (γ × α)) : sum_prod_distrib _ _ _
             ...   ≃ ((α × β) ⊕ (α × γ)) : sum_congr (prod_comm _ _) (prod_comm _ _)

@[simp] theorem prod_sum_distrib_apply_left {α β γ} (a : α) (b : β) :
   prod_sum_distrib α β γ (a, sum.inl b) = sum.inl (a, b) := rfl
@[simp] theorem prod_sum_distrib_apply_right {α β γ} (a : α) (c : γ) :
   prod_sum_distrib α β γ (a, sum.inr c) = sum.inr (a, c) := rfl

def bool_prod_equiv_sum (α : Type u) : (bool × α) ≃ (α ⊕ α) :=
calc (bool × α) ≃ ((unit ⊕ unit) × α)       : prod_congr bool_equiv_unit_sum_unit (equiv.refl _)
        ...     ≃ (α × (unit ⊕ unit))       : prod_comm _ _
        ...     ≃ ((α × unit) ⊕ (α × unit)) : prod_sum_distrib _ _ _
        ...     ≃ (α ⊕ α)                   : sum_congr (prod_unit _) (prod_unit _)
end

section
open sum nat
def nat_equiv_nat_sum_unit : ℕ ≃ (ℕ ⊕ punit.{u+1}) :=
⟨λ n, match n with zero := inr punit.star | succ a := inl a end,
 λ s, match s with inl n := succ n | inr punit.star := zero end,
 λ n, begin cases n, repeat { refl } end,
 λ s, begin cases s with a u, { refl }, {cases u, { refl }} end⟩

@[simp] def nat_sum_unit_equiv_nat : (ℕ ⊕ punit.{u+1}) ≃ ℕ :=
nat_equiv_nat_sum_unit.symm

@[simp] def nat_prod_nat_equiv_nat : (ℕ × ℕ) ≃ ℕ :=
⟨λ p, nat.mkpair p.1 p.2,
 nat.unpair,
 λ p, begin cases p, apply nat.unpair_mkpair end,
 nat.mkpair_unpair⟩

@[simp] def nat_sum_bool_equiv_nat : (ℕ ⊕ bool) ≃ ℕ :=
calc (ℕ ⊕ bool) ≃ (ℕ ⊕ (unit ⊕ unit)) : sum_congr (equiv.refl _) bool_equiv_unit_sum_unit
           ...  ≃ ((ℕ ⊕ unit) ⊕ unit) : (sum_assoc ℕ unit unit).symm
           ...  ≃ (ℕ ⊕ unit)          : sum_congr nat_sum_unit_equiv_nat (equiv.refl _)
           ...  ≃ ℕ                   : nat_sum_unit_equiv_nat

@[simp] def bool_prod_nat_equiv_nat : (bool × ℕ) ≃ ℕ :=
⟨λ ⟨b, n⟩, bit b n, bodd_div2,
 λ ⟨b, n⟩, by simp [bool_prod_nat_equiv_nat._match_1, bodd_bit, div2_bit],
 λ n, by simp [bool_prod_nat_equiv_nat._match_1, bit_decomp]⟩

@[simp] def nat_sum_nat_equiv_nat : (ℕ ⊕ ℕ) ≃ ℕ :=
(bool_prod_equiv_sum ℕ).symm.trans bool_prod_nat_equiv_nat

def int_equiv_nat_sum_nat : ℤ ≃ (ℕ ⊕ ℕ) :=
by refine ⟨_, _, _, _⟩; intro z; {cases z; [left, right]; assumption} <|> {cases z; refl}

def int_equiv_nat : ℤ ≃ ℕ :=
int_equiv_nat_sum_nat.trans nat_sum_nat_equiv_nat

def prod_equiv_of_equiv_nat {α : Sort*} (e : α ≃ ℕ) : (α × α) ≃ α :=
calc (α × α) ≃ (ℕ × ℕ) : prod_congr e e
        ...  ≃ ℕ       : nat_prod_nat_equiv_nat
        ...  ≃ α       : e.symm

end

def list_equiv_of_equiv {α β : Type*} : α ≃ β → list α ≃ list β
| ⟨f, g, l, r⟩ :=
  by refine ⟨list.map f, list.map g, λ x, _, λ x, _⟩;
     simp [id_of_left_inverse l, id_of_right_inverse r]

section
open nat list
private def list.to_nat : list ℕ → ℕ
| []     := 0
| (a::l) := succ (mkpair l.to_nat a)

private def list.of_nat : ℕ → list ℕ
| 0        := []
| (succ v) := match unpair v, unpair_le v with
  | (v₂, v₁), h :=
    have v₂ < succ v, from lt_succ_of_le h,
    v₁ :: list.of_nat v₂
  end

private theorem list.of_nat_to_nat : ∀ l : list ℕ, list.of_nat (list.to_nat l) = l
| []     := rfl
| (a::l) := by simp [list.to_nat, list.of_nat, unpair_mkpair, *]

private theorem list.to_nat_of_nat : ∀ n : ℕ, list.to_nat (list.of_nat n) = n
| 0        := rfl
| (succ v) := begin
  cases e : unpair v with v₁ v₂,
  have := lt_succ_of_le (unpair_le v),
  have IH := have v₁ < succ v, by rwa e at this, list.to_nat_of_nat v₁,
  simp [list.of_nat, e, list.to_nat, IH, mkpair_unpair' e]
end


def list_nat_equiv_nat : list ℕ ≃ ℕ :=
⟨list.to_nat, list.of_nat, list.of_nat_to_nat, list.to_nat_of_nat⟩

def list_equiv_self_of_equiv_nat {α : Type} (e : α ≃ ℕ) : list α ≃ α :=
calc list α ≃ list ℕ : list_equiv_of_equiv e
        ... ≃ ℕ      : list_nat_equiv_nat
        ... ≃ α      : e.symm
end

section
def decidable_eq_of_equiv [h : decidable_eq α] : α ≃ β → decidable_eq β
| ⟨f, g, l, r⟩ b₁ b₂ :=
  match h (g b₁) (g b₂) with
  | (is_true he) := is_true $ have f (g b₁) = f (g b₂), from congr_arg f he, by rwa [r, r] at this
  | (is_false hn) := is_false $ λeq, hn.elim $ by rw [eq]
  end
end

def inhabited_of_equiv [inhabited α] : α ≃ β → inhabited β
| ⟨f, g, l, r⟩ := ⟨f (default _)⟩

section
open subtype

def subtype_equiv_of_subtype {p : α → Prop} : Π (e : α ≃ β), {a : α // p a} ≃ {b : β // p (e.symm b)}
| ⟨f, g, l, r⟩ :=
  ⟨subtype.map f $ assume a ha, show p (g (f a)), by rwa [l],
   subtype.map g $ assume a ha, ha,
   assume p, by simp [map_comp, l.f_g_eq_id]; rw [map_id]; refl,
   assume p, by simp [map_comp, r.f_g_eq_id]; rw [map_id]; refl⟩

def subtype_subtype_equiv_subtype {α : Type u} (p : α → Prop) (q : subtype p → Prop) :
  subtype q ≃ {a : α // ∃h:p a, q ⟨a, h⟩ } :=
⟨λ⟨⟨a, ha⟩, ha'⟩, ⟨a, ha, ha'⟩,
  λ⟨a, ha⟩, ⟨⟨a, ha.cases_on $ assume h _, h⟩, by cases ha; exact ha_h⟩,
  assume ⟨⟨a, ha⟩, h⟩, rfl, assume ⟨a, h₁, h₂⟩, rfl⟩

end

namespace set
open set

protected def univ (α) : @univ α ≃ α :=
⟨subtype.val, λ a, ⟨a, trivial⟩, λ ⟨a, _⟩, rfl, λ a, rfl⟩

protected def empty (α) : (∅ : set α) ≃ empty :=
equiv_empty $ λ ⟨x, h⟩, not_mem_empty x h

protected def union {α} {s t : set α} [decidable_pred s] (H : s ∩ t = ∅) :
  (s ∪ t : set α) ≃ (s ⊕ t) :=
⟨λ ⟨x, h⟩, if hs : x ∈ s then sum.inl ⟨_, hs⟩ else sum.inr ⟨_, h.resolve_left hs⟩,
 λ o, match o with
 | (sum.inl ⟨x, h⟩) := ⟨x, or.inl h⟩
 | (sum.inr ⟨x, h⟩) := ⟨x, or.inr h⟩
 end,
 λ ⟨x, h'⟩, by by_cases x ∈ s; simp [union._match_1, union._match_2, h]; congr,
 λ o, by rcases o with ⟨x, h⟩ | ⟨x, h⟩; simp [union._match_1, union._match_2, h];
   simp [show x ∉ s, from λ h', eq_empty_iff_forall_not_mem.1 H _ ⟨h', h⟩]⟩

protected def singleton {α} (a : α) : ({a} : set α) ≃ punit.{u} :=
⟨λ _, punit.star, λ _, ⟨a, mem_singleton _⟩,
 λ ⟨x, h⟩, by simp at h; subst x,
 λ ⟨⟩, rfl⟩

protected def insert {α} {s : set.{u} α} [decidable_pred s] {a : α} (H : a ∉ s) :
  (insert a s : set α) ≃ (s ⊕ punit.{u+1}) :=
by rw ← union_singleton; exact
(set.union $ inter_singleton_eq_empty.2 H).trans
  (sum_congr (equiv.refl _) (set.singleton _))

protected def sum_compl {α} (s : set α) [decidable_pred s] :
  (s ⊕ (-s : set α)) ≃ α :=
(set.union (inter_compl_self _)).symm.trans
  (by rw union_compl_self; exact set.univ _)

protected def prod {α β} (s : set α) (t : set β) :
  (s.prod t) ≃ (s × t) :=
⟨λ ⟨⟨x, y⟩, ⟨h₁, h₂⟩⟩, ⟨⟨x, h₁⟩, ⟨y, h₂⟩⟩,
 λ ⟨⟨x, h₁⟩, ⟨y, h₂⟩⟩, ⟨⟨x, y⟩, ⟨h₁, h₂⟩⟩,
 λ ⟨⟨x, y⟩, ⟨h₁, h₂⟩⟩, rfl,
 λ ⟨⟨x, h₁⟩, ⟨y, h₂⟩⟩, rfl⟩

protected noncomputable def image {α β} (f : α → β) (s : set α) (H : injective f) :
  s ≃ (f '' s) :=
⟨λ ⟨x, h⟩, ⟨f x, mem_image_of_mem _ h⟩,
 λ ⟨y, h⟩, ⟨classical.some h, (classical.some_spec h).1⟩,
 λ ⟨x, h⟩, subtype.eq (H (classical.some_spec (mem_image_of_mem f h)).2),
 λ ⟨y, h⟩, subtype.eq (classical.some_spec h).2⟩

@[simp] theorem image_apply {α β} (f : α → β) (s : set α) (H : injective f) (a h) :
  set.image f s H ⟨a, h⟩ = ⟨f a, mem_image_of_mem _ h⟩ := rfl

protected noncomputable def range {α β} (f : α → β) (H : injective f) :
  α ≃ range f :=
(set.univ _).symm.trans $ (set.image f univ H).trans (equiv.cast $ by rw image_univ)

@[simp] theorem range_apply {α β} (f : α → β) (H : injective f) (a) :
  set.range f H a = ⟨f a, set.mem_range_self _⟩ :=
by dunfold equiv.set.range equiv.set.univ;
   simp [set_coe_cast, -image_univ, image_univ.symm]

end set

noncomputable def of_bijective {α β} {f : α → β} (hf : bijective f) : α ≃ β :=
begin
  have hg := bijective_comp equiv.plift.symm.bijective
    (bijective_comp hf equiv.plift.bijective),
  refine equiv.plift.symm.trans (equiv.trans _ equiv.plift),
  exact (set.range _ hg.1).trans
    ((equiv.cast (by rw set.range_iff_surjective.2 hg.2)).trans (set.univ _))
end

@[simp] theorem of_bijective_to_fun {α β} {f : α → β} (hf : bijective f) : (of_bijective hf : α → β) = f :=
begin
  funext a, dunfold of_bijective equiv.set.univ,
  have hg := bijective_comp equiv.plift.symm.bijective
    (bijective_comp hf equiv.plift.bijective),
  simp [set.set_coe_cast, (∘), set.range_iff_surjective.2 hg.2],
end

section
open set
set_option eqn_compiler.zeta true

noncomputable def set.bUnion_eq_sigma_of_disjoint {α β} {s : set α} {t : α → set β}
  (h : pairwise_on s (disjoint on t)) : (⋃i∈s, t i) ≃ (Σi:s, t i.val) :=
let f : (Σi:s, t i.val) → (⋃i∈s, t i) := λ⟨⟨a, ha⟩, ⟨b, hb⟩⟩, ⟨b, mem_bUnion ha hb⟩ in
have injective f,
  from assume ⟨⟨a₁, ha₁⟩, ⟨b₁, hb₁⟩⟩ ⟨⟨a₂, ha₂⟩, ⟨b₂, hb₂⟩⟩ eq,
  have b_eq : b₁ = b₂, from congr_arg subtype.val eq,
  have a_eq : a₁ = a₂, from classical.by_contradiction $ assume ne,
    have b₁ ∈ t a₁ ∩ t a₂, from ⟨hb₁, b_eq.symm ▸ hb₂⟩,
    have t a₁ ∩ t a₂ ≠ ∅, from ne_empty_of_mem this,
    this $ h _ ha₁ _ ha₂ ne,
  sigma.eq (subtype.eq a_eq) (subtype.eq $ by subst b_eq; subst a_eq),
have surjective f,
  from assume ⟨b, hb⟩,
  have ∃a∈s, b ∈ t a, by simpa using hb,
  let ⟨a, ha, hb⟩ := this in ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, rfl⟩,
(equiv.of_bijective ⟨‹injective f›, ‹surjective f›⟩).symm

end

section swap
variable [decidable_eq α]
open decidable

def swap_core (a b r : α) : α :=
if r = a then b
else if r = b then a
else r

theorem swap_core_self (r a : α) : swap_core a a r = r :=
by by_cases r = a; simp [swap_core, *]

theorem swap_core_swap_core (r a b : α) : swap_core a b (swap_core a b r) = r :=
begin
  by_cases hb : r = b,
  { by_cases ha : r = a,
    { simp [hb.symm, ha.symm, swap_core_self] },
    { have : b ≠ a, by rwa [hb] at ha,
      simp [swap_core, *] } },
  { by_cases ha : r = a,
    { have : b ≠ a, begin rw [ha] at hb, exact ne.symm hb end,
      simp [swap_core, *] },
    simp [swap_core, *] }
end

theorem swap_core_comm (r a b : α) : swap_core a b r = swap_core b a r :=
begin
  by_cases hb : r = b,
  { by_cases ha : r = a,
    { simp [hb.symm, ha.symm, swap_core_self] },
    { have : b ≠ a, by rwa [hb] at ha,
      simp [swap_core, *] } },
  { by_cases ha : r = a,
    { have : a ≠ b, by rwa [ha] at hb,
      simp [swap_core, *] },
    simp [swap_core, *] }
end

/-- `swap a b` is the permutation that swaps `a` and `b` and
  leaves other values as is. -/
def swap (a b : α) : perm α :=
⟨swap_core a b, swap_core a b, λr, swap_core_swap_core r a b, λr, swap_core_swap_core r a b⟩

theorem swap_self (a : α) : swap a a = equiv.refl _ :=
eq_of_to_fun_eq $ funext $ λ r, swap_core_self r a

theorem swap_comm (a b : α) : swap a b = swap b a :=
eq_of_to_fun_eq $ funext $ λ r, swap_core_comm r _ _

theorem swap_apply_def (a b x : α) : swap a b x = if x = a then b else if x = b then a else x :=
rfl

theorem swap_apply_left (a b : α) : swap a b a = b :=
if_pos rfl

theorem swap_apply_right (a b : α) : swap a b b = a :=
by by_cases b = a; simp [swap_apply_def, *]

theorem swap_apply_of_ne_of_ne {a b x : α} : x ≠ a → x ≠ b → swap a b x = x :=
by simp [swap_apply_def] {contextual := tt}

theorem swap_swap (a b : α) : (swap a b).trans (swap a b) = equiv.refl _ :=
eq_of_to_fun_eq $ funext $ λ x, swap_core_swap_core _ _ _

theorem swap_comp_apply {a b x : α} (π : perm α) :
  π.trans (swap a b) x = if π x = a then b else if π x = b then a else π x :=
by cases π; refl

end swap
end equiv

instance {α} [subsingleton α] : subsingleton (ulift α) := equiv.ulift.subsingleton
instance {α} [subsingleton α] : subsingleton (plift α) := equiv.plift.subsingleton

instance {α} [decidable_eq α] : decidable_eq (ulift α) := equiv.ulift.decidable_eq
instance {α} [decidable_eq α] : decidable_eq (plift α) := equiv.plift.decidable_eq
