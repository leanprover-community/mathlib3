/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro

In the standard library we cannot assume the univalence axiom.
We say two types are equivalent if they are isomorphic.

Two equivalent types have the same cardinality.
-/
import data.prod data.nat.pairing tactic
open function

universes u v w
variables {α : Sort u} {β : Sort v} {γ : Sort w}

namespace subtype

def map {p : α → Prop} {q : β → Prop} (f : α → β) (h : ∀a, p a → q (f a)) :
  subtype p → subtype q
| ⟨v, hv⟩ := ⟨f v, h v hv⟩

lemma map_comp {p : α → Prop} {q : β → Prop} {r : γ → Prop} {x : subtype p}
  (f : α → β) (h : ∀a, p a → q (f a)) (g : β → γ) (l : ∀a, q a → r (g a)) :
  map g l (map f h x) = map (g ∘ f) (assume a ha, l (f a) $ h a ha) x :=
by cases x with v h; refl

lemma map_id {p : α → Prop} {h : ∀a, p a → p (id a)} : map (@id α) h = id :=
funext $ assume ⟨v, h⟩, rfl

end subtype

namespace function

lemma left_inverse.f_g_eq_id {f : α → β} {g : β → α} (h : left_inverse f g) : f ∘ g = id :=
funext $ h

lemma right_inverse.g_f_eq_id {f : α → β} {g : β → α} (h : right_inverse f g) : g ∘ f = id :=
funext $ h

end function

structure equiv (α : Sort*) (β : Sort*) :=
  (to_fun    : α → β)
  (inv_fun   : β → α)
  (left_inv  : left_inverse inv_fun to_fun)
  (right_inv : right_inverse inv_fun to_fun)

namespace equiv
@[reducible] def perm (α : Sort*) := equiv α α

infix ` ≃ `:50 := equiv

instance : has_coe_to_fun (α ≃ β) :=
⟨_, to_fun⟩

@[simp] lemma coe_fn_mk (f : α → β) (g l r) : (equiv.mk f g l r : α → β) = f :=
rfl

lemma eq_of_to_fun_eq : ∀ {e₁ e₂ : equiv α β}, (e₁ : α → β) = e₂ → e₁ = e₂
| ⟨f₁, g₁, l₁, r₁⟩ ⟨f₂, g₂, l₂, r₂⟩ h :=
  have f₁ = f₂, from h,
  have g₁ = g₂, from funext $ assume x,
    have f₁ (g₁ x) = f₂ (g₂ x), from (r₁ x).trans (r₂ x).symm,
    have f₁ (g₁ x) = f₁ (g₂ x), by subst f₂; exact this,
    show g₁ x = g₂ x,           from injective_of_left_inverse l₁ this,
  by simp *

@[refl] protected def refl (α : Sort*) : α ≃ α :=
⟨id, id, λ x, rfl, λ x, rfl⟩

@[symm] protected def symm : α ≃ β → β ≃ α
| ⟨f, g, h₁, h₂⟩ := ⟨g, f, h₂, h₁⟩

@[trans] protected def trans : α ≃ β → β ≃ γ → α ≃ γ
| ⟨f₁, g₁, l₁, r₁⟩ ⟨f₂, g₂, l₂, r₂⟩ :=
  ⟨f₂ ∘ f₁, g₁ ∘ g₂,
    λ x, show g₁ (g₂ (f₂ (f₁ x))) = x, by rw [l₂, l₁],
    λ x, show f₂ (f₁ (g₁ (g₂ x))) = x, by rw [r₁, r₂]⟩

def id := equiv.refl α

@[simp] lemma coe_fn_symm_mk (f : α → β) (g l r) : ((equiv.mk f g l r).symm : β → α) = g :=
rfl

lemma id_apply (x : α) : @id α x = x :=
rfl

lemma comp_apply (g : β ≃ γ) (f : α ≃ β) (x : α) : (g ∘ f) x = g (f x) :=
by cases g; cases f; simp [equiv.trans, *]

lemma apply_inverse_apply : ∀ (e : α ≃ β) (x : β), e (e.symm x) = x
| ⟨f₁, g₁, l₁, r₁⟩ x := by simp [equiv.symm]; rw r₁

lemma inverse_apply_apply : ∀ (e : α ≃ β) (x : α), e.symm (e x) = x
| ⟨f₁, g₁, l₁, r₁⟩ x := by simp [equiv.symm]; rw l₁

lemma eq_iff_eq_of_injective {f : α → β} (inj : injective f) (a b : α) : f a = f b ↔ a = b :=
⟨λ h, inj h, λ h, by rw h⟩

lemma apply_eq_iff_eq : ∀ (f : α ≃ β) (x y : α), f x = f y ↔ x = y
| ⟨f₁, g₁, l₁, r₁⟩ x y := eq_iff_eq_of_injective (injective_of_left_inverse l₁) x y

lemma apply_eq_iff_eq_inverse_apply : ∀ (f : α ≃ β) (x : α) (y : β), f x = y ↔ x = f.symm y
| ⟨f₁, g₁, l₁, r₁⟩ x y := by simp [equiv.symm];
  show f₁ x = y ↔ x = g₁ y; from
  ⟨λ e : f₁ x = y, e ▸ (l₁ x).symm,
   λ e : x = g₁ y, e.symm ▸ r₁ y⟩

def equiv_empty (h : α → false) : α ≃ empty :=
⟨λ x, (h x).elim, λ e, e.rec _, λ x, (h x).elim, λ e, e.rec _⟩

def false_equiv_empty : false ≃ empty :=
equiv_empty _root_.id

lemma empty_of_not_nonempty {α : Sort*} (h : ¬ nonempty α) : α ≃ empty :=
⟨assume a, (h ⟨a⟩).elim, assume e, e.rec_on _, assume a, (h ⟨a⟩).elim, assume e, e.rec_on _⟩

protected lemma ulift {α : Type u} : ulift α ≃ α :=
⟨ulift.down, ulift.up, ulift.up_down, ulift.down_up⟩

@[congr] def arrow_congr {α₁ β₁ α₂ β₂ : Sort*} : α₁ ≃ α₂ → β₁ ≃ β₂ → (α₁ → β₁) ≃ (α₂ → β₂)
| ⟨f₁, g₁, l₁, r₁⟩ ⟨f₂, g₂, l₂, r₂⟩ :=
  ⟨λ (h : α₁ → β₁) (a : α₂), f₂ (h (g₁ a)),
   λ (h : α₂ → β₂) (a : α₁), g₂ (h (f₁ a)),
   λ h, funext $ λ a, by dsimp; rw [l₁, l₂],
   λ h, funext $ λ a, by dsimp; rw [r₁, r₂]⟩

section
@[simp] def arrow_unit_equiv_unit (α : Sort*) : (α → unit) ≃ unit :=
⟨λ f, (), λ u f, (), λ f, funext $ λ x, by cases f x; refl, λ u, by cases u; reflexivity⟩

@[simp] def unit_arrow_equiv (α : Sort*) : (unit → α) ≃ α :=
⟨λ f, f (), λ a u, a, λ f, funext $ λ x, by cases x; refl, λ u, rfl⟩

@[simp] def empty_arrow_equiv_unit (α : Sort*) : (empty → α) ≃ unit :=
⟨λ f, (), λ u e, e.rec _, λ f, funext $ λ x, x.rec _, λ u, by cases u; refl⟩

@[simp] def false_arrow_equiv_unit (α : Sort*) : (false → α) ≃ unit :=
calc (false → α) ≃ (empty → α) : arrow_congr false_equiv_empty (equiv.refl _)
             ... ≃ unit        : empty_arrow_equiv_unit _

lemma arrow_empty_unit {α : Sort*} : (empty → α) ≃ unit :=
⟨λf, (), λu e, e.rec_on _, assume f, funext $ assume e, e.rec_on _, assume u, unit_eq _ _⟩

end

@[congr] def prod_congr {α₁ β₁ α₂ β₂ : Sort*} : α₁ ≃ α₂ → β₁ ≃ β₂ → (α₁ × β₁) ≃ (α₂ × β₂)
| ⟨f₁, g₁, l₁, r₁⟩ ⟨f₂, g₂, l₂, r₂⟩ :=
  ⟨λ ⟨a, b⟩, (f₁ a, f₂ b), λ ⟨a, b⟩, (g₁ a, g₂ b),
   λ ⟨a, b⟩, show (g₁ (f₁ a), g₂ (f₂ b)) = (a, b), by rw [l₁ a, l₂ b],
   λ ⟨a, b⟩, show (f₁ (g₁ a), f₂ (g₂ b)) = (a, b), by rw [r₁ a, r₂ b]⟩

@[simp] def prod_comm (α β : Sort*) : (α × β) ≃ (β × α) :=
⟨λ⟨a, b⟩, (b, a), λ⟨a, b⟩, (b, a), λ⟨a, b⟩, rfl, λ⟨a, b⟩, rfl⟩

@[simp] def prod_assoc (α β γ : Sort*) : ((α × β) × γ) ≃ (α × (β × γ)) :=
⟨λ ⟨⟨a, b⟩, c⟩, ⟨a, ⟨b, c⟩⟩, λ⟨a, ⟨b, c⟩⟩, ⟨⟨a, b⟩, c⟩, λ ⟨⟨a, b⟩, c⟩, rfl, λ ⟨a, ⟨b, c⟩⟩, rfl⟩

section
@[simp] def prod_unit_right (α : Sort*) : (α × unit) ≃ α :=
⟨λ p, p.1, λ a, (a, ()), λ ⟨_, ⟨⟩⟩, rfl, λ a, rfl⟩

@[simp] def prod_unit_left (α : Sort*) : (unit × α) ≃ α :=
calc (unit × α) ≃ (α × unit) : prod_comm _ _
            ... ≃ α          : prod_unit_right _

@[simp] def prod_empty_right (α : Sort*) : (α × empty) ≃ empty :=
equiv_empty (λ ⟨_, e⟩, e.rec _)

@[simp] def prod_empty_left (α : Sort*) : (empty × α) ≃ empty :=
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

def bool_equiv_unit_sum_unit : bool ≃ (unit ⊕ unit) :=
⟨λ b, cond b inl inr (),
 λ s, sum.rec_on s (λ_, tt) (λ_, ff),
 λ b, by cases b; refl,
 λ s, by rcases s with ⟨⟨⟩⟩ | ⟨⟨⟩⟩; refl⟩

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

@[simp] def sum_empty_right (α : Sort*) : (α ⊕ empty) ≃ α :=
⟨λ s, match s with inl a := a | inr e := empty.rec _ e end,
 inl,
 λ s, by rcases s with _ | ⟨⟨⟩⟩; refl,
 λ a, rfl⟩

@[simp] def sum_empty_left (α : Sort*) : (empty ⊕ α) ≃ α :=
(sum_comm _ _).trans $ sum_empty_right _

@[simp] def option_equiv_sum_unit (α : Sort*) : option α ≃ (α ⊕ unit) :=
⟨λ o, match o with none := inr () | some a := inl a end,
 λ s, match s with inr _ := none | inl a := some a end,
 λ o, by cases o; refl,
 λ s, by rcases s with _ | ⟨⟨⟩⟩; refl⟩
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
 λ f, funext $ λ p, by cases p; refl⟩

open sum
def sum_arrow_equiv_prod_arrow (α β γ : Type*) : ((α ⊕ β) → γ) ≃ ((α → γ) × (β → γ)) :=
⟨λ f, (f ∘ inl, f ∘ inr),
 λ p s, sum.rec_on s p.1 p.2,
 λ f, funext $ λ s, by cases s; refl,
 λ p, by cases p; refl⟩

def sum_prod_distrib (α β γ : Sort*) : ((α ⊕ β) × γ) ≃ ((α × γ) ⊕ (β × γ)) :=
⟨λ p, match p with (inl a, c) := inl (a, c) | (inr b, c) := inr (b, c) end,
 λ s, match s with inl (a, c) := (inl a, c) | inr (b, c) := (inr b, c) end,
 λ p, by rcases p with ⟨_ | _, _⟩; refl,
 λ s, by rcases s with ⟨_, _⟩ | ⟨_, _⟩; refl⟩

def prod_sum_distrib (α β γ : Sort*) : (α × (β ⊕ γ)) ≃ ((α × β) ⊕ (α × γ)) :=
calc (α × (β ⊕ γ)) ≃ ((β ⊕ γ) × α)       : prod_comm _ _
             ...   ≃ ((β × α) ⊕ (γ × α)) : sum_prod_distrib _ _ _
             ...   ≃ ((α × β) ⊕ (α × γ)) : sum_congr (prod_comm _ _) (prod_comm _ _)

def bool_prod_equiv_sum (α : Type u) : (bool × α) ≃ (α ⊕ α) :=
calc (bool × α) ≃ ((unit ⊕ unit) × α)       : prod_congr bool_equiv_unit_sum_unit (equiv.refl _)
        ...     ≃ (α × (unit ⊕ unit))       : prod_comm _ _
        ...     ≃ ((α × unit) ⊕ (α × unit)) : prod_sum_distrib _ _ _
        ...     ≃ (α ⊕ α)                   : sum_congr (prod_unit_right _) (prod_unit_right _)
end

section
open sum nat
def nat_equiv_nat_sum_unit : ℕ ≃ (ℕ ⊕ unit) :=
⟨λ n, match n with zero := inr () | succ a := inl a end,
 λ s, match s with inl n := succ n | inr () := zero end,
 λ n, begin cases n, repeat { refl } end,
 λ s, begin cases s with a u, { refl }, {cases u, { refl }} end⟩

@[simp] def nat_sum_unit_equiv_nat : (ℕ ⊕ unit) ≃ ℕ :=
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

def list_equiv_of_equiv {α β : Type} : α ≃ β → list α ≃ list β
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

end

section swap
variable [h : decidable_eq α]
include h
open decidable

def swap_core (a b r : α) : α :=
if r = a then b
else if r = b then a
else r

lemma swap_core_self (r a : α) : swap_core a a r = r :=
by by_cases r = a; simp [swap_core, *]

lemma swap_core_swap_core (r a b : α) : swap_core a b (swap_core a b r) = r :=
begin
  by_cases r = b with hb,
  { by_cases r = a with ha,
    { simp [hb.symm, ha.symm, swap_core_self] },
    { have : b ≠ a, by rwa [hb] at ha,
      simp [swap_core, *] } },
  { by_cases r = a with ha,
    { have : b ≠ a, begin rw [ha] at hb, exact ne.symm hb end,
      simp [swap_core, *] },
    simp [swap_core, *] }
end

lemma swap_core_comm (r a b : α) : swap_core a b r = swap_core b a r :=
begin
  by_cases r = b with hb,
  { by_cases r = a with ha,
    { simp [hb.symm, ha.symm, swap_core_self] },
    { have : b ≠ a, by rwa [hb] at ha,
      simp [swap_core, *] } },
  { by_cases r = a with ha,
    { have : a ≠ b, by rwa [ha] at hb,
      simp [swap_core, *] },
    simp [swap_core, *] }
end

def swap (a b : α) : perm α :=
⟨swap_core a b, swap_core a b, λr, swap_core_swap_core r a b, λr, swap_core_swap_core r a b⟩

lemma swap_self (a : α) : swap a a = id :=
eq_of_to_fun_eq $ funext $ λ r, swap_core_self r a

lemma swap_comm (a b : α) : swap a b = swap b a :=
eq_of_to_fun_eq $ funext $ λ r, swap_core_comm r _ _

lemma swap_apply_def (a b x : α) : swap a b x = if x = a then b else if x = b then a else x :=
rfl

lemma swap_apply_left (a b : α) : swap a b a = b :=
if_pos rfl

lemma swap_apply_right (a b : α) : swap a b b = a :=
by by_cases b = a; simp [swap_apply_def, *]

lemma swap_apply_of_ne_of_ne {a b x : α} : x ≠ a → x ≠ b → swap a b x = x :=
by simp [swap_apply_def] {contextual := tt}

lemma swap_swap (a b : α) : (swap a b).trans (swap a b) = id :=
eq_of_to_fun_eq $ funext $ λ x, swap_core_swap_core _ _ _

lemma swap_comp_apply {a b x : α} (π : perm α) :
  π.trans (swap a b) x = if π x = a then b else if π x = b then a else π x :=
by cases π; refl

end swap
end equiv
