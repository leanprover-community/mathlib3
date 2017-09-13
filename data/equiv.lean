/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

In the standard library we cannot assume the univalence axiom.
We say two types are equivalent if they are isomorphic.

Two equivalent types have the same cardinality.
-/
import data.prod data.nat.pairing
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
| (mk f₁ g₁ l₁ r₁) (mk f₂ g₂ l₂ r₂) h :=
  have f₁ = f₂, from h,
  have g₁ = g₂, from funext $ assume x,
    have f₁ (g₁ x) = f₂ (g₂ x), from eq.trans (r₁ x) (eq.symm (r₂ x)),
    have f₁ (g₁ x) = f₁ (g₂ x), by subst f₂; exact this,
    show g₁ x = g₂ x,          from injective_of_left_inverse l₁ this,
  by simp *

@[refl] protected def refl (α : Sort*) : α ≃ α :=
mk (@id α) (@id α) (λ x, rfl) (λ x, rfl)

@[symm] protected def symm : α ≃ β → β ≃ α
| (mk f g h₁ h₂) := mk g f h₂ h₁

@[trans] protected def trans : α ≃ β → β ≃ γ → α ≃ γ
| (mk f₁ g₁ l₁ r₁) (mk f₂ g₂ l₂ r₂) :=
  mk (f₂ ∘ f₁) (g₁ ∘ g₂)
   (show ∀ x, g₁ (g₂ (f₂ (f₁ x))) = x, by intros; rewrite [l₂, l₁]; reflexivity)
   (show ∀ x, f₂ (f₁ (g₁ (g₂ x))) = x, by intros; rewrite [r₁, r₂]; reflexivity)

def id := equiv.refl α

namespace ops
  postfix ⁻¹ := equiv.symm
  notation e₁ ∘ e₂  := equiv.trans e₂ e₁
end ops
open equiv.ops

@[simp] lemma coe_fn_symm_mk (f : α → β) (g l r) : ((equiv.mk f g l r)⁻¹ : β → α) = g :=
rfl

lemma id_apply (x : α) : @id α x = x :=
rfl

lemma comp_apply (g : β ≃ γ) (f : α ≃ β) (x : α) : (g ∘ f) x = g (f x) :=
begin cases g; cases f; simp [equiv.trans, *] end

lemma inverse_apply_apply : ∀ (e : α ≃ β) (x : α), e⁻¹ (e x) = x
| (mk f₁ g₁ l₁ r₁) x := begin simp [equiv.symm], rw l₁ end

lemma eq_iff_eq_of_injective {f : α → β} (inj : injective f) (a b : α) : f a = f b ↔ a = b :=
iff.intro
  (assume : f a = f b, inj this)
  (assume : a = b,     by rewrite this)

lemma apply_eq_iff_eq : ∀ (f : α ≃ β) (x y : α), f x = f y ↔ x = y
| (mk f₁ g₁ l₁ r₁) x y := eq_iff_eq_of_injective (injective_of_left_inverse l₁) x y

lemma apply_eq_iff_eq_inverse_apply : ∀ (f : α ≃ β) (x : α) (y : β), f x = y ↔ x = f⁻¹ y
| (mk f₁ g₁ l₁ r₁) x y :=
  begin
    simp [equiv.symm],
    apply iff.intro,
    { assume : f₁ x = y, subst this, exact (l₁ x).symm },
    { assume : x = g₁ y, subst this, exact r₁ y }
  end

def false_equiv_empty : empty ≃ false :=
mk (λ e, empty.rec _ e) (λ h, false.rec _ h) (λ e, empty.rec _ e) (λ h, false.rec _ h)

@[congr] def arrow_congr {α₁ β₁ α₂ β₂ : Sort*} : α₁ ≃ α₂ → β₁ ≃ β₂ → (α₁ → β₁) ≃ (α₂ → β₂)
| (mk f₁ g₁ l₁ r₁) (mk f₂ g₂ l₂ r₂) :=
  mk
   (λ (h : α₁ → β₁) (a : α₂), f₂ (h (g₁ a)))
   (λ (h : α₂ → β₂) (a : α₁), g₂ (h (f₁ a)))
   (λ h, funext $ λ a, by dsimp; rw [l₁, l₂]; reflexivity)
   (λ h, funext $ λ a, by dsimp; rw [r₁, r₂]; reflexivity)

section
open unit
@[simp] def arrow_unit_equiv_unit (α : Sort*) : (α → unit) ≃ unit :=
mk (λ f, ()) (λ u, (λ f, ()))
   (λ f, funext (λ x, by cases (f x); reflexivity))
   (λ u, by cases u; reflexivity)

@[simp] def unit_arrow_equiv (α : Sort*) : (unit → α) ≃ α :=
mk (λ f, f ()) (λ a, (λ u, a))
   (λ f, funext (λ x, by cases x; reflexivity))
   (λ u, rfl)

@[simp] def empty_arrow_equiv_unit (α : Sort*) : (empty → α) ≃ unit :=
mk (λ f, ()) (λ u, λ e, empty.rec _ e)
   (λ f, funext (λ x, empty.rec _ x))
   (λ u, by cases u; reflexivity)

@[simp] def false_arrow_equiv_unit (α : Sort*) : (false → α) ≃ unit :=
calc (false → α) ≃ (empty → α) : arrow_congr false_equiv_empty.symm (equiv.refl _)
             ... ≃ unit        : empty_arrow_equiv_unit _
end

@[congr] def prod_congr {α₁ β₁ α₂ β₂ : Sort*} : α₁ ≃ α₂ → β₁ ≃ β₂ → (α₁ × β₁) ≃ (α₂ × β₂)
| (mk f₁ g₁ l₁ r₁) (mk f₂ g₂ l₂ r₂) :=
  mk (λ ⟨a, b⟩, (f₁ a, f₂ b)) (λ ⟨a, b⟩, (g₁ a, g₂ b))
    (λ ⟨a, b⟩, show (g₁ (f₁ a), g₂ (f₂ b)) = (a, b), by rw [l₁ a, l₂ b])
    (λ ⟨a, b⟩, show (f₁ (g₁ a), f₂ (g₂ b)) = (a, b), by rw [r₁ a, r₂ b])

@[simp] def prod_comm (α β : Sort*) : (α × β) ≃ (β × α) :=
mk (λ⟨a, b⟩, (b, a)) (λ⟨a, b⟩, (b, a))
   (λ⟨a, b⟩, rfl)
   (λ⟨a, b⟩, rfl)

@[simp] def prod_assoc (α β γ : Sort*) : ((α × β) × γ) ≃ (α × (β × γ)) :=
mk (λ ⟨⟨a, b⟩, c⟩, ⟨a, ⟨b, c⟩⟩) (λ⟨a, ⟨b, c⟩⟩, ⟨⟨a, b⟩, c⟩) (λ ⟨⟨a, b⟩, c⟩, rfl) (λ ⟨a, ⟨b, c⟩⟩, rfl)

section
@[simp] def prod_unit_right (α : Sort*) : (α × unit) ≃ α :=
mk (λ p, p.1)
   (λ a, (a, ()))
   (λ ⟨_, ⟨⟩⟩, rfl)
   (λ a, rfl)

@[simp] def prod_unit_left (α : Sort*) : (unit × α) ≃ α :=
calc (unit × α) ≃ (α × unit) : prod_comm _ _
            ... ≃ α          : prod_unit_right _

@[simp] def prod_empty_right (α : Sort*) : (α × empty) ≃ empty :=
mk (λ p, empty.rec _ p.2) (λ e, empty.rec _ e) (λ p, empty.rec _ p.2)  (λ e, empty.rec _ e)

@[simp] def prod_empty_left (α : Sort*) : (empty × α) ≃ empty :=
calc (empty × α) ≃ (α × empty) : prod_comm _ _
             ... ≃ empty       : prod_empty_right _
end

section
open sum
def sum_congr {α₁ β₁ α₂ β₂ : Sort*} : α₁ ≃ α₂ → β₁ ≃ β₂ → (α₁ ⊕ β₁) ≃ (α₂ ⊕ β₂)
| (mk f₁ g₁ l₁ r₁) (mk f₂ g₂ l₂ r₂) :=
  mk
   (λ s, match s with inl a₁ := inl (f₁ a₁) | inr b₁ := inr (f₂ b₁) end)
   (λ s, match s with inl a₂ := inl (g₁ a₂) | inr b₂ := inr (g₂ b₂) end)
   (λ s, match s with inl a := congr_arg inl (l₁ a) | inr a := congr_arg inr (l₂ a) end)
   (λ s, match s with inl a := congr_arg inl (r₁ a) | inr a := congr_arg inr (r₂ a) end)

open bool unit
def bool_equiv_unit_sum_unit : bool ≃ (unit ⊕ unit) :=
mk (λ b, match b with tt := inl () | ff := inr () end)
   (λ s, match s with inl () := tt | inr () := ff end)
   (λ b, by cases b; refl)
   (λ s, by cases s with u u; cases u; refl)

@[simp] def sum_comm (α β : Sort*) : (α ⊕ β) ≃ (β ⊕ α) :=
mk (λ s, match s with inl a := inr a | inr b := inl b end)
   (λ s, match s with inl b := inr b | inr a := inl a end)
   (λ s, by cases s; refl)
   (λ s, by cases s; refl)

@[simp] def sum_assoc (α β γ : Sort*) : ((α ⊕ β) ⊕ γ) ≃ (α ⊕ (β ⊕ γ)) :=
mk (λ s, match s with inl (inl a) := inl a | inl (inr b) := inr (inl b) | inr c := inr (inr c) end)
   (λ s, match s with inl a := inl (inl a) | inr (inl b) := inl (inr b) | inr (inr c) := inr c end)
   (λ s, begin cases s with ab c, cases ab, repeat { refl } end)
   (λ s, begin cases s with a bc, refl, cases bc, repeat { refl } end)

@[simp] def sum_empty_right (α : Sort*) : (α ⊕ empty) ≃ α :=
mk (λ s, match s with inl a := a | inr e := empty.rec _ e end)
   (λ a, inl a)
   (λ s, begin cases s with a e, { refl }, exact empty.rec _ e end)
   (λ a, rfl)

@[simp] def sum_empty_left (α : Sort*) : (empty ⊕ α) ≃ α :=
calc (empty ⊕ α) ≃ (α ⊕ empty) : sum_comm _ _
          ...    ≃ α           : sum_empty_right _
end

section
def arrow_prod_equiv_prod_arrow (α β γ : Type*) : (γ → α × β) ≃ ((γ → α) × (γ → β)) :=
mk (λ f, (λ c, (f c).1, λ c, (f c).2))
   (λ p, λ c, (p.1 c, p.2 c))
   (λ f, funext $ λ c, prod.mk.eta)
   (λ p, begin cases p, { refl } end)

def arrow_arrow_equiv_prod_arrow (α β γ : Sort*) : (α → β → γ) ≃ (α × β → γ) :=
mk (λ f, λ p, f p.1 p.2)
   (λ f, λ a b, f (a, b))
   (λ f, rfl)
   (λ f, funext (λ p, begin cases p, { refl } end))

open sum
def sum_arrow_equiv_prod_arrow (α β γ : Type*) : ((α ⊕ β) → γ) ≃ ((α → γ) × (β → γ)) :=
mk (λ f, (λ a, f (inl a), λ b, f (inr b)))
   (λ p, (λ s, match s with inl a := p.1 a | inr b := p.2 b end))
   (λ f, funext (λ s, begin cases s, { refl }, { refl } end))
   (λ p, begin cases p, { refl } end)

def sum_prod_distrib (α β γ : Sort*) : ((α ⊕ β) × γ) ≃ ((α × γ) ⊕ (β × γ)) :=
mk (λ p, match p with (inl a, c) := inl (a, c) | (inr b, c) := inr (b, c) end)
   (λ s, match s with inl (a, c) := (inl a, c) | inr (b, c) := (inr b, c) end)
   (λ p, begin cases p with ab c, cases ab, repeat { refl } end)
   (λ s, begin cases s with ac bc, cases ac, { refl }, cases bc, { refl } end)

def prod_sum_distrib (α β γ : Sort*) : (α × (β ⊕ γ)) ≃ ((α × β) ⊕ (α × γ)) :=
calc (α × (β ⊕ γ)) ≃ ((β ⊕ γ) × α)       : prod_comm _ _
             ...   ≃ ((β × α) ⊕ (γ × α)) : sum_prod_distrib _ _ _
             ...   ≃ ((α × β) ⊕ (α × γ)) : sum_congr (prod_comm _ _) (prod_comm _ _)

def bool_prod_equiv_sum (α : Sort*) : (bool × α) ≃ (α ⊕ α) :=
calc (bool × α) ≃ ((unit ⊕ unit) × α)       : prod_congr bool_equiv_unit_sum_unit (equiv.refl _)
        ...     ≃ (α × (unit ⊕ unit))       : prod_comm _ _
        ...     ≃ ((α × unit) ⊕ (α × unit)) : prod_sum_distrib _ _ _
        ...     ≃ (α ⊕ α)                   : sum_congr (prod_unit_right _) (prod_unit_right _)
end

section
open sum nat unit
def nat_equiv_nat_sum_unit : nat ≃ (nat ⊕ unit) :=
mk (λ n, match n with zero := inr () | succ a := inl a end)
   (λ s, match s with inl n := succ n | inr () := zero end)
   (λ n, begin cases n, repeat { refl } end)
   (λ s, begin cases s with a u, { refl }, {cases u, { refl }} end)

@[simp] def nat_sum_unit_equiv_nat : (nat ⊕ unit) ≃ nat :=
equiv.symm nat_equiv_nat_sum_unit

@[simp] def nat_prod_nat_equiv_nat : (nat × nat) ≃ nat :=
mk (λ p, nat.mkpair p.1 p.2)
   (λ n, nat.unpair n)
   (λ p, begin cases p, apply nat.unpair_mkpair end)
   (λ n, nat.mkpair_unpair n)

@[simp] def nat_sum_bool_equiv_nat : (nat ⊕ bool) ≃ nat :=
calc (ℕ ⊕ bool) ≃ (ℕ ⊕ (unit ⊕ unit)) : sum_congr (equiv.refl _) bool_equiv_unit_sum_unit
             ...  ≃ ((ℕ ⊕ unit) ⊕ unit) : (sum_assoc ℕ unit unit).symm
             ...  ≃ (ℕ ⊕ unit)          : sum_congr nat_sum_unit_equiv_nat (equiv.refl _)
             ...  ≃ ℕ                   : nat_sum_unit_equiv_nat

/- TODO: port even / odd
open decidable
@[simp] def nat_sum_nat_equiv_nat : (nat ⊕ nat) ≃ nat :=
mk (λ s, match s with inl n := 2*n | inr n := 2*n + 1 end)
   (λ n, if even n then inl (n / 2) else inr ((n - 1) / 2))
   (λ s, begin
           have two_gt_0 : 2 > zero, from dec_trivial,
           cases s,
             {{ refl }, rewrite [if_pos (even_two_mul _), nat.mul_div_cancel_left _ two_gt_0]},
             {{ refl }, rewrite [if_neg (not_even_two_mul_plus_one _), nat.add_sub_cancel,
                              nat.mul_div_cancel_left _ two_gt_0]}
         end)
   (λ n, by_cases
          (λ h : even n,
            by rewrite [if_pos h]; { refl }; rewrite [nat.mul_div_cancel' (dvd_of_even h)])
          (λ h : ¬ even n,
            begin
              rewrite [if_neg h], { refl },
              cases n,
                {exact absurd even_zero h},
                {rewrite [-(add_one a), nat.add_sub_cancel,
                          nat.mul_div_cancel' (dvd_of_even (even_of_odd_succ (odd_of_not_even h)))]}
            end))

def prod_equiv_of_equiv_nat {α : Sort*} : α ≃ nat → (α × α) ≃ α :=
assume e, calc
  (α × α) ≃ (nat × nat) : prod_congr e e
     ...  ≃ nat         : nat_prod_nat_equiv_nat
     ...  ≃ α           : equiv.symm e
-/

end

section
open decidable or
def decidable_eq_of_equiv [h : decidable_eq α] : α ≃ β → decidable_eq β
| (mk f g l r) :=
  assume b₁ b₂, match h (g b₁) (g b₂) with
  | (is_true he) := is_true $ have f (g b₁) = f (g b₂), from congr_arg f he, by rwa [r, r] at this
  | (is_false hn) := is_false $ λeq, absurd (by rw [eq]) hn
  end
end

def inhabited_of_equiv [inhabited α] : α ≃ β → inhabited β
| (mk f g l r) := inhabited.mk $ f $ default α

section
open subtype

def subtype_equiv_of_subtype {p : α → Prop} : Π(e : α ≃ β), {a : α // p a} ≃ {b : β // p (e⁻¹ b)}
| (mk f g l r) :=
  mk
    (subtype.map f $ assume a ha, show p (g (f a)), by rwa [l])
    (subtype.map g $ assume a ha, ha)
    (assume p, by simp [map_comp, l.f_g_eq_id]; rw [map_id]; refl)
    (assume p, by simp [map_comp, r.f_g_eq_id]; rw [map_id]; refl)

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
mk (swap_core a b) (swap_core a b) (λr, swap_core_swap_core r a b) (λr, swap_core_swap_core r a b)

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
