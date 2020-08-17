/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import logic.function.iterate
import order.basic

universe variables u v w

def nary_func (α : list (Type u)) (β : Type (max u v)) : Type (max u v) :=
α.foldr (→) β

namespace nary_func
variables {α : list (Type u)} {β : Type (max u v)}

def domains (f : nary_func α β) := α

def codomain (f : nary_func α β) := β

instance : Π (α : list (Type u)) (β : Type (max u v)) [preorder β], preorder (nary_func α β)
| []        β I := I
| (α :: αs) β I := show _root_.preorder (α → nary_func αs β),
                   from @pi.preorder α (λ a, nary_func αs β) (λ a, @preorder _ _ I)

def comp : Π (f : list (Σ (α : list Type*) (β : Type*), nary_func α β))
  {γ : Type*} (g : nary_func (f.map $ λ fi, fi.2.1) γ),
  nary_func ((f.map $ λ (fi : Σ _ _, nary_func _ _), fi.1).foldr (++) []) γ
| []                        γ g := g
| (⟨[], β, f⟩ :: fs)        γ g := comp fs (g f)
| (⟨(α :: αs), β, f⟩ :: fs) γ g := λ a, comp (⟨αs, β, f a⟩ :: fs) g

def uncurry : Π {α : list (Type u)} {β : Type (max u v)} (f : nary_func α β),
  (α.foldr ((×) : Type u → Type u → Type u) punit) → β
| [] β b := λ _, b
| (α :: αs) β f := λ a, uncurry (f $ a.1) a.2

def curry : Π {α : list (Type u)} {β : Type (max u v)}
  (f : (α.foldr ((×) : Type u → Type u → Type u) punit) → β),
  nary_func α β
| [] β b := b punit.star
| (α :: αs) β f := λ a, curry $ λ as, f (a, as)

def uncurry' : Π {α : Type u} {αs : list (Type u)} {β : Type (max u v)} (f : nary_func (α :: αs) β),
  (αs.foldl ((×) : Type u → Type u → Type u) α) → β
| α [] β f := f
| α₁ (α₂ :: αs) β f := uncurry' (function.uncurry f)

end nary_func

def nary_const : Π (αs : list Type*) {β : Type*} (b : β), nary_func αs β
| []     β b := b
| (α::l) β b := λ a, nary_const l b

def nary_proj (α : Type u) :
  Π (n : ℕ) (i : fin n), nary_func.{u u} (list.repeat α n) α
| 0     ⟨i, h⟩   := (i.not_lt_zero h).elim
| (n+1) ⟨0, h⟩   := show α → (nary_func.{u u} (list.repeat α n) α),
                    from λ a, nary_const (list.repeat α n) a
| (n+1) ⟨i+1, h⟩ := show α → (nary_func.{u u} (list.repeat α n) α),
                    from λ a, nary_proj n ⟨i, nat.lt_of_succ_lt_succ h⟩

def function_class := Π ⦃α : list Type⦄ ⦃β : Type⦄, nary_func α β → Prop.

namespace function_class
open nary_func

variables (ℱ : function_class)

/-- Closed under n-ary composition -/
def is_comp_closed : Prop :=
∀ (f : list (Σ (α : list Type) (β : Type), nary_func α β))
  {γ : Type} (g : nary_func (f.map $ λ fi, fi.2.1) γ),
  (∀ fi ∈ f, ℱ (sigma.snd (sigma.snd fi))) → ℱ g → ℱ (g.comp f)

/-- Limited recursion predicate -/
def has_limrec : Prop :=
∀ {n} (f : nary_func (list.repeat ℕ (n+1)) ℕ),
  (∃ j, f ≤ j ∧ ℱ j ∧ ℱ (f 0) ∧
    ∃ (h : nary_func (list.repeat ℕ (n+2)) ℕ),
      ℱ h ∧ ∀ i, uncurry (f (i+1)) = λ u, uncurry (h i (uncurry (f i) u)) u)
  → ℱ f

def admissible_nary_to_pow {m n : ℕ}
  (f : nary_func (list.repeat ℕ m) ((list.repeat ℕ n).foldr ((×) : Type → Type → Type) punit)) : Prop :=
∀ i : fin n, ℱ $ curry $ (nary_proj ℕ n i).uncurry ∘ f.uncurry

structure retract (X : Type) :=
{n : ℕ}
(ι : X → ((list.repeat ℕ n).foldr ((×) : Type → Type → Type) punit))
(π : ((list.repeat ℕ n).foldr ((×) : Type → Type → Type) punit) → X)
(is_retract : ∀ x, π (ι x) = x)
(admissible : ℱ.admissible_nary_to_pow $ curry (ι ∘ π))

class basic : Prop :=
(zero : ℱ (show nary_func [ℕ] ℕ, from λ _, (0:ℕ)))
(succ : ℱ (show nary_func [ℕ] ℕ, from nat.succ))
(proj : ∀ n i, ℱ (nary_proj ℕ n i))
(comp : is_comp_closed ℱ)

end function_class

def grzegorczyk_function_arity : ℕ → ℕ
| 0 := 2
| _ := 1

def grzegorczyk_function : Π (n : ℕ),
  nary_func (list.repeat ℕ (grzegorczyk_function_arity n)) ℕ
| 0     := (+)
| 1     := show ℕ → ℕ, from λ k, k^2 + 2
| (n+2) := show ℕ → ℕ, from λ k, (grzegorczyk_function (n+1))^[k] 2
