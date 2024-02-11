/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import meta.univs
import tactic.lint
import tactic.ext
import logic.function.basic

/-!
# Sigma types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves basic results about sigma types.

A sigma type is a dependent pair type. Like `α × β` but where the type of the second component
depends on the first component. This can be seen as a generalization of the sum type `α ⊕ β`:
* `α ⊕ β` is made of stuff which is either of type `α` or `β`.
* Given `α : ι → Type*`, `sigma α` is made of stuff which is of type `α i` for some `i : ι`. One
  effectively recovers a type isomorphic to `α ⊕ β` by taking a `ι` with exactly two elements. See
  `equiv.sum_equiv_sigma_bool`.

`Σ x, A x` is notation for `sigma A` (note the difference with the big operator `∑`).
`Σ x y z ..., A x y z ...` is notation for `Σ x, Σ y, Σ z, ..., A x y z ...`. Here we have
`α : Type*`, `β : α → Type*`, `γ : Π a : α, β a → Type*`, ...,
`A : Π (a : α) (b : β a) (c : γ a b) ..., Type*`  with `x : α` `y : β x`, `z : γ x y`, ...

## Notes

The definition of `sigma` takes values in `Type*`. This effectively forbids `Prop`- valued sigma
types. To that effect, we have `psigma`, which takes value in `Sort*` and carries a more complicated
universe signature in consequence.
-/

section sigma
variables {α α₁ α₂ : Type*} {β : α → Type*} {β₁ : α₁ → Type*} {β₂ : α₂ → Type*}

namespace sigma

instance [inhabited α] [inhabited (β default)] : inhabited (sigma β) :=
⟨⟨default, default⟩⟩

instance [h₁ : decidable_eq α] [h₂ : ∀a, decidable_eq (β a)] : decidable_eq (sigma β)
| ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ := match a₁, b₁, a₂, b₂, h₁ a₁ a₂ with
  | _, b₁, _, b₂, is_true (eq.refl a) :=
    match b₁, b₂, h₂ a b₁ b₂ with
    | _, _, is_true (eq.refl b) := is_true rfl
    | b₁, b₂, is_false n := is_false (assume h, sigma.no_confusion h (λe₁ e₂, n $ eq_of_heq e₂))
    end
  | a₁, _, a₂, _, is_false n := is_false (assume h, sigma.no_confusion h (λe₁ e₂, n e₁))
  end

@[simp, nolint simp_nf] -- sometimes the built-in injectivity support does not work
theorem mk.inj_iff {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂} :
  sigma.mk a₁ b₁ = ⟨a₂, b₂⟩ ↔ (a₁ = a₂ ∧ b₁ == b₂) :=
by simp

@[simp] theorem eta : ∀ x : Σ a, β a, sigma.mk x.1 x.2 = x
| ⟨i, x⟩ := rfl

@[ext]
lemma ext {x₀ x₁ : sigma β} (h₀ : x₀.1 = x₁.1) (h₁ : x₀.2 == x₁.2) : x₀ = x₁ :=
by { cases x₀, cases x₁, cases h₀, cases h₁, refl }

lemma ext_iff {x₀ x₁ : sigma β} : x₀ = x₁ ↔ x₀.1 = x₁.1 ∧ x₀.2 == x₁.2 :=
by { cases x₀, cases x₁, exact sigma.mk.inj_iff }

/-- A specialized ext lemma for equality of sigma types over an indexed subtype. -/
@[ext]
lemma subtype_ext {β : Type*} {p : α → β → Prop} :
  ∀ {x₀ x₁ : Σ a, subtype (p a)}, x₀.fst = x₁.fst → (x₀.snd : β) = x₁.snd → x₀ = x₁
| ⟨a₀, b₀, hb₀⟩ ⟨a₁, b₁, hb₁⟩ rfl rfl := rfl

lemma subtype_ext_iff {β : Type*} {p : α → β → Prop} {x₀ x₁ : Σ a, subtype (p a)} :
  x₀ = x₁ ↔ x₀.fst = x₁.fst ∧ (x₀.snd : β) = x₁.snd :=
⟨λ h, h ▸ ⟨rfl, rfl⟩, λ ⟨h₁, h₂⟩, subtype_ext h₁ h₂⟩

@[simp] theorem «forall» {p : (Σ a, β a) → Prop} :
  (∀ x, p x) ↔ (∀ a b, p ⟨a, b⟩) :=
⟨assume h a b, h ⟨a, b⟩, assume h ⟨a, b⟩, h a b⟩

@[simp] theorem «exists» {p : (Σ a, β a) → Prop} :
  (∃ x, p x) ↔ (∃ a b, p ⟨a, b⟩) :=
⟨assume ⟨⟨a, b⟩, h⟩, ⟨a, b, h⟩, assume ⟨a, b, h⟩, ⟨⟨a, b⟩, h⟩⟩

/-- Map the left and right components of a sigma -/
def map (f₁ : α₁ → α₂) (f₂ : Πa, β₁ a → β₂ (f₁ a)) (x : sigma β₁) : sigma β₂ :=
⟨f₁ x.1, f₂ x.1 x.2⟩

end sigma

lemma sigma_mk_injective {i : α} : function.injective (@sigma.mk α β i)
| _ _ rfl := rfl

lemma function.injective.sigma_map {f₁ : α₁ → α₂} {f₂ : Πa, β₁ a → β₂ (f₁ a)}
  (h₁ : function.injective f₁) (h₂ : ∀ a, function.injective (f₂ a)) :
  function.injective (sigma.map f₁ f₂)
| ⟨i, x⟩ ⟨j, y⟩ h :=
begin
  obtain rfl : i = j, from h₁ (sigma.mk.inj_iff.mp h).1,
  obtain rfl : x = y, from h₂ i (sigma_mk_injective h),
  refl
end

lemma function.injective.of_sigma_map {f₁ : α₁ → α₂} {f₂ : Πa, β₁ a → β₂ (f₁ a)}
  (h : function.injective (sigma.map f₁ f₂)) (a : α₁) : function.injective (f₂ a) :=
λ x y hxy, sigma_mk_injective $ @h ⟨a, x⟩ ⟨a, y⟩ (sigma.ext rfl (heq_iff_eq.2 hxy))

lemma function.injective.sigma_map_iff {f₁ : α₁ → α₂} {f₂ : Πa, β₁ a → β₂ (f₁ a)}
  (h₁ : function.injective f₁) :
  function.injective (sigma.map f₁ f₂) ↔ ∀ a, function.injective (f₂ a) :=
⟨λ h, h.of_sigma_map, h₁.sigma_map⟩

lemma function.surjective.sigma_map {f₁ : α₁ → α₂} {f₂ : Πa, β₁ a → β₂ (f₁ a)}
  (h₁ : function.surjective f₁) (h₂ : ∀ a, function.surjective (f₂ a)) :
  function.surjective (sigma.map f₁ f₂) :=
begin
  simp only [function.surjective, sigma.forall, h₁.forall],
  exact λ i, (h₂ _).forall.2 (λ x, ⟨⟨i, x⟩, rfl⟩)
end

/-- Interpret a function on `Σ x : α, β x` as a dependent function with two arguments.

This also exists as an `equiv` as `equiv.Pi_curry γ`. -/
def sigma.curry {γ : Π a, β a → Type*} (f : Π x : sigma β, γ x.1 x.2) (x : α) (y : β x) : γ x y :=
f ⟨x,y⟩

/-- Interpret a dependent function with two arguments as a function on `Σ x : α, β x`.

This also exists as an `equiv` as `(equiv.Pi_curry γ).symm`. -/
def sigma.uncurry {γ : Π a, β a → Type*} (f : Π x (y : β x), γ x y) (x : sigma β) : γ x.1 x.2 :=
f x.1 x.2

@[simp]
lemma sigma.uncurry_curry {γ : Π a, β a → Type*} (f : Π x : sigma β, γ x.1 x.2) :
  sigma.uncurry (sigma.curry f) = f :=
funext $ λ ⟨i, j⟩, rfl

@[simp]
lemma sigma.curry_uncurry {γ : Π a, β a → Type*} (f : Π x (y : β x), γ x y) :
  sigma.curry (sigma.uncurry f) = f :=
rfl

/-- Convert a product type to a Σ-type. -/
def prod.to_sigma {α β} (p : α × β) : Σ _ : α, β := ⟨p.1, p.2⟩

@[simp] lemma prod.fst_comp_to_sigma {α β} : sigma.fst ∘ @prod.to_sigma α β = prod.fst := rfl
@[simp] lemma prod.fst_to_sigma {α β} (x : α × β) : (prod.to_sigma x).fst = x.fst := rfl
@[simp] lemma prod.snd_to_sigma {α β} (x : α × β) : (prod.to_sigma x).snd = x.snd := rfl
@[simp] lemma prod.to_sigma_mk {α β} (x : α) (y : β) : (x, y).to_sigma = ⟨x, y⟩ := rfl

-- we generate this manually as `@[derive has_reflect]` fails
@[instance]
protected meta def {u v} sigma.reflect [reflected_univ.{u}] [reflected_univ.{v}]
  {α : Type u} (β : α → Type v)
  [reflected _ α] [reflected _ β] [hα : has_reflect α] [hβ : Π i, has_reflect (β i)] :
  has_reflect (Σ a, β a) :=
λ ⟨a, b⟩, (by reflect_name : reflected _ @sigma.mk.{u v}).subst₄ `(α) `(β) `(a) `(b)

end sigma

section psigma
variables {α : Sort*} {β : α → Sort*}

namespace psigma

/-- Nondependent eliminator for `psigma`. -/
def elim {γ} (f : ∀ a, β a → γ) (a : psigma β) : γ :=
psigma.cases_on a f

@[simp] theorem elim_val {γ} (f : ∀ a, β a → γ) (a b) : psigma.elim f ⟨a, b⟩ = f a b := rfl

instance [inhabited α] [inhabited (β default)] : inhabited (psigma β) :=
⟨⟨default, default⟩⟩

instance [h₁ : decidable_eq α] [h₂ : ∀a, decidable_eq (β a)] : decidable_eq (psigma β)
| ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ := match a₁, b₁, a₂, b₂, h₁ a₁ a₂ with
  | _, b₁, _, b₂, is_true (eq.refl a) :=
    match b₁, b₂, h₂ a b₁ b₂ with
    | _, _, is_true (eq.refl b) := is_true rfl
    | b₁, b₂, is_false n := is_false (assume h, psigma.no_confusion h (λe₁ e₂, n $ eq_of_heq e₂))
    end
  | a₁, _, a₂, _, is_false n := is_false (assume h, psigma.no_confusion h (λe₁ e₂, n e₁))
  end

theorem mk.inj_iff {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂} :
  @psigma.mk α β a₁ b₁ = @psigma.mk α β a₂ b₂ ↔ (a₁ = a₂ ∧ b₁ == b₂) :=
iff.intro psigma.mk.inj $
  assume ⟨h₁, h₂⟩, match a₁, a₂, b₁, b₂, h₁, h₂ with _, _, _, _, eq.refl a, heq.refl b := rfl end

@[ext]
lemma ext {x₀ x₁ : psigma β} (h₀ : x₀.1 = x₁.1) (h₁ : x₀.2 == x₁.2) : x₀ = x₁ :=
by { cases x₀, cases x₁, cases h₀, cases h₁, refl }

lemma ext_iff {x₀ x₁ : psigma β} : x₀ = x₁ ↔ x₀.1 = x₁.1 ∧ x₀.2 == x₁.2 :=
by { cases x₀, cases x₁, exact psigma.mk.inj_iff }

@[simp] theorem «forall» {p : (Σ' a, β a) → Prop} :
  (∀ x, p x) ↔ (∀ a b, p ⟨a, b⟩) :=
⟨assume h a b, h ⟨a, b⟩, assume h ⟨a, b⟩, h a b⟩

@[simp] theorem «exists» {p : (Σ' a, β a) → Prop} :
  (∃ x, p x) ↔ (∃ a b, p ⟨a, b⟩) :=
⟨assume ⟨⟨a, b⟩, h⟩, ⟨a, b, h⟩, assume ⟨a, b, h⟩, ⟨⟨a, b⟩, h⟩⟩

/-- A specialized ext lemma for equality of psigma types over an indexed subtype. -/
@[ext]
lemma subtype_ext {β : Sort*} {p : α → β → Prop} :
  ∀ {x₀ x₁ : Σ' a, subtype (p a)}, x₀.fst = x₁.fst → (x₀.snd : β) = x₁.snd → x₀ = x₁
| ⟨a₀, b₀, hb₀⟩ ⟨a₁, b₁, hb₁⟩ rfl rfl := rfl

lemma subtype_ext_iff {β : Sort*} {p : α → β → Prop} {x₀ x₁ : Σ' a, subtype (p a)} :
  x₀ = x₁ ↔ x₀.fst = x₁.fst ∧ (x₀.snd : β) = x₁.snd :=
⟨λ h, h ▸ ⟨rfl, rfl⟩, λ ⟨h₁, h₂⟩, subtype_ext h₁ h₂⟩

variables {α₁ : Sort*} {α₂ : Sort*} {β₁ : α₁ → Sort*} {β₂ : α₂ → Sort*}

/-- Map the left and right components of a sigma -/
def map (f₁ : α₁ → α₂) (f₂ : Πa, β₁ a → β₂ (f₁ a)) : psigma β₁ → psigma β₂
| ⟨a, b⟩ := ⟨f₁ a, f₂ a b⟩

end psigma

end psigma
